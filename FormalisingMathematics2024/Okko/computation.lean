import Mathlib.tactic


noncomputable section ComputationOkko

variable {state_ alphabet_ : Type}

structure TuringMachine  --[Fintype state_] [Fintype alphabet_]
  where
  -- δ : Q → G → Q × G × Bool
  Q : Finset state_ -- states
  S : Finset alphabet_ -- input
  G : Finset alphabet_ -- tape alphabet plus leftChar and rightChar
  Gz: Zero G
  leftChar : G
  rightChar : G
  δ : Q → G → Q × G × Bool -- transition
  -- δ : state_ → alphabet_ → state_ × alphabet_ × Bool -- transition
  q0 : Q -- start state
  qAcc : Q -- accept state
  qRej : Q -- reject state
  acc_neq_rej : qAcc ≠ qRej
  transition_left {q : Q} : (δ q leftChar).2 = ⟨leftChar,True⟩
  transition_left_r {q : Q} (a): (δ q a).2.1 = leftChar → a = leftChar
  transition_right {q : Q} (a): (δ q a).2.1 = rightChar → (a = rightChar ∧ (δ q a).2.2 = False)
  δ_state (q : Q) (a : G) := (δ q a).1
  δ_alpha (q : Q) (a : G) := (δ q a).2.1
  δ_direction (q : Q) (a : G) := (δ q a).2.2
  rej_loop (a) : δ_state qRej a = qRej

-- def TuringMachine.δ_state (M : @TuringMachine state_ alphabet_) (q : M.Q) (a : M.G) := (M.δ q a).1
-- def TuringMachine.δ_alpha (M : @TuringMachine state_ alphabet_) (q : M.Q) (a : M.G) := (M.δ q a).2.1
-- def TuringMachine.δ_direction (M : @TuringMachine state_ alphabet_) (q : M.Q) (a : M.G) := (M.δ q a).2.2


structure TuringConfiguration (M : @TuringMachine state_ alphabet_) where
  q : M.Q
  tape : ℕ → M.G
  -- tape : ℕ →₀ M.G
  index : ℕ
  -- u : List M.G
  a : M.G := tape index
  -- v : List M.G

def TuringConfiguration.yield {M : @TuringMachine state_ alphabet_} (C : TuringConfiguration M) : TuringConfiguration M where
  q := M.δ_state C.q C.a
  -- tape := C.tape.set C.index (M.δ_alpha C.q C.a)
  tape := fun n ↦ if n = C.index then (M.δ_alpha C.q C.a) else C.tape n
  index := if (M.δ_direction C.q C.a) then C.index + 1 else C.index - 1


def is_leading {X} (f : X → X) (s : ℕ → X) := (∀i, f (s i) = s (i + 1))
def sequence_leads {X} (f : X → X) (a b: X) : Prop := ∃s : ℕ → X, ∃n, (∀i < n, f (s i) = s (i + 1)) ∧ s 0 = a ∧ s n = b


def sequence_leading {X} (f : X → X) (a: X) : ℕ → X
    | 0 => a
    | i + 1 => f (sequence_leading f a i)

theorem sequence_leading_is_leading {X} {f : X → X} {a: X} : is_leading f (sequence_leading f a) := by
  unfold is_leading
  intro i
  rfl



theorem sequence_leading' {X} (f : X → X) (a: X) : ∃!s : ℕ → X, (is_leading f s) ∧ s 0 = a := by
  use sequence_leading f a
  refine ⟨⟨?_,?_⟩,?_⟩
  · unfold is_leading
    intro i
    rfl
  · rfl

  intro s
  simp only [and_imp]
  intro l s0a
  ext i
  induction i with
  | zero =>
    rw [s0a]
    rfl
  | succ i' ih =>
    have := l i'
    rw [←this,ih]
    rfl




def sequence_leading_choose {X} (f : X → X) (a: X) : ℕ → X := (sequence_leading' f a).choose

theorem sequence_leading_spec_A {X} (f : X → X) (a: X) : is_leading f (sequence_leading_choose f a) := (sequence_leading' f a).choose_spec.left.left

theorem sequence_leading_spec_B {X} (f : X → X) (a: X) : (sequence_leading_choose f a) 0 = a := (sequence_leading' f a).choose_spec.left.right


theorem sequence_leading_value {X} (f : X → X) (a: X) : (sequence_leading_choose f a) = sequence_leading f a := by
  -- have t0:= (sequence_leading' f a).choose_spec
  have seqq: ∀ (y : ℕ → X), (fun s ↦ is_leading f s ∧ s 0 = a) y → y = sequence_leading f a := by
    -- copied from above
    intro s
    simp only [and_imp]
    intro l s0a
    ext i
    induction i with
    | zero => exact s0a
    | succ i' ih =>
      rw [←l i',ih]
      rfl
  have := seqq (sequence_leading_choose f a)
  simp only [and_imp] at this
  apply this
  · unfold is_leading
    intro i
    apply sequence_leading_spec_A
  apply sequence_leading_spec_B



-- theorem sequence_leading_unique {X} (f : X → X) (a: X) (s) : (is_leading f s) ∧ s 0 = a ↔ s = sequence_leading f a := by sorry
-- theorem sequence_leading_unique' {X} (f : X → X) (a: X) (s) : (is_leading f s) → s 0 = a → s = sequence_leading f a := by sorry



theorem sequence_leads_iff {X} (f : X → X) (a b: X) : sequence_leads f a b ↔ ∃n, sequence_leading_choose f a n = b := by
  constructor
  · intro ⟨ab_s,ab_n,ab_yield,ab_0,ab_1⟩
    use ab_n
    rw [←ab_1]
    have : ∀ i ≤ ab_n, sequence_leading_choose f a i = ab_s i := by
      intro i i_le
      induction i with
      | zero => rw [sequence_leading_spec_B,ab_0]
      | succ i' ih =>
        have prev := ih (by linarith )
        have t1:= sequence_leading_spec_A f a i'
        have t2:= ab_yield i' (by linarith)
        exact (prev ▸ t1) ▸ t2
    exact this ab_n (by linarith only)
  · intro ⟨n,w⟩
    refine ⟨(sequence_leading_choose f a), n, ?_,?_,?_⟩
    · intro i _
      exact sequence_leading_spec_A ..
    · exact sequence_leading_spec_B ..
    · exact w


@[trans]
theorem leads_trans {X} (f : X → X) (a b c: X) : sequence_leads f a b → sequence_leads f b c → sequence_leads f a c := by

  intro ⟨ab_s,ab_n,ab_yield,ab_0,ab_1⟩ ⟨bc_s,bc_n,bc_yield,bc_0,bc_1⟩
  -- use fun i ↦ if i < ab_n then ab_s i else bc_s (i - ab_n)
  -- use (ab_n + bc_n)
  refine ⟨fun i ↦ if i ≤ ab_n then ab_s i else bc_s (i - ab_n), (ab_n + bc_n), ?_,?_,?_⟩
  ·
    intro i i_lt
    simp
    by_cases h : i = ab_n
    {
      simp [h]
      simp [ab_1]
      simp [←bc_0]
      exact bc_yield 0 (by linarith)
    }
    by_cases h1 : i < ab_n
    {
      have h1' : i + 1 ≤ ab_n := by linarith
      simp [h1.le,h1']
      exact ab_yield i h1
    }
    simp at h1
    have hh: ab_n < i := Ne.lt_of_le' h h1
    have hw : ab_n < i + 1 := by linarith
    simp [hh.not_le]
    simp [hw.not_le]
    have := bc_yield (i - ab_n) (by {
      rw [propext (tsub_lt_iff_left h1)]
      exact i_lt
    })
    rw [this]
    apply congrArg
    exact tsub_add_eq_add_tsub h1

  ·
    simp only [zero_le, ge_iff_le, tsub_eq_zero_of_le, ite_true]
    exact ab_0
  ·
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, add_tsub_cancel_left]
    by_cases h : bc_n = 0
    {
      simp only [h, add_zero, ite_true]
      rw [ab_1, ←bc_1, h, bc_0]
    }
    simp [h]
    exact bc_1

theorem leads_self {X} (f : X → X) (a: X) : sequence_leads f a a := by

  rw [sequence_leads_iff]
  use 0
  rw [sequence_leading_value]
  rfl





def TuringConfiguration.leads {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) (b : TuringConfiguration M) : Prop :=
    sequence_leads TuringConfiguration.yield a b

def TuringConfiguration.acceptsImmediate {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  a.q = M.qAcc

def TuringConfiguration.rejectsImmediate {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  a.q = M.qRej

def TuringConfiguration.rejects_leads {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  ∃b, b.rejectsImmediate ∧ a.leads b

def TuringConfiguration.accepts {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  ∃b, b.acceptsImmediate ∧ a.leads b


theorem TuringConfiguration.rejects_of_leads_rej {M : @TuringMachine state_ alphabet_} (C : TuringConfiguration M) :
    C.rejects_leads → ¬ C.accepts := by
  intro ⟨rej,r_q,⟨rs,rn,r_yield,r0,r1⟩⟩
  intro ⟨acc,a_q,⟨as,an,a_yield,a0,a1⟩⟩
  have : ∀ i, i ≤ an → i ≤ rn → as i = rs i := by
    intro i ian irn
    induction i with
    | zero => rw [a0, r0]
    | succ i' ih =>
      have prev := ih (by linarith only [ian]) (by linarith only [irn])
      have t1 := a_yield i' (by linarith only [ian])
      have t2 := r_yield i' (by linarith only [irn])
      exact (prev ▸ t1) ▸ t2




  sorry


end ComputationOkko
