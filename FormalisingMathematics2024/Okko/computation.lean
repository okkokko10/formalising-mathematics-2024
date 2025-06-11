import Mathlib.tactic


noncomputable section ComputationOkko


section lead


def sequence_leading {X} (f : X → X) (a: X) : ℕ → X
    | 0 => a
    | i + 1 => f (sequence_leading f a i)

def is_leading {X} (f : X → X) (s : ℕ → X) := (∀i, f (s i) = s (i + 1))
theorem is_leading_def {X} {f : X → X} {s : ℕ → X} : is_leading f s ↔ (∀i, f (s i) = s (i + 1)) := by rfl
def is_leading_limited {X} (f : X → X) (n : ℕ) (s : ℕ → X) := (∀i < n, f (s i) = s (i + 1))
theorem is_leading_limited_def {X} {f : X → X} {n : ℕ} {s : ℕ → X} : is_leading_limited f n s ↔ (∀i < n, f (s i) = s (i + 1)) := by rfl

theorem is_leading_then_limited {X} {f : X → X} {s : ℕ → X} (h : is_leading f s) (n : ℕ) : is_leading_limited f n s := by
  refine is_leading_limited_def.mpr ?_
  intro i _
  exact h i


def leads {X} (f : X → X) (a b: X) : Prop := ∃n, sequence_leading f a n = b
theorem leads_def {X} {f : X → X} {a b: X} : leads f a b ↔ ∃n, sequence_leading f a n = b := by rfl

@[simp]
theorem sequence_leading_succ {X} {f : X → X} {a: X} {i : ℕ} : sequence_leading f a (i + 1) = f (sequence_leading f a i) := by rfl
@[simp]
theorem sequence_leading_zero {X} {f : X → X} {a: X} : sequence_leading f a 0 = a := by rfl


theorem sequence_leading_tail {X} {f : X → X} {a: X} (n : ℕ) {i : ℕ} :
    (sequence_leading f a) (n + i) = sequence_leading f (sequence_leading f a n) i := by
  induction i with
  | zero =>
    dsimp only [Nat.zero_eq, Nat.add_zero]
    simp only [sequence_leading_zero]
  | succ i' hi =>
    simp only [sequence_leading_succ]
    rw [← hi]
    simp only [←sequence_leading_succ]
    apply congrArg
    rfl



theorem sequence_leading_is_leading {X} {f : X → X} {a: X} : is_leading f (sequence_leading f a) := by
  rw [is_leading_def]
  intro i
  rfl


theorem is_leading_eq_sequence_leading {X} {f : X → X} {s : ℕ → X} (h : is_leading f s) : s = sequence_leading f (s 0) := by
  rw [is_leading_def] at h
  ext i
  induction i with
  | zero =>
    exact sequence_leading_zero.symm
  | succ i' hi =>
    rw [←h]
    rw [hi]
    exact sequence_leading_succ


theorem is_leading_limited_eq_sequence_leading {X} {f : X → X} {n : ℕ} {s : ℕ → X} (h : is_leading_limited f n s) : ∀i ≤ n, s i = sequence_leading f (s 0) i := by
  intro i i_n
  rw [is_leading_limited_def] at h
  induction i with
  | zero =>
    exact sequence_leading_zero.symm
  | succ i' hi =>
    rw [sequence_leading_succ]
    have : i' <  n := (by linarith only [i_n])
    specialize hi this.le
    rw [←hi]
    specialize h i' this
    rw [←h]


theorem leads_alt_def {X} {f : X → X} {a b : X} : leads f a b ↔ (∃s : ℕ → X, ∃n, is_leading_limited f n s ∧ s 0 = a ∧ s n = b) := by
  rw [leads_def]
  constructor
  ·
    intro ⟨n,w⟩
    use (sequence_leading f a)
    use n
    refine ⟨?_,?_,?_⟩
    intro i _
    exact sequence_leading_succ
    exact sequence_leading_zero
    exact w
  ·
    intro ⟨s,n,w1,s0a,snb⟩
    use n
    have := is_leading_limited_eq_sequence_leading w1 n (by rfl)
    rw [s0a,snb] at this
    rw [this]








section old_sequence_leading_choose


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



theorem sequence_leads_iff' {X} (f : X → X) (a b: X) : leads f a b ↔ ∃n, sequence_leading_choose f a n = b := by
  constructor
  ·
    simp_rw [leads_alt_def]

    intro ⟨ab_s,ab_n,ab_yield,ab_0,ab_1⟩
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

    simp_rw [leads_alt_def]
    refine ⟨(sequence_leading_choose f a), n, ?_,?_,?_⟩
    · intro i _
      exact sequence_leading_spec_A ..
    · exact sequence_leading_spec_B ..
    · exact w

end old_sequence_leading_choose

@[trans]
theorem leads_trans {X} (f : X → X) (a b c: X) : leads f a b → leads f b c → leads f a c := by
  simp_rw [leads_def]
  intro ⟨an,fab⟩ ⟨bn,fbc⟩
  use (an + bn)
  rw [sequence_leading_tail]
  rw [fab,fbc]
  done


theorem leads_self {X} (f : X → X) (a: X) : leads f a a := by
  rw [leads_def]
  use 0
  exact sequence_leading_zero



-- structure sequence_le {X} (f : X → X) extends LE X, Preorder X where
  -- toLE := leads
  -- le := leads f
  -- le_refl (x : X) :=
  --   sorry
    --leads_self f
  -- le_trans := sorry





end lead



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



def TuringConfiguration.leads' {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) (b : TuringConfiguration M) : Prop :=
    leads TuringConfiguration.yield a b

def TuringConfiguration.acceptsImmediate {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  a.q = M.qAcc

def TuringConfiguration.rejectsImmediate {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  a.q = M.qRej

def TuringConfiguration.rejects_leads {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  ∃b, b.rejectsImmediate ∧ a.leads' b

def TuringConfiguration.accepts {M : @TuringMachine state_ alphabet_} (a : TuringConfiguration M) : Prop :=
  ∃b, b.acceptsImmediate ∧ a.leads' b


theorem TuringConfiguration.rejects_of_leads_rej {M : @TuringMachine state_ alphabet_} (C : TuringConfiguration M) :
    C.rejects_leads → ¬ C.accepts := by
  unfold rejects_leads accepts leads'
  simp_rw [leads_alt_def]
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
