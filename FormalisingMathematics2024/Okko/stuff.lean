import Mathlib.tactic



-- theorem matrix_dot_exchange
--   {A B F iA iB iF C : Type}
--   {a : iA → A} {b : iB → B}
--   [Fintype iA] [Fintype iB] [Fintype iF]
--   {Hfb : (iF → F) → (iB → B) → C }
--   {Haf : (iA → A) → (iFt → Ft) → C }
--   {f : (iA → A) → (iF → F) }
--   {}
--   :


example --matrix_dot_exchange
  {A B C : Type}
  {X Y : Type}
  {sX : Finset X}
  {sY : Finset Y}
  {a : Y → A} {b : X → B}
  [Fintype Y] [Fintype X]
  [AddCommMonoid (X → B)]
  [AddCommMonoid C]
  {H : B → B → C }
  [HAdd B B B]
  {Ht : A → A → C }
  {F  : (Y → A) → (X → B) }
  {Ft : (X → B) → (Y → A) }
  (H_ldistr : ∀(x y z), H (x + y) z = H x z + H y z)
  (H_rdistr : ∀(x y z), H x (y + z) = H x y + H x z)
  :
    Finset.sum sX (fun x ↦ H (F a x) (b x)) =
    Finset.sum sY (fun y ↦ Ht (a y) (Ft b y))

    :=
    by
      sorry



section Theory_of_Computation_9

#check Countable

def countable {S : Type} (X : Set S) : Prop := ∃ f : ℕ → S, Set.range f = X

-- def countable {S : Type} (X : Set S) : Prop := ∃ f : ℕ → X, Function.Surjective f


def injective {S T : Type} (f : S → T) (X : Set S) : Prop := ∀ a b, a ∈ X → b ∈ X → f a = f b → a = b

#check Function.Surjective

def countably_infinite {S : Type} (X : Set S) : Prop := ∃ f : ℕ → X, Function.Bijective f

theorem countable' {S : Type} {X : Set S} : countable X ↔ ∃ g : S → ℕ, injective g X := by
  constructor

  intro cou
  have ⟨f,f_surj⟩ := cou
  unfold injective
  simp [Set.range] at f_surj
  have f_surj2 (x) :  x ∈ X ↔ (∃ y, f y = x)  := by simp only [← f_surj, Set.mem_setOf_eq]

  -- if there is a function f : ℕ → S, there exists an injecion g from a subset of ℕ to S with all the duplicates removed
  -- if f is a surjection, then g is a bijection.

  -- have hg : ∃ g : S → ℕ,

  sorry

  sorry


/-
If A is a countably infinite set, then it has only countable subsets, i.e.
if B ⊆ A, then B is either finite or countably infinite.
-/
theorem countable_subset_countable {S : Type} {A : Set S} : countable A →  ∀B ⊆ A, countable B := by

  intro h B B_subset_A

  have ⟨g,g_inj⟩ := countable'.mp h

  rw [countable']
  use g
  rw [injective] at *
  -- have subs (x) : x ∈ B → x ∈ A := by exact fun a ↦ B_subset_A a



  intro a b aB bB
  exact g_inj a b (B_subset_A aB) (B_subset_A bB)

  done



/-
If A is an uncountable set, then it has both uncountable and countably
infinite subsets.
-/
theorem uncountable_has_uncountable_subset {S : Type} {A : Set S} :  ¬ countable A → ∃ B ⊆ A, ¬ countable B := by

  intro uncA
  use A


  -- have : ∃ a, a∈ A :=
  -- by_contra cont

  -- simp at cont

  -- have  := countable_subset_countable

  -- simp at uncA





  done




-- def countably_infinite {S : Type} (X : Set S) : Prop := ∃ f : ℕ → S, Set.range f = X


-- theorem uncountable_has_countably_infinite_subset {S : Type} {A : Set S} :  ¬ countable A → ∃ B ⊆ A, countable B ∧ Set.Infinite B := by

theorem uncountable_has_countably_infinite_subset {S : Type} {A : Set S} :  ¬ countable A → ∃ B ⊆ A, countably_infinite B := by

  intros unc_A

  have nemA : Set.Nonempty A := sorry

  let w := Classical.choice nemA

  -- have ff : ∃ f : ℕ → S, True := by


  sorry
  done


end Theory_of_Computation_9



example (a b c d e f g N : Prop) : (b ∨ a) ∨ (c ∨ d) ∨ (e ∨ f) ∨ g → c := by

  intro long
  -- rw [or_comm] at long
  -- convert_to
  simp only [or_assoc] at long
  norm_num

  done
