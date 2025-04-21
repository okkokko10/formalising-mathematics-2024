import Mathlib.tactic



noncomputable section Excercise1

/-
Excercise Sheet 1
4. Let 0 ≠ a,b ∈ ℝⁿ and define A = abᵀ ∈ ℝⁿˣⁿ
(a) R(A) = span{a}
(b) N(A) = {x ∈ ℝⁿ | bᵀx = 0}

-/

variable {N : Type} [Fintype N] [Finite N] [DecidableEq N]

-- variable [AddCommMonoid (N → ℝ)] [AddCommGroup (N → ℝ)] [Module ℝ (N → ℝ)]

open BigOperators

/-- x y ↦ xᵀy -/
def dotProduct : (N → ℝ) → (N → ℝ) → ℝ := fun x y ↦ ∑ n, (x n) * (y n)


lemma positive_definiteness_lemma (x : (N → ℝ)) (subset : Finset N) :
  0 ≤ ∑ n in subset, x n * x n := by
  set f := (fun (n) ↦ x n * x n)
  let p (s) := 0 ≤ ∑ i in s, f i
  have empty : p ∅ := by exact Eq.le rfl
  classical
    refine subset.induction_on (empty) ?_
    intro a s ans previous
    rw [Finset.sum_insert ans]
    have xaxa_nonneg : 0 ≤ x a * x a  := mul_self_nonneg (x a)
    exact add_nonneg xaxa_nonneg previous

-- ### definition 2.2
theorem positive_definitenessA (x : (N → ℝ)) : 0 ≤ dotProduct x x := by
  unfold dotProduct
  exact positive_definiteness_lemma x Finset.univ

theorem positive_definitenessB (x : (N → ℝ)) : x = 0 ↔ dotProduct x x = 0 := by
  unfold dotProduct
  constructor
  · intro x0
    simp only [x0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · intro d0
    by_contra nonzero
    have ⟨i,nonzero_at_i⟩  : ∃n, x n ≠ 0 := by exact Function.ne_iff.mp nonzero
    set f := (fun (n) ↦ x n * x n)
    have taken := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
    rw [d0] at taken

    suffices 0 ≤ ∑ x in Finset.erase Finset.univ i, f x by{
      have positive_i : 0 < f i := by
        simp only [mul_self_pos, ne_eq]
        exact nonzero_at_i
      linarith
      }
    exact positive_definiteness_lemma x (Finset.erase Finset.univ i)
theorem symmetry (x y : (N → ℝ)) : dotProduct x y = dotProduct y x := by
  unfold dotProduct
  conv => left; right; intro n; rw [mul_comm]
  done

theorem bilinearity (a b : ℝ) (x y z : (N → ℝ)) :
    (dotProduct ((a • x) + (b • y)) z)
    = a * (dotProduct x z) + b * (dotProduct y z) := by
  unfold dotProduct
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp [Finset.mul_sum,←Finset.sum_add_distrib]
  suffices ∀n, (a * x n + b * y n) * z n = a * (x n * z n) + b * (y n * z n) by
    simp_rw [this]
  intro n
  ring



lemma linearity (a : ℝ) (x y : (N → ℝ)) :
  (dotProduct (a • x) y) = a * (dotProduct x y) := by
  have := bilinearity a 0 x 0 y
  simp only [smul_zero, add_zero, smul_eq_mul, zero_mul] at this
  exact this



/--the matrix x yᵀ-/
def mul_transpose (x y : (N → ℝ)) : (N → ℝ) → (N → ℝ) :=
  (fun (v : (N → ℝ)) ↦ ((dotProduct y v)) • x)

/-- span {x}-/
def singleton_span (x : (N → ℝ)) := Set.range (fun (t : ℝ) ↦ t • x)

/-- N(A) -/
def nullspace (A : (N → ℝ) → (N → ℝ)) := {v | A v = 0}

variable (a b : (N → ℝ))

variable (ha : a ≠ 0) (hb : b ≠ 0)

-- excercise 4a
-- range A = span {a}
example : Set.range (mul_transpose a b) = singleton_span a := by
  ext p
  unfold singleton_span mul_transpose
  simp only [Set.mem_range]
  rw [← @exists_exists_eq_and _ _ (dotProduct b ·) (· • a = p)]
  -- ⊢ (∃ y, (∃ w, dotProduct b w = y) ∧ a • y = p) ↔ ∃ y, a • y = p
  suffices (∀y, (∃ w, dotProduct b w = y)) by {
    simp only [this,true_and]
  }

  intro y
  set q := dotProduct b b with q_def
  have q_nonzero : q ≠ 0 := by
    rw [ne_eq, q_def, ←positive_definitenessB]
    exact hb
  have spec_w (t) : dotProduct b ((t / q) • b) = t := by
    rw [symmetry, linearity, ←q_def]
    exact div_mul_cancel t q_nonzero

  use ((y / q) • b)
  exact spec_w y

-- excercise 4b
-- N(A) = {x | bᵀx = 0}
example : nullspace (mul_transpose a b) = {v | dotProduct b v = 0} := by
  unfold nullspace mul_transpose
  -- ⊢ {v | dotProduct b v • a = 0} = {v | dotProduct b v = 0}
  ext v
  simp_rw [Set.mem_setOf_eq]
  set p := dotProduct b v
  rw [smul_eq_zero, or_iff_left_iff_imp]
  intro a0
  exfalso
  exact ha a0

end Excercise1
