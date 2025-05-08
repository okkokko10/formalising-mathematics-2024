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

structure InnerProduct (X : Type) [AddCommGroup X] [Module ℝ X] where
  toFun : X → X → ℝ
  positive_definitenessA : ∀(x : X), 0 ≤ toFun x x
  positive_definitenessB : ∀(x : X), x = 0 ↔ toFun x x = 0
  symmetry : ∀(x y), toFun x y = toFun y x
  bilinearity : ∀ (a b : ℝ) (x y z : X),
    (toFun ((a • x) + (b • y)) z)
    = a * (toFun x z) + b * (toFun y z)

variable {X Y Z : Type} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]

-- instance : CoeFun (InnerProduct X) (fun _ ↦ X → X → ℝ) where
--   coe w := w.toFun

instance : CoeFun (InnerProduct X) (fun _ ↦ X → X → ℝ) where
  coe w := w.toFun

def InnerProduct.bilinearMapRight (prod : InnerProduct X) (a : X) : (X →ₗ[ℝ] ℝ) where
  toFun := fun b ↦ (prod a b)
  map_add' := by
    intro x y
    simpa [prod.symmetry a _, one_smul, one_mul] using prod.bilinearity 1 1 x y a
  map_smul' := by
    intro r x
    simpa [prod.symmetry a _, RingHom.id_apply, smul_eq_mul, smul_zero, add_zero,
      zero_mul] using prod.bilinearity r 0 x 0 a

def InnerProduct.toBilinearMap (prod : InnerProduct X) : (X →ₗ[ℝ] X →ₗ[ℝ] ℝ) := {
    toFun := prod.bilinearMapRight
    map_add' := by
      intro x y
      ext v
      simpa only [LinearMap.add_apply, one_smul, one_mul] using prod.bilinearity 1 1 x y v
    map_smul' := by
      intro r x
      ext v
      simpa only [RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul, smul_zero, add_zero,
        zero_mul] using prod.bilinearity r 0 x 0 v
    }

instance : Coe (InnerProduct X) (X →ₗ[ℝ] X →ₗ[ℝ] ℝ) where
  coe w : (X →ₗ[ℝ] X →ₗ[ℝ] ℝ) := w.toBilinearMap

-- @[simp]
theorem InnerProduct.bilinear_ext {prod : InnerProduct X} (x y): prod x y = prod.toBilinearMap x y := rfl

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



noncomputable def dot : InnerProduct (N → ℝ) where
  toFun := dotProduct
  positive_definitenessA := positive_definitenessA
  positive_definitenessB := positive_definitenessB
  symmetry  := symmetry
  bilinearity := bilinearity


lemma linearity (a : ℝ) (x y : (N → ℝ)) :
  (dotProduct (a • x) y) = a * (dotProduct x y) := by
  have := bilinearity a 0 x 0 y
  simp only [smul_zero, add_zero, smul_eq_mul, zero_mul] at this
  exact this


theorem InnerProduct.linearity (prod : InnerProduct X) (a : ℝ) (x y : X) :
  (prod (a • x) y) = a * (prod x y) := by
  have := prod.bilinearity a 0 x 0 y
  simp only [smul_zero, add_zero, smul_eq_mul, zero_mul] at this
  exact this

/--the matrix x yᵀ-/
def mul_transpose (x y : (N → ℝ)) : (N → ℝ) → (N → ℝ) :=
  (fun (v : (N → ℝ)) ↦ ((dotProduct y v)) • x)



/--the matrix x yᵀ-/
def InnerProduct.matrix (prod : InnerProduct Y) (x : X) (y : Y) : Y →ₗ[ℝ] X where
  toFun := (prod y · • x)
  map_add' := by
    intro a b
    simp only

    simp_rw [prod.symmetry y]
    rw [←Module.add_smul]
    have := prod.bilinearity 1 1 a b y
    simp only [one_smul, one_mul] at this
    rw [this]
  map_smul' := by
    intro r z
    simp only [RingHom.id_apply]
    have := prod.bilinearity r 0 z 0 y
    simp [prod.symmetry] at this
    rw [this]
    exact mul_smul r (prod y z) x

@[simp]
theorem InnerProduct.matrix_fun (prod : InnerProduct Y) (x : X) (y : Y) : prod.matrix x y = (prod y · • x) := rfl


/--xaᵀ bzᵀ = aᵀb * xzᵀ -/
theorem InnerProduct.matrix_comp {prodY : InnerProduct Y} {prodZ : InnerProduct Z} {x : X} {a b : Y} {z : Z} :
    (prodY.matrix x a) ∘ₗ (prodZ.matrix b z) = (prodY a b) • (prodZ.matrix x z) := by
  ext v
  -- rewrite [LinearMap.comp_apply]
  -- simp only [LinearMap.smul_apply]
  -- rw [mul_transpose]
  simp only [LinearMap.coe_comp, matrix_fun, Function.comp_apply, LinearMap.smul_apply]
  simp only [InnerProduct.bilinear_ext]
  rw [map_smul,← smul_assoc, smul_eq_mul, mul_comm, smul_eq_mul]
  done

def InnerProduct.rowVector (prod : InnerProduct X) (x : X) : (X →ₗ[ℝ] ℝ) := prod.matrix (1 : ℝ) x

-- @[simp]
theorem InnerProduct.rowVector_eq (prod : InnerProduct X) (x : X) : prod x = prod.rowVector x := by
  ext v
  unfold rowVector
  simp only [matrix_fun, smul_eq_mul, mul_one]


-- todo: coercion
instance RealProduct : InnerProduct ℝ where
  toFun := (· * ·)
  positive_definitenessA := by exact fun x ↦ mul_self_nonneg x
  positive_definitenessB := by exact fun x ↦ Iff.symm mul_self_eq_zero
  symmetry := by exact fun x y ↦ mul_comm x y
  bilinearity := by
    intros
    simp only [smul_eq_mul]
    ring


/-- all inner products of ℝ are like this-/
example : ∀(d : InnerProduct ℝ),∃e > 0, d.toFun =  ( · * · * e) := by
  intro d
  use (d 1 1)
  constructor
  · rw [gt_iff_lt]
    have dA:= d.positive_definitenessA 1
    have dB:= d.positive_definitenessB 1
    simp only [one_ne_zero, false_iff] at dB
    exact Ne.lt_of_le' dB dA
  ext a b
  simp_rw [d.bilinear_ext]
  nth_rw 1 [←mul_one a,←mul_one b]
  simp_rw [←smul_eq_mul,map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

def InnerProduct.columnVector (x : X) : (ℝ →ₗ[ℝ] X) := RealProduct.matrix x (1 : ℝ)

instance : Coe X (ℝ →ₗ[ℝ] X) where
  coe x := InnerProduct.columnVector x


theorem InnerProduct.asMatrices {prod : InnerProduct X} {x y : X} :
    prod x y = prod.rowVector x ∘ₗ InnerProduct.columnVector y := by
  ext
  simp
  unfold columnVector
  simp only [matrix_fun, rowVector_eq, smul_eq_mul, map_smul]

-- def InnerProduct.vector_transpose {x : X}


-- theorem InnerProduct.makeMatrix (prod : InnerProduct Y) (mat : Y →ₗ[ℝ] X) :
--   prod.matrix x y = (prod y · • x)

-- /-- xᵀAᵀ = (Ax)ᵀ -/
theorem InnerProduct.transpose_exists (prodX : InnerProduct X) (prodY : InnerProduct Y) (mat : X →ₗ[ℝ] Y) :
    ∃ (matT : Y →ₗ[ℝ] X), ∀x, (prodX.rowVector x) ∘ₗ matT = prodY.rowVector (mat x) := by



  sorry

-- def InnerProduct.transpose (prod : InnerProduct X) (mat : Y →ₗ[ℝ] X) :  X →ₗ[ℝ] Y :=




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

section Excercise3




end Excercise3
