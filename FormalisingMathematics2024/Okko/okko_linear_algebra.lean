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


section Excercise10

#check Matrix


#check InnerProductSpace.norm_sq_eq_inner

#check inner_self_eq_norm_sq_to_K

#check bilinearity

example {n : ℕ} {M : Type} [NormedAddCommGroup M] [Module ℝ M] [InnerProductSpace ℝ M]
    (y b : M) (y0 : y ≠ 0) (b0 : b ≠ 0) (β : ℝ) :
    @IsROrC.ofReal ℝ Real.isROrC ‖ (⟪y, b ⟫_ℝ / ⟪y, y⟫_ℝ) • y - b‖ ^ 2 ≤ @IsROrC.ofReal ℝ Real.isROrC ‖β • y - b‖ ^ 2 := by

  set α := (⟪y, b ⟫_ℝ / ⟪y, y⟫_ℝ) with a_def
  -- simp_rw [inner_self_eq_norm_sq_to_K y]

  rw [←inner_self_eq_norm_sq_to_K]
  rw [←inner_self_eq_norm_sq_to_K]
  simp_rw [@real_inner_sub_sub_self]


  sorry

-- can you make an orthonormal basis always?

open BigOperators

variable {V : Type} [NormedAddCommGroup V] [Module ℝ V]
variable {N : Type} [Fintype N] [DecidableEq N]
variable {N' : Type} [Fintype N'] [DecidableEq N']

def apply_basis (bas : N → V) (c : N → ℝ) := ∑ i : N, c i • bas i

def apply_basis' (bas : N → V) : (N → ℝ) →ₗ[ℝ] V where
  toFun := apply_basis bas
  map_add' := by
    intro x y
    unfold apply_basis
    rw [←Finset.sum_add_distrib]
    simp_rw [←add_smul]
    rfl
  map_smul' := by
    intro r c
    simp only [RingHom.id_apply]
    unfold apply_basis
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply congrArg
    ext x
    exact mul_smul r (c x) (bas x)


def apply_basis_left (c : N → ℝ) : (N → V) →ₗ[ℝ] V where
  toFun := (apply_basis · c)
  map_add' := by
    intro x y
    unfold apply_basis
    rw [←Finset.sum_add_distrib]
    simp only [Pi.add_apply, smul_add]
  map_smul' := by
    intro r y
    simp only [RingHom.id_apply]
    unfold apply_basis
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply congrArg
    ext x
    exact smul_algebra_smul_comm r (c x) (y x)

@[simp]
theorem coe_apply_basis' {bas : N → V} {c : N → ℝ} : apply_basis bas c = apply_basis' bas c := by rfl

-- @[simp]
theorem coe_apply_basis_left {bas : N → V} {c : N → ℝ} : apply_basis bas c = apply_basis_left c bas := by rfl
theorem coe_apply_basis_left' {bas : N → V} {c : N → ℝ} : apply_basis' bas c = apply_basis_left c bas := by rfl


-- is x a linear combination of bas.
def hasBasis (bas : N → V) (x : V) := ∃ c : N → ℝ, x = apply_basis bas c

def linearIndependence (bas : N → V) := ∀ c : N → ℝ, c = 0 ↔ 0 = apply_basis bas c

def orthogonalPair {N1 : Type} (product : V → V → ℝ) (bas : N1 → V) (a b : N1) := a ≠ b → product (bas a) (bas b) = 0
def orthogonal {N1 : Type} (product : V → V → ℝ) (bas : N1 → V) := ∀a b : N1, orthogonalPair product bas a b

def normal {N1 : Type} (product : V → V → ℝ) (bas : N1 → V) := ∀a : N1, product (bas a) (bas a) = 1

def BasisShiftAdd (bas : N → V) (i j : N) (r : ℝ) := (fun k : N ↦ bas k + if k = i then  r • bas j else 0)

def BasisShiftScale (bas : N → V) (i : N) (r : ℝ) := (fun k : N ↦ (if k = i then r else 1) • bas k)

def WithBasis (bas : N → V) (X : Subspace ℝ V) := ∀x, x ∈ X ↔ hasBasis bas x

-- unsure
theorem withBasis_eq_iff_hasBasis_eq (bas1 bas2 : N → V) : (hasBasis bas1 = hasBasis bas2) ↔ (WithBasis bas1 = WithBasis bas2) := by
  unfold WithBasis
  constructor
  · intro h
    rw [h]
  · intro h
    simp at h
    -- have qq(X) : ∀ (x : V), x ∈ X ↔ hasBasis bas1 x
    sorry

theorem basisContainsItself (bas : N → V) (i : N) : hasBasis bas (bas i) := by

  use (fun k : N ↦ if k = i then 1 else 0)
  unfold apply_basis
  simp [ite_zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  done

theorem basisContainsApplications (bas : N → V) (c : N → ℝ) : hasBasis bas (apply_basis bas c) := by
  unfold hasBasis
  tauto

def Irow (i : N) := fun k ↦ if k = i then (1 : ℝ) else 0

theorem basis_Irow (bas : N → V) (i : N) : bas i = apply_basis bas (Irow i) := by
  unfold Irow apply_basis
  simp [ite_zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem Irow_assoc {i : N} {u : N → ℝ} : (fun k : N ↦ if k = i then u k else (0)) = (u i) • (Irow i) := by
  ext k
  unfold Irow
  simp
  aesop


-- (lb1 : linearIndependence bas1) (lb2 : linearIndependence bas2)
theorem basisLE (bas1 : N → V) (bas2 : N' → V) :
    (hasBasis bas1 ≤ hasBasis bas2) ↔ ∀ i : N, hasBasis bas2 (bas1 i) := by

  rw [@Pi.le_def]
  constructor
  intro le i
  specialize le (bas1 i)
  exact le (basisContainsItself _ _)
  intro h x
  intro ⟨c,cx⟩
  unfold hasBasis at h ⊢
  have (i : N) : bas1 i = ∑ j : N', (h i).choose j • bas2 j := by
    exact (h i).choose_spec

  unfold apply_basis at *
  simp_rw [this] at cx
  simp_rw [Finset.smul_sum] at cx
  rw [@Finset.sum_comm] at cx
  simp_rw [← smul_assoc] at cx
  simp_rw [←Finset.sum_smul] at cx
  rw [cx]
  use (fun x ↦ ∑ i : N, c i • Exists.choose (h i) x)

theorem basisEQ (bas1 bas2 : N → V)  :
    (hasBasis bas1 = hasBasis bas2) ↔ ((∀ i : N, hasBasis bas2 (bas1 i)) ∧ ∀ i : N, hasBasis bas1 (bas2 i)) := by
  simp [←basisLE]
  exact le_antisymm_iff

lemma BasisShiftAdd_same (bas : N → V) {i j : N} (hij : i ≠ j) (r : ℝ) :
    hasBasis (BasisShiftAdd bas i j r) = hasBasis bas := by
  rw [basisEQ _ _]
  unfold hasBasis
  unfold BasisShiftAdd
  unfold apply_basis
  constructor
  ·
    intro k

    split
    ·
      use (fun jj ↦ (if jj = k then 1 else 0) + (if jj = j then r else 0))
      simp_rw [add_smul]
      rw [Finset.sum_add_distrib]
      simp only [ite_zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · use (fun jj ↦ if jj = k then 1 else 0)
      simp [ite_zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · intro k
    simp only [smul_add, smul_ite_zero]
    simp_rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

    by_cases h : k = i
    ·
      rw [h]
      use (fun x ↦ if x = j then -r else 0) + (fun x ↦ if x = i then 1 else 0)
      simp
      simp [hij]
      simp_rw [add_smul]
      simp_rw [Finset.sum_add_distrib]
      simp [ite_zero_smul, neg_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_smul,
        neg_add_cancel_comm]
    ·
      use (fun x ↦ if x = k then 1 else 0)
      simp
      intro ik
      exact (h ik.symm).elim

lemma BasisShiftScale_same (bas : N → V) (i : N) {r : ℝ} (hr : r ≠ 0) :
    hasBasis (BasisShiftScale bas i r) = hasBasis bas := by
  rw [basisEQ _ _]
  unfold hasBasis
  unfold BasisShiftScale
  unfold apply_basis
  constructor
  · intro k
    split
    ·
      use (fun q : N ↦ (if q = k then r else 0))
      simp
    · use (fun q : N ↦ (if q = k then 1 else 0))
      simp

  · intro k
    let w := if k = i then r⁻¹ else 1
    use (fun q : N ↦ (if q = k then w else 0))
    simp
    aesop

lemma BasisShiftScale_linInd (bas : N → V) (lb : linearIndependence bas) (i : N) {r : ℝ}  (hr : r ≠ 0) : linearIndependence (BasisShiftScale bas i r) := by

  sorry

lemma BasisShiftAdd_linInd (bas : N → V) (lb : linearIndependence bas) {i j : N} (hij : i ≠ j) (r : ℝ) :
    linearIndependence (BasisShiftAdd bas i j r) := by

  sorry


-- (hc : c i ≠ 0)
def BasisShiftFree (bas : N → V) (i : N) (c : N → ℝ) := fun k : N ↦ (if k = i then apply_basis bas c else bas k)

-- lemma BasisShiftFree_same
example (bas : N → V) (i : N) (c : N → ℝ) (hc : c i ≠ 0) :
    hasBasis (BasisShiftFree bas i c) = hasBasis bas := by
  rw [basisEQ _ _]
  unfold hasBasis
  unfold BasisShiftFree
  unfold apply_basis
  simp only
  constructor
  · intro k
    split
    {
      use c
    }
    {
      use (fun q : N ↦ (if q = k then 1 else 0))
      simp
    }
  · intro k

    by_cases h : k = i
    {
      rw [h]
      have (x): (if x = i then ∑ i : N, c i • bas i else bas x) = ((if x = i then ∑ i : N, c i • bas i else 0) + if x = i then 0 else bas x) := by
        aesop
      simp_rw [this]
      simp
      simp_rw [Finset.sum_add_distrib]
      simp
      have (x): (if x = i then 0 else bas x) = bas x - if x = i then bas x else 0 := by sorry
      simp [this]
      simp [smul_sub]

      suffices ∃ c_1 : N → ℝ, bas i = c_1 i • (∑ j : N, c j • bas j - bas i) + ∑ x : N, c_1 x • bas x by
        simp_rw [←add_sub_assoc]
        simp_rw [add_sub_right_comm]
        simp_rw [←smul_sub]
        exact this
      have (c_1 : N → ℝ): c_1 i • (∑ j : N, c j • bas j - bas i) + ∑ x : N, c_1 x • bas x = bas i := by
        calc
          c_1 i • (∑ j : N, c j • bas j - bas i) + ∑ x : N, c_1 x • bas x = c_1 i • (∑ j : N, c j • bas j - bas i) + ∑ x : N, c_1 x • bas x := sorry
          _ = c_1 i • (∑ j : N, c j • bas j ) - c_1 i • bas i + ∑ x : N, c_1 x • bas x := sorry
          _ =  (∑ j : N, c_1 i • c j • bas j ) - c_1 i • bas i + ∑ x : N, c_1 x • bas x := sorry
          _ =  (∑ j : N, c_1 i • c j • bas j ) + ∑ x : N, c_1 x • bas x - c_1 i • bas i := sorry
          _ =  (∑ x : N, (c_1 i • c x • bas x + c_1 x • bas x) ) - c_1 i • bas i := sorry
          _ =  (∑ x : N, ((c_1 i • c x + c_1 x) • bas x) ) - c_1 i • bas i := sorry


        sorry

      use (fun q : N ↦ (if q = i then 2 else 0))
      simp [h]
      sorry
    }
    {
      use (fun q : N ↦ (if q = k then 1 else 0))
      simp [h]
    }

noncomputable instance (p : N → Prop) : Fintype {x | p x} := by
  exact Fintype.ofFinite ↑{x | p x}

@[simp]
def LimitedBasis (bas : N → V) (p : N → Prop) : ({x | p x} → V) := fun i ↦ bas i

def limitedBasis_le  (bas : N → V) (p : N → Prop) : hasBasis (LimitedBasis bas p) ≤ hasBasis bas := by
  apply (basisLE _ _).mpr
  simp only [Set.coe_setOf, LimitedBasis, Set.mem_setOf_eq, Subtype.forall]
  exact fun a _ ↦ basisContainsItself bas a

def combinedSpace (A B : V → Prop) (x : V) := ∃a b, A a ∧ B b ∧ x = a + b

-- lemma combinedSpace_cols (a : N → V) (b : N' → V) : (combinedSpace (hasBasis a) (hasBasis b))

theorem ite_distrib {S : Type} [AddCommMonoid S](p)[Decidable p](a b : S) : (if p then a else b) = (if p then a else 0) + (if p then 0 else b) := by
  aesop


lemma hasBasis_ite (p : N → Prop) [DecidablePred p] (a b : N → V) : hasBasis (fun k ↦ if p k then a k else b k)
    = combinedSpace (hasBasis (LimitedBasis a p)) (hasBasis (LimitedBasis b (pᶜ))) := by
  unfold combinedSpace
  unfold hasBasis
  ext x
  constructor
  {
    intro ⟨c,c_s⟩
    rw [c_s]
    use apply_basis (LimitedBasis a p) (c ·)
    use apply_basis (LimitedBasis b pᶜ) (c ·)
    refine ⟨?_,?_,?_⟩
    · use (c ·)
    · use (c ·)
    ·

      unfold apply_basis
      simp
      rw [← @Finset.sum_sum_elim]
      simp
      sorry
  }
  unfold apply_basis
  simp
  -- simp only [Set.coe_setOf, Pi.compl_apply, exists_and_left]

  -- apply le_antisymm
  -- {
  --   rw [basisLE _ _]

  --   sorry
  -- }

  sorry


lemma BasisShiftFree_same (bas : N → V) (lb : linearIndependence bas) (i : N) (c : N → ℝ) (hc : c i ≠ 0) :
    hasBasis (BasisShiftFree bas i c) = hasBasis bas := by
  apply le_antisymm
  {
    apply (basisLE _ _).mpr
    intro x
    unfold BasisShiftFree
    split
    exact basisContainsApplications bas c
    exact basisContainsItself bas x
  }
  {

    apply (basisLE _ _).mpr
    intro y
    unfold BasisShiftFree
    by_cases h : i = y
    {
      rw [h]
      unfold hasBasis
      -- use ?_
      rw [apply_basis]
      simp
      simp [coe_apply_basis_left']
      conv in if _ = y then _ else _ =>{
        rw [ite_distrib]
      }
      change ∃ c_1, bas y = (apply_basis_left c_1) ((fun k ↦ (if k = y then ∑ i : N, c i • bas i else 0)) + fun k ↦ if k = y then 0 else bas k)
      simp only [map_add]

      -- simp_rw [Irow_assoc (u := fun _ ↦ (∑ i : N, c i • bas i))]
      simp only [←coe_apply_basis_left]
      unfold apply_basis

      let d := fun k ↦ if k = y then (c y)⁻¹ else - (c y)⁻¹ * c k
      simp only [smul_ite_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      use ?_
      simp [Finset.smul_sum]
      simp [←Finset.sum_add_distrib]
      symm

      have key(x) : (?w y • c x + ?w x * if x = y then 0 else 1) = if x = y then 1 else 0 := ?_
      calc
        ∑ x : N, (?w y • c x • bas x + ?w x • if x = y then 0 else bas x) = ∑ x : N, (?w y • c x • bas x + ?w x • if x = y then 0 else bas x) := sorry
        _ = ∑ x : N, (?w y • c x • bas x + ?w x • if x = y then 0 else bas x) := sorry
        _ = ∑ x : N, ((?w y • c x • bas x + ?w x • (if x = y then 0 else (1 : ℝ)) • bas x)) := by
          simp_rw [ite_smul _ _ _]
          simp
        _ = ∑ x : N, ((?w y • c x • bas x + (?w x * if x = y then 0 else 1) • bas x)) := by
          simp_rw [mul_smul]
        _ = ∑ x : N, ((?w y • c x + ?w x * if x = y then 0 else 1) • bas x) := by
          simp_rw [add_smul]
          simp
          simp_rw [mul_smul]
        _ = ∑ x : N, (if x = y then 1 else 0) • bas x := by
          simp_rw [key _]
          simp
        _ = bas y := by simp

      rotate_left
      exact d
      split
      {
        simp
        rw [(_ : x = y)]
        rw [h] at hc
        exact inv_mul_cancel hc
        assumption
      }
      -- - d y * c x = d x
      simp
      split
      tauto
      simp
    }
    have : (fun k ↦ if k = i then apply_basis bas c else bas k) y = bas y := by
      simp
      tauto
    rw [←this]

    apply basisContainsItself
  }



lemma BasisShiftFree_linInd (bas : N → V) (lb : linearIndependence bas) (i : N) (c : N → ℝ) (hc : c i ≠ 0) :
    linearIndependence (BasisShiftFree bas i c) := by

  sorry

lemma BasisOneOrthogonal (product : InnerProduct V) (bas : N → V)
    (lb : linearIndependence bas) (i : N) :
    ∃ obas : N → V, hasBasis obas = hasBasis bas
    ∧ linearIndependence obas ∧ (∀j ≠ i, obas j = bas j)
    ∧ (∀j ≠ i, orthogonalPair product bas i j) := by

  -- use ?_
  -- refine ⟨?_,?_,?_,?_⟩


  sorry


example {n : ℕ} (product : InnerProduct V) (bas : Fin n → V) (lb : linearIndependence bas) :
    ∃obas : Fin n → V, hasBasis obas = hasBasis bas ∧ linearIndependence obas ∧ orthogonal product obas ∧ normal product obas
    := by




  -- #check ∑ i in , i
  sorry





end Excercise10
