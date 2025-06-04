/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic


namespace Section17sheet2

/-

# Basic calculus

-/
-- Thanks to Moritz Doll on the Zulip for writing this one!
/-- If `f : ℝ → ℝ` is differentiable at `x`, then the obvious induced function `ℝ → ℂ` is
also differentiable at `x`. -/
theorem Complex.differentiableAt_coe
    {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (f y : ℂ)) x := by
  apply Complex.ofRealClm.differentiableAt.comp _ hf

-- Here's a harder example
example (a : ℂ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => Complex.exp (-(a * ↑y ^ 2))) x := by
  apply DifferentiableAt.comp (g := Complex.exp)
  ·
    exact Complex.differentiableAt_exp

  ·
    apply DifferentiableAt.comp (f:= Complex.ofReal') (g:= fun y ↦ -(a * y ^ 2))
    · simp only [differentiableAt_neg_iff]
      apply DifferentiableAt.const_mul
      norm_num

    apply Complex.differentiableAt_coe
    simp only [differentiableAt_id']

noncomputable def φ₁ : ℝ → ℝ × ℝ := fun x => (Real.cos x, Real.sin x)

example : ContDiffOn ℝ ⊤ (fun x => (Real.cos x, Real.sin x)) (Set.Icc 0 1) := by
  apply contDiffOn_top.mpr
  intro n
  -- intro x xS
  refine ContDiffOn.prod ?hf ?hg
  refine contDiffOn_of_differentiableOn ?hf.h
  intro m mn
  let w := (iteratedFDerivWithin ℝ m (fun x ↦ Real.cos x) (Set.Icc 0 1))
  simp at w

  sorry

end Section17sheet2
