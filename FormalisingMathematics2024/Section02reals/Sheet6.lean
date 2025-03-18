/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  intro ε ε_pos
  have ts := |(37:ℝ)|⁻¹
  have ts_pos : ts > 0 := by sorry
  have ts_inv : |37| =  ts⁻¹  := by sorry
    -- how to show |37| = 37

  have εt_pos : ε * ts > 0 := by exact Real.mul_pos ε_pos ts_pos
  specialize h (ε * ts) εt_pos

  obtain ⟨X, hX⟩ := h
  use X
  intro n xln
  specialize hX n xln
  ring_nf
  -- have ww(x : ℝ)(y : ℝ) (w: x < y) : 2 * x < 2 * y := by linarith
  have hh :   |a n - t| *  ts⁻¹ < ε
  . exact (mul_inv_lt_iff' ts_pos).mpr hX

  have hh1 :  |(a n - t)* 37| < ε
  . rw [abs_mul]
    rw [ts_inv]
    exact hh
  rw [sub_mul] at hh1
  exact hh1




  -- rw at hX
  -- have ww(x : ℝ)(y : ℝ) : ( |y*x| = |y| * |x|) := by exact abs_mul y x
  -- have w1(x : ℝ)(y : ℝ)(z : ℝ) : ( z*(y-x) = z*y - z*x) := by exact mul_sub z y x



/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε ε_pos
  let ca := |c|
  have hca :  0 < ca := by exact abs_pos_of_pos hc


  have εt_pos : ε / ca > 0 := by exact div_pos ε_pos hca
  specialize h (ε / ca) εt_pos

  obtain ⟨X, hX⟩ := h
  use X
  intro n xln
  specialize hX n xln
  ring_nf
  -- have ww(x : ℝ)(y : ℝ) (w: x < y) : 2 * x < 2 * y := by linarith
  have hh :  ca * |a n - t|  < ε
  . exact (lt_div_iff' hca).mp hX
  have hh1 :  |c* (a n - t)| < ε
  . rw [abs_mul]
    exact hh
  rw [mul_sub] at hh1
  exact hh1




/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε ε_pos
  let ca := |c|
  have hca :  0 < ca := by exact abs_pos_of_neg hc


  have εt_pos : ε / ca > 0 := by exact div_pos ε_pos hca
  specialize h (ε / ca) εt_pos

  obtain ⟨X, hX⟩ := h
  use X
  intro n xln
  specialize hX n xln
  ring_nf
  -- have ww(x : ℝ)(y : ℝ) (w: x < y) : 2 * x < 2 * y := by linarith
  have hh :  ca * |a n - t|  < ε
  . exact (lt_div_iff' hca).mp hX
  have hh1 :  |c* (a n - t)| < ε
  . rw [abs_mul]
    exact hh
  rw [mul_sub] at hh1
  exact hh1

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by

  let ca := |c|

  by_cases z : c = 0
  .
    rw [z]
    ring_nf

    intro ε ε_pos
    ring_nf

    rw [abs_zero]
    -- simp only [abs_zero]
    -- have ε_pos1 : 0 < ε := ε_pos

    -- change 0 < ε at ε_pos

    . use 1
      intros
      exact ε_pos

    -- simp only [ε_pos]
    -- simp only [implies_true, forall_const, exists_const]
    done


  intro ε ε_pos

  have hca :  0 < ca := by exact abs_pos.mpr z


  have εt_pos : ε / ca > 0 := by exact div_pos ε_pos hca
  specialize h (ε / ca) εt_pos

  obtain ⟨X, hX⟩ := h
  use X
  intro n xln
  specialize hX n xln
  ring_nf
  -- have ww(x : ℝ)(y : ℝ) (w: x < y) : 2 * x < 2 * y := by linarith
  have hh :  ca * |a n - t|  < ε
  . exact (lt_div_iff' hca).mp hX
  -- have hh1 :  |c* (a n - t)| < ε
  -- . rw [abs_mul]
  --   exact hh
  -- rw [mul_sub] at hh1
  -- exact hh1
  rw [←mul_sub]
  rw [abs_mul]

  exact (lt_div_iff' hca).mp hX

  -- exact hh


-- Okko: How to use the similarity of c * _ and _ * c without using commutativity?

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by

  let ca := |c|

  by_cases z : ca = 0
  .


    intro ε ε_pos
    norm_num
    . use 1
      intros n _
      rw [← sub_mul]
      rw [abs_mul]

      change |a n - t| * ca < ε
      rw [z]
      simp only [mul_zero]

      exact ε_pos

    done


  intro ε ε_pos

  have hca : 0 < ca := Ne.lt_of_le' z (abs_nonneg c)


  have εt_pos : ε / ca > 0 := div_pos ε_pos hca
  specialize h (ε / ca) εt_pos

  obtain ⟨X, hX⟩ := h
  use X
  intro n xln
  specialize hX n xln
  norm_num
  -- have hh :  ca * |a n - t| < ε := (lt_div_iff' hca).mp hX
  apply (lt_div_iff' hca).mp at hX


  rw [← sub_mul]
  rw [abs_mul]
  rw [mul_comm]

  exact hX

  -- exact hh
  done

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  -- have w1 := tendsTo_add h1 h2
  -- simp only [sub_add_cancel] at w1
  simpa using tendsTo_add h1 h2

  done

/-- Okko: I made this.
    How to represent "everything"?
    this surely holds for any t, not just reals.
    - wait, nevermind, it's only defined on metric spaces.
    -/
theorem tendsTo_const (t : ℝ) : TendsTo (fun n ↦ t) t := by
  rw [tendsTo_def]
  norm_num
  intro ε ε_pos
  simp [ε_pos]

  done







/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  let b : (ℕ → ℝ) := fun n ↦ t
  have hb : (TendsTo b t) := by exact tendsTo_const t
  have ab : (fun (n : ℕ) ↦ a n - t) = (fun (n : ℕ) ↦ a n - b n) := by rfl
  rw [ab]

  -- let cc : ℝ := 0
  -- by_cases (false)
  -- .
  --   -- approach A
  --   sorry
  --   done
  -- -- approach B






  constructor
  .
    intro ha
    have hhh := tendsTo_sub ha hb
    rewrite [sub_self] at hhh -- Okko: how would this be done in one line?
    exact hhh
  .
    intro hab
    have tw := tendsTo_of_tendsTo_sub (hab) hb
    rw [zero_add] at tw
    exact tw
    done


theorem cauchy_schwarz_inequality (x y : ℝ) : |x*y| ≤ |x| * |y| := by
  exact Eq.le (abs_mul x y)
  done
/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by


  have csi (n) := cauchy_schwarz_inequality (a n) (b n)

  let upper_bound_small (n ε ) := |a n| * |b n| < ε
  let actual_small (n ε ) := |a n * b n| < ε

  have bound (n ε ) : (upper_bound_small n ε) → actual_small n ε := by
    intro q
    exact gt_of_gt_of_ge q (csi n)

  rw [tendsTo_def] at *
  norm_num at *
  -- have ac_h : ∀(n ε), actual_small n ε ↔ |a n * b n| < ε := by simp

  intro ε ε_pos
  -- have q : (∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |a n| < ε) ∧ (∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |b n| < ε)
  -- . exact { left := ha, right := hb }
  -- have qq : (∀ (ε : ℝ), 0 < ε → (∃ B, ∀ (n : ℕ), B ≤ n → |a n| < ε) ∧ ( ∃ B, ∀ (n : ℕ), B ≤ n → |b n| < ε) )
  -- . exact fun ε a_1 ↦ { left := ha ε a_1, right := hb ε a_1 }


  let ε_sqrt := Real.sqrt ε
  have ε_sqrt_pos : ε_sqrt > 0 := by exact Real.sqrt_pos.mpr ε_pos

  -- have ee : ε_sqrt ^ 2 = ε := by exact Real.sq_sqrt (LT.lt.le ε_pos)
  have ee : ε_sqrt * ε_sqrt = ε := by exact
    (Real.sqrt_eq_iff_mul_self_eq_of_pos ε_sqrt_pos).mp rfl
  -- Okko: wth is that name



  obtain ⟨X, hX⟩ := ha ε_sqrt ε_sqrt_pos
  obtain ⟨Y, hY⟩ := hb ε_sqrt ε_sqrt_pos
  use max X Y
  intro n gt_max
  have Y_n: Y ≤ n := by exact le_of_max_le_right gt_max
  have X_n: X ≤ n := by exact le_of_max_le_left gt_max
  specialize hX n X_n
  specialize hY n Y_n
  clear X_n Y_n gt_max X Y ha hb
  have iww : |a n| * |b n| < ε_sqrt * ε_sqrt := by
    clear * - hX hY
    have a1 := abs_nonneg (a n)
    have b1 := abs_nonneg (b n)
    exact mul_lt_mul'' hX hY a1 b1

  rw [ee] at iww
  apply bound at iww -- Okko: this apply cannot be converted to specialize as is. why?
  exact iww

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
example {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by


  have csi (n) := cauchy_schwarz_inequality (a n) (b n)

  let upper_bound_small (n ε ) := |a n| * |b n| < ε
  let actual_small (n ε ) := |a n * b n| < ε

  have bound (n ε ) : (upper_bound_small n ε) → actual_small n ε := by
    intro q
    exact gt_of_gt_of_ge q (csi n)

  norm_num at bound
  clear * - bound ha hb

  rw [tendsTo_def] at *
  norm_num at *
  -- clear actual_small upper_bound_small csi

  intro ε ε_pos


  let ε_sqrt := Real.sqrt ε
  have ε_sqrt_pos : ε_sqrt > 0 := by exact Real.sqrt_pos.mpr ε_pos
  have ee : ε_sqrt * ε_sqrt = ε := by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos ε_sqrt_pos).mp rfl
  -- Okko: wth is that name

  specialize ha ε_sqrt ε_sqrt_pos
  specialize hb ε_sqrt ε_sqrt_pos
  cases' ha with X hX
  cases' hb with Y hY
  use max X Y
  intro n gt_max
  specialize hX n (le_of_max_le_left gt_max)
  specialize hY n (le_of_max_le_right gt_max)
  clear gt_max X Y

  have iww : |a n| * |b n| < ε_sqrt * ε_sqrt := by
    have a1 := abs_nonneg (a n)
    have b1 := abs_nonneg (b n)
    exact mul_lt_mul'' hX hY a1 b1

  rw [ee] at iww
  apply bound at iww
  exact iww






/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
    -- a(n)-t tends to 0
    -- (a n - t) * (b n - u) tends to 0
    -- = lim { (a n - t) * (b n) } + lim{ (a n - t) * (-u) }
    -- = lim { (a n) * (b n) } + lim { (-t) * (b n) } + lim{ (a n) * (-u) } + lim{ (-t) * (-u) }

    -- lim{ (a n - t) * (b n - u) }
    -- = lim{ (a n) * (b n) - (a n) * u - t * (b n) - t * (- u) }
    have ha1 := tendsTo_sub_lim_iff.mp ha
    have hb1 := tendsTo_sub_lim_iff.mp hb
    -- rw [tendsTo_sub_lim_iff] at ha hb
    have whh := tendsTo_zero_mul_tendsTo_zero ha1 hb1
    simp at whh
    have eqq(n) : ((a n) * (b n) - (a n) * u - t * (b n) + t * u) = ((a n - t) * (b n - u)) := by linarith


    have w : TendsTo (fun n ↦ (a n) * (b n) - (a n) * u - t * (b n) + t * u) 0 := by
      simp only [eqq]
      exact whh
    let f := fun n ↦ (a n) * (b n) - (a n) * u - t * (b n)
    let tu := t * u
    -- have w1 : TendsTo (fun n ↦ f n + tu) 0 := by exact w
    have w2 : TendsTo (fun n ↦ f n - (- tu)) 0 := by
      norm_num
      exact w
    have lim_f := tendsTo_sub_lim_iff.mpr w2
    have lim_au := tendsTo_mul_const u ha
    have lim_tb := tendsTo_const_mul t hb
    -- apply tendsTo_neg at lim_au
    have www := tendsTo_add (tendsTo_add lim_f lim_au) lim_tb
    -- norm_num at www
    -- simp at www
    -- have w23(n) : (a n * b n) = (f n + a n * u + t * b n) := by ring

    ring_nf at www
    rw [mul_comm] at www -- revert the commutation ring_nf needlessly made
    exact www
    -- have www1 : TendsTo (fun n ↦ a n * b n) (t * u) := by
    --   ring_nf at www
    --   rw [mul_comm] at www -- revert the commutation ring_nf needlessly made
    --   exact www
    -- exact www1
    -- Okko: how to stop ring_nf from commuting?






    -- have uu := tendsTo_add

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by



  -- apply tendsTo_sub_lim_iff.mp at hs
  -- apply tendsTo_sub_lim_iff.mp at ht
  have hst := tendsTo_sub hs ht
  norm_num at hst
  clear hs ht a
  rw [tendsTo_def] at hst



  by_contra st

  -- have w : s = t := by sorry

  have stm : s-t ≠ 0 := by
    intro
    apply st
    linarith

  let e : ℝ := |s-t|

  have e_pos : 0 < e := by
    exact abs_pos.mpr stm

  specialize hst (e/2) (by linarith)
  cases' hst with B h
  specialize h B (Nat.le_refl B)
  norm_num at h
  rw [abs_sub_comm] at h

  linarith








  done


-- something we never used!
/-- A sequence has at most one limit. -/
example (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  rw [tendsTo_def] at *

  by_contra st

  -- have w : s = t := by sorry

  have stm : s-t ≠ 0 := by
    intro
    apply st
    linarith

  let e : ℝ := |s-t|

  have e_pos : 0 < e := by
    exact abs_pos.mpr stm

  specialize ht e e_pos
  cases' ht with Bt ht
  specialize hs e e_pos
  cases' hs with Bs hs

  let B := max Bt Bs
  specialize ht B (Nat.le_max_left Bt Bs)
  specialize hs B (Nat.le_max_right Bt Bs)

  simp only [e] at hs ht
  set w := a B
  rw [abs_sub_comm] at hs
  -- s is closer to w than to t
  -- t is closer to w than to s





  sorry

end Section2sheet6
