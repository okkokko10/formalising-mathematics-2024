/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro nt
  apply nt
  triv

  done

example : False → ¬True := by
  -- intro f
  -- change False → True → False
  intro f
  exfalso
  assumption

  done

example : ¬False → True := by
  intro --nf
  -- change False → False at nf
  by_contra h
  apply h
  triv

  done

example : True → ¬False := by
  intro
  by_contra
  assumption
  done

example : False → ¬P := by
  intro f
  exfalso
  assumption
  done

example : P → ¬P → False := by
  intro p np
  -- change P → False at np
  apply np at p
  exact p
  done

example : P → ¬¬P := by
  intro p

  intro nnp
  apply nnp at p
  apply p


  done

example : (P → Q) → ¬Q → ¬P := by
  intro pq
  intro nq
  by_contra h
  apply pq at h
  apply nq at h
  apply h
  done

example : ¬¬False → False := by
  intro nnf
  apply nnf
  intro f
  apply f


  done

example : ¬¬P → P := by
  intro nnp
  -- by_cases h : P
  -- exact h

  -- apply nnp at h
  -- exfalso
  -- apply h

  by_contra h
  apply nnp at h
  exact h

  done

example : (¬Q → ¬P) → P → Q := by
  intro a p
  by_contra h
  apply a at h
  apply h at p
  exact p
  done
