/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro piq
  -- rewrite [piq]
  -- triv
  rw [piq]

  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h
  rw [h]
  intro h
  rw [h]

  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros pq qr
  rw [pq]
  rw [qr]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro pAq
  cases' pAq with p q
  constructor
  exact q
  exact p

  intro pAq
  cases' pAq with p q
  constructor
  exact q
  exact p


  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor

  intros a
  rcases a with ⟨⟨p,q⟩,r⟩
  constructor
  exact p
  constructor
  exact q
  exact r

  intros a
  cases' a with p qr
  cases' qr with q r
  constructor
  constructor
  exact p
  exact q
  exact r




  done

example : P ↔ P ∧ True := by
  constructor
  intros p

  constructor
  exact p
  triv
  intros pAt
  cases' pAt with p
  exact p

  done

example : False ↔ P ∧ False := by
  constructor
  intro
  exfalso; assumption
  intro a
  cases' a with p f
  exact f
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intros a b
  rw [a]
  rw [b]


  done

example : ¬(P ↔ ¬P) := by
  intro a
  cases' a with l r
  change P → P → False at l
  change (P → False) → P at r
  by_cases h : P

  . apply l
    . exact h
    . exact h
  . apply r at h
    apply l
    . exact h
    . exact h












  -- by_cases h : P
  -- Okko: how would you convert P into P↔True




  done
