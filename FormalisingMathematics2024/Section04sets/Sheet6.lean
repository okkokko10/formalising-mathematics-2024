/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  -- rw [Set.subset_def]

  unfold Set.preimage
  unfold Set.image
  simp only [Set.mem_setOf_eq]
  rw [Set.subset_def]
  simp
  intro x xS
  use x
  done

example : f '' (f ⁻¹' T) ⊆ T := by

  unfold Set.image
  unfold Set.preimage
  simp only [Set.mem_setOf_eq]
  rw [Set.subset_def]
  simp only [Set.mem_setOf_eq]

  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, imp_self, implies_true]




  done

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by

  unfold Set.image
  unfold Set.preimage
  simp_rw [Set.subset_def]
  simp_rw [Set.mem_setOf]
  constructor
  · intro L x xS
    apply L (f x)
    use x
    done
  intros w1 y w2
  have ⟨a,aS,fay⟩ := w2
  specialize w1 a aS
  exact fay ▸ w1
  done

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  unfold Set.preimage
  ext x
  simp_rw [Set.mem_setOf]
  unfold id
  rfl
  done


-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext x
  unfold Set.image
  simp_rw [Set.mem_setOf]
  unfold id
  constructor
  · intro ⟨a,aS,ax⟩
    exact ax ▸ aS
    done
  · intros xS
    use x
    done
  done

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  simp_rw [Set.mem_preimage]
  simp only [Function.comp_apply]
  done

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext x
  simp_rw [Set.mem_image]

  simp only [Function.comp_apply, exists_exists_and_eq_and]
  done
