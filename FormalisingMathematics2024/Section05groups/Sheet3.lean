/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Subgroups and group homomorphisms

Like subsets of a type, a subgroup of a group isn't a type
and so it isn't a group! You can *make* a subgroup into a group,
but a group is a type and a subgroup is a term.

-/

section Subgroups

-- let `G` be a group
variable (G : Type) [Group G]

-- The type of subgroups of `G` is `Subgroup G`

-- Let `H` be a subgroup of `G`
variable (H : Subgroup G)

-- Just like subsets, elements of the subgroup `H` are terms `g` of type `G`
-- satisfying `g ∈ H`.

example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem ha hb -- I found this with `exact?` and then used dot notation.

-- You could instead do `apply H.mul_mem` and go on from there.

-- Try this one:

-- infixl:70 " * "   => fun {G : Type} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) ↦ (Subgroup.mul_mem H ha hb)

-- postfix:max "⁻¹" => fun {G : Type} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) ↦ (Subgroup.inv_mem H ha)
-- infixl:70 " * "  => mul_mem
-- postfix:max "⁻¹" => inv_mem


example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  -- set ac := a * c
  -- have : ac ∈ H := by exact Subgroup.mul_mem H ha hc
  -- have := ha * hb
  -- have ww := fun {a b : G} (ha : a ∈ H) (hb : b ∈ H) ↦ H.mul_mem ha hb
  -- exact ha * hb⁻¹ * H.one_mem * (ha * hc)
  -- exact ha ∈* hb∈⁻¹ ∈* H.one_mem ∈* (ha ∈* hc)

  exact H.mul_mem (H.mul_mem (H.mul_mem ha (H.inv_mem hb)) H.one_mem) (H.mul_mem ha hc)


  done

/-

## Lattice notation for sub-things

Given two subgroups of a group, we can look at their intersection
(which is a subgroup) and their union (which in general isn't).
This means that set-theoretic notations such as `∪` and `∩` are not
always the right concepts in group theory. Instead, Lean uses
"lattice notation". The intersection of two subgroups `H` and `K` of `G`
is `H ⊓ K`, and the subgroup they generate is `H ⊔ K`. To say
that `H` is a subset of `K` we use `H ≤ K`. The smallest subgroup
of `G`, i.e., {e}, is `⊥`, and the biggest subgroup (i.e. G, but
G is a group not a subgroup so it's not G) is `⊤`.

-/

-- intersection of two subgroups, as a subgroup
example (H K : Subgroup G) : Subgroup G := H ⊓ K
-- note that H ∩ K *doesn't work* because `H` and `K` don't
-- have type `Set G`, they have type `Subgroup G`. Lean
-- is very pedantic!

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  -- true by definition!
  rfl

#check Set.range
-- Note that `a ∈ H ⊔ K ↔ a ∈ H ∨ a ∈ K` is not true; only `←` is true.
-- Take apart the `Or` and use `exact?` to find the relevant lemmas.
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by

  intro aHK
  cases' aHK with h hr
  exact Subgroup.mem_sup_left h
  exact Subgroup.mem_sup_right hr

  done

end Subgroups

/-

## Group homomorphisms

The notation is `→*`, i.e. "function which preserves `*`."

-/

section Homomorphisms

-- Let `G` and `H` be groups
variable (G H : Type) [Group G] [Group H]

-- Let `φ` be a group homomorphism
variable (φ : G →* H)

-- `φ` preserves multiplication

example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b -- this is the term: no `by`

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  -- if `φ.map_mul` means that `φ` preserves multiplication
  -- (and you can rewrite with this) then what do you think
  -- the lemmas that `φ` preserves inverse and one are called?
  -- have bi := φ.map_inv b
  -- have : φ (a * b⁻¹ * 1) = φ (a * b⁻¹) * φ 1 := by exact φ.map_mul _ _
  rewrite [←φ.map_one]
  rewrite [←φ.map_inv]
  rewrite [←φ.map_mul]
  rewrite [←φ.map_mul]
  rfl
  done

-- Group homomorphisms are extensional: if two group homomorphisms
-- are equal on all inputs the they're the same.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  -- Use the `ext` tactic.
  ext x
  exact h x
  done

end Homomorphisms
