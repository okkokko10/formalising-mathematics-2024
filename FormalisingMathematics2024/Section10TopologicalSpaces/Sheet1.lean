/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    triv
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    triv
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    triv

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    dsimp only
    right
    triv
    -- use `dsimp`
  isOpen_inter := by
    intros s t f g
    cases' g with h h
    ·
      rw [h]
      simp only [Set.inter_empty]
      tauto
    rw [h]
    simp only [Set.inter_univ]
    exact f
    -- use `cases'`
  isOpen_sUnion := by
    intro F
    simp only [Set.sUnion_eq_empty]
    intro f
    by_cases h : Set.univ ∈ F
    · right
      have := Set.subset_sUnion_of_mem h
      exact Set.univ_subset_iff.mp this
    left
    intro s sF
    have t1:= f s sF
    have t2: s ≠ Set.univ := by exact ne_of_mem_of_not_mem sF h
    simp [t2] at t1
    exact t1
    -- do cases on whether Set.univ ∈ F


-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by


  have := TopologicalSpace.isOpen_sUnion (∅ : Set (Set X))
  simp at this
  exact this

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  unfold IsOpen
  -- simp only [Set.mem_univ]
  norm_num
  use 1
  norm_num


lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  unfold IsOpen at *
  intro x xst
  obtain ⟨dt,dt_pos, ht'⟩ := ht x (Set.mem_of_mem_inter_right xst)
  obtain ⟨ds,ds_pos, hs'⟩ := hs x (Set.mem_of_mem_inter_left xst)
  let d := min ds dt
  have hds : d ≤ ds := by exact min_le_left ds dt
  have hdt : d ≤ dt := by exact min_le_right ds dt
  have d_pos : d > 0 := by exact lt_min ds_pos dt_pos
  refine ⟨d,d_pos,fun y ⟨w1,w2⟩ ↦ ⟨hs' y ⟨?_,?_⟩,ht' y ⟨?_,?_⟩⟩⟩
    <;> linarith only [hds, hdt, w1, w2]


lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  unfold IsOpen at *
  intro x xU
  have ⟨s,sF,xs⟩ := xU
  specialize hF s sF x xs
  obtain ⟨d,d_pos,hF'⟩ := hF
  refine ⟨d,d_pos,fun y w ↦ ?_⟩
  have := hF' y w
  -- simp_rw [Set.mem_sUnion]
  refine ⟨s, sF, this⟩

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
