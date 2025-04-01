/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question.

-/

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by


  constructor
  · intros h a b c
    have w1 := h a b c
    by_cases ab : (a ≤ b) --<;>


    · by_cases ba : (b ≤ a) --<;>


      have a_b : a = b := le_antisymm ab ba
      simp_rw [a_b] at *
      simp

    -- have axb : ¬ a = b := by
    --   by_contra qq
    --   have q1 := (le_refl a)
    --   nth_rw 1 [qq] at q1

    -- by_cases ac : (a ≤ c) <;>
    -- by_cases ca : (c ≤ a) <;>
    -- by_cases bc : (b ≤ c) <;>
    -- by_cases cb : (c ≤ b) <;>

    -- simp [ab,ba,ac,ca,bc,cb] at w1 ⊢
      -- try simp [ab,ba,ac,ca,bc,cb,w1]
    done
    -- have w2 : a ≤ a ⊔ b ⊓ c := le_sup_left
    -- rw [w1] at w2
    -- have w3 := h (a ⊓ b) a c
    -- simp at w3
    -- rw [w3]

    -- apply le_antisymm
    -- · apply inf_le_inf_left
    --   simp
    --   have := h c a b
    --   rw [sup_comm] at this
    --   rw [this]
    --   simp


    done

  ·
    done

  sorry



example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by


  -- have h1 : ∀ a b c : L, a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by exact fun a b c ↦ sup_inf_le
  -- have h2 : ∀ a b c : L, (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by exact fun a b c ↦ le_inf_sup
  simp_rw [le_antisymm_iff]
  simp only [sup_inf_le, le_inf_sup, true_and, and_true]

  constructor
  · intro h a b c

    -- (the supremum is either) ↔ (the infinum is either)
    --
    -- a ≤ b ≤ c
    -- a, b ≤ c
    -- a ≤ b, c
    -- a b c

    have w := h (a ⊓ b) a c
    refine le_trans ?_ w
    simp
    refine le_trans ?_ (le_sup_right : c ≤ a ⊓ b ⊔ c)



    sorry




  sorry
