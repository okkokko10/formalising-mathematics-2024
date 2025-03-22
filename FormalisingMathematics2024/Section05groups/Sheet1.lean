/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Groups

## How to use Lean's groups

In previous courses I have made groups from scratch, but it's kind of irritating
to do (because all the lemma names like `mul_one` are already taken) and I'm
not entirely sure that most students want to know how to make their own
groups, rings, whatever: what's the point if these things are there already?

So in this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
/-  Let's see what just happened.
    The tactic state now looks like this:

    G : Type
    inst✝ : Group G
    g : G
    ⊢ g⁻¹ * g = 1

    So G is what most mathematicians would call a "set", and what in this course
    we call a "type" (they're the same thing as far as you're concerned), and
    `g : G` just mean "g is an element of G". The remaining thing is this
    `inst✝` thing, and that means "G has a multiplication `*`, an identity `1`,
    an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
    all of this will be taken care of by "instances", which are a part
    of Lean's "type class inference system". The type class inference system
    is the system which deals with stuff in square brackets. You don't have
    to worry about it right now -- all that matters is that you have access
    to all the group axioms. This one is called `inv_mul_self g`.
-/
  inv_mul_self g

-- Why don't you use `exact?` to see the names of the other axioms
-- of a group? Note that when `exact?` has run, you can click on
-- the output (the blue output in the infoview) and replace `exact?`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?
example (a b c : G) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c


-- can be found with `library_search` if you didn't know the answer already
example (a : G) : a * 1 = a := by
  exact mul_one a


-- Can you guess the last two?
example (a : G) : 1 * a = a := by
  exact one_mul a

example (a : G) : a * a⁻¹ = 1 := by
  exact mul_inv_self a

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  rw [←mul_assoc]

  -- have (x : G) : x⁻¹ * x = 1 := by exact mul_left_inv x
  rw [mul_left_inv a]
  exact one_mul b



example : a * (a⁻¹ * b) = b := by
  simp only [mul_inv_cancel_left]
  done

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  -- hint for this one if you're doing it from first principles: `b * (a * c) = (b * a) * c`
  have ca := congrArg (fun x ↦ a⁻¹ * x) h2
  have ba := congrArg (fun x ↦ x * a⁻¹) h1
  simp only [inv_mul_cancel_left, mul_one] at ca
  simp only [mul_inv_cancel_right, one_mul] at ba
  have := ca.symm ▸ ba
  exact Eq.trans ba ca.symm


  done

example : a * b = 1 ↔ a⁻¹ = b := by

  constructor
  · intro ab1
    apply congrArg (fun x↦ a⁻¹ * x) at ab1
    simp only [inv_mul_cancel_left, mul_one] at ab1
    exact ab1.symm
  · intro a1b
    apply congrArg (fun x↦ a * x) at a1b
    simp only [mul_right_inv] at a1b
    exact a1b.symm
  done

example : (1 : G)⁻¹ = 1 := by
  -- exact inv_one
  have h : (1 : G)⁻¹ = (1 : G)⁻¹ := by rfl
  nth_rw 2 [←mul_one (1 : G)⁻¹] at h
  rw [mul_left_inv] at h
  exact h

  done

example : a⁻¹⁻¹ = a := by
  -- exact inv_inv a
  -- both sides a⁻¹ *
  -- a⁻¹ * a⁻¹⁻¹ = a ⁻¹ * a
  suffices a⁻¹ * a⁻¹⁻¹ = a ⁻¹ * a by
    apply congrArg (fun x ↦ a * x) at this
    rw [mul_left_inv] at this
    rw [mul_inv_cancel_left] at this
    rw [mul_one] at this
    exact this
    done
  rw [mul_left_inv]
  rw [mul_right_inv]
  done

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  exact mul_inv_rev a b
  -- (a * b)⁻¹ = b⁻¹ * a⁻¹
  -- suffices (a * b)⁻¹ * 1 = b⁻¹ * a⁻¹ by
  --   exact mul_one (a * b)⁻¹ ▸ this
    -- rw [mul_one] at this
    -- exact this
    -- done
  -- suffices (a * b)⁻¹ * a * a⁻¹ = b⁻¹ * a⁻¹ by
    -- have w : (a * a⁻¹) = 1 := by exact mul_inv_self a
    -- rw [←mul_inv_self a]


  -- (a * b)⁻¹ * a = b⁻¹
  -- (a * b)⁻¹ * a * 1 = b⁻¹
  -- (a * b)⁻¹ * a * b * b⁻¹ = b⁻¹
  -- (a * b)⁻¹ * a * b = 1
  -- (a * b)⁻¹ * (a * b) = 1


  done

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by

  intros a b
  -- suffices b * a * b * a = b * b * a * a by

  --   apply congrArg (b⁻¹ * · * a⁻¹) at this
  --   simp only [mul_left_inj, mul_right_inj] at this

  --   done
  rw [
    ←mul_left_inj a,
    ←mul_right_inj b,
    mul_assoc b a a,
    mul_assoc a b a,
    ←mul_assoc b a (b * a),
    h a,
    mul_one b,
    h b,
    h (b * a)
    ]
  done
