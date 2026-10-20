-- A tactics is a command that tells Lean how to make progress on a proof.
-- After by, lean enter tactic mode and shows a goal: what is left to prove, togather with the hypothesis available.
-- Each tatic transforms the goal(or splits it into smaller goals) untill none remain.
import Mathlib

 -- 1. exact: Close the goal with a term that matches it exactly
example (p : Prop) (hp : p) : p := by -- 'by' starts tactic mode
  exact hp -- this tactic closes the goal

-- 2. intro: Assumes the left side of P → Q (or a variable of ∀)
example (p:Prop) : p → p := by
  intro h
  exact h

-- 3. apply: Work backwards: to get q from p → q, the goal becomes p.
example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  apply hpq
  exact hp

-- 4. constructor: Splits p ∧ q into 2 goals p and q
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  . exact hp
  . exact hq

-- 5. obtain: Splits a hypothesis apart (∧, ∃ \, ...)
example (p q : Prop) (h : p ∧ q) : q := by
 obtain ⟨ hp, hq ⟩ := h
 exact hq

-- 6. left/right: Choose which side of p ∨ q to prove
example (p q : Prop) (hp : p) : p ∨ q := by
 left
 exact hp

-- 7. Use: Gives the witness for an ∃ goal
example : ∃ n : ℕ, n + 2 = 5 := by
 use 3

-- 8. rfl: Proves a = a, including after computation.
example: 2 + 2 = 4 := by
 rfl

-- 9. rw: Rewrites the goal using an equation
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
 rw[h]

-- 10. simp: Simplifies using large database of rules
example (a : ℕ) : a+0=a :=by
 simp

-- 11. ring: Proves identities in commutative (semi)rings.
example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
 ring

-- 12. norm_num: Prove Numerical facts
example: (3 : ℝ) * 4 - 2 = 10 := by
 norm_num

-- 13. linarith: Proves linear (in)equalities from hypothesis
example (x y : ℝ) (h1 : x < y) (h2 : y < 5) : x < 5 := by
 linarith
