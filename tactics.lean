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

-- 9.
