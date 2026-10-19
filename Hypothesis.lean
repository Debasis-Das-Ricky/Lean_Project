-- A hypothesis is a named assumption.
-- Formally, it is a variable whose type is a proposition(Prop).
-- If P is a statement, then h : P means "h is a proof of P".
-- Inside the proof you may use P as a known fact by reffering to h.

import Mathlib

-- We have a real number x, we know x > 0(h), and we must prove x^2 > 0.

-- Five way to create hypothesis

-- A. As an argument of a theorem: This is the most common way.
-- Anything in parentheses before the colon is assumed for the whole proof.

theorem sq_pos_of_pos' (x : ℝ) (h : x>0) : x^2 > 0 := by
  positivity

example (a b : ℕ) (h₁ : a=2) (h₂ : b=3) : a + b = 5 := by
  rw [h₁, h₂]


-- B. With intro: When the goal is an implication P → Q,
-- the tactic intro h moves P into the hypothesis under the name h.
-- This is the formal version of "assume P"

example (x:ℕ): x=3 → x+1=4 := by
  intro h   -- now h: x = 3, goal: x+1 = 4
  rw [h]

-- C. With have: Proves an intermediate fact and adds it as a new hypothesis,
-- like writing a lemma in middle of a pen and paper proof.

example (x : ℝ) (h : x>2) : x>1 := by
  have h2 : (2 : ℝ) > 1 := by norm_num
  linarith

-- D. With obtain: Splits a compound hypothesis into pieces.
-- From h : p ∧ q you get two separate hypothesis hp : p and hq : q

example (p q : Prop) (h : p ∧ q) : q := by
  obtain ⟨ hp, hq ⟩ := h
  exact hq

-- E. With variable: Declares assumptions shared by many theorems in a file.
-- Lean adds a variable to a theorem only when the theorem uses it: for a hypothesis
-- that is not mentioned in the statement, write include to force it in.

variable (x : ℝ) (hx : 0 < x)
example : 0 < x + 1 := by
  linarith
