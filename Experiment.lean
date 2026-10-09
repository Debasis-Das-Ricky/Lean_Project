-- Samples.lean
-- A first set of basic Lean 4 examples

-- 1. Simple arithmetic proof
example : 2 + 2 = 4 := by
  rfl

-- 2. A proof using `decide` for decidable propositions
example : 3 * 3 = 9 := by
  decide

-- 3. Basic logic: modus ponens
example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  exact hpq hp
