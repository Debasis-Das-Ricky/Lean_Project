-- Mathlib has no theorem literally named "homogeneous system has a solution".
-- The fact is so basic that it appears in the form "A times the zero vector is zero".
-- A homogeneous system is written A ⋆ᵥ x = 0, where ⋆ᵥ is Mathlib's notation for the matrix-vector product Ax.
-- A homogeneous system is written A *ᵥ x = 0, where *ᵥ is Mathlib's notation for the matrix-vector product Ax.

import Mathlib


-- homogeneous system has a solution
theorem homogeneous_has_solution {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) : ∃ x : n → ℝ, Matrix.mulVec A x = 0 :=
  ⟨0, Matrix.mulVec_zero A⟩
