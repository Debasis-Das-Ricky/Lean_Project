import Mathlib

open Filter Topology

-- Theorem 1: 1/n → 0

theorem one_div_n_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

-- Theorem 2(New): 1/n^2 → 0, using theorem 1:

theorem one_div_n_sq_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  -- Use Theorem 1 twice: (1/n) * (1/n) → 0 * 0
  have h := one_div_n_tendsto_zero.mul one_div_n_tendsto_zero
  -- Simplify the limit 0 * 0 to 0
  rw [mul_zero] at h
  -- Show (1/n) * (1/n) = 1/n² for every n, then transfer the limit
  exact h.congr (fun n => by ring)
