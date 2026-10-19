-- Yes, it is possible, but only by assuming somthing false.
-- Lean can not prove 2=6 on its own, because the statement is false.
-- What it can prove is the conditional statement "if 1=3, then 2=6".

import Mathlib

theorem two_eq_six (h : 1=3) : 2 = 6 := by
    calc 2 = 2 *1 := by norm_num
     _ = 2*3 := by rw [h]
     _ = 6 := by norm_num
