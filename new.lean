#eval 5+7

def triple_five(n : Nat) :=
     n + n + n

theorem tri_five_eq_15 : triple_five 5 = 15 := by
        rfl
