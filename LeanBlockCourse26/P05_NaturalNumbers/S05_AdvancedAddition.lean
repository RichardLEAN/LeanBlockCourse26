/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import LeanBlockCourse26.P05_NaturalNumbers.S04_Power

/-
# Advanced Addition
=====================
-/

namespace MyNat

/-
## Exercise Block B01
-/

-- Exercise 1.1
theorem add_right_cancel {n m k : MyNat} (h : n + k = m + k) : n = m := by
  sorry

-- Exercise 1.2
theorem add_left_cancel {n m k : MyNat} (h : k + n = k + m) : n = m := by
  sorry

-- Exercise 1.3
theorem add_left_eq_self {n m : MyNat} (h : n + m = m) : n = 0 := by
  sorry

-- Exercise 1.4 (Master)
theorem add_right_eq_self {n m : MyNat} (h : n + m = n) : m = 0 := by
  sorry

-- Exercise 1.5 (Master)
theorem add_right_eq_zero {n m : MyNat} (h : n + m = 0) : n = 0 := by
  sorry

-- Exercise 1.6 (Master)
theorem add_left_eq_zero {n m : MyNat} (h : n + m = 0) : m = 0 := by
 sorry

end MyNat
