/-
This part is mostly inspired by the `Natural Number Game`:
https://adam.math.hhu.de/#/g/leanprover-community/nng4
-/

import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import LeanBlockCourse26.P05_NaturalNumbers.S05_AdvancedAddition

/-
# Inequalities
=====================
-/

namespace MyNat

/-
## Inequality

We define `m ≤ n` as `∃ k, m = n + k`.
-/
