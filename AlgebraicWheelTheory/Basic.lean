import Mathlib.Algebra.Ring.Defs


/-- A Wheel is a `Semiring` satisfying a few more rules:
* There is a multiplicative unary map `wDiv` which is an involution.
* Given an arbitrary `a b c : α` , ` (a + b*c)*(wDiv b) = a*(wDiv b) + c` .
* For any term `a : α` , we have `0*(wDiv 0) + a = 0*(wDiv 0)`.
-/
class Wheel.{u} (α : Type u) extends Semiring α where
wDiv (a : α) : α
inv_wDiv: ∀ a : α, wDiv (wDiv a) = a
mul_wDiv: ∀ a b : α, wDiv (a*b) = (wDiv a)*(wDiv b)
add_wDiv: ∀ a b c: α, (a + b*c)*(wDiv b) = a*(wDiv b) + c
wDiv_zero_add: ∀ a : α, 0*(wDiv 0) + a = 0*(wDiv 0)
