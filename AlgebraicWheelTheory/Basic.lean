import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs

/-- A Wheel is an algebraic structure which has two binary operations `(+,*)`, like a ring.
Similarly to a commutative ring, a Wheel is a commutative monoid in both operations. Additionally,
there is a multiplicative unary map `wDiv` which is an involution, as well as a few idiosyncratic
properties in the interactions of the `+`,`*` and `wDiv`.
-/
class Wheel.{u} (α : Type u) extends AddCommMonoid α, CommMonoid α where
wDiv (a : α) : α
inv_wDiv: ∀ a : α, wDiv (wDiv a) = a
mul_wDiv: ∀ a b : α, wDiv (a*b) = (wDiv a)*(wDiv b)
add_wDiv: ∀ a b c: α, (a + b*c)*(wDiv b) = a*(wDiv b) + c + 0*b
left_mul_distrib: ∀ a b c: α, (a + b)*c + 0*c = a*c + b*c
left_mul_distrib': ∀ a b c: α, (a + 0*b)*c = a*c + 0*b
zero_mul_zero: 0*0 = 0
div_add_zero: ∀ a b : α, wDiv (a + 0*b) = (wDiv a) + 0*b
wDiv_zero_add: ∀ a : α, 0*(wDiv 0) + a = 0*(wDiv 0)
