import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Defs
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


open Wheel

universe u
variable {α: Type u} [Wheel α]


attribute [simp] inv_wDiv mul_wDiv add_wDiv zero_mul_zero div_add_zero wDiv_zero_add


/-- If we have that `wDiv 1` is one, then `wDiv` is a Monoid Automorphism on `α`.
-/
instance toMonoidHom [h : Fact (wDiv (1 : α) = 1)] : MonoidHom α α where
 toFun := wDiv
 map_one' := by
  apply h.out
 map_mul' := by simp


lemma zero_mul_add: ∀{a b: α}, a*0 + b*0 = 0*a*b := by
 sorry

lemma wdiv_self: ∀a : α, a * wDiv a = 0*a*a := by
 intro a
 have t1 := add_wDiv a a 0
 have t2 := div_add_zero a 0
 have t3 := mul_wDiv (wDiv a) (wDiv a)
 rw [inv_wDiv a] at t3
 --rw [mul_assoc,←t3]
 sorry
