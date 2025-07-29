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
variable {α: Type u} [Wheel α] ( a b: α)


prefix:100  "\\ₐ" => wDiv

attribute [simp] inv_wDiv mul_wDiv add_wDiv zero_mul_zero div_add_zero wDiv_zero_add


/-- We have that `wDiv 1` is one, in general
-/
lemma Wheel.wDiv_one: \ₐ 1 = (1:α) := by
  calc  \ₐ 1 = (1:α)* \ₐ 1 := by simp
          _   = \ₐ\ₐ 1 * \ₐ 1 := by simp
          _   = \ₐ (\ₐ 1 * 1) := by rw [mul_wDiv]
          _   = \ₐ \ₐ 1  := by simp
          _   = 1 := by simp




/-- Since we have that `wDiv 1` is one, therefore `wDiv` is a Monoid Automorphism on `α`.
-/
instance Wheel.toMonoidHom: MonoidHom α α where
 toFun := wDiv
 map_one' := wDiv_one
 map_mul' := mul_wDiv

example: ∀(x y z: α),0*x + 0*y + 0*z + 0*z = 0*(x*y*z)^2 := by
  intro x y z
  simp [pow_two]
  have t1:= left_mul_distrib x y 0
  have t2 := left_mul_distrib z z 0
  rw [mul_comm 0 x,mul_comm 0 y,mul_comm 0 z,←t1,add_assoc,←t2]
  sorry






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
