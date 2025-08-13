/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
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
zero_mul_zero: (0:α)*0 = 0
div_add_zero: ∀ a b : α, wDiv (a + 0*b) = (wDiv a) + 0*b
wDiv_zero_add: ∀ a : α, 0*(wDiv 0) + a = 0*(wDiv 0)


open Wheel

universe u
variable {α : Type u} [Wheel α] (a b : α)


prefix:100  "\\ₐ" => wDiv

attribute [simp] inv_wDiv mul_wDiv add_wDiv zero_mul_zero div_add_zero wDiv_zero_add


/-- We have that `wDiv 1` is one, in general
-/
@[simp, grind]
lemma Wheel.wdiv_one : \ₐ1 = (1:α) := by
  calc  \ₐ 1 = (1:α)* \ₐ 1 := by simp
          _   = \ₐ\ₐ 1 * \ₐ 1 := by simp
          _   = \ₐ (\ₐ 1 * 1) := by rw [mul_wDiv]
          _   = \ₐ \ₐ 1  := by simp
          _   = 1 := by simp

/-- For any two terms `a b :α` with `[Wheel α]` , we have that `0*a + 0*b = 0*a*b`.
-/
@[simp, grind]
lemma Wheel.zero_mul_add : ∀a b: α, 0*a + 0*b = 0*a*b := by
 intro a b
 rw [add_comm,←left_mul_distrib' 0 a b]
 simp


/-- For any `a :α` and `[Wheel α]` , `(0* \ₐ 0)*a = 0* \ₐ 0`. Morally, this is like
saying infinity times anything is infinity, complementing the axiom `wDiv_zero_add`.
-/
@[simp, grind]
lemma Wheel.zero_wdiv_mul : ∀a: α, (0* \ₐ 0)*a = 0* \ₐ 0 := by
  intro a
  rw [←zero_mul_add,wDiv_zero_add]

/--  For any `a :α` and `[Wheel α]` , `a*\ₐa = 1 + 0*(a*\ₐa)` .
-/
@[simp, grind]
lemma Wheel.wdiv_self : ∀a: α, a*\ₐa = 1 + 0*(a*\ₐa) := by
  intro a
  have := add_wDiv 0 (a:α) 1
  simp only [zero_add,mul_one] at this
  nth_rw 1 [this]
  rw [add_comm _ 1,add_assoc]
  suffices h: 0 * \ₐa + 0 * a = 0 * (a * \ₐa) by rw [h]
  simp
  rw [mul_assoc,mul_comm _ a]

/-- For any `a b c :α` and `[Wheel α]` , ` a*c = b*c → a + 0*c*\ₐc = b + 0*c*\ₐc `. This is the
version of cancellation that wheels enjoy.
-/
lemma Wheel.wdiv_right_cancel': ∀a b c: α, a*c = b*c → a + 0*c*\ₐc = b + 0*c*\ₐc := by
  intro a b c hab
  have: (a * c *\ₐc) = (b * c *\ₐc) := by rw [hab]
  rw [mul_assoc,mul_assoc,wdiv_self c,mul_comm,mul_comm b] at this
  rw [left_mul_distrib',left_mul_distrib'] at this
  simp only [one_mul,←mul_assoc] at this
  exact this

/-- Since we have that `wDiv 1` is one, therefore `wDiv` is a Monoid Automorphism on `α`.
-/
instance Wheel.toMonoidHom : MonoidHom α α where
 toFun := wDiv
 map_one' := wdiv_one
 map_mul' := mul_wDiv

/-- If `c  :α` is a unit and `[Wheel α]` , then the inverse and Wheel self-division are related.
The predicate version -/
lemma Wheel.isUnit_add_eq_div_add' (c : α) (hc : IsUnit c):∃b:α,c * b = 1 ∧ b * c = 1
 ∧ (b + (0:α)*\ₐc = \ₐc + 0*b) := by
 rw [isUnit_iff_exists] at hc
 obtain ⟨x,hx1,hx2⟩ := hc
 use x
 refine ⟨hx1,hx2,?_⟩
 calc x + 0 * \ₐc = x*\ₐ(x*c) + 0*\ₐc := by simp [hx2]
 _ = x*(\ₐx)*\ₐc + 0*\ₐc := by rw [mul_wDiv,←mul_assoc]
 _ = \ₐc + 0*x*\ₐx + 0*\ₐc := by rw [wdiv_self,left_mul_distrib',one_mul,←mul_assoc]
 _ = \ₐc + 0*x*\ₐx*\ₐc := by rw [add_assoc,mul_assoc 0,zero_mul_add]
 _ = \ₐc + 0*x := by rw [mul_assoc (0*x),←mul_wDiv,hx2,wdiv_one,mul_one]

/-- If `c  :α` is a unit and `[Wheel α]` , then the inverse and Wheel self-division are related. -/
lemma Wheel.isUnit_add_eq_div_add (c : αˣ): (c⁻¹ + (0:α)*\ₐ↑c = \ₐ↑c + 0*c⁻¹) := by
 have: c⁻¹ * c = (1:α) := by simp
 calc c⁻¹ + (0:α) * \ₐ↑c = c⁻¹*\ₐ(↑c⁻¹*↑c) + 0*\ₐ↑c := by simp
 _ = c⁻¹*(\ₐ↑c⁻¹)*\ₐ↑c + 0*\ₐ↑c := by rw [mul_wDiv,←mul_assoc]
 _ = \ₐ↑c + 0*↑c⁻¹*\ₐ↑c⁻¹ + 0*\ₐ↑c := by rw [wdiv_self,left_mul_distrib',one_mul,←mul_assoc]
 _ = \ₐ↑c + 0*↑c⁻¹*\ₐ↑c⁻¹*\ₐ↑c := by rw [add_assoc,mul_assoc 0,zero_mul_add]
 _ = \ₐ↑c + 0*↑c⁻¹ := by rw [mul_assoc,←mul_wDiv,this,wdiv_one,mul_one]


/-- If  `c  :α` is a unit and `[Wheel α]` , then we have that `0*\ₐc + 0*\ₐc⁻¹ = 0`.  -/
@[simp]
lemma Wheel.isUnit_zero_eq_div_mul_add (c : αˣ): (0:α)*\ₐ↑c + (0:α)*\ₐ↑c⁻¹ = 0 := by
 rw [zero_mul_add,mul_assoc,←mul_wDiv,show c * c⁻¹ = (1:α) by simp,wdiv_one,mul_one]


/-- If  `c  :α` is a unit and `[Wheel α]`, then the inverse `c⁻¹` is related to `\ₐc` as follows:-/
lemma Wheel.isUnit_inv_eq_div_add (c : αˣ): c⁻¹  = \ₐ↑c + (0:α)*c⁻¹*\ₐ↑c⁻¹ := by
 calc ↑c⁻¹ = ↑c⁻¹ + (0:α)*\ₐ↑c +  0*\ₐ↑c⁻¹  := by rw [add_assoc,isUnit_zero_eq_div_mul_add,add_zero]
 _ =  (↑c⁻¹ +  0*\ₐ↑c) + (0:α)*\ₐ↑c⁻¹       := by rw [add_assoc]
 _ =  \ₐ↑c + 0*c⁻¹ + (0:α)*\ₐ↑c⁻¹           := by rw [isUnit_add_eq_div_add c]
 _ =  \ₐ↑c + (0:α)*c⁻¹*\ₐ↑c⁻¹               := by rw [add_assoc,zero_mul_add]



example : ∀(x y z: α),0*x + 0*y + 0*z + 0*z = 0*x*y*(z^2) := by
 intro x y z
 calc 0*x + 0*y + 0*z + 0*z = 0*(x*y) + 0*z + 0*z := by rw [zero_mul_add,mul_assoc]
 _ = 0*x*y*z + 0*z := by rw [zero_mul_add,←mul_assoc]
 _ = 0*(x*y*z) + 0*z := by rw [mul_assoc,mul_assoc,←mul_assoc x]
 _ = 0*(x*y*z)*z := by simp
 _ = 0*x*(y*z^2) := by rw [mul_assoc x,←mul_assoc,mul_assoc (0*x),mul_assoc y,←pow_two]
 _ = 0*x*y*(z^2) := by simp only [mul_assoc]
