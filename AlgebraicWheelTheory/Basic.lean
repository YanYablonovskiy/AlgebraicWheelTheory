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
/-!
# Algebraic wheels

Within this file , for a type `α` , an algebraic structure `Wheel α` is defined as a type-class.
Some straightforward results are provided given such a `Wheel α`.

## Main results

- `Wheel`: the definition of the wheel type-class
- `Wheel.instCommGroup` : the subgroup induced by the wheel.
- `Wheel.instSemiRing`  : the semiring induced by the wheel.

As well as all associated instances, and assorted wheel identities.

## Notation

 - `\ₐ` : The notation for the wheel division unary operation, input as `\\ₐ`.

## References

See JESPER CARLSTRÖM (2004) for the original account  `Wheels – on division by zero`.
-/


/-- A Wheel is an algebraic structure which has two binary operations `(+,*)`, like a ring.
Similarly to a commutative ring, a Wheel is a commutative monoid in both operations. Additionally,
there is a multiplicative unary map `wDiv` which is an involution, as well as a few idiosyncratic
properties in the interactions of the `+`,`*` and `wDiv`.
-/
@[ext]
class Wheel.{u} (α : Type u) extends AddCommMonoid α, CommMonoid α where
/-- The map emulating division. -/
wDiv (a : α) : α
/-- This `wDiv` must be an involution -/
inv_wDiv: ∀ a : α, wDiv (wDiv a) = a
/-- This `wDiv` map is multiplicative. -/
wDiv_mul: ∀ a b : α, wDiv (a*b) = (wDiv a)*(wDiv b)
add_mul_wDiv: ∀ a b c: α, (a + b*c)*(wDiv b) = a*(wDiv b) + c + 0*b
right_mul_distrib: ∀ a b c: α, (a + b)*c + 0*c = a*c + b*c
right_mul_distrib': ∀ a b c: α, (a + 0*b)*c = a*c + 0*b
zero_mul_zero: (0:α)*0 = 0
div_add_zero: ∀ a b : α, wDiv (a + 0*b) = (wDiv a) + 0*b
wDiv_zero_add: ∀ a : α, 0*(wDiv 0) + a = 0*(wDiv 0)


open Wheel



universe u
variable {α : Type u} [W : Wheel α] (a b : α)

prefix:100  "\\ₐ" => wDiv

attribute [simp] inv_wDiv wDiv_mul add_mul_wDiv zero_mul_zero div_add_zero wDiv_zero_add

/-- We have that `wDiv 1` is one, in general
-/
@[simp, grind]
lemma Wheel.wdiv_one : \ₐ1 = (1:α) := by
  calc  \ₐ 1 = (1:α)* \ₐ 1 := by simp
          _   = \ₐ\ₐ 1 * \ₐ 1 := by simp
          _   = \ₐ (\ₐ 1 * 1) := by rw [wDiv_mul]
          _   = \ₐ \ₐ 1  := by simp
          _   = 1 := by simp

/-- For any two terms `a b :α` with `[Wheel α]` , we have that `0*a + 0*b = 0*a*b`.
-/
@[simp, grind]
lemma Wheel.zero_mul_add : ∀a b: α, 0*a + 0*b = 0*a*b := by
 intro a b
 rw [add_comm,←right_mul_distrib' 0 a b]
 simp

/-- For any `a :α` and `[Wheel α]` , `(0* \ₐ 0)*a = 0* \ₐ 0`. Morally, this is like
saying infinity times anything is infinity, complementing the axiom `wDiv_zero_add`.
-/
@[simp, grind]
lemma Wheel.zero_wdiv_mul : ∀a: α, (0* \ₐ 0)*a = 0* \ₐ 0 := by
  intro a
  rw [←zero_mul_add,wDiv_zero_add]

/-- For any `a :α` and `[Wheel α]` , `a*\ₐa = 1 + 0*(a*\ₐa)` .
-/
@[simp, grind]
lemma Wheel.wdiv_self : ∀a: α, a*\ₐa = 1 + 0*(a*\ₐa) := by
  intro a
  have := add_mul_wDiv 0 (a:α) 1
  simp only [zero_add,mul_one] at this
  nth_rw 1 [this]
  rw [add_comm _ 1,add_assoc]
  suffices h: 0 * \ₐa + 0 * a = 0 * (a * \ₐa) by rw [h]
  simp
  rw [mul_assoc,mul_comm _ a]

/-- Defining the map from Wheels to its largest contained Semirings -/
@[reducible]
def 𝓡 (α : Type u) [Wheel α] := {x : α // (0 : α) * x = 0}
/-- Defining the map from Wheels to its Group -/
@[reducible]
def 𝓢 (α : Type u) [Wheel α] := {x : α // 0 * x = 0 ∧ 0 * \ₐx = 0}

@[reducible]
def 𝓢' (α : Type u) [Wheel α] := {x : (𝓡 α) //  0 * \ₐ(x.val) = 0}

@[reducible]
def 𝓢to𝓡 {α : Type u} [Wheel α] : (𝓢 α) → (𝓡 α) := fun ⟨x,⟨hx,_⟩⟩ ↦ ⟨x,hx⟩

@[reducible]
def 𝓡to𝓢' (α : Type u) [Wheel α] : (x:(𝓡 α)) → (0 * \ₐ(x.val) = 0) → (𝓢' α) :=
 fun x hx ↦ ⟨x,hx⟩

@[reducible]
def 𝓡to𝓢 {α : Type u} [Wheel α] : (x:(𝓡 α)) → (0 * \ₐ(x.val) = 0) → (𝓢 α) :=
 fun x hx ↦ ⟨x,⟨x.prop,hx⟩⟩

instance [Wheel α] : Coe (𝓢 α) (𝓡 α) where
 coe := 𝓢to𝓡

instance [Wheel α] : Coe (𝓢 α) (𝓢' α) where
 coe := fun ⟨x,⟨hxz,hxdiv⟩⟩ ↦ ⟨⟨x,hxz⟩,hxdiv⟩

instance [Wheel α] : Coe (𝓢' α) (𝓢 α) where
 coe := fun ⟨⟨x,hxz⟩,hxdiv⟩ ↦ ⟨x,⟨hxz,hxdiv⟩⟩

/-- Addition instance for the induced semiring -/
instance : Add (𝓡 α) where
 add := fun a b ↦ by
  refine ⟨a + b, ?_⟩
  calc 0*(↑a + ↑b) = (a + b)*(0:α) + 0*0 := by rw [zero_mul_zero,add_zero,mul_comm]
  _ = 0 := by rw [right_mul_distrib,mul_comm,a.prop,mul_comm,b.prop,zero_add]

/-- Multiplication instance for the induced group -/
instance : Mul (𝓢 α) where
 mul := fun a b ↦ by
  refine ⟨a*b, ⟨by rw [←mul_assoc,a.prop.1,b.prop.1],?_⟩⟩
  rw [wDiv_mul,←mul_assoc,a.prop.2,b.prop.2]

lemma mul𝓢_def : ∀(a b : (𝓢 α)),a*b = ⟨a.val,a.prop⟩*⟨b.val,b.prop⟩ := fun a b ↦ by rfl

lemma mul𝓢_def' : ∀(a b : (𝓢 α)),a*b = ⟨a.val*b.val,(a*b).prop⟩ := fun a b ↦ by rfl

instance : Inv (𝓢 α) where
 inv := fun a ↦ ⟨\ₐa, ⟨a.prop.2,by rw [inv_wDiv,a.prop.1]⟩⟩

lemma inv𝓢_def : ∀(a : (𝓢 α)), a⁻¹ = ⟨\ₐ↑a,a⁻¹.prop⟩ := fun a ↦ by rfl

/-- Multiplication instance for the induced semiring -/
instance : Mul (𝓡 α) where
  mul := fun a b ↦ by
   refine ⟨a * b, ?_⟩
   rw [←mul_assoc,←zero_mul_add,a.prop,b.prop,zero_add]

lemma mul𝓡_def : ∀(a b : (𝓡 α)),a*b = ⟨a.val,a.prop⟩*⟨b.val,b.prop⟩ := fun a b ↦ by rfl

lemma mul𝓡_def' : ∀(a b : (𝓡 α)),a*b = ⟨a.val*b.val,(a*b).prop⟩ := fun a b ↦ by rfl

lemma mul𝓡_coe : ∀(a b : (𝓡 α)),a.val*b.val = (a*b).val := fun _ _ ↦ rfl

/-- CommMagma instance for the multiplicative monoid -/
instance Wheel.instSCommMagma : CommMagma (𝓢 α) where
 mul_comm := fun a b ↦ by
  ext
  convert W.mul_comm a b

/-- CommMagma instance for the multiplicative monoid -/
instance Wheel.instRCommMagma : CommMagma (𝓡 α) where
 mul := fun a b ↦ a * b
 mul_comm := fun a b ↦ by
  ext
  convert W.mul_comm a b

instance Wheel.instLeftDistrib : LeftDistribClass (𝓡 α) where
 left_distrib := by
  intro a b c;ext
  calc a * (b + c) = (b + c)*a + (0:α)*a := by rw [mul_comm,a.prop,add_zero]
  _ = a*b + a*c :=                      by simp_rw [right_mul_distrib,mul_comm]

/-- AddCommMagma instance for the additive monoid -/
instance Wheel.instAddCommMagma : AddCommMagma (𝓡 α) where
 add := fun a b ↦ a + b
 add_comm := fun a b ↦ by ext;convert W.add_comm a b

/-- AddCommMonoid instance for the AdditiveCommMonoid of the induced semiring TODO: GOLF -/
instance Wheel.instAddCommMonoid : AddCommMonoid (𝓡 α) where
 add_assoc := fun a b c ↦ by
  ext
  convert W.add_assoc a b c
 zero := ⟨0,zero_mul_zero⟩
 zero_add := fun a ↦ by ext;convert W.zero_add a
 add_zero := fun a ↦ by ext;convert W.add_zero a
 nsmul := fun n a ↦ by
  refine ⟨n • a, ?_ ⟩
  induction' n with m ih
  · rw [zero_nsmul,zero_mul_zero]
  · rw [succ_nsmul,mul_comm]
    calc ((m • a.val) + ↑a) * 0 = (m • ↑a + ↑a) * 0 + 0*0 := by rw [zero_mul_zero,add_zero]
    _ =  (m • ↑a) * 0 + ↑a*0 := by rw [right_mul_distrib]
    _ = 0 := by  rw [mul_comm,ih,mul_comm,a.prop,zero_add]
 nsmul_succ := by intro n a; ext; convert W.nsmul_succ n a
 nsmul_zero := fun x ↦ by ext; convert W.nsmul_zero x

/-- CommMonoid instance for the multiplicative CommMonoid of the induced semiring -/
instance Wheel.instRCommMonoid : CommMonoid (𝓡 α) where
 mul_assoc := fun a b c ↦ by
  ext
  convert W.mul_assoc a b c
 one := ⟨1,mul_one 0⟩
 one_mul := fun a ↦ by ext;convert W.one_mul a
 mul_one := fun a ↦ by ext;convert W.mul_one a

/-- CommMonoid instance for the induced group. -/
instance Wheel.instSCommMonoid : CommMonoid (𝓢 α) where
 mul_assoc := fun a b c ↦ by
  ext
  convert W.mul_assoc a b c
 one := ⟨1,⟨mul_one 0,by rw [wdiv_one,mul_one 0]⟩⟩
 one_mul := fun a ↦ by ext;convert W.one_mul a
 mul_one := fun a ↦ by ext;convert W.mul_one a


/-- The commutative group corresponding to the "subset" of a wheel `[W:Wheel α]`:
 `{ w ∈ W |  0*w = 0 ∧ 0*\ₐw = 0}`. Note this is strictly not the case, as it is a subtype,
but its the analogous case. -/
instance Wheel.instCommGroup : CommGroup (𝓢 α) where
  inv_mul_cancel := fun a ↦ by
   rw [inv𝓢_def,mul_comm,mul𝓢_def']
   ext;congr
   rw [wdiv_self,←mul_assoc,a.prop.1,a.prop.2,add_zero]


/-- The Semiring induced by a `[W:Wheel α]`,the corresponding to the "subset":
`{ w ∈ W |  0*w = 0}`. Note this is strictly not the case, as it is a subtype,
but its the analogous case. -/
instance Wheel.instSemiRing : Semiring (𝓡 α) where
  left_distrib := left_distrib
  right_distrib := fun a b c ↦ by
    simp only [mul_comm,left_distrib]
  zero_mul := fun a ↦ by
   ext; convert a.prop
  mul_zero := fun a ↦ by ext; rw [mul_comm]; convert a.prop


/-- A predicate version when an explicit option is needed, without typeclass baggage. -/
def Wheel.toSemiring {α : Type u} [Wheel α] (hα : ∀a:α, 0*a = 0): Semiring α := by
 have left_distrib: ∀(a b c:α),a*(b + c) = a*b + a*c := by
  intro a b c
  calc a * (b + c) = (b + c)*a + 0*a := by rw [mul_comm,hα a,add_zero]
  _ = a*b + a*c :=                      by simp_rw [right_mul_distrib,mul_comm]
 exact {
 left_distrib := left_distrib
 right_distrib := fun a b c ↦ by simp [mul_comm,left_distrib]
 zero_mul := hα
 mul_zero := fun a ↦ by rw [mul_comm,hα]}



/-- For any `a b c :α` and `[Wheel α]` , ` a*c = b*c → a + 0*c*\ₐc = b + 0*c*\ₐc `. This is the
version of cancellation that wheels enjoy.
-/
lemma Wheel.wdiv_right_cancel' : ∀a b c: α, a*c = b*c → a + 0*c*\ₐc = b + 0*c*\ₐc := by
  intro a b c hab
  have: (a * c *\ₐc) = (b * c *\ₐc) := by rw [hab]
  rw [mul_assoc,mul_assoc,wdiv_self c,mul_comm,mul_comm b] at this
  rw [right_mul_distrib',right_mul_distrib'] at this
  simp only [one_mul,←mul_assoc] at this
  exact this

/-- Since we have that `wDiv 1` is one, therefore `wDiv` is a Monoid Automorphism on `α`.
-/
instance Wheel.toMonoidHom : MonoidHom α α where
 toFun := wDiv
 map_one' := wdiv_one
 map_mul' := wDiv_mul

/-- If `c  :α` is a unit and `[Wheel α]` , then the inverse and Wheel self-division are related.
The predicate version -/
lemma Wheel.isUnit_add_eq_div_add' (c : α) (hc : IsUnit c):∃b:α,c * b = 1 ∧ b * c = 1
 ∧ (b + (0:α)*\ₐc = \ₐc + 0*b) := by
 rw [isUnit_iff_exists] at hc
 obtain ⟨x,hx1,hx2⟩ := hc
 use x
 refine ⟨hx1,hx2,?_⟩
 calc x + 0 * \ₐc = x*\ₐ(x*c) + 0*\ₐc := by simp [hx2]
 _ = x*(\ₐx)*\ₐc + 0*\ₐc := by rw [wDiv_mul,←mul_assoc]
 _ = \ₐc + 0*x*\ₐx + 0*\ₐc := by rw [wdiv_self,right_mul_distrib',one_mul,←mul_assoc]
 _ = \ₐc + 0*x*\ₐx*\ₐc := by rw [add_assoc,mul_assoc 0,zero_mul_add]
 _ = \ₐc + 0*x := by rw [mul_assoc (0*x),←wDiv_mul,hx2,wdiv_one,mul_one]

/-- If `c  :α` is a unit and `[Wheel α]` , then the inverse and Wheel self-division are related. -/
lemma Wheel.isUnit_add_eq_div_add (c : αˣ) : (c⁻¹ + (0:α)*\ₐ↑c = \ₐ↑c + 0*c⁻¹) := by
 have: c⁻¹ * c = (1:α) := by simp
 calc c⁻¹ + (0:α) * \ₐ↑c = c⁻¹*\ₐ(↑c⁻¹*↑c) + 0*\ₐ↑c := by simp
 _ = c⁻¹*(\ₐ↑c⁻¹)*\ₐ↑c + 0*\ₐ↑c := by rw [wDiv_mul,←mul_assoc]
 _ = \ₐ↑c + 0*↑c⁻¹*\ₐ↑c⁻¹ + 0*\ₐ↑c := by rw [wdiv_self,right_mul_distrib',one_mul,←mul_assoc]
 _ = \ₐ↑c + 0*↑c⁻¹*\ₐ↑c⁻¹*\ₐ↑c := by rw [add_assoc,mul_assoc 0,zero_mul_add]
 _ = \ₐ↑c + 0*↑c⁻¹ := by rw [mul_assoc,←wDiv_mul,this,wdiv_one,mul_one]


/-- If  `c  :α` is a unit and `[Wheel α]` , then we have that `0*\ₐc + 0*\ₐc⁻¹ = 0` . -/
@[simp]
lemma Wheel.isUnit_zero_eq_div_mul_add (c : αˣ) : (0:α)*\ₐ↑c + (0:α)*\ₐ↑c⁻¹ = 0 := by
 rw [zero_mul_add,mul_assoc,←wDiv_mul,show c * c⁻¹ = (1:α) by simp,wdiv_one,mul_one]


/-- If  `c  :α` is a unit and `[Wheel α]`, then the inverse `c⁻¹` is related to `\ₐc` as follows -/
lemma Wheel.isUnit_inv_eq_div_add (c : αˣ) : c⁻¹  = \ₐ↑c + (0:α)*c⁻¹*\ₐ↑c⁻¹ := by
 calc ↑c⁻¹ = ↑c⁻¹ + (0:α)*\ₐ↑c +  0*\ₐ↑c⁻¹  := by rw [add_assoc,isUnit_zero_eq_div_mul_add,add_zero]
 _ =  (↑c⁻¹ +  0*\ₐ↑c) + (0:α)*\ₐ↑c⁻¹       := by rw [add_assoc]
 _ =  \ₐ↑c + 0*c⁻¹ + (0:α)*\ₐ↑c⁻¹           := by rw [isUnit_add_eq_div_add c]
 _ =  \ₐ↑c + (0:α)*c⁻¹*\ₐ↑c⁻¹               := by rw [add_assoc,zero_mul_add]


/-- If  `c  :α` is a unit and `[Wheel α]`, then the inverse `\ₐc` is further related to  `c⁻¹` -/
lemma Wheel.isUnit_div_eq_inv_add (c : αˣ) : \ₐ↑c = c⁻¹ + (0:α)*↑c*\ₐ↑c := by
 calc \ₐ↑c = \ₐ↑c + (0:α)*↑c⁻¹ +(0:α)*↑c := by simp [add_assoc,zero_mul_add]
 _ =  ↑c⁻¹ + 0 * \ₐ↑c * ↑c := by simp [←isUnit_add_eq_div_add,add_assoc,zero_mul_add]
 _ =  c⁻¹ + (0:α)*↑c*\ₐ↑c :=  by simp only [mul_assoc,mul_comm]


/-- If `x : (𝓡 α)` is `\ₐ`-invertible , then it is also part of (𝓢 α) -/
@[reducible]
def Wheel.isUnit_wdiv_coe (x : (𝓡 α)ˣ) (hinv : x⁻¹ = \ₐ(x : α)) : (𝓢 α) := by
 refine ⟨ x, ⟨(x:𝓡 α).prop,?_⟩⟩
 calc (0:α) * \ₐ↑↑x = (0*(↑x)) * \ₐ↑↑x := by rw [(x:𝓡 α).prop]
 _ = 0 * (↑↑x * ↑↑x⁻¹) := by rw [mul_assoc,←hinv]
 _ = 0*↑↑(x*x⁻¹) := by rfl
 _ = 0 := by rw [(show ↑↑(x * x⁻¹)=(1:α) by simp;congr),mul_one];


/-- If  (x : 𝓡 α) is a unit, then it is a unit of the original wheel. -/
lemma Wheel.isRUnit_isUnit (x : 𝓡 α) (hru : IsUnit x) : IsUnit (x:α) := by
 rw [isUnit_iff_exists] at *
 obtain ⟨y,hxy,hyx⟩ := hru
 use y.val
 simp [mul𝓡_coe,hxy,hyx];rfl


example : ∀(x y z: α),0*x + 0*y + 0*z + 0*z = 0*x*y*(z^2) := by
 intro x y z
 calc 0*x + 0*y + 0*z + 0*z = 0*(x*y) + 0*z + 0*z := by rw [zero_mul_add,mul_assoc]
 _ = 0*x*y*z + 0*z := by rw [zero_mul_add,←mul_assoc]
 _ = 0*(x*y*z) + 0*z := by rw [mul_assoc,mul_assoc,←mul_assoc x]
 _ = 0*(x*y*z)*z := by simp
 _ = 0*x*(y*z^2) := by rw [mul_assoc x,←mul_assoc,mul_assoc (0*x),mul_assoc y,←pow_two]
 _ = 0*x*y*(z^2) := by simp only [mul_assoc]
