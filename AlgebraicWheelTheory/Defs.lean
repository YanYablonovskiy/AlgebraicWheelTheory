/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
import AlgebraicWheelTheory.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Defs
/-!
# Auxillary definitions

Following JESPER CARLSTRÖM (2004) , some auxillary structures are defined.

## Main results

- `InvolutionMonoid` : the definition of an Involution monoid.
- `InvolutionMonoidHom` : defining a Involution monoid homomorphism.

As well as some associated instances, and examples/identities.

## Notation

 - `⋆` : The notation for the involution operation, aka star to use the mathlib machinery.

## References

See JESPER CARLSTRÖM (2004) for the original account  `Wheels – on division by zero`.
-/


open Star in
/-- Notation for the star operation, which is co-opted to be the involution. -/
postfix:100  "⋆" => Star.star

universe u

universe v

variable {α : Type u} {β : Type v}

/-- Defining the Involution Monoid, which is a Monoid that has involution operation `⋆`
which skew-distributes over the Monoid operation. -/
class abbrev InvolutionMonoid (α: Type u) := Monoid α, StarMul α

alias StarMonoid := InvolutionMonoid

namespace InvolutionMonoid

/-- The instance allowing for forgetful synthesis of `InvolutionMonoid α` from `Group α`. -/
instance instDivMonoid [DivisionMonoid α] : InvolutionMonoid α where
 star x := x⁻¹
 star_involutive := inv_inv
 star_mul := mul_inv_rev

instance : Mul String where
 mul x y := x ++ y

@[simp]
def mul_string_def (x y : String) : x*y = x ++ y := rfl

instance : One String where
 one := ""

@[simp]
def one_string_def : 1 = "" := rfl

instance : MulOneClass String where
 one := ""
 one_mul _ := rfl
 mul_one x := String.append_empty x


instance : Monoid String where
 mul x y := x.append y
 mul_assoc x y z := String.append_assoc x y z
 one := ""
 one_mul x := rfl
 mul_one x := by simp

/-- The instance of an involution monoid from a field with decideable equality. May not be
optimally forgetful yet (see instance below it for attempt ). But is true to the source material.
-/
instance instField [Field α] [DecidableEq α] : InvolutionMonoid α where
 star x := dite (x = 0) (fun _ ↦ 0) (fun _ ↦ x⁻¹)
 star_involutive x := match em (x=0) with
 | Or.inl hx0 => by simp [hx0]
 | Or.inr hxne0 => by simp [hxne0, inv_inv x]
 star_mul x y := match (em (x=0)) with
 | Or.inl hx0 => match (em (y=0)) with
   | Or.inl hy0  => by simp [hx0,hy0]
   | Or.inr hny0 => by simp [hx0,hny0]
 | Or.inr hy0 => match (em (x=0)) with
   | Or.inl hx0  => by simp [hx0]
   | Or.inr hnx0 => by simp [hnx0]





@[simp]
def String.reverse (x : String) : String := x.toList.reverse.toString

--TO-DO: Fix this, why is it so hard.
-- instance: InvolutionMonoid String where
--  star  := String.reverse
--  star_involutive  x := by sorry
--  star_mul x y := by sorry

/-- Showing that a group is an involution monoid -/
def group_example [Group α] : InvolutionMonoid α := inferInstance

section

variable {R : Type*} {m : Type*} [DecidableEq m] [Fintype m]

/-- The instance of an involution monoid for square matrices. -/
instance instSqMatrix [CommRing R] [Fintype m] : InvolutionMonoid (Matrix m m R) where
 star x := x.transpose
 star_involutive x := x.transpose_transpose
 star_mul x y := x.transpose_mul y

end

/-- Definition of a `* Unit` , which is a unit such that the inverse coincidences with the star. -/
structure StarUnit (α : Type u) [InvolutionMonoid α] extends Units α where
 inv_eq_star : (inv = val⋆)

postfix:1025 "ˣ*" => Units

/-- An involution monoid $(M,⋆)$ is $⋆$-invertible if every unit is a star unit. -/
structure IsStarInv (α : Type u) [InvolutionMonoid α] : Prop where
 inv_eq_star : ∀(x : αˣ), x⁻¹ = x⋆

open Function in
example [InvolutionMonoid α] : Involutive (fun x : α ↦ x⋆) := by
 simp [Involutive]

theorem isUnit_star' [InvolutionMonoid α] {x : α} : IsUnit (x⋆) ↔ IsUnit x := isUnit_star

end InvolutionMonoid

/-- An involution monoid homomorphism is a monoid homomorphism `f` between two involution monoids
`(M₁,⋆₁)` and `(M₂,⋆₂)` such that `∀x ∈ M₁, f (x⋆₁) = f (x)⋆₂ ` . -/
@[ext]
class InvolutionMonoidHom (α : Type u) (β : Type v) [InvolutionMonoid α]
    [InvolutionMonoid β] extends α →ₙ* β where
  invol_hom (x : α) : toFun (x⋆) = (toFun x)⋆

namespace InvolutionMonoidHom

open Function in
instance [InvolutionMonoid α] [InvolutionMonoid β] : FunLike (InvolutionMonoidHom α β) α β where
 coe inv_mh := inv_mh.toFun
 coe_injective' := by
  rw [Injective]
  intro x y heq
  exact InvolutionMonoidHom.ext_iff.mpr heq

instance [InvolutionMonoid α] [InvolutionMonoid β] [InvolutionMonoidHom α β] :
    MulHomClass (InvolutionMonoidHom α β) α β where
  map_mul := fun f x y ↦ (f.map_mul' x y)



end InvolutionMonoidHom
