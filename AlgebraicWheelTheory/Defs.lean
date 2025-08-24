import AlgebraicWheelTheory.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Star.Basic


open Star in
postfix:100  "⋆" => Star.star

universe u

class abbrev InvolutionMonoid (α: Type u) := Monoid α, StarMul α

namespace InvolutionMonoid

universe v

variable {α : Type u} {β : Type v}

instance [DivisionMonoid α] : InvolutionMonoid α where
 star x := x⁻¹
 star_involutive := inv_inv
 star_mul := mul_inv_rev

open Function in
example [InvolutionMonoid α] : Involutive (fun x : α ↦ x⋆) := by
 simp [Involutive]

@[ext]
structure InvolutionMonoidHom (α : Type u) (β : Type v) [InvolutionMonoid α]
    [InvolutionMonoid β] where
  toFun : α →ₙ* β
  invol_hom (x : α) : toFun (x⋆) = (toFun x)⋆

#check IsUnit.star

theorem isUnit_star' [InvolutionMonoid α] {x : α} : IsUnit (x⋆) ↔ IsUnit x := isUnit_star


open Function in
instance [InvolutionMonoid α] [InvolutionMonoid β] : FunLike (InvolutionMonoidHom α β) α β where
 coe inv_mh := inv_mh.toFun
 coe_injective' := by
  rw [Injective]
  intro x y heq
  ext z;simp [heq]

variable [Field α]


end InvolutionMonoid
