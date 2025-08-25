/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
import AlgebraicWheelTheory.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Star.Basic
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

namespace InvolutionMonoid

/-- The instance allowing for forgetful synthesis of `InvolutionMonoid α` from `Group α`. -/
instance [DivisionMonoid α] : InvolutionMonoid α where
 star x := x⁻¹
 star_involutive := inv_inv
 star_mul := mul_inv_rev

open Function in
example [InvolutionMonoid α] : Involutive (fun x : α ↦ x⋆) := by
 simp [Involutive]

end InvolutionMonoid

/-- An involution monoid homomorphism is a monoid homomorphism `f` between two involution monoids
`(M₁,⋆₁)` and `(M₂,⋆₂)` such that `∀x ∈ M₁, f (x⋆₁) = f (x)⋆₂ ` . -/
@[ext]
class InvolutionMonoidHom (α : Type u) (β : Type v) [InvolutionMonoid α]
    [InvolutionMonoid β] where
  toFun : α →ₙ* β
  invol_hom (x : α) : toFun (x⋆) = (toFun x)⋆

namespace InvolutionMonoidHom

theorem isUnit_star' [InvolutionMonoid α] {x : α} : IsUnit (x⋆) ↔ IsUnit x := isUnit_star


open Function in
instance [InvolutionMonoid α] [InvolutionMonoid β] : FunLike (InvolutionMonoidHom α β) α β where
 coe inv_mh := inv_mh.toFun
 coe_injective' := by
  rw [Injective]
  intro x y heq
  ext z;simp [heq]

def toMulHom (α β : Type u) [InvolutionMonoid α] [InvolutionMonoid β] [InvolutionMonoidHom α β]
    : MulHom α β where
  toFun := toFun
  map_mul' := by simp

instance [InvolutionMonoid α] [InvolutionMonoid β] [InvolutionMonoidHom α β]: MulHomClass (InvolutionMonoidHom α β) α β where
  map_mul := by intros; simp


end InvolutionMonoidHom
