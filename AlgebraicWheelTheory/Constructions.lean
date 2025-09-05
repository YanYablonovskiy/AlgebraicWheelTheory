/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
import AlgebraicWheelTheory.Basic
import AlgebraicWheelTheory.Defs
/-!
# Constructions

As in JESPER CARLSTRÖM (2004) , constructions of involution monoids from familiar structures
are defined.

## Main results

- `_` : sorry
- `_` : sorry

The main construction is from a commutative monoid to an involution monoid, and
solves the following universal problem:

`Let M be a commutative monoid and X an arbitrary subset of M.
 Then find an involution-monoid M∗X with η(M,X) : M → T(M∗X),
 having the property that whenever N, is a commutative involu
 tion-monoid and ϕ : M → N a monoid-morphism with ϕ(x)ϕ(x) =
 ϕ(x)ϕ(x) = e for every x ∈ X, then there is a unique ˆϕ : M∗
 X → N, with ϕ=T(ˆϕ)◦η(M,X). '

## Notation

 - `⋆` : sorry

## References

See JESPER CARLSTRÖM (2004) for the original account  `Wheels – on division by zero`.
-/

section CommtoInvMonoid

universe u

variable {α : Type u} [M : CommMonoid α] (X : Set α)

/-- Star operation instance for a cartesian product of two commutative monoids. -/
instance instProdStar : Star (α × α) where
 star := fun ⟨x₁,x₂⟩ ↦ ⟨x₂,x₁⟩

/-- Involution instance for a cartesian product of two commutative monoids. To be used to construct
an involution monoid on α. -/
instance instProdInvMon : InvolutionMonoid (α × α) where
 star_involutive x := rfl
 star_mul x y := by
  ext <;> simp [star,mul_comm]


end CommtoInvMonoid
