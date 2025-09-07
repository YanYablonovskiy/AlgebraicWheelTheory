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


/-- Defines the congruence ( equivalence ) relation:
(x, y) ≡S (x,y) means ∃s1,s2 : (s1,s1)(x,y) = (s2,s2)(x,y). -/
@[reducible, simp]
def equiv_rel : (α × α) → (α × α) → Prop :=
  fun ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ ↦ ∃ (a b : α) , (a, a) * (x₁,x₂) = (b, b) * (y₁,y₂)

/-- Defines the Setoid instance for the equivalence relation: equiv_rel. -/
instance instProdSetoid : Setoid (α × α) where
  r := equiv_rel
  iseqv := by
    refine ⟨fun x ↦ ⟨1,1,rfl⟩ , by rintro x y ⟨a,b,h⟩; simp; exact ⟨b,a, by simp only [h]⟩,?_⟩
    rintro x y z ⟨a1,b1,h₁⟩ ⟨a2,b2,h₂⟩
    refine ⟨a1 * a2, b1 * b2, ?_⟩
    repeat rw [show ∀x y:α,(x*y,x*y)=(x,x)*(y,y) by simp]
    rw [mul_comm,←mul_assoc,mul_comm x,h₁]
    rw [mul_assoc,mul_comm y,h₂,←mul_assoc]

/-- The quotient space for the equivalence operation: equiv_rel.
In the same universe as α, to be the InvMon instance after coerctions -/
def MStar : Type u :=  Quotient instProdSetoid (α := α × α)

end CommtoInvMonoid
