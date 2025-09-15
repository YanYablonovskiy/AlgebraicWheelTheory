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

set_option pp.proofs true

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

@[simp]
lemma prod_star_def (x : α × α) :
    x⋆ = (x.2,x.1) :=
  rfl

lemma star_prod_def (x : α × α) : x⋆⋆ = x := rfl


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

def ConProdSetoid : Con (α × α) where
 mul' := by
  rintro w x y z ⟨a1,b1,h⟩ ⟨a2,b2,h2⟩
  refine ⟨a1*a2,b1*b2,?_⟩
  repeat rw [show ∀k1 k2 k3 k4 : α, (k1*k2,k3*k4)=(k1,k3)*(k2,k4) by simp]
  rw [mul_comm (a1,a1),←mul_assoc,mul_assoc (a2,a2),h]
  rw [mul_comm,←mul_assoc,mul_comm (y.1,y.2),h2]
  simp only [←mul_assoc,mul_comm]

/-- The quotient space for the equivalence operation: equiv_rel.
In the same universe as α, to be the InvMon instance after coerctions -/
@[reducible]
def MStar : Type u :=  (ConProdSetoid (α:=α)).Quotient

namespace MStar

noncomputable
instance : Coe (@MStar α M) (α × α) where
 coe x := x.out

noncomputable
instance : Star (@MStar α M)  where
 star x := ⟦x.out⋆⟧

noncomputable
instance : Star (Quotient (ConProdSetoid (α := α)).toSetoid) where
 star x := ⟦x.out⋆⟧

@[simp, symm]
lemma star_def (x : @MStar α M) : x⋆ = ⟦x.out⋆⟧ := rfl

@[simp, symm]
lemma star_def' (x : @MStar α M) : x⋆ = ⟦(x.out.2,x.out.1)⟧ := rfl

@[simp, symm]
lemma prod_out_def (x : (@MStar α M)) : (⟦(x.out.1,x.out.2)⟧ :  (@MStar α M)) = ⟦x.out⟧ :=
  Quotient.sound ⟨1,1,by congr⟩

@[simp, symm]
lemma prod_out_star (x : (@MStar α M)) : (⟦(x.out.2,x.out.1)⟧ :  (@MStar α M)) = ⟦x.out⋆⟧ :=
  Quotient.sound ⟨1,1,by congr⟩

@[simp, symm]
lemma star_out_eq_out_star (x : (@MStar α M)) : (⟦x⋆.out⟧ : (@MStar α M)) = ⟦x.out⋆⟧ := by simp

@[simp, symm]
lemma out_star_eq_star_out (x : (@MStar α M)) : (⟦x.out⟧⋆ : (@MStar α M)) = ⟦x⋆.out⟧ := by simp

end MStar

end CommtoInvMonoid
