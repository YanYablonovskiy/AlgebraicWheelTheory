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

lemma prod_star_assoc (x : α × α) : (x⋆)⋆ = x⋆⋆ := rfl

lemma star_star' (x : α × α) : x⋆⋆ = x := rfl


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

structure InvCon [Star (α × α)] extends Con (α × α) where
  star' x y (hxy : r x y) : r (x⋆) (y⋆)

def InvConProd : InvCon (α := α) where
  mul' := by
    rintro w x y z ⟨a1,b1,h⟩ ⟨a2,b2,h2⟩
    refine ⟨a1*a2,b1*b2,?_⟩
    repeat rw [show ∀k1 k2 k3 k4 : α, (k1*k2,k3*k4)=(k1,k3)*(k2,k4) by simp]
    rw [mul_comm (a1,a1),←mul_assoc,mul_assoc (a2,a2),h]
    rw [mul_comm,←mul_assoc,mul_comm (y.1,y.2),h2]
    simp only [←mul_assoc,mul_comm]
  star' := fun x y ⟨a,b,h⟩ ↦ by
    refine ⟨a,b,?_⟩
    simp [Prod.eq_iff_fst_eq_snd_eq] at h
    simp [h]

/-- The quotient space for the equivalence operation: equiv_rel.
In the same universe as α, to be the InvMon instance after coercions.
This is Definition 2.6 of the reference. -/
@[reducible]
def MStar (α : Type u) [CommMonoid α] : Type u :=  (InvConProd (α:=α)).Quotient

namespace Function.Surjective

protected abbrev involutionmonoid {M₂ : Type u} [InvolutionMonoid α]
    [Monoid M₂] [Star M₂] (f : α → M₂) (hf : Surjective f) (mul : ∀ x y, f (x * y) = f x * f y)
    (invol : ∀ x, f (x⋆) = (f x)⋆) : InvolutionMonoid M₂ where
  star_involutive := by
    rw [Involutive]
    intro x
    have (y : α) : f ( y⋆⋆ ) =  (f y)⋆⋆ := by simp only [invol]
    obtain ⟨⟨xₐₐinv,hxₐ⟩,xinv,hx⟩ := And.intro (hf (x⋆⋆)) (hf x)
    rw [←hx,←this xinv,star_involutive]
  star_mul x y := by
   have (x y : α) : f (x * y)⋆ =  f (y⋆) * f (x⋆) := by
    calc f (x * y)⋆ = f ((x * y)⋆) := (invol (x * y)).symm
    _ = f ( (y⋆) * (x⋆) ) := congrArg f (star_mul x y)
    _ = f (y⋆) * f (x⋆) := mul (y⋆) (x⋆)
   obtain ⟨⟨xinv,hx⟩,yinv,hy⟩ := And.intro (hf x) (hf y)
   rw [←hx,←hy,←invol xinv,←invol yinv,←this,mul]

end Function.Surjective

namespace MStar

universe v

variable {N : Type v} [InvolutionMonoid N] (ϕ : α →ₙ* N)

noncomputable
instance : Coe (MStar α) (α × α) where
 coe x := x.out

noncomputable
instance : Star (MStar α)  where
 star := Quotient.map (fun r ↦ r⋆)
   (fun a b ⟨c,⟨d,h⟩⟩ ↦ ⟨c,⟨d,by simpa [Prod.eq_iff_fst_eq_snd_eq,And.comm] using h⟩⟩)

lemma prod_out_def (x : (MStar α)) : (⟦(x.out.1,x.out.2)⟧ : MStar α) = ⟦x.out⟧ :=
  Quotient.sound ⟨1,1,by congr⟩

lemma prod_out_star (x : (MStar α)) : (⟦(x.out.2,x.out.1)⟧ : MStar α) = ⟦x.out⋆⟧ :=
  Quotient.sound ⟨1,1,by congr⟩

lemma star_out (x : α × α) : ⟦x⋆⟧ = (⟦x⟧⋆ : MStar α) := rfl

lemma out_star_eq_star_out (x : MStar α) : (⟦x.out⟧⋆ : MStar α) = ⟦x⋆.out⟧ := by simp

lemma star_assoc (x : (MStar α)) : (x⋆)⋆ = x⋆⋆ := by
 rfl

lemma out_star_star (x : MStar α) : ⟦x.out⋆⋆⟧  = x := by
 rw [star_star,Quotient.out_eq]

lemma equiv_star_quot_eq (x y : α × α) : equiv_rel x y →
    (⟦x⋆⟧ : (MStar α) ) = ⟦y⋆⟧ := fun ⟨a,b,h⟩ ↦ by
  refine Quotient.sound ⟨a,b,?_⟩
  simpa [Prod.eq_iff_fst_eq_snd_eq,And.comm] using h


noncomputable
instance involutionMonoid : InvolutionMonoid (MStar α) where
 star_involutive x := Quotient.inductionOn x (fun _ ↦ rfl)
 star_mul x y := Quotient.inductionOn₂ x y (fun a b ↦ Quotient.sound (by simp [mul_comm]) )

noncomputable
def φ : InvolutionMonoidHom (MStar α) N where
 toFun x := (ϕ x.out.1)*(ϕ x.out.2)⋆
 map_mul' := sorry
 invol_hom := sorry


end MStar

end CommtoInvMonoid
