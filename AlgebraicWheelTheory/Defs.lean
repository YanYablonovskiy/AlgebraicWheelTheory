import AlgebraicWheelTheory.Basic
import Mathlib.Logic.Function.Basic

class InvolutionMonoid α extends Monoid α where
 op : α → α
 hinv_op (x:α) :  op (op x) = x

namespace InvolutionMonoid

attribute [simp] op

universe u

variable {α : Type u}

open Function in
theorem invol_fun_of_invol_monoid (IM : InvolutionMonoid α) : Involutive (IM.op) := by
 rw [Involutive]; exact IM.hinv_op

end InvolutionMonoid
