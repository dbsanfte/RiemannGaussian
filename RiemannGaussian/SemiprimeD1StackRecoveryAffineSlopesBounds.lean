/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBounds
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopes
/-! # One paid row reversal has linear whole-source cost in the ACTUAL original framed slope bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopesBounds
open SemiprimeD1StackRecoveryAffineView
open SemiprimeRationalBits (RationalWord)
/-- The actual complete framed vector length is the sum of actual per-row bit lengths plus its terminator. -/
theorem vector_sum (xs:List RationalWord):
    (vector xs).length=(xs.map (fun x=>2*(x.numerator.magnitude.length+x.denominator.length)+5)).sum+1:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change (SemiprimeD1StackRecoveryGridView.slopeRow x (vector xs)).length=_
    rw [SemiprimeD1StackRecoveryGridByteBounds.slopeRow_length,ih]
    simp only [List.map_cons,List.sum_cons]
    omega
/-- Reversing row ORDER changes none of the physically copied raw sign/padding/framing bytes. -/
theorem vector_reverse_length (xs:List RationalWord):(vector xs.reverse).length=(vector xs).length:=by
  rw [vector_sum,List.map_reverse,List.sum_reverse,←vector_sum]
/-- Every TRUE tag, actual two-Field/two-Frame call, both scalar drains and final EOF are paid once. -/
theorem reverse_le (xs:List RationalWord):
    SemiprimeD1StackRecoveryAffineSlopeReverse.runBound xs≤ 30*(vector xs).length:=by
  induction xs with
  | nil=>change 2≤30*1;decide
  | cons x xs ih=>
    change SemiprimeD1StackRecoveryAffineSlopeReverse.rowTime x+
      SemiprimeD1StackRecoveryAffineSlopeReverse.runBound xs≤ _
    rw [SemiprimeD1StackRecoveryAffineReadBounds.row_length]
    unfold SemiprimeD1StackRecoveryAffineSlopeReverse.rowTime
    omega
/-- Whole real original-tape copy/reversal/literal-ONE seed costs a fixed linear actual-byte budget. -/
theorem source_le (xs:List RationalWord):
    SemiprimeD1StackRecoveryAffineSlopes.runBound xs≤ 50*((vector xs).length+1):=by
  have h:=reverse_le xs
  unfold SemiprimeD1StackRecoveryAffineSlopes.runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopesBounds
