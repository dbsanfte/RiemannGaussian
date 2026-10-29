/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayRead
/-! # Linear own complete physical array-access clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBounds
open SemiprimeD1StackRecoveryAffineView
open SemiprimeRationalBits (RationalWord)
/-- Actual row bytes include both raw fields, their framing tags/delimiters and occurrence tag. -/
theorem row_length (x:RationalWord) (xs:List RationalWord):
    (vector (x::xs)).length=2*((signed x).length+x.denominator.length)+3+(vector xs).length:=by
  simp only [vector,SemiprimeD1StackRecoveryGridView.slopeTape,List.foldr_cons,
    SemiprimeD1StackRecoveryGridView.slopeRow,SemiprimeD1StackRecoveryGridView.signed,
    signed,SemiprimeSourceHistogramKeyBits.frame_length,List.length_cons]
  omega
/-- Every actual tag/count/field/tail/skip/EOF step is linear in actual tape bytes and actual markers. -/
theorem loop_le (xs:List RationalWord) (n:Nat):
    SemiprimeD1StackRecoveryAffineReadLoop.runBound xs n≤20*((vector xs).length+n+1):=by
  induction xs generalizing n with
  | nil=>
    cases n with
    | zero=>change 6≤20*(1+0+1);decide
    | succ n=>change n+6≤20*(1+(n+1)+1);omega
  | cons x xs ih=>
    cases n with
    | zero=>
      change 8*((signed x).length+x.denominator.length)+19+(vector xs).length≤_
      rw [row_length]
      omega
    | succ n=>
      have h:=ih n
      change 9*((signed x).length+x.denominator.length)+20+SemiprimeD1StackRecoveryAffineReadLoop.runBound xs n≤_
      rw [row_length]
      omega
/-- Both real preserving copies and the entire actual read loop have one fixed linear physical-input cap. -/
theorem source_le (xs:List RationalWord) (n:Nat):
    SemiprimeD1StackRecoveryAffineArrayRead.runBound xs n≤30*((vector xs).length+n+1):=by
  have h:=loop_le xs n
  unfold SemiprimeD1StackRecoveryAffineArrayRead.runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBounds
