/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsExecution
import RiemannGaussian.SemiprimeD1StackNormalizedInverseWidths
/-! # Physical input and fitted coefficient widths, independent of validity and elapsed time -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsWidths
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeRationalBits (RationalWord zeroWord)
namespace B
export SemiprimeD1StackNormalizedInverseWidths (bytes execute_bytes row_bytes read_bytes tape_bytes zero_bytes)
end B
namespace Spec
export SemiprimeD1StackRecoveryWeightsSpec (combine dotLoop weight array)
end Spec
/-- All six actual original words, including q unary markers and every paid W byte. -/
def inputSize (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):Nat:=
  (SemiprimeD1StackNormalizedInverse.tape inverse).length+(SemiprimeD1StackNormalizedInverse.tape powers).length+B.bytes scalar+q+width.length+1
/-- Every physical input is paid; no dimension or numerical value is hidden in this size. -/
theorem input_caps (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    1 ≤ inputSize inverse powers scalar q width ∧
    (SemiprimeD1StackNormalizedInverse.tape inverse).length ≤ inputSize inverse powers scalar q width ∧
    (SemiprimeD1StackNormalizedInverse.tape powers).length ≤ inputSize inverse powers scalar q width ∧
    B.bytes scalar ≤ inputSize inverse powers scalar q width ∧ q ≤ inputSize inverse powers scalar q width ∧ width.length ≤ inputSize inverse powers scalar q width:=by
  unfold inputSize
  omega
/-- Each sum successor is physically twice-fitted, regardless of zero denominators or W0. -/
theorem combine_bytes (width:List Bool) (inverse powers:List RationalWord) (j k:Nat) (acc:RationalWord):
    B.bytes (Spec.combine width inverse powers j k acc)=2*width.length+1:=B.execute_bytes .add _ _ width
/-- Every actual accumulated suffix is fitted or its literal ZERO seed; elapsed steps are irrelevant. -/
theorem dot_bytes (width:List Bool) (inverse powers:List RationalWord) (j n:Nat) (acc:RationalWord)
    (hacc:B.bytes acc ≤ 2*width.length+2):B.bytes (Spec.dotLoop width inverse powers j n acc) ≤ 2*width.length+2:=by
  induction n generalizing acc with
  | zero=>exact hacc
  | succ n ih=>exact ih _ (by rw [combine_bytes];omega)
/-- The final scalar product has exactly both fitted fields and its sign, even at W0. -/
theorem weight_bytes (width:List Bool) (q j:Nat) (scalar:RationalWord) (inverse powers:List RationalWord):
    B.bytes (Spec.weight width q j scalar inverse powers)=2*width.length+1:=B.execute_bytes .mul _ _ width
/-- Every chronological output coefficient has the actual fitted cap, without a Valid/Fits premise. -/
theorem array_bytes (width:List Bool) (q:Nat) (scalar:RationalWord) (inverse powers:List RationalWord):
    ∀word∈Spec.array width q scalar inverse powers,B.bytes word=2*width.length+1:=by
  intro word hw
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hw
  exact weight_bytes width q j scalar inverse powers
/-- Entire physical output is paid by q and W VALUES, not by their logarithms. -/
theorem array_tape_bytes (width:List Bool) (q:Nat) (scalar:RationalWord) (inverse powers:List RationalWord):
    (SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers)).length ≤ q*(4*width.length+5)+1:=by
  have h:=B.tape_bytes (Spec.array width q scalar inverse powers) (2*width.length+1)
    (by intro word hw;exact (array_bytes width q scalar inverse powers word hw).le)
  simpa only [Spec.array,List.length_map,List.length_range,show 2*(2*width.length+1)+3=4*width.length+5 by omega] using h
/-- The finite loop's arbitrary reached suffix pays its entire physical output tail. -/
theorem rows_bytes (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (r:Nat) (out:List Bool):
    (SemiprimeD1StackRecoveryWeightsOuter.rows inverse powers scalar q width r out).length=r*(4*width.length+5)+out.length:=by
  induction r generalizing out with
  | zero=>simp only [SemiprimeD1StackRecoveryWeightsOuter.rows,List.range_zero,List.map_nil,List.foldr_nil,Nat.zero_mul,Nat.zero_add]
  | succ r ih=>
    rw [SemiprimeD1StackRecoveryWeightsOuter.rows_succ,ih,B.row_bytes,weight_bytes,Nat.add_mul]
    omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsWidths
