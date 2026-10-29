/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineExecution
/-! # Original-dimension Valid/Fits discharge for the ACTUAL whole affine source
The original metadata guard supplies u<=M and the paid physical width covers
NodeBits.width a M. No individual Fits answer or coefficient sequence enters
the program; exact original build bytes were already acquired by its real run.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineValues
open SemiprimeD1StackRecoveryAffine
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (array retained done)
end E
/-- Proof interpretation of the exact array physically framed by the same whole source. -/
def outputArray (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool):Array SemiprimeRationalBits.RationalWord:=
  (E.array a M u selected width).toArray
/-- Original width/metadata alone give all semantic fit capacities, exact coefficients and positive raw denominators. -/
theorem acquired_values (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool)
    (hu:u≤ M) (hW:SemiprimeD1RecoveryNodeBits.width a M≤ width.length):
    SemiprimeJetBits.decode (outputArray a M u selected width)=
      (SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u selected.val).denominator.coefficients ∧
    SemiprimeJetBits.Valid (outputArray a M u selected width) ∧
    SemiprimeJetBits.Bounded (outputArray a M u selected width) width.length:=by
  have h:=SemiprimeD1RecoveryNodeBits.denominator_correct width a M u selected hu hW
  simpa only [outputArray,E.array,Array.toArray_toList,E.retained] using h
/-- Every actual indexed coefficient denominator is positive; out-of-range reads use the literal valid ZERO. -/
theorem denominator_positive (a M u:Nat) (selected:Fin (2^(a+1))) (width:List Bool)
    (hu:u≤ M) (hW:SemiprimeD1RecoveryNodeBits.width a M≤ width.length) (i:Nat):
    0<SemiprimeBitArithmetic.bitValue (SemiprimeJetBits.wordAt (outputArray a M u selected width) i).denominator:=
  SemiprimeJetBits.wordAt_valid _ (acquired_values a M u selected width hu hW).2.1 i
/-- SAME complete five-word source internally acquires the valid, correctly fitted ORIGINAL denominator array. -/
theorem source_run_valid (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val)
    (hu:u≤ M) (hW:SemiprimeD1RecoveryNodeBits.width a M≤ width.length):
    ∃s≤ SemiprimeD1StackRecoveryAffineExecution.timeBound a M u selected t width,
      SemiprimeD1StackCalls.run program s
        (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (E.done a M u selected t width) ∧
      SemiprimeJetBits.decode (outputArray a M u selected width)=
        (SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u selected.val).denominator.coefficients ∧
      SemiprimeJetBits.Valid (outputArray a M u selected width) ∧
      SemiprimeJetBits.Bounded (outputArray a M u selected width) width.length:=by
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryAffineExecution.source_run a M u selected t width ht
  exact ⟨s,hs,hr,acquired_values a M u selected width hu hW⟩
end RiemannGaussian.SemiprimeD1StackRecoveryAffineValues
