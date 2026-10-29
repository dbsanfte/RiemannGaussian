/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersSpec
import RiemannGaussian.SemiprimeD1StackRecoveryGridValues
/-! # Original acquired Grid argument supplies every power capacity internally
No sequence of Fits assertions or power values is a source input. The original
width theorem and actual Grid argument lineage discharge all native capacities.
The physical prepared four-word source is bound separately to these words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersValues
open SemiprimeD1StackRecoveryPowersSpec
/-- The argument is the actual stopped104-bank word, not a rational-value supplier. -/
def argument (a M u:Nat) (t width:List Bool):SemiprimeRationalBits.RationalWord:=
  SemiprimeD1StackRecoveryGridEncoding.outputWord (SemiprimeD1StackRecoveryGridExecution.result a M u t width) .argument
/-- Original retained q, already physically acquired by the sealed affine caller. -/
def retained (a M u:Nat) (t:Fin (2^(a+1))):Nat:=
  SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t.val
/-- Exact complete power values, validity and width from actual original Grid inputs and paid Node width alone. -/
theorem original_values (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length):
    (array width (argument a M u t width) (retained a M u selected)).map SemiprimeRationalBits.RationalWord.value=
      (SemiprimeD1RecoveryWeightRun.powersRun (SemiprimeD1WeightPrecision.argument a selected.val) (retained a M u selected)).value.toList ∧
    (∀x∈array width (argument a M u t width) (retained a M u selected),x.Valid) ∧
    (∀x∈array width (argument a M u t width) (retained a M u selected),SemiprimeRationalBits.Width x width.length):=by
  have ha:=SemiprimeD1StackRecoveryGridValues.argument_value a M u selected t width ht hu hW
  have hc:=((SemiprimeD1RecoveryNodeBits.scalar_caps a M u selected.val hu).2.2).trans hW
  rw [array_native]
  have hkeys:∀k∈(SemiprimeD1RecoveryScalarRun.indices (retained a M u selected)).value,k≤retained a M u selected:=by
    rw [SemiprimeD1RecoveryScalarRun.indices_value]
    exact fun k hk=>(List.mem_range.mp hk).le
  have h:=SemiprimeD1RecoveryScalarWeightBits.powers_correct width a (SemiprimeD1TaperedLoss.height M u) u selected
    (argument a M u t width) ha.1 ha.2.1 hc _ hkeys
  have hv:=SemiprimeD1RecoveryScalarWeightBits.powers_original width a (SemiprimeD1TaperedLoss.height M u) u selected
    (argument a M u t width) ha.1 ha.2.1 hc
  exact ⟨hv,h.2⟩
/-- Actual complete original-family power denominators are positive; no raw zero-denominator assumption is hidden. -/
theorem denominator_positive (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length)
    (x:SemiprimeRationalBits.RationalWord) (hx:x∈array width (argument a M u t width) (retained a M u selected)):
    0<SemiprimeBitArithmetic.bitValue x.denominator:=
  (original_values a M u selected t width ht hu hW).2.1 x hx
end RiemannGaussian.SemiprimeD1StackRecoveryPowersValues
