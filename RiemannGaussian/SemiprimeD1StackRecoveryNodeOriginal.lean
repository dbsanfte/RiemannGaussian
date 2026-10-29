/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeStorage
/-! # Whole actual five-word source equals complete original acquireAt byte array
Every coefficient is acquired by real indexed reads/multiply/add/normalization;
original metadata and paid W alone discharge canonical values/denominators.
The literal N-only caller and recursive scalar counter remain separate joins.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeOriginal
open SemiprimeD1StackRecoveryNode SemiprimeD1StackRecoveryNodeEncoding
open SemiprimeD1StackRecoveryNodeBounds
/-- ALL actual old140 source/cache/shadow words survive the whole weight call byte-for-byte. -/
theorem old_retained (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool) (role:N.Stack):
    result a M u selected t width (node role)=SemiprimeD1StackRecoveryNodeInputsEncoding.result a M u selected t width role:=
  SemiprimeD1StackRecoveryNodeView.old_retained _ _ role
/-- The complete chronological coefficient tape is the only newly acquired physical word. -/
theorem output_word (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):
    result a M u selected t width output=tape a M u selected width:=by
  unfold result V.result
  rw [Function.update_self]
/-- RAW complete array equality with original acquireAt, including q0/W0/defaults and operand order. -/
theorem words_original (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):
    words a M u selected width=(SemiprimeD1RecoveryNodeBits.acquireAt width a M u selected).words:=
  SemiprimeD1StackRecoveryWeightsLegacy.array_acquireAt width a M u selected
/-- Original dimension guard and actual W derive all canonical numerator/denominator fields internally. -/
theorem values_original (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool)
    (hu:u≤M) (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length):
    let actual:=words a M u selected width
    let expected:=(SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u selected.val).weights.toList
    actual.map SemiprimeRationalBits.RationalWord.value=expected ∧ (∀x∈actual,x.Valid) ∧
      (∀x∈actual,SemiprimeRationalBits.Width x width.length) ∧
      actual.map (fun x=>(x.numerator.value,SemiprimeBitArithmetic.bitValue x.denominator))=expected.map (fun x=>(x.num,x.den)):=
  SemiprimeD1StackRecoveryWeightsLegacy.array_values width a M u selected hu hW
/-- SAME actual whole source acquires the ENTIRE original local weights and retains the whole real old cache. -/
theorem source_run_original (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u selected t width) ∧
      (done a M u selected t width).data output=
        SemiprimeD1StackNormalizedInverse.tape (SemiprimeD1RecoveryNodeBits.acquireAt width a M u selected).words ∧
      (∀role,(done a M u selected t width).data (node role)=SemiprimeD1StackRecoveryNodeInputsEncoding.result a M u selected t width role):=by
  obtain ⟨s,hs,hr⟩:=source_run_bounded a M u selected t width ht
  refine ⟨s,hs,hr,?_,old_retained a M u selected t width⟩
  change result a M u selected t width output=_
  rw [output_word,tape,words_original]
/-- SAME actual-Grid-ready program continuation computes every remaining array/weight with no source replay. -/
theorem ready_run_original (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (gridReady a M u selected t width)=some (done a M u selected t width) ∧
      (done a M u selected t width).data output=
        SemiprimeD1StackNormalizedInverse.tape (SemiprimeD1RecoveryNodeBits.acquireAt width a M u selected).words:=by
  obtain ⟨s,hs,hr⟩:=ready_run_bounded a M u selected t width ht
  refine ⟨s,hs,hr,?_⟩
  change result a M u selected t width output=_
  rw [output_word,tape,words_original]
end RiemannGaussian.SemiprimeD1StackRecoveryNodeOriginal
