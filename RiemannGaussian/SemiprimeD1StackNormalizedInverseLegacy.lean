/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseExecution
import RiemannGaussian.SemiprimeD1RecoveryNodeBits
/-! # Exact old inverse arrays and original recovery width/validity bridge
The prepared source receives only its physical denominator array, q markers and
W template. The literal upstream Affine source join is a separate obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseLegacy
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseEncoding SemiprimeD1StackNormalizedInverseExecution
open SemiprimeD1StackNormalizedInverseReadBuffers
/-- The actual halted output is exactly the WHOLE old array tape, independently of Valid/Fits and W. -/
theorem output_legacy (a : Array SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    (done a.toList q width).data (aux .output)=tape (SemiprimeNormalizedInverseBits.build width a q).words.toList := by
  change SemiprimeD1StackNormalizedInverseEncoding.result a.toList q width (aux .output)=_
  rw [SemiprimeD1StackNormalizedInverseEncoding.result,Function.update_self]
  simp only [outputWords,SemiprimeD1StackNormalizedInverseAcquisition.acquired,Array.toArray_toList]
/-- Actual run and exact old byte output are asserted for the SAME source execution. -/
theorem source_run_legacy (a : Array SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ∃t≤runBound a.toList q width,
      SemiprimeD1StackCalls.run program t (initial (tape a.toList) (unary q) width)=some (done a.toList q width) ∧
      (done a.toList q width).data (aux .output)=tape (SemiprimeNormalizedInverseBits.build width a q).words.toList := by
  obtain ⟨t,ht,hr⟩:=source_run a.toList q width
  exact ⟨t,ht,hr,output_legacy a q width⟩
/-- Original acquired grid/affine array, a proof specification of the prepared denominator word tape. -/
def denominator (width : List Bool) (a M u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    Array SemiprimeRationalBits.RationalWord :=
  let grid:=SemiprimeD1RecoveryGridBits.acquire width a M u t
  let q:=SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t.val
  (SemiprimeAffineJetBits.build width q grid.grid.slopes).words
/-- Actual width is derived from original dimensions; no inverse/Fits/validity witness is an extra source operand. -/
theorem original_valid (width : List Bool) (a M u : ℕ) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hM : u≤M) (hW : SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    let q:=SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t.val
    let inv:=SemiprimeNormalizedInverseBits.build width (denominator width a M u t) q
    SemiprimeJetBits.decode inv.words=(SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u t.val).inverse.coefficients ∧
      SemiprimeJetBits.Valid inv.words ∧ SemiprimeJetBits.Bounded inv.words width.length := by
  exact SemiprimeD1RecoveryNodeBits.inverse_correct width a M u t hM hW
end RiemannGaussian.SemiprimeD1StackNormalizedInverseLegacy
