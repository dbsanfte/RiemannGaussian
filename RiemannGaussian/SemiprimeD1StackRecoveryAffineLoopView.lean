/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeStage
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeRead
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopes
/-! # Complete original-bank invariant of the actual chronological affine-array source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopView
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeRationalBits (RationalWord)
/-- Actual current full coefficient tape; this changes only its physical array word. -/
def array (w:Words) (xs:List RationalWord):Words:={w with added:=Function.update w.added .array (vector xs)}
/-- Actual current array and unread reversed-slope tape, with all original104 words retained. -/
def state (w:Words) (xs slopes:List RationalWord):Words:=
  SemiprimeD1StackRecoveryAffineSlopeRead.tape (array w xs) (vector slopes)
/-- Both original delimiters have been physically consumed on the actual final state. -/
def finished (w:Words) (xs:List RationalWord):Words:=
  SemiprimeD1StackRecoveryAffineSlopeRead.tape (array w xs) []
/-- Exact raw output of one native convolution array, used only as the source-run invariant. -/
def multiply (width:List Bool) (xs:List RationalWord) (c:RationalWord) (q:Nat):List RationalWord:=
  (SemiprimeJetBits.multiplyBits width xs.toArray #[SemiprimeJetBits.oneWord,c] q).words.toList
/-- After a real original slope is evaluated, all original104 cells are restored and the actual next array is installed. -/
theorem stage_result (w:Words) (xs rest:List RationalWord) (c:RationalWord) (width:List Bool) (q:Nat)
    (hs:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hm:w.added .remaining=[]) (hn:w.added .nextArray=[]):
    SemiprimeD1StackRecoveryAffineSlopeStage.result (putReg (state w xs rest) .slope c)
      (SemiprimeD1StackRecoveryAffineSlopeStage.bytes xs c width q)=state w (multiply width xs c q) rest:=by
  rw [SemiprimeD1StackRecoveryAffineSlopeStage.bytes_original]
  let base:=state w xs rest
  change SemiprimeD1StackRecoveryAffineArrayMove.result
    (SemiprimeD1StackRecoveryAffineCoefficientBuffers.buffers
      (SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg (putReg base .slope c) .slope) []
      (vector (multiply width xs c q))) (vector (multiply width xs c q))=_
  rw [SemiprimeD1StackRecoveryAffineSlopeBuffers.erase_put base c hs hd]
  dsimp only [base,state,array,SemiprimeD1StackRecoveryAffineSlopeRead.tape,
    SemiprimeD1StackRecoveryAffineArrayMove.result,SemiprimeD1StackRecoveryAffineCoefficientBuffers.buffers]
  congr 1
  funext slot
  cases slot <;> simp [hm,hn]
/-- One paid reversal/seed output is exactly the initial whole slope-loop bank, including literal ONE for empty slopes. -/
theorem slopes_state (w:Words) (slopes:List RationalWord) (hr:w.added .reader=[]):
    SemiprimeD1StackRecoveryAffineSlopes.result w slopes=state w [SemiprimeJetBits.oneWord] slopes.reverse:=by
  dsimp only [SemiprimeD1StackRecoveryAffineSlopes.result,SemiprimeD1StackRecoveryAffineSlopeBuffers.buffers,
    state,array,SemiprimeD1StackRecoveryAffineSlopeRead.tape]
  congr 1
  funext slot
  cases slot <;> simp [hr,oneArray,vector]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopView
