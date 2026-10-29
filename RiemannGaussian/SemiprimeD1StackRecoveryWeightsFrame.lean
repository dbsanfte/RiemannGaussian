/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
/-! # Actual completed scalar-product framing BEFORE all8 cache drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsFrame
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace H
export SemiprimeD1StackNormalizedInverse (signed row)
end H
/-- Actual coefficient framing writes only the retained newest-first built-array tape. -/
def framed (w : Words) (word : SemiprimeRationalBits.RationalWord) : Words :=
  {w with auxiliary:=Function.update w.auxiliary .output (H.row word (w.auxiliary .output))}
/-- Both REAL preserving Frames and literal TRUE row tag precede every coefficient cache drain. -/
theorem frame_run (w : Words) (word : SemiprimeRationalBits.RationalWord)
    (hn : w.registers (.product,false)=H.signed word) (hd : w.registers (.product,true)=word.denominator)
    (hs : w.auxiliary .fieldFrameScratch=[]) :
    Runs program (6*((H.signed word).length+word.denominator.length)+11)
      ((.local (.frame true))) (bank w) ((.local (.clearCoefficient 0))) (bank (framed w word)) := by
  let first : Words := {w with auxiliary:=Function.update w.auxiliary .output (frame word.denominator (w.auxiliary .output))}
  let second : Words := {first with auxiliary:=Function.update first.auxiliary .output (frame (H.signed word) (first.auxiliary .output))}
  have h0:=P.frame_call true ((.local (.frame true))) ((.local (.frame false)))
    rfl (bank w) word.denominator (w.auxiliary .output) hd rfl hs
  change Runs program _ _ _ _ (Function.update (bank w) (aux .output) _) at h0
  rw [update_aux] at h0
  have h1:=P.frame_call false ((.local (.frame false))) ((.local .tag))
    rfl (bank first) (H.signed word) (first.auxiliary .output) hn rfl hs
  change Runs program _ _ _ _ (Function.update (bank first) (aux .output) _) at h1
  rw [update_aux] at h1
  have h2:=P.push_run ((.local .tag)) ((.local (.clearCoefficient 0))) (aux .output) true
    (bank second) rfl
  change Runs program 1 _ _ _ (Function.update (bank second) (aux .output) (true::second.auxiliary .output)) at h2
  rw [update_aux] at h2
  have he : ({second with auxiliary:=Function.update second.auxiliary .output (true::second.auxiliary .output)}:Words)=framed w word := by
    dsimp only [second,first,framed,H.row]
    rw [Function.update_self,Function.update_self,Function.update_idem,Function.update_idem]
  rw [he] at h2
  have h:=P.join (P.join h0 h1) h2
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsFrame
