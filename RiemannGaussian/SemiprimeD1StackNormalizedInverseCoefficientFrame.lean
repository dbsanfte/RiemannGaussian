/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCalls
/-! # Actual newest-first coefficient row framing without clearing its value early -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficientFrame
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual coefficient framing writes only the retained newest-first built-array tape. -/
def framed (w : Words) (word : SemiprimeRationalBits.RationalWord) : Words :=
  {w with auxiliary:=Function.update w.auxiliary .prefixReverse (row word (w.auxiliary .prefixReverse))}
/-- Both REAL preserving Frames and literal TRUE row tag precede every coefficient cache drain. -/
theorem frame_run (w : Words) (word : SemiprimeRationalBits.RationalWord)
    (hn : w.registers (.acc,false)=signed word) (hd : w.registers (.acc,true)=word.denominator)
    (hs : w.auxiliary .fieldFrameScratch=[]) :
    Runs program (6*((signed word).length+word.denominator.length)+11)
      (ctl (.frameCoefficient true)) (store w) (ctl (.clearCoefficient 0)) (store (framed w word)) := by
  let first : Words := {w with auxiliary:=Function.update w.auxiliary .prefixReverse (frame word.denominator (w.auxiliary .prefixReverse))}
  let second : Words := {first with auxiliary:=Function.update first.auxiliary .prefixReverse (frame (signed word) (first.auxiliary .prefixReverse))}
  have h0:=PTrace.frame_call (.coefficient true) (ctl (.frameCoefficient true)) (ctl (.frameCoefficient false))
    rfl (store w) word.denominator (w.auxiliary .prefixReverse) hd rfl hs
  change Runs program _ _ _ _ (Function.update (store w) (aux .prefixReverse) _) at h0
  rw [update_aux] at h0
  have h1:=PTrace.frame_call (.coefficient false) (ctl (.frameCoefficient false)) (ctl .tagCoefficient)
    rfl (store first) (signed word) (first.auxiliary .prefixReverse) hn rfl hs
  change Runs program _ _ _ _ (Function.update (store first) (aux .prefixReverse) _) at h1
  rw [update_aux] at h1
  have h2:=PTrace.push_run (ctl .tagCoefficient) (ctl (.clearCoefficient 0)) (aux .prefixReverse) true
    (store second) rfl
  change Runs program 1 _ _ _ (Function.update (store second) (aux .prefixReverse) (true::second.auxiliary .prefixReverse)) at h2
  rw [update_aux] at h2
  have he : ({second with auxiliary:=Function.update second.auxiliary .prefixReverse (true::second.auxiliary .prefixReverse)}:Words)=framed w word := by
    dsimp only [second,first,framed,row]
    rw [Function.update_self,Function.update_self,Function.update_idem,Function.update_idem]
  rw [he] at h2
  have h:=PTrace.join (PTrace.join h0 h1) h2
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficientFrame
