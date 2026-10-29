/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrimitives
import RiemannGaussian.SemiprimeD1StackCachePhaseBankEncoding
/-! # Physical logging of the ACTUAL per-phase source output
A real preserving Frame, literal tag and genuine ReverseWord prepend one actual
chunk to the reverse history. The complete238-role stopped bank is preserved.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankLog
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact actual one-phase logger work; previous outer history is never scanned. -/
def logTime (payload:List Bool):Nat:=(6*payload.length+5)+1+(2*(chunk payload).length+3)
/-- Real log copies the source output, including rejected[false], before any callee cleanup. -/
theorem log_run (bank:P.Stack→List Bool) (w:Aux→List Bool) (payload:List Bool)
    (hp:bank (SemiprimeD1StackCachePhase.blockStack (SemiprimeD1StackCachePhase.Blocks.aux .output))=payload)
    (hs:bank P.copyScratch=[]) (hb:w .buffer=[]):
    Runs program (logTime payload) (.local .frame) (data bank w) (.local (.clear false 0))
      (data bank (Function.update (Function.update w .buffer []) .history ((chunk payload).reverse++w .history))):=by
  have h0:=frame_call .frame .tag rfl (data bank w) payload [] hp hb hs
  change Runs program _ _ _ _ (Function.update (data bank w) (aux .buffer) (frame payload [])) at h0
  rw [←data_update_aux] at h0
  let framed:=Function.update w .buffer (frame payload [])
  have h1:=push_run .tag (.local .append) (aux .buffer) true (data bank framed) rfl
  change Runs program 1 _ _ _ (Function.update (data bank framed) (aux .buffer) (chunk payload)) at h1
  rw [←data_update_aux] at h1
  have htag:Function.update framed .buffer (chunk payload)=Function.update w .buffer (chunk payload):=by dsimp [framed];rw [Function.update_idem]
  rw [htag] at h1
  have h2:=reverse_call false .append (.clear false 0) rfl
    (data bank (Function.update w .buffer (chunk payload))) (chunk payload) (w .history) rfl rfl
  change Runs program _ _ _ _ (Function.update
    (Function.update (data bank (Function.update w .buffer (chunk payload))) (aux .buffer) [])
      (aux .history) ((chunk payload).reverse++w .history)) at h2
  rw [←data_update_aux,←data_update_aux,Function.update_idem] at h2
  have h:=join (join h0 h1) h2
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankLog
