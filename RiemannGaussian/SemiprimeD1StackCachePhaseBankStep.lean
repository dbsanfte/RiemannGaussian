/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankRead
import RiemannGaussian.SemiprimeD1StackCachePhaseBankLog
import RiemannGaussian.SemiprimeD1StackCachePhaseBankCleanup
/-! # Whole actual per-issued-phase acquisition, log and complete reuse cleanup
A real matching reference/child read feeds ONE complete CachePhase source.
The restored guard derives rejection/acceptance. Actual output is physically
logged before every236 nonpersistent source word is physically drained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankStep
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankEncoding SemiprimeD1StackCachePhaseBankRead
open SemiprimeD1StackCachePhaseBankCalls SemiprimeD1StackCachePhaseBankLog
open SemiprimeD1StackCachePhaseBankClearEncoding SemiprimeD1StackCachePhaseBankBinding
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackJetFoldWords (modeTape)
namespace Cleanup
export SemiprimeD1StackCachePhaseBankCleanup (source_run)
end Cleanup
/-- Sum of the SAME actual parser/call/logger/cleanup caps, independent of past output history. -/
def rowBound (bits:List Bool) (r:Request bits):Nat:=
  readTime (A.reference bits r.1) (modeTape r.2)+callBound bits r.1 r.2+
    logTime (payload bits r)+sweepTime (O.rootDone bits r.1 r.2).data 0
/-- Whole one-phase literal source body, including rejected/empty output and all236 real cleanup drains. -/
theorem row_run (bits:List Bool) (r:Request bits) (rest:List (Request bits))
    (originalRefs originalChildren history out:List Bool):
    ∃t ≤rowBound bits r,Runs program t (.local .header)
      (data (base bits) (words {references:=originalRefs,children:=originalChildren,referenceReader:=references bits (r::rest),childReader:=children (r::rest),history:=history,output:=out}))
      (.local .header)
      (data (base bits) (words {references:=originalRefs,children:=originalChildren,referenceReader:=references bits rest,childReader:=children rest,history:=(chunk (payload bits r)).reverse++history,output:=out})):=by
  let ready:Words:={references:=originalRefs,children:=originalChildren,referenceReader:=references bits rest,childReader:=children rest,history:=history,output:=out}
  let logged:Words:={ready with history:=(chunk (payload bits r)).reverse++history}
  have h0:=read_run (R.result bits R.heap) (R.result bits (R.aux .counter)) originalRefs originalChildren
    (A.reference bits r.1) (modeTape r.2) (references bits rest) (children rest) history out
  obtain ⟨t,ht,h1⟩:=original_call bits r.1 r.2 (words ready)
  have h2:=log_run (O.rootDone bits r.1 r.2).data (words ready) (payload bits r) rfl
    (SemiprimeD1StackCachePhaseBankStopped.original_scratch bits r.1 r.2) rfl
  simp only [words_update,setWord] at h2
  have h3:=Cleanup.source_run false (O.rootDone bits r.1 r.2).data (words logged)
  rw [original_cleared] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  unfold rowBound
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseBankStep
