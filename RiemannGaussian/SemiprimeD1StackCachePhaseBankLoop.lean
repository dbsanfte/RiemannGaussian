/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankStep
import RiemannGaussian.SemiprimeD1StackCachePhaseBankFinish
/-! # Complete physical issued-reference/child replay
Every occurrence executes its own real source call and236-word cleanup. Source
order/repeats are preserved by actual tagged reverse logging; matched physical
terminators and EOFs are checked before one final real reverse/status write.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankLoop
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankEncoding SemiprimeD1StackCachePhaseBankStep
open SemiprimeD1StackCachePhaseBankFinish SemiprimeD1StackCachePhaseBankPrimitives
open SemiprimeD1StackProcedureTrace
/-- Exact chronological phase-payload chunks, without the one final physical false sentinel. -/
def chunks (bits:List Bool):List (Request bits)→List Bool
  | []=>[]
  | r::rs=>chunk (payload bits r)++chunks bits rs
/-- Chunk chunks plus its real final false is EXACT the target phase bank. -/
theorem chunks_vector (bits:List Bool) (requests:List (Request bits)):
    chunks bits requests++[false]=result bits requests:=by
  induction requests with
  | nil=>rfl
  | cons r requests ih=>
    rw [chunks,List.append_assoc,ih]
    change (true::SemiprimeSourceHistogramKeyBits.frame (payload bits r) [])++result bits requests=
      true::SemiprimeSourceHistogramKeyBits.frame (payload bits r) (result bits requests)
    rw [List.cons_append,SemiprimeD1StackRecoveryCoordinateEncoding.frame_append,List.nil_append]
/-- Sum of SAME actual per-phase source caps and the real final EOF/reverse/status cost. -/
def replayBound (bits:List Bool):List (Request bits)→List Bool→Nat
  | [],history=>finishTime history
  | r::rest,history=>rowBound bits r+replayBound bits rest ((chunk (payload bits r)).reverse++history)
/-- Entire real replay from acquired reference and per-phase child vectors, without phase objects/cache answers as inputs. -/
theorem replay_run (bits:List Bool) (requests:List (Request bits))
    (originalRefs originalChildren history out:List Bool):
    ∃t ≤replayBound bits requests history,Runs program t (.local .header)
      (data (base bits) (words {references:=originalRefs,children:=originalChildren,referenceReader:=references bits requests,childReader:=children requests,history:=history,output:=out}))
      (.local .done)
      (Function.update (data (base bits) (words {references:=originalRefs,children:=originalChildren,output:=history.reverse++chunks bits requests++out})) status [true]):=by
  induction requests generalizing history with
  | nil=>
    rw [replayBound]
    refine ⟨finishTime history,le_rfl,?_⟩
    have h:=finish_run (base bits) rfl originalRefs originalChildren history out
    simpa only [chunks,List.append_nil,references,children,List.map_nil,SemiprimeD1TensorTapeCodec.vectorBits] using h
  | cons r requests ih=>
    rw [replayBound]
    obtain ⟨t0,ht0,h0⟩:=row_run bits r requests originalRefs originalChildren history out
    obtain ⟨t1,ht1,h1⟩:=ih ((chunk (payload bits r)).reverse++history)
    have h:=join h0 h1
    refine ⟨t0+t1,Nat.add_le_add ht0 ht1,?_⟩
    simpa only [chunks,List.reverse_append,List.reverse_reverse,List.append_assoc] using h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankLoop
