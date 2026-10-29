/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankExecution
import RiemannGaussian.SemiprimeD1StackCachePhaseBankRowBounds
/-! # Own complete physical phase-bank polynomial
Actual occurrence count, stopped output lengths and236-word cleanup costs are
paid by actual input bytes and real source traces. No subtree clock is raised.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankBounds
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1StackCachePhaseBankInputBounds SemiprimeD1StackCachePhaseBankRowBounds
open SemiprimeD1StackCachePhaseBankStep SemiprimeD1StackCachePhaseBankLoop
open SemiprimeD1StackCachePhaseBankFinish SemiprimeD1StackCachePhaseBankPrepare
open SemiprimeD1StackCachePhaseBankExecution
/-- Sum of actual whole-source per-phase caps, independent of prior logger history. -/
def rowsSum (bits:List Bool):List (Request bits)→Nat
  | []=>0
  | r::rs=>rowBound bits r+rowsSum bits rs
/-- Actual tagged chunk-history length recurrence. -/
theorem chunks_cons_length (bits:List Bool) (r:Request bits) (requests:List (Request bits)):
    (chunks bits (r::requests)).length=(chunk (payload bits r)).length+(chunks bits requests).length:=by
  rw [chunks,List.length_append]
/-- Exact actual source-loop cap: real phase work and ONE real final history reversal. -/
theorem replay_eq (bits:List Bool) (requests:List (Request bits)) (history:List Bool):
    replayBound bits requests history=rowsSum bits requests+2*(chunks bits requests).length+2*history.length+8:=by
  induction requests generalizing history with
  | nil=>
    simp only [replayBound,rowsSum,chunks,finishTime,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
  | cons r requests ih=>
    rw [replayBound,ih,rowsSum,chunks_cons_length,List.length_append,List.length_reverse]
    omega
/-- Real per-occurrence caps sum only over physically present input references. -/
theorem rowsSum_le (bits:List Bool) (requests:List (Request bits)) (B:Nat)
    (hb:∀r∈requests,rowBound bits r ≤B):rowsSum bits requests ≤requests.length*B:=by
  induction requests with
  | nil=>simp only [rowsSum,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons r requests ih=>
    have h0:=hb r List.mem_cons_self
    have h1:=ih (fun q hq=>hb q (List.mem_cons_of_mem r hq))
    simp only [rowsSum,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- Real acquired output payload widths pay their exact physically logged chunks. -/
theorem chunks_bound (bits:List Bool) (requests:List (Request bits)) (B:Nat)
    (hb:∀r∈requests,(payload bits r).length ≤B):
    (chunks bits requests).length ≤requests.length*(2*B+2):=by
  induction requests with
  | nil=>simp only [chunks,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons r requests ih=>
    have h0:=hb r List.mem_cons_self
    have h1:=ih (fun q hq=>hb q (List.mem_cons_of_mem r hq))
    rw [chunks_cons_length,chunk_length,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- Fixed degree18 and coefficient are chosen before every physical input. -/
def runBound (bits:List Bool) (requests:List (Request bits)):Nat:=10^100*(capacity bits requests)^18
/-- SAME whole literal program's actual source cap fits its own four-input physical-byte polynomial. -/
theorem timeBound_le (bits:List Bool) (requests:List (Request bits)):
    timeBound bits requests ≤runBound bits requests:=by
  let S:=capacity bits requests
  have hS:1 ≤S:=by dsimp [S,capacity];omega
  have hn:requests.length ≤S:=by
    have h:=request_count bits requests
    dsimp [S,capacity,resource]
    omega
  have hrow:=rowsSum_le bits requests (10^85*S^16) (fun r hr=>row_bound bits requests r hr)
  have hsum:rowsSum bits requests ≤10^85*S^17:=by
    calc
      _ ≤requests.length*(10^85*S^16):=hrow
      _ ≤S*(10^85*S^16):=Nat.mul_le_mul_right _ hn
      _=10^85*S^17:=by ring
  have hword:=chunks_bound bits requests (10^81*S^16) (fun r hr=>payload_length bits requests r hr)
  have hpos:1 ≤S^16:=Nat.pow_pos (by omega)
  have hinner:2*(10^81*S^16)+2 ≤10^82*S^16:=by norm_num only;omega
  have hchunks:(chunks bits requests).length ≤10^82*S^17:=by
    calc
      _ ≤requests.length*(2*(10^81*S^16)+2):=hword
      _ ≤S*(10^82*S^16):=Nat.mul_le_mul hn hinner
      _=10^82*S^17:=by ring
  have hprep:prepareTime (references bits requests) (children requests) ≤10*S:=by
    dsimp [S,capacity,resource]
    unfold prepareTime
    omega
  have hpow:S^17 ≤S^18:=Nat.pow_le_pow_right hS (by decide)
  have hlin:S ≤S^18:=by simpa only [pow_one] using Nat.pow_le_pow_right hS (by decide:1 ≤18)
  have hp:1 ≤S^18:=Nat.pow_pos (by omega)
  have hr:rowsSum bits requests ≤10^85*S^18:=hsum.trans (Nat.mul_le_mul_left _ hpow)
  have hc:(chunks bits requests).length ≤10^82*S^18:=hchunks.trans (Nat.mul_le_mul_left _ hpow)
  unfold timeBound runBound
  change prepareTime (references bits requests) (children requests)+replayBound bits requests []+1 ≤10^100*S^18
  rw [replay_eq]
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
  norm_num only at hr hc ⊢
  omega
/-- Actual whole4input program truly halts with exact data and own fixed physical-byte polynomial. -/
theorem source_run_bounded (bits:List Bool) (requests:List (Request bits)):
    ∃t ≤runBound bits requests,SemiprimeD1StackCalls.run program t (source bits requests)=some (done bits requests):=by
  obtain ⟨t,ht,hr⟩:=source_run bits requests
  exact ⟨t,ht.trans (timeBound_le bits requests),hr⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseBankBounds
