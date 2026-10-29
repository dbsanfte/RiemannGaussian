/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankStep
import RiemannGaussian.SemiprimeD1StackCachePhaseBankInputBounds
/-! # Same physical per-phase own cost from four actual input lengths
Real stopped-bank word bounds pay the actual logger and all236 real drains.
No phase output size, bank height or child runtime is an advised resource.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankRowBounds
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1StackCachePhaseBankInputBounds SemiprimeD1StackCachePhaseBankStep
open SemiprimeD1StackCachePhaseBankRead SemiprimeD1StackCachePhaseBankCalls
open SemiprimeD1StackCachePhaseBankLog SemiprimeD1StackCachePhaseBankClearEncoding
/-- Actual source-payload chunk has only its real tag, encoded payload bits and frame delimiter. -/
theorem chunk_length (word:List Bool):(chunk word).length=2*word.length+2:=by
  simp only [chunk,SemiprimeD1StackRecoveryCoordinateEncoding.chunk,List.length_cons,
    SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
/-- Each actually acquired phase output word is bounded by the same actual callee run. -/
theorem payload_length (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    (payload bits r).length ≤10^81*(capacity bits requests)^16:=
  stopped_word_global bits requests r hr _
/-- Actual two source-field parses are charged to real retained-vector bytes. -/
theorem read_time (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    readTime (SemiprimeD1StackFreshBankRestoreOriginal.reference bits r.1) (SemiprimeD1StackJetFoldWords.modeTape r.2)
      ≤100*capacity bits requests:=by
  have h0:=reference_length bits requests r hr
  have h1:=child_length bits requests r hr
  unfold readTime capacity resource
  omega
/-- The real whole238-role callee and actual outer return fit the SAME physical input bound. -/
theorem call_time (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    callBound bits r.1 r.2 ≤10^81*(capacity bits requests)^16:=by
  have hs:=component_size bits requests r hr
  have hp:=Nat.mul_le_mul_left (10^80) (Nat.pow_le_pow_left hs 16)
  have hpos:1 ≤(capacity bits requests)^16:=Nat.pow_pos (by unfold capacity;omega)
  unfold callBound
  norm_num only at hp ⊢
  omega
/-- Every physically traversed log byte belongs to this actual acquired phase payload. -/
theorem log_time (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    logTime (payload bits r) ≤10^83*(capacity bits requests)^16:=by
  have h:=payload_length bits requests r hr
  have hpos:1 ≤(capacity bits requests)^16:=Nat.pow_pos (by unfold capacity;omega)
  unfold logTime
  rw [chunk_length]
  norm_num only at h ⊢
  omega
/-- All236 real word drains and both retained-role jumps are paid from the actual stopped source bank. -/
theorem sweep_time (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    sweepTime (O.rootDone bits r.1 r.2).data 0 ≤10^84*(capacity bits requests)^16:=by
  have h:=sweepTime_le (O.rootDone bits r.1 r.2).data _ (stopped_word_global bits requests r hr)
  have hpos:1 ≤(capacity bits requests)^16:=Nat.pow_pos (by unfold capacity;omega)
  norm_num only at h ⊢
  omega
/-- One whole actual source iteration has a fixed degree16 in the physical four-input bytes. -/
theorem row_bound (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    rowBound bits r ≤10^85*(capacity bits requests)^16:=by
  have h0:=read_time bits requests r hr
  have h1:=call_time bits requests r hr
  have h2:=log_time bits requests r hr
  have h3:=sweep_time bits requests r hr
  have hlin:capacity bits requests ≤(capacity bits requests)^16:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by unfold capacity;omega:1 ≤capacity bits requests) (by decide:1 ≤16)
  unfold rowBound
  norm_num only at h0 h1 h2 h3 ⊢
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseBankRowBounds
