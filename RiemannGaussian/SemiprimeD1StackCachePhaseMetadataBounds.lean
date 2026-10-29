/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseInputBounds
/-! # Actual restored unary cache bytes pay rank and precision VALUES
The binary precision is never assumed small by its bit length: its actual unary
WIDTH was materialized by the producer and is present in the physical heap.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseMetadataBounds
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseInputBounds SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldInputBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)
/-- Every actual NEW cache word is paid by the SAME original heap-access trace. -/
theorem child_cache_word_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) (k:X.Stack) :
    (SemiprimeD1StackJetContextCorrectness.finalData (q::axes) newP k).length≤1001*inputSize banks i modes :=by
  have h:=restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.childStack k)))
  change (banks[i.val] (Fresh.contextStack (Header.childStack k))).length≤_ at h
  rw [hv.child] at h
  exact h
/-- Actual rank, numerical precision, encoded header and binary precision bytes have one paid cap. -/
theorem child_dimensions (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    (q::axes).prod≤1001*inputSize banks i modes ∧ bitValue newP≤1001*inputSize banks i modes ∧
      (vectorBits ((q::axes).map unary)).length≤1001*inputSize banks i modes ∧
      newP.length≤1001*inputSize banks i modes :=by
  have hr:=child_cache_word_le banks i axes p q newP modes hv X.rankCache
  have hw:=child_cache_word_le banks i axes p q newP modes hv X.widthCache
  have ha:=child_cache_word_le banks i axes p q newP modes hv X.axesCache
  have hb:=child_cache_word_le banks i axes p q newP modes hv X.precisionBits
  change (List.replicate (q::axes).prod true).length≤_ at hr
  simp only [List.length_replicate] at hr
  rw [SemiprimeD1StackJetContextCorrectness.width_value] at hw
  exact ⟨hr,hw,ha,hb⟩
/-- The entire actual fold capacity, including dense output and raw supplied child fields, is a fixed physical-input quadratic. -/
theorem fold_resource_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    SemiprimeD1StackJetFoldBounds.resource (q::axes) newP modes≤100000000*(inputSize banks i modes+1)^2 :=by
  obtain ⟨hr,hw,ha,hb⟩:=child_dimensions banks i axes p q newP modes hv
  have hlength:(q::axes).length≤(vectorBits ((q::axes).map unary)).length:=by
    simpa only [List.length_map] using vector_count_le ((q::axes).map unary)
  have hmax:childMax modes ≤ inputSize banks i modes:=
    (childMax_le_tape modes).trans (by unfold inputSize;omega)
  have hmul:=Nat.mul_le_mul hr hw
  change (q::axes).prod+bitValue newP+(q::axes).length+
    (List.replicate (bitValue newP) true).length+(vectorBits ((q::axes).map unary)).length+
    2*(List.replicate (q::axes).prod true).length+newP.length+1+
    (2*(q::axes).prod*bitValue newP+2*(q::axes).prod+1)+childMax modes+1≤_
  simp only [List.length_replicate]
  nlinarith only [hr,hw,ha,hb,hlength,hmax,hmul]
/-- The ACTUAL stopped fold output, subsequently copied into the extractor, is paid by that same physical-input quadratic. -/
theorem folded_length_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    (folded axes q newP modes Fold.output).length≤10000000*(inputSize banks i modes+1)^2 :=by
  obtain ⟨hr,hw,_ha,_hb⟩:=child_dimensions banks i axes p q newP modes hv
  have hmul:=Nat.mul_le_mul hr hw
  have h:=SemiprimeD1StackJetFoldBounds.output_length (q::axes) newP modes
  change (folded axes q newP modes Fold.output).length≤
    2*(q::axes).prod*bitValue newP+2*(q::axes).prod+1 at h
  nlinarith only [hr,hw,hmul,h]
end RiemannGaussian.SemiprimeD1StackCachePhaseMetadataBounds
