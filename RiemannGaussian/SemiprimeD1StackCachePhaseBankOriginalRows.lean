/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalRows
/-! # Actual restored guard, exact native block words and Coordinate21 ABI
The blocks below are derived from the actual stopped phase source. Rejected
phases remain present with an empty block vector. OLD precision remains two;
NEW working precision is read from the distinct originally acquired cache.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankOriginalRows
open SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace X
export SemiprimeD1StackCachePhaseRootOriginal (good dimension newPrecision)
end X
namespace Col
export SemiprimeD1StackRecoveryCoordinateEncoding (tape)
export SemiprimeD1StackRecoveryCoordinateOriginalRows (originalTape originalPhases phaseWords)
end Col
attribute [local irreducible] SemiprimeD1StackFreshBankRestoreOriginal.banks
  SemiprimeD1StackRootPhaseParametersEncoding.phases
  SemiprimeD1StackRootPhaseParametersEncoding.exponentValue
  SemiprimeD1StackRootPhaseParametersEncoding.levelsValue
  SemiprimeD1StackRootPhaseParametersEncoding.edgeValue
  SemiprimeD1StackCachePhaseRootOriginal.good
  SemiprimeD1StackCachePhaseRootOriginal.dimension
  SemiprimeD1StackCachePhaseRootOriginal.newPrecision
/-- Actual native ascending OLD-coordinate blocks of the literal NEW-precision right fold. -/
def blocks (bits:List Bool) (r:Request bits):List (List (List Bool)):=
  if X.good bits r.1 then
    (List.range (X.dimension bits r.1)).map (fun j=>
      (SemiprimeD1JetBlockBits.extract (⟨[],2⟩:SemiprimeD1JetAxes.Context) j
        (SemiprimeD1StackCachePhaseExecution.coefficients [] (X.dimension bits r.1)
          (X.newPrecision bits r.1) r.2)).words)
  else []
/-- The actual complete238-role output equals that native block codec, without a branch flag input. -/
theorem payload_native (bits:List Bool) (r:Request bits):
    payload bits r=vectorBits ((blocks bits r).map vectorBits):=by
  cases hg:X.good bits r.1 with
  | false=>
    unfold payload O.rootDone blocks
    simp only [hg,Bool.false_eq_true,ite_false,List.map_nil]
    rfl
  | true=>
    unfold payload O.rootDone blocks
    simp only [hg,ite_true]
    have h:=SemiprimeD1StackCachePhaseOriginal.output_native
      (SemiprimeD1StackFreshBankRestoreOriginal.banks bits) (SemiprimeD1StackFreshBankRestoreOriginal.ordinal bits r.1)
      [] [false,true] (X.dimension bits r.1) (X.newPrecision bits r.1) r.2
    have hp:SemiprimeBitArithmetic.bitValue [false,true]=2:=by decide
    rw [hp] at h
    simpa only [SemiprimeD1StackCachePhaseExecution.done,List.map_map,Function.comp_def] using h
/-- Exact Coordinate21 phase-bank bytes preserve chronological duplicates and every rejected row. -/
theorem result_codec (bits:List Bool) (requests:List (Request bits)):
    result bits requests=Col.tape (requests.map (blocks bits)):=by
  unfold result Col.tape
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro r _
  exact payload_native bits r
/-- A rejected issued phase produces the literal empty-vector payload, rather than being omitted. -/
theorem rejected_payload (bits:List Bool) (r:Request bits) (hg:X.good bits r.1=false):
    payload bits r=[false]:=by
  rw [payload_native]
  simp only [blocks,hg,Bool.false_eq_true,ite_false,List.map_nil]
  rfl
/-- Proof-side old PhaseRun representation of these ACTUAL block bytes; no report clock is transported. -/
def phase (bits:List Bool) (r:Request bits):SemiprimeD1RecursiveCounter.PhaseRun:=
  ⟨(blocks bits r).toArray,if X.good bits r.1 then SemiprimeBitArithmetic.bitValue (X.newPrecision bits r.1) else 0,0⟩
/-- The ordered PhaseRun view contains no supplied cache answers: all blocks were acquired by the real source. -/
def phases (bits:List Bool) (requests:List (Request bits)):Array SemiprimeD1RecursiveCounter.PhaseRun:=
  (requests.map (phase bits)).toArray
/-- Exact original PhaseRun/block encoder, independent of native report clocks. -/
theorem original_tape (bits:List Bool) (requests:List (Request bits)):
    result bits requests=Col.originalTape (phases bits requests):=by
  rw [result_codec]
  unfold Col.originalTape Col.originalPhases phases
  simp only [List.map_map,Function.comp_def]
  rfl
/-- The actual logged phase count includes all rejected and repeated issued references. -/
theorem phase_count (bits:List Bool) (requests:List (Request bits)):(phases bits requests).size=requests.length:=by
  simp only [phases,List.size_toArray,List.length_map]
end RiemannGaussian.SemiprimeD1StackCachePhaseBankOriginalRows
