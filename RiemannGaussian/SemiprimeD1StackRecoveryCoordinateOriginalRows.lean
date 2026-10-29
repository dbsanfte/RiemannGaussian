/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesEncoding
import RiemannGaussian.SemiprimeD1PhysicalRecursiveCounter
import RiemannGaussian.SemiprimeD1RecursivePhaseBounds
/-! # Exact original PhaseRun/block encoder and physical coordinate-cache identity
PhaseRun arrays specify actual retained block bytes only in proofs. The source
accepts neither PhaseRun objects nor a prepared coordinate cache. A paid outer
phase-bank producer/logger join remains an explicit upstream obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalRows
open SemiprimeD1StackRecoveryCoordinateEncoding
namespace N
export SemiprimeD1RecursiveCounter (PhaseRun emptyPhase coordinate)
end N
namespace P
export SemiprimeD1PhysicalRecursiveCounter (coordinateCache)
end P
/-- Actual block inventory of one native retained phase, including empty/rejected phases. -/
def phaseWords (phase:N.PhaseRun):List (List (List Bool)):=phase.blocks.toList
/-- Original chronological phase order and ascending block order, with every empty phase retained. -/
def originalPhases (phases:Array N.PhaseRun):Phases:=phases.toList.map phaseWords
/-- Physical original phase-bank input codec; no coordinate selection has occurred in these bytes. -/
def originalTape (phases:Array N.PhaseRun):List Bool:=tape (originalPhases phases)
/-- The source's actual column interpretation is EXACT the old copied two-level coordinate cache. -/
theorem columns_original (phases:Array N.PhaseRun) (key:List Bool):
    columns (originalPhases phases) key=P.coordinateCache (N.coordinate phases (SemiprimeBitArithmetic.bitValue key)):=by
  rw [P.coordinateCache,SemiprimeD1RecursivePhaseBounds.coordinate_values]
  simp only [originalPhases,columns,row,phaseWords,Array.toList_map,List.map_map,Function.comp_def]
/-- Exact old RecoveryEntries child-tape bytes, retaining all raw coefficient padding/defaults. -/
theorem result_original (phases:Array N.PhaseRun) (key:List Bool):
    result (originalPhases phases) key=SemiprimeD1StackRecoveryEntriesEncoding.childTape
      (P.coordinateCache (N.coordinate phases (SemiprimeBitArithmetic.bitValue key))):=by
  unfold result
  rw [columns_original]
  rfl
/-- An empty actual phase still has one outer occurrence and acquires an empty row. -/
theorem empty_phase_row (key:List Bool):row key (phaseWords N.emptyPhase)=[]:=rfl
/-- The original chronological phase inventory includes every empty phase without dropping it. -/
theorem original_count (phases:Array N.PhaseRun):(originalPhases phases).length=phases.size:=by
  simp only [originalPhases,List.length_map,Array.length_toList]
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginalRows
