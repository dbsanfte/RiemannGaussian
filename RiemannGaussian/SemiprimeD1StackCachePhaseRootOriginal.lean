/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseOriginal
/-! # The actual original issued phase heap feeds the complete coefficient consumer
Both original phase branches are covered. The producer's original binary input
determines actual heap/counter/reference words; prepared child-result bytes
remain an explicit input. This is not an original-N-only factoring endpoint.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseRootOriginal
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseOriginal SemiprimeD1StackCachePhaseClock SemiprimeD1StackCachePhaseInputBounds
open SemiprimeD1StackJetFoldWords (Modes modeTape)
namespace A
export SemiprimeD1StackFreshBankRestoreOriginal
  (banks ordinal reference root_heap root_counter reference_eq bank_at)
end A
namespace P
export SemiprimeD1StackRootPhaseParametersEncoding (phases exponentValue levelsValue edgeValue)
end P
namespace R
export SemiprimeD1StackRootPhaseFreshRecords (heap aux)
export SemiprimeD1StackRootPhaseFreshRecordsEncoding (result)
end R
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackRootPhaseFreshRecordsEncoding.freshResult
  SemiprimeD1StackRootPhaseParametersEncoding.phases
  SemiprimeD1StackRootPhaseParametersEncoding.exponentValue
  SemiprimeD1StackRootPhaseParametersEncoding.levelsValue
  SemiprimeD1StackRootPhaseParametersEncoding.edgeValue
/-- Original acquired phase point at its actual chronological output-reference position. -/
def point (bits:List Bool) (i:Fin (P.phases bits).length) :List Bool :=(P.phases bits)[i.val]
/-- Actual original guarded q, named only in the proof-side result. -/
def dimension (bits:List Bool) (i:Fin (P.phases bits).length) :Nat :=
  SemiprimeD1StackPhaseChildContextPrimitives.count (P.exponentValue bits) (P.levelsValue bits) (P.edgeValue bits) (point bits i)
/-- Actual original NEW binary precision; OLD parent precision remains exactly binary two. -/
def newPrecision (bits:List Bool) (i:Fin (P.phases bits).length) :List Bool :=
  SemiprimeD1StackPhaseChildContextPrimitives.precision (P.exponentValue bits) (P.levelsValue bits)
    (P.edgeValue bits) (point bits i) [false,true]
/-- Actual originally acquired good marker, without an external branch adviser. -/
def good (bits:List Bool) (i:Fin (P.phases bits).length) :Bool :=
  SemiprimeD1StackPhaseChildContextArithmetic.good (P.exponentValue bits) (P.levelsValue bits) (P.edgeValue bits) (point bits i)
/-- Actual reached original heap/counter, actual issued reference and literal nested child results only. -/
def rootSource (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :C.State Stack Label :=
  initial (R.result bits R.heap) (R.result bits (R.aux .counter)) (A.reference bits i) (modeTape modes)
/-- All four actual original consumer input bit lengths plus one. -/
def rootSize (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :Nat :=
  (R.result bits R.heap).length+(R.result bits (R.aux .counter)).length+(A.reference bits i).length+
    (modeTape modes).length+1
/-- Original accepted/rejected target, with every238-role field specified. -/
def rootDone (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :C.State Stack Label :=
  if good bits i then
    done (A.banks bits) (A.ordinal bits i) [] [false,true] (dimension bits i) (newPrecision bits i) modes
  else SemiprimeD1StackCachePhaseRejected.done (A.banks bits) (A.ordinal bits i) (modeTape modes)
/-- Generic physical initial bridge is instantiated using only already proved original byte equalities. -/
theorem rootSource_eq (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :
    rootSource bits i modes=source (A.banks bits) (A.ordinal bits i) modes :=
  initial_from (A.banks bits) (A.ordinal bits i) modes _ _ _ (A.root_heap bits) (A.root_counter bits) (A.reference_eq bits i)
/-- Same actual original four-input bit resource, without expanding any source arithmetic. -/
theorem rootSize_eq (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :
    rootSize bits i modes=inputSize (A.banks bits) (A.ordinal bits i) modes :=
  inputSize_from (A.banks bits) (A.ordinal bits i) modes _ _ _ (A.root_heap bits) (A.root_counter bits) (A.reference_eq bits i)
/-- The actual selected record carries the original phase marker, including every rejected phase. -/
theorem guard_original (bits:List Bool) (i:Fin (P.phases bits).length) :
    (A.banks bits)[(A.ordinal bits i).val] (Fresh.contextStack (Header.aux .valid))=[good bits i] :=by
  rw [A.bank_at]
  unfold SemiprimeD1StackRootPhaseFreshRecordsEncoding.freshResult
  rfl
/-- Both complete context caches and q are supplied internally by the actual original accepted record. -/
theorem cache_original (bits:List Bool) (i:Fin (P.phases bits).length) (hg:good bits i=true) :
    ValidCache (A.banks bits)[(A.ordinal bits i).val] [] [false,true] (dimension bits i) (newPrecision bits i) :=by
  rw [A.bank_at]
  unfold SemiprimeD1StackRootPhaseFreshRecordsEncoding.freshResult
  exact valid_fresh (P.exponentValue bits) (P.levelsValue bits) (P.edgeValue bits) (point bits i) [false,true] [] hg
/-- Every original issued phase, accepted or rejected, executes the SAME complete literal consumer at its own bit bound. -/
theorem root_source_run (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :
    ∃t ≤ 10^80*(rootSize bits i modes+1)^16,
      SemiprimeD1StackCalls.run program t (rootSource bits i modes)=some (rootDone bits i modes) :=by
  have hsource:=rootSource_eq bits i modes
  have hsize:=rootSize_eq bits i modes
  cases hg:good bits i with
  | false=>
    have hflag:(A.banks bits)[(A.ordinal bits i).val] (Fresh.contextStack (Header.aux .valid))=[false]:=by
      rw [guard_original,hg]
    obtain ⟨t,ht,he⟩:=rejected_run_bounded (A.banks bits) (A.ordinal bits i) modes hflag
    refine ⟨t,by simpa only [polynomial,hsize] using ht,?_⟩
    rw [hsource]
    simpa only [rootDone,hg,Bool.false_eq_true,ite_false] using he
  | true=>
    have hv:=cache_original bits i hg
    have hq:0 < dimension bits i:=fresh_q_positive (P.exponentValue bits) (P.levelsValue bits) (P.edgeValue bits) (point bits i) hg
    obtain ⟨t,ht,he⟩:=source_run_bounded (A.banks bits) (A.ordinal bits i) [] (by simp) [false,true]
      (dimension bits i) hq (newPrecision bits i) modes hv
    refine ⟨t,by simpa only [polynomial,hsize] using ht,?_⟩
    rw [hsource]
    simpa only [rootDone,hg,ite_true] using he
/-- Both actual original branches are genuine clean halts with every238-role data word specified. -/
theorem rootDone_halted (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes) :
    rootDone bits i modes=(⟨none,none,none,(rootDone bits i modes).data,[]⟩:C.State Stack Label) :=by
  unfold rootDone
  split_ifs <;> rfl
/-- Every actual original issued-phase prefix counts ALL238 data words and every real return cell. -/
theorem root_machine_prefix_cells (bits:List Bool) (i:Fin (P.phases bits).length) (modes:Modes)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (rootSource bits i modes)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10^85*(rootSize bits i modes+1)^16 :=by
  obtain ⟨t,ht,he⟩:=root_source_run bits i modes
  have hsize:=rootSize_eq bits i modes
  have ht':t ≤ polynomial (A.banks bits) (A.ordinal bits i) modes:=by
    simpa only [polynomial,hsize] using ht
  rw [rootSource_eq,rootDone_halted] at he
  rw [rootSource_eq] at hr
  have hs:=SemiprimeD1StackCachePhaseStorage.machine_prefix_of_halt (A.banks bits) (A.ordinal bits i) modes
    (rootDone bits i modes).data t ht' he fuel cfg hr
  simpa only [hsize] using hs
end RiemannGaussian.SemiprimeD1StackCachePhaseRootOriginal
