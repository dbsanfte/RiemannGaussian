/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBinding
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsFinish
/-! # Whole N-only phase-cache acquisition, chronological Fresh sweep and real halt -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsExecution
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives SemiprimeD1StackRootPhaseFreshRecordsSource
open SemiprimeD1StackRootPhaseFreshRecordsBinding SemiprimeD1StackRootPhaseFreshRecordsLoop
open SemiprimeD1StackRootPhaseFreshRecordsFinish SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- Own whole-source clock includes one acquired source, one reference copy,
every real cached Fresh row and one final chronological reference reversal. -/
def runBound (bits:List Bool) :Nat :=
  SemiprimeD1StackRootPhaseParametersExecution.runBound bits+
  5*(O.result bits R.output).length+
  sweepBound (O.result bits) (banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits))
    (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits)
    (entries (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)) []+
  2*(A.stream (A.references (O.phases bits).length)).length+12
/-- One original binary N acquires all source banks ONCE, copies actual issued
references ONCE and executes every actual cache restore/Fresh/85-word heap row. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q,q+1 ≤ runBound bits ∧ Runs program q .start (input bits) .done (result bits) :=by
  let root:=O.result bits
  let bs:=banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)
  let es:=entries (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)
  let rs:=records (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)
  obtain ⟨g,hg,h0⟩:=root_call bits hc hN
  rw [afterRoot_view] at h0
  have h1:=copy_refs root
  have h2:=seed_header root (root R.output)
  have hreader:root R.output=tape es:=source_reader bits
  rw [hreader] at h1 h2
  obtain ⟨r,hr,h3⟩:=rows_run root bs (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) es []
    (source_heap bits) (source_counter bits) (entries_bank _ _ _ _)
  dsimp only [es] at h3
  rw [entries_cached] at h3
  simp only [List.nil_append] at h3
  change Runs program r .header (loop root (tape es) [] 0 []) .finishSeed
    (loop root [] (SemiprimeD1StackHeapAllocate.heapBytes rs) rs.length (A.stream (A.references rs.length)).reverse) at h3
  have h4:=finish_run root rs
  have hall:=compose (compose (compose (compose h0 h1) h2) h3) h4
  refine ⟨_,?_,hall⟩
  have hlen:rs.length=(O.phases bits).length:=by simp only [rs,records,List.length_map]
  change (g+1)+(5*(tape es).length+4)+1+r+(2*(A.stream (A.references rs.length)).length+4)+1 ≤ runBound bits
  rw [hlen]
  unfold runBound
  rw [source_reader]
  change r ≤ sweepBound (O.result bits) _ _ _ _ _ [] at hr
  dsimp only [es,bs] at hr ⊢
  omega
/-- Genuine whole original-N-only source includes the actual final halt and leaves all finite flags/returns clear. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits) :=by
  obtain ⟨q,hq,hr⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result bits) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Fixed finite compiled source certificate for this SAME N-only program and its own actual clock. -/
noncomputable def freshRecordsInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits))
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits) :=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output .start program
  let h:=source_run bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsExecution
