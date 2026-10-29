/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueExecution
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueHistory
/-! # Uniform polynomial clock for the same binary-N-only Boolean factor acquirer -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueBounds
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueSource
open SemiprimeD1StackBooleanFactorCatalogueLoop SemiprimeD1StackBooleanFactorCatalogueExecution
open SemiprimeD1StackBooleanFactorCataloguePrimitives
open SemiprimeD1BooleanFactorCatalogueIndices (key scopeWords indices vertex)
open SemiprimeD1BooleanFactorCatalogueIndicesBounds (occurrences)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
/-- Shared actual-width envelope, derived from the acquired source in proofs only. -/
def resource (bits : List Bool) : Nat :=
  112*(occurrences (bitValue bits)+1)^2+8*(bits.length+10000000000000*(bits.length+1)^5)+300
/-- One fixed per-factor polynomial, including repeated catalogue scans. -/
def cap (bits : List Bool) : Nat :=10^150*(bits.length+1)^35
/-- Complete actual original-N clock; constants are fixed before the whole family. -/
def runBound (bits : List Bool) : Nat :=10^170*(bits.length+1)^40
attribute [local irreducible] cap resource afterRows indices
/-- The actual original occurrence domain is linear in binary input width. -/
theorem occurrences_linear (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    occurrences (bitValue bits) ≤ 12800*bits.length := by
  have h:=SemiprimeD1RootTensorTables.actual_incidence_bound (bitValue bits) hN
  rw [←SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] at h
  exact h
/-- Actual scope width and descriptor acquisition imply the fixed per-row polynomial. -/
theorem resource_le_cap (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    resource bits ≤ cap bits := by
  let I:=bits.length+1
  have hI:1 ≤ I:=by dsimp [I];omega
  have hM:=occurrences_linear bits hc hN
  have hM1:occurrences (bitValue bits)+1 ≤ 12801*I:=by dsimp [I];omega
  have hM2:=Nat.pow_le_pow_left hM1 2
  rw [mul_pow] at hM2
  have h2:I^2 ≤ I^35:=Nat.pow_le_pow_right hI (by decide : 2 ≤ 35)
  have hM35:=hM2.trans (Nat.mul_le_mul_left ((12801:Nat)^2) h2)
  have h5:I^5 ≤ I^35:=Nat.pow_le_pow_right hI (by decide : 5 ≤ 35)
  have h1:I ≤ I^35:=by simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1 ≤ 35)
  have hlen:bits.length ≤ I^35:=(by dsimp [I];omega : bits.length ≤ I).trans h1
  have hP:1 ≤ I^35:=Nat.succ_le_of_lt (Nat.pow_pos (by dsimp [I];omega))
  unfold resource cap
  change 112*(occurrences (bitValue bits)+1)^2+8*(bits.length+10000000000000*I^5)+300 ≤ 10^150*I^35
  nlinarith only [hM35,h5,hlen,hP]
/-- One actual row, all cleanup and the subsequent EOF read fit the shared width envelope. -/
theorem rowBudget_le_resource (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f : Fin (factorCount (bitValue bits))) :
    rowBudget bits (occurrences (bitValue bits)) f.val f+1 ≤ resource bits := by
  let M:=occurrences (bitValue bits)
  let v:=vertex (bitValue bits) f
  have hs:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.scope_count_le bits hc hN f
  have hb:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length (scopeWords bits f.val) M
    (SemiprimeD1BooleanFactorCatalogueIndicesBounds.scope_word_length_le bits hc hN f)
  have hd:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.descriptor_length_le bits hc hN f
  have hm:=SemiprimeD1StackBooleanDescriptorRecordEncoding.record_length (E.vertex v) []
  rw [SemiprimeD1StackBooleanDescriptorRecordEncoding.record_vertex] at hm
  have hA:=Nat.mul_le_mul_right (M+1) (Nat.add_le_add_right hs 1)
  have hB:=Nat.mul_le_mul_right (2*M+2) hs
  unfold rowBudget SemiprimeD1StackBooleanDescriptorRecordAll.rowBound resource
  change 110*((scopeWords bits f.val).length+1)*(M+1)+
      7*(SemiprimeD1StackBooleanDescriptorRecordEncoding.record (E.vertex v) []).length+222+
      SemiprimeD1StackBooleanDescriptorRecordEncoding.mass (E.vertex v)+
      (SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits f.val)).length+9+1 ≤
    112*(M+1)^2+8*(bits.length+10000000000000*(bits.length+1)^5)+300
  rw [SemiprimeD1StackBooleanDescriptorRecordEncoding.record_vertex]
  simp only [List.length_nil,Nat.add_zero] at hm
  change (SemiprimeD1VertexCatalogueEncoding.vertex v []).length ≤ _ at hd
  nlinarith
/-- Each original row plus its real next-EOF test has an own fixed polynomial cost. -/
theorem rowBudget_le_cap (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f : Fin (factorCount (bitValue bits))) :
    rowBudget bits (occurrences (bitValue bits)) f.val f+1 ≤ cap bits :=
  (rowBudget_le_resource bits hc hN f).trans (resource_le_cap bits hc hN)
/-- Every retained-source query is paid from its actual copy/filter execution clock. -/
theorem query_le_cap (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f : Fin (factorCount (bitValue bits))) :
    SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key f.val)+2 ≤ cap bits := by
  have hb:bits≠[]:=by intro h;rw [h] at hN;exact Nat.lt_irrefl _ hN
  have h0:SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key f.val)+2 ≤
      SemiprimeD1StackFactorScopeFibreExecution.timeBound bits (key f.val):=by
    unfold SemiprimeD1StackFactorScopeFibreExecution.timeBound;omega
  have h1:=SemiprimeD1StackFactorScopeFibreBounds.timeBound_le bits (key f.val) hb
  have h2:=SemiprimeD1StackFactorScopeFibreBounds.original_timeBound bits hc hN f
  have hcst:(10:Nat)^140 ≤ 10^150:=by norm_num
  unfold cap
  exact h0.trans (h1.trans (h2.trans (Nat.mul_le_mul_right _ hcst)))
/-- Actual history grows by at most one shared polynomial allowance per original descriptor. -/
theorem history_le_cap (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f : Fin (factorCount (bitValue bits))) (hist : List Bool) :
    (DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits f.val) hist).length ≤ hist.length+cap bits := by
  have hr:=resource_le_cap bits hc hN
  have hs:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.scope_count_le bits hc hN f
  have hp:=SemiprimeD1StackBooleanRecordBounds.ports_length (scopeWords bits f.val) (occurrences (bitValue bits))
    (SemiprimeD1BooleanFactorCatalogueIndicesBounds.scope_word_value_le bits hc hN f)
  have hB:=Nat.mul_le_mul_right (2*occurrences (bitValue bits)+2) hs
  unfold SemiprimeD1StackBooleanDescriptorRecordAll.afterHistory
  cases hm:SemiprimeD1StackBooleanDescriptorRecordOriginal.originalMode (vertex (bitValue bits) f) with
  | none=>exact Nat.le_add_right _ _
  | some mode=>
    have ht:=SemiprimeD1StackBooleanRecordBounds.table_length mode
    simp only [List.length_append,List.length_reverse]
    have hl:(SemiprimeD1StackBooleanRecord.R.row (SemiprimeD1StackBooleanRecord.S.result (scopeWords bits f.val))
        (SemiprimeD1StackBooleanRecord.table mode)).length=
      2*(SemiprimeD1StackBooleanRecord.S.result (scopeWords bits f.val)).length+
        2*(SemiprimeD1StackBooleanRecord.table mode).length+3 := by
      simp only [SemiprimeD1StackVertexRecordStream.row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
        List.length_nil]
      omega
    rw [hl]
    have hp2:(SemiprimeD1StackBooleanRecord.S.result (scopeWords bits f.val)).length ≤
        occurrences (bitValue bits)*(2*occurrences (bitValue bits)+2)+1:=by omega
    have hr2:112*(occurrences (bitValue bits)+1)^2+300 ≤ cap bits:=by
      unfold resource at hr
      omega
    have hx:2*(SemiprimeD1StackBooleanRecord.S.result (scopeWords bits f.val)).length+
        2*(SemiprimeD1StackBooleanRecord.table mode).length+3 ≤
        112*(occurrences (bitValue bits)+1)^2+300 := by nlinarith only [hp2,ht]
    omega
/-- Actual repeated copy/filter work is linear in the number of physically
processed descriptors, with a fixed original-width polynomial per descriptor. -/
theorem loopBudget_le (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) :
    loopBudget bits (occurrences (bitValue bits)) n fs ≤ 2*cap bits*fs.length := by
  induction fs generalizing n with
  | nil=>rfl
  | cons f fs ih=>
    have horder:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.cons_values (bitValue bits) n f fs hseq
    have hr:=rowBudget_le_cap bits hc hN f
    rw [horder.1] at hr
    cases fs with
    | nil=>
      change rowBudget bits (occurrences (bitValue bits)) n f+1+0 ≤ 2*cap bits*1
      omega
    | cons g gs=>
      have hg:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.cons_values (bitValue bits) (n+1) g gs horder.2
      have hq:=query_le_cap bits hc hN g
      rw [hg.1] at hq
      have hi:=ih (n+1) horder.2
      change rowBudget bits (occurrences (bitValue bits)) n f+1+
          (SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+
            loopBudget bits (occurrences (bitValue bits)) (n+1) (g::gs)) ≤
        2*cap bits*((g::gs).length+1)
      nlinarith only [hr,hq,hi]
/-- The actual accumulated history has a fixed polynomial width per emitted row. -/
theorem history_bound (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hist : List Bool) :
    (afterRows bits n fs hist).length ≤ hist.length+cap bits*fs.length := by
  rw [SemiprimeD1StackBooleanFactorCatalogueHistory.afterRows_fold bits n fs hseq]
  exact SemiprimeD1StackBooleanFactorCatalogueHistory.fold_length
    (fun f=>DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits f.val))
    (cap bits) (history_le_cap bits hc hN) fs hist
/-- The same whole actual setup has a fixed polynomial allowance from original N. -/
theorem setup_le_cap (bits : List Bool) : setupBound bits ≤ cap bits := by
  have hI:1 ≤ bits.length+1:=by omega
  have h30:=Nat.pow_le_pow_right hI (by decide : 30 ≤ 35)
  have h5:=Nat.pow_le_pow_right hI (by decide : 5 ≤ 35)
  have h1:(bits.length+1) ≤ (bits.length+1)^35:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1 ≤ 35)
  have hp:1 ≤ (bits.length+1)^35:=Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  unfold setupBound SemiprimeD1StackFactorScopeFibreBounds.runBound cap
  simp only [List.length_nil,Nat.zero_add,Nat.mul_one]
  nlinarith only [h30,h5,h1,hp]
/-- Complete WHOLE N-only Boolean factor-record acquisition clock, including
source acquisition, every query/cleanup, output reversal and literal halt. -/
theorem timeBound_le_runBound (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    timeBound bits ≤ runBound bits := by
  have hs:=setup_le_cap bits
  have hl:=loopBudget_le bits hc hN 0 (indices (bitValue bits)) (indices_sequence (bitValue bits))
  have hh0:=history_bound bits hc hN 0 (indices (bitValue bits)) (indices_sequence (bitValue bits)) []
  have hh:(afterRows bits 0 (indices (bitValue bits)) []).length ≤ cap bits*(indices (bitValue bits)).length:=
    hh0.trans (Nat.zero_add _).le
  have hC:1 ≤ cap bits:=Nat.succ_le_of_lt (by unfold cap;positivity)
  have hm:timeBound bits ≤ cap bits*(4*(indices (bitValue bits)).length+5):=by
    unfold timeBound
    nlinarith only [hs,hl,hh,hC]
  have hF:=SemiprimeD1StackFactorScopeFibreBounds.factor_count_le bits hc hN
  have hp:1 ≤ (bits.length+1)^5:=Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  have hFC:4*(indices (bitValue bits)).length+5 ≤ 10000000000000000*(bits.length+1)^5:=by
    rw [indices_length]
    nlinarith only [hF,hp]
  calc
    _ ≤ cap bits*(4*(indices (bitValue bits)).length+5):=hm
    _ ≤ cap bits*(10000000000000000*(bits.length+1)^5):=Nat.mul_le_mul_left _ hFC
    _ = (10^150*10000000000000000)*((bits.length+1)^35*(bits.length+1)^5):=by unfold cap;ring
    _ = 10^166*((bits.length+1)^35*(bits.length+1)^5):=by
      rw [show (10000000000000000:Nat)=10^16 by norm_num,←pow_add]
    _ ≤ 10^170*((bits.length+1)^35*(bits.length+1)^5):=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 1 ≤ (10:Nat)) (by decide : 166 ≤ 170))
    _ = runBound bits:=by unfold runBound;rw [←pow_add]
/-- Actual original-N source trace with the fixed polynomial, not a retained report clock. -/
theorem source_run_polynomial (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ runBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (timeBound_le_runBound bits hc hN),hr⟩
/-- Same actual finite-control machine, from canonical binary N alone, with its
entire own polynomial clock and no acquired-data or branch supplier. -/
noncomputable def machineBounded (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits) := by
  have h:=machineCatalogue bits hc hN
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le_runBound bits hc hN)⟩
/-- Entire actual218-role source and all real return cells, at every reached prefix. -/
theorem polynomial_prefix_cells (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr:C.run program fuel (initial bits)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length ≤ 219*(bits.length+runBound bits) :=
  (prefix_cells bits hc hN fuel finish hr).trans
    (Nat.mul_le_mul_left 219 (Nat.add_le_add_left (timeBound_le_runBound bits hc hN) bits.length))
/-- Same complete inventory in the actual compiled binary-N machine. -/
theorem polynomial_machine_prefix_cells (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 219*(bits.length+runBound bits) :=
  (machine_prefix_cells bits hc hN fuel cfg hr).trans
    (Nat.mul_le_mul_left 219 (Nat.add_le_add_left (timeBound_le_runBound bits hc hN) bits.length))
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueBounds
