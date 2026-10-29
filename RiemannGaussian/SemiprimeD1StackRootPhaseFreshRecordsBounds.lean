/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSweepBounds
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCaps
/-! # Same whole N-only345-role source has a fixed polynomial original-bit clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBounds
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsSource SemiprimeD1StackRootPhaseFreshRecordsBinding
open SemiprimeD1StackRootPhaseFreshRecordsLoop SemiprimeD1StackRootPhaseFreshRecordsExecution
open SemiprimeD1StackRootPhaseFreshRecordsSweepBounds
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1StackRootPhaseParametersEncoding.result
/-- Fixed original-bit radius pays every retained source word and the full honest client resource. -/
def radius (bits:List Bool) :Nat :=10^155*(bits.length+1)^20
/-- Every smaller fixed physical/N-value cap is included without changing runtime code. -/
theorem radius_dominates (bits:List Bool) (c d:Nat) (hc:c ≤ 10^155) (hd:d ≤ 20) :
    c*(bits.length+1)^d ≤ radius bits :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)
/-- The radius includes every fixed finite empty-input corner. -/
theorem radius_pos (bits:List Bool) :1 ≤ radius bits :=by
  have h:0<radius bits:=by unfold radius;positivity
  omega
/-- Actual issued list preserves its original chronological length. -/
theorem entries_length (a u edges:Nat) (rows:List (List Bool)) :(entries a u edges rows).length=rows.length :=by
  simp only [entries,List.length_ofFn]
/-- Every physically read phase word is literally from the actual acquired original grid. -/
theorem entries_phase (a u edges:Nat) (rows:List (List Bool)) (e:Entry (banks a u edges rows))
    (he:e∈entries a u edges rows) :e.2∈rows :=by
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
  exact List.getElem_mem i.isLt
/-- Whole actual source clock includes every growing output heap, real ordinal
scan, rejected row, complete85cache serialization and all345-cell cleanup charges. -/
theorem radius_clock (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    runBound bits ≤ 10^30*(radius bits)^4 :=by
  let B:=radius bits
  let root:=O.result bits
  let bs:=banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)
  let es:=entries (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)
  have hB:1 ≤ B:=radius_pos bits
  have hr:∀k,(root k).length ≤ B:=fun k=>
    (SemiprimeD1StackRootPhaseFreshRecordsCaps.root_word bits hc hN k).trans
      (radius_dominates bits (10^153) 20 (by norm_num) (by omega))
  have hK:(O.phases bits).length ≤ B:=
    (SemiprimeD1StackRootPhaseParametersCaps.phase_count_le bits hc).trans
      (radius_dominates bits (10^30) 4 (by norm_num) (by omega))
  have hel:es.length=(O.phases bits).length:=entries_length _ _ _ _
  have hlen:es.length ≤ B:=hel.le.trans hK
  have hi:∀e∈es,e.1.val ≤ B:=by
    intro e _
    have hlt:=e.1.isLt
    change e.1.val < (banks _ _ _ _).length at hlt
    simp only [banks,List.length_map] at hlt
    omega
  have hresource:∀e∈es,SemiprimeD1StackPhaseCacheFreshBounds.resource bs e.1
      (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) e.2 [false,true] [] ≤ B:=by
    intro e he
    exact (SemiprimeD1StackRootPhaseFreshRecordsCaps.client_resource bits hc hN e.1 e.2
      (entries_phase _ _ _ _ e he)).trans (radius_dominates bits (10^154) 20 (by norm_num) (by omega))
  have hs:=sweepBound_le root bs (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) es [] B
    hB hr (source_heap bits) (source_counter bits) (entries_bank _ _ _ _) hresource hi
    (by simpa only [List.length_nil,Nat.zero_add] using hlen) (by intro w hw;cases hw)
  have htape: (root R.output).length ≤ 4*B^2+1:=by
    have he:root R.output=tape es:=source_reader bits
    rw [he]
    exact tape_bound es B hB hlen hi
  have hfinal:(A.stream (A.references (O.phases bits).length)).length ≤ 4*B^2:=history_bound _ B hB hK
  have hsource:SemiprimeD1StackRootPhaseParametersExecution.runBound bits ≤ B:=
    (SemiprimeD1StackRootPhaseParametersBounds.runBound_le bits hc hN).trans
      (radius_dominates bits (10^150) 20 (by norm_num) (by omega))
  have hprod:es.length*(10^28*B^3) ≤ B*(10^28*B^3):=Nat.mul_le_mul_right _ hlen
  have he:B*(10^28*B^3)=10^28*B^4:=by ring
  rw [he] at hprod
  have h1:B ≤ B^4:=Nat.le_pow (by decide)
  have h2:B^2 ≤ B^4:=Nat.pow_le_pow_right hB (by decide)
  have h4:1 ≤ B^4:=one_le_pow₀ hB
  change SemiprimeD1StackRootPhaseParametersExecution.runBound bits+5*(root R.output).length+
    sweepBound root bs _ _ _ es []+2*(A.stream (A.references (O.phases bits).length)).length+12 ≤ 10^30*B^4
  omega
/-- Fixed degree80 whole bit-clock for THIS actual N-only source, with no old/native clock transport. -/
theorem runBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    runBound bits ≤ 10^650*(bits.length+1)^80 :=by
  have h:=radius_clock bits hc hN
  have he:∀x:Nat,10^30*(10^155*x^20)^4=10^650*x^80:=by intro x;ring
  unfold radius at h
  rw [he] at h
  exact h
/-- Real complete halt is reached under the closed original-input polynomial. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ 10^650*(bits.length+1)^80,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits) :=by
  obtain ⟨q,hq,hr⟩:=source_run bits hc hN
  exact ⟨q,hq.trans (runBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBounds
