/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersUniform
/-! # Original-input numerical envelopes discharged from the actual acquired source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersCaps
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersRows SemiprimeD1StackRootPhaseParametersResources
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1StackRootPhaseParametersInventory.roles
/-- One fixed proof-side radius bounds actual retained source and single-record bytes. -/
def radius (bits:List Bool) : Nat :=10^70*(bits.length+1)^10
/-- Fixed smaller-degree numerical envelopes are absorbed without changing the program. -/
theorem radius_dominates (bits:List Bool) (c d:Nat) (hc:c ≤ 10^70) (hd:d ≤ 10) :
    c*(bits.length+1)^d ≤ radius bits :=by
  exact Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)
/-- The physical radius is positive, including every finite initial corner case. -/
theorem radius_pos (bits:List Bool) : 1 ≤ radius bits :=by
  have h:0<radius bits:=by unfold radius;positivity
  omega
/-- Actual original phase list cardinality is at most the full acquired binary grid. -/
theorem phase_count_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    (phases bits).length ≤ 10^30*(bits.length+1)^4 :=by
  have h:= (SemiprimeD1StackRootPhaseGridBounds.numeric_bounds bits.length (exponentValue bits)
    (SemiprimeD1StackRootPhaseGridBounds.exponent_le bits hc)).2
  unfold phases
  split
  · rw [SemiprimeD1StackAssignmentOrder.assignments_length]
    exact h
  · exact Nat.zero_le _
/-- Every actually parsed phase word has the actual original acquired binary width. -/
theorem phase_word_width (bits:List Bool) (t:List Bool) (ht:t∈phases bits) : t.length=exponentValue bits+1 :=by
  unfold phases at ht
  split at ht
  · exact (SemiprimeD1StackAssignmentOrder.assignments_width _ _ t ht).trans List.length_replicate
  · cases ht
/-- Actual parent metadata and binary phase width are polynomial in original N width. -/
theorem input_size_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (t:List Bool) (ht:t∈phases bits) :
    edgeValue bits+exponentValue bits+levelsValue bits+t.length+3 ≤ 10^9*(bits.length+1) :=by
  have ha:exponentValue bits+2 ≤ 10^8*(bits.length+1):=
    (SemiprimeD1StackRootPhaseGridBounds.numeric_bounds bits.length (exponentValue bits)
      (SemiprimeD1StackRootPhaseGridBounds.exponent_le bits hc)).1
  have hu:=SemiprimeD1Schedule.levels_le (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
  change levelsValue bits ≤ _ at hu
  rw [SemiprimeD1StackRootPhaseGridBounds.lambda_eq bits hc] at hu
  have hl:Nat.clog 2 (2^20*bits.length+2) ≤ 2^20*bits.length+2:=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hm:=SemiprimeD1StackRootScopeBankOriginal.occurrence_le_scale bits hN
  rw [←SemiprimeD1StackRootScheduleOriginal.width_original bits hc] at hm
  change edgeValue bits ≤ 2^20*bits.length at hm
  rw [phase_word_width bits t ht]
  omega
/-- This stopped bank's physical mass is derived from its ACTUAL successful source run. -/
theorem stopped_mass_bound (a u edges:Nat) (t:List Bool) :
    stoppedMass a u edges t ≤ 10^15*(edges+a+u+t.length+3)^4 :=by
  obtain ⟨q,_,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionExecution.source_run a u edges t [false,true]
  have h:=SemiprimeD1StackPhaseWorkingPrecisionBounds.prefix_cells a u edges t [false,true] q
    (SemiprimeD1StackPhaseWorkingPrecisionExecution.done a u edges t [false,true]) hr
  change stoppedMass a u edges t+0 ≤ 10^15*(edges+a+u+t.length+2+1)^4 at h
  simpa only [Nat.add_zero,Nat.add_assoc] using h
/-- Every framed word is physically bounded by the actual complete stopped mass. -/
theorem record_length_bound (a u edges:Nat) (t:List Bool) :
    (record a u edges t).length ≤ 10^17*(edges+a+u+t.length+3)^4 :=by
  let inputSize:=edges+a+u+t.length+3
  let B:=10^15*inputSize^4
  have hb:stoppedMass a u edges t ≤ B:=stopped_mass_bound a u edges t
  have hw:∀k:P.Stack,(stopped a u edges t k).length ≤ B:=by
    intro k
    exact (Finset.single_le_sum (f:=fun k:P.Stack=>(stopped a u edges t k).length)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)).trans hb
  have hsum:∀ks:List P.Stack,(ks.map (fun k=>2*(stopped a u edges t k).length+1)).sum ≤ ks.length*(2*B+1):=by
    intro ks
    induction ks with
    | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_refl]
    | cons k ks ih=>
      have hk:=hw k
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have h:=hsum I.roles
  rw [SemiprimeD1StackRootPhaseParametersInventory.roles_length] at h
  change (record a u edges t).length ≤ _
  have he:(record a u edges t).length=(I.roles.map (fun k=>2*(stopped a u edges t k).length+1)).sum:=phaseRecord_length (stopped a u edges t)
  rw [he]
  have hpos:1 ≤ inputSize^4:=one_le_pow₀ (Nat.succ_le_succ (Nat.zero_le (edges+a+u+t.length+2)))
  dsimp only [B] at h
  change _ ≤ 10^17*inputSize^4
  omega
/-- All48 actual source words, actual source clock and complete physical record
are bounded from original N alone; no expected-result or advised-size premise remains. -/
theorem phase_caps (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (t:List Bool) (ht:t∈phases bits) :
    t.length ≤ radius bits ∧
    SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound (exponentValue bits) (levelsValue bits) (edgeValue bits) t [false,true] ≤ radius bits ∧
    stoppedMass (exponentValue bits) (levelsValue bits) (edgeValue bits) t ≤ radius bits ∧
    (record (exponentValue bits) (levelsValue bits) (edgeValue bits) t).length ≤ radius bits :=by
  let I:=edgeValue bits+exponentValue bits+levelsValue bits+t.length+3
  have hi:I ≤ 10^9*(bits.length+1):=input_size_le bits hc hN t ht
  have h4:I^4 ≤ 10^36*(bits.length+1)^4:=by
    have h:=Nat.pow_le_pow_left hi 4
    convert h using 1
    ring
  have hd:=radius_dominates bits (10^53) 4 (by norm_num) (by decide)
  have hwide:10^17*I^4 ≤ radius bits:=by
    have h:=Nat.mul_le_mul_left (10^17) h4
    have he:10^17*(10^36*(bits.length+1)^4)=10^53*(bits.length+1)^4:=by ring
    rw [he] at h
    exact h.trans hd
  have hpos:1 ≤ I^4:=one_le_pow₀ (Nat.succ_le_succ
    (Nat.zero_le (edgeValue bits+exponentValue bits+levelsValue bits+t.length+2)))
  have htI:t.length ≤ I:=by dsimp [I];omega
  have hi4:I ≤ I^4:=Nat.le_pow (by decide)
  refine ⟨htI.trans (hi4.trans (by omega)),?_,?_,?_⟩
  · change 10^12*(edgeValue bits+exponentValue bits+levelsValue bits+t.length+2+1)^4 ≤ radius bits
    have he:edgeValue bits+exponentValue bits+levelsValue bits+t.length+2+1=I:=by dsimp [I]
    rw [he]
    omega
  · have h:=stopped_mass_bound (exponentValue bits) (levelsValue bits) (edgeValue bits) t
    change stoppedMass _ _ _ _ ≤ 10^15*I^4 at h
    omega
  · exact (record_length_bound (exponentValue bits) (levelsValue bits) (edgeValue bits) t).trans hwide
/-- Parent operands and actual phase count satisfy the same original-N radius. -/
theorem metadata_caps (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    exponentValue bits ≤ radius bits ∧ levelsValue bits ≤ radius bits ∧ edgeValue bits ≤ radius bits ∧
      (phases bits).length ≤ radius bits :=by
  have ha:exponentValue bits+2 ≤ 10^8*(bits.length+1):=
    (SemiprimeD1StackRootPhaseGridBounds.numeric_bounds bits.length (exponentValue bits)
      (SemiprimeD1StackRootPhaseGridBounds.exponent_le bits hc)).1
  have hu:=SemiprimeD1Schedule.levels_le (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
  change levelsValue bits ≤ _ at hu
  rw [SemiprimeD1StackRootPhaseGridBounds.lambda_eq bits hc] at hu
  have hl:Nat.clog 2 (2^20*bits.length+2) ≤ 2^20*bits.length+2:=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hm:=SemiprimeD1StackRootScopeBankOriginal.occurrence_le_scale bits hN
  rw [←SemiprimeD1StackRootScheduleOriginal.width_original bits hc] at hm
  change edgeValue bits ≤ 2^20*bits.length at hm
  have hd:=radius_dominates bits (10^8) 1 (by norm_num) (by decide)
  rw [pow_one] at hd
  refine ⟨by omega,by omega,by omega,?_⟩
  exact (phase_count_le bits hc).trans (radius_dominates bits (10^30) 4 (by norm_num) (by decide))
/-- All126 actual retained original source/grid words remain charged at their real completed width. -/
theorem root_mass_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    rootMass (SemiprimeD1StackRootPhaseGridEncoding.result bits) ≤ radius bits :=by
  obtain ⟨q,_,hr⟩:=SemiprimeD1StackRootPhaseGridExecution.source_run bits hc hN
  have h:=SemiprimeD1StackRootPhaseGridBounds.prefix_cells bits hc hN q
    (SemiprimeD1StackRootPhaseGridEncoding.done bits) hr
  change rootMass (SemiprimeD1StackRootPhaseGridEncoding.result bits)+0 ≤ _ at h
  have hpoly:=SemiprimeD1StackRootPhaseGridBounds.polynomial_space bits hc hN
  have he:=h.trans (hpoly.trans (radius_dominates bits (10^63) 10 (by norm_num) (by omega)))
  simpa only [Nat.add_zero] using he
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersCaps
