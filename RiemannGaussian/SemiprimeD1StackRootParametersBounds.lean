/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootParametersExecution

/-! # One original-input clock and complete storage for all root parameters -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootParametersBounds
open SemiprimeD1StackRootParameters SemiprimeD1StackRootParametersExecution
open SemiprimeBitArithmetic (bitValue)
/-- The retained metadata source initially has only its binary N role populated. -/
theorem metadata_input (bits:List Bool) (k:M.Stack) :
    M.input bits k=(if k=M.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct M.originalInput M.edges (.inl .start) M.program bits
  have he:=hi.trans (SemiprimeD1StackRootControllerMetadataBounds.initial_eq bits)
  exact (congrArg (fun cfg:SemiprimeD1StackRootControllerMetadata.machine.Cfg=>cfg.stk (some k)) he).symm
/-- Genuine one-input initialization, before any parameter has been acquired. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:SemiprimeD1StackCalls.initial originalInput (.inl .start) bits=initial bits := by
    apply congrArg (fun d=>(⟨some (.inl .start),none,none,d,[]⟩:C.State Stack Label))
    funext k
    cases k with
    | inl k=>
      change (if (Sum.inl k:Stack)=originalInput then bits else [])=M.input bits k
      rw [metadata_input]
      simp only [originalInput,metadataStack,Sum.inl.injEq]
    | inr k=>rfl
  exact (SemiprimeD1StackCalls.initial_correct originalInput leaf (.inl .start) program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Fixed degree ten bounds the same complete actual clock before every input N. -/
theorem runBound_le (bits:List Bool) : runBound bits ≤ 10^51*(bits.length+1)^10 := by
  have hm:M.runBound bits ≤ 10^50*(bits.length+1)^10 :=
    (SemiprimeD1StackRootControllerMetadataBounds.runBound_eq bits).le.trans
      (SemiprimeD1StackRootControllerMetadataBounds.polynomial_le bits.length)
  have h3:(bits.length+1)^3 ≤ (bits.length+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1:1 ≤ (bits.length+1)^10 := one_le_pow₀ (by omega)
  unfold runBound
  omega
/-- Actual one-program original-input execution under the fixed polynomial majorant. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^51*(bits.length+1)^10,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (runBound_le bits),hr⟩
/-- The same genuine machine starts with N alone and acquires every operand. -/
noncomputable def acquireInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^51*(bits.length+1)^10) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput leaf (.inl .start) program
  let h:=source_run_polynomial bits hc hN
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- Every initial role, including all new divider/output roles, is charged to the sole input. -/
theorem initial_role_bound (bits:List Bool) (k:Stack) : ((initial bits).data k).length ≤ bits.length := by
  cases k with
  | inl k=>
    change (M.input bits k).length ≤ bits.length
    rw [metadata_input]
    split <;> simp
  | inr k=>exact Nat.zero_le _
/-- Every successful real prefix ends no later than this same program's actual halt. -/
theorem prefix_fuel_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) : fuel ≤ runBound bits := by
  obtain ⟨t,ht,he⟩:=source_run bits hc hN
  have hf:fuel ≤ t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All108 actual roles, old input shadow, fresh work and real return cells are included. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 109*(bits.length+runBound bits+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out
    (initial_role_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 108*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega
/-- Identical inventory bound at every prefix of the actual original-input compiled machine. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 109*(bits.length+runBound bits+1) := by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput leaf (.inl .start) program fuel (initial bits)
  change (SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:=he.trans hr
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hrun
/-- One degree-ten original-input polynomial bounds the entire live cell footprint. -/
theorem polynomial_space (bits:List Bool) :
    109*(bits.length+runBound bits+1) ≤ 10^54*(bits.length+1)^10 := by
  have hn:bits.length+1 ≤ (bits.length+1)^10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ bits.length+1) (by decide:1 ≤ 10)
  have ht:=runBound_le bits
  omega
/-- Every actual compiled step uses at most four fundamental commands. -/
theorem compile_depth (pc:Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackRootParametersBounds
