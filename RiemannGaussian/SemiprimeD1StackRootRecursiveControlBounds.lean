/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecursiveControlExecution

/-! # Original-input acquisition and branch share one actual polynomial clock
The branch cost is bounded by the size of the actual acquired parameter
words. No native report clock or solved-value supplier is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootRecursiveControlBounds
open SemiprimeD1StackRootRecursiveControl SemiprimeD1StackRootRecursiveControlEncoding
open SemiprimeD1StackRootRecursiveControlExecution
open SemiprimeBitArithmetic (bitValue)
/-- Genuine one-input initialization of the existing parameter source. -/
theorem source_input (bits:List Bool) (k:P.Stack) :
    P.input bits k=(if k=P.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct P.originalInput P.leaf (.inl .start) P.program bits
  have he:=hi.trans (SemiprimeD1StackRootParametersBounds.initial_eq bits)
  exact (congrArg (fun cfg:SemiprimeD1StackRootParameters.machine.Cfg=>cfg.stk (some k)) he).symm
/-- The controller has no second input, advised branch or prepared root metadata. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:SemiprimeD1StackCalls.initial originalInput (.inl .start) bits=initial bits := by
    apply congrArg (fun d=>(⟨some (.inl .start),none,none,d,[]⟩:C.State Stack Label))
    funext k
    cases k with
    | inl k=>
      change (if (Sum.inl k:Stack)=originalInput then bits else [])=P.input bits k
      rw [source_input]
      simp only [originalInput,sourceStack,Sum.inl.injEq]
    | inr k=>rfl
  exact (SemiprimeD1StackCalls.initial_correct originalInput output (.inl .start) program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Actual produced-word capacity follows from the source's own successful run. -/
theorem produced_word_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∀k:P.Stack,(P.result bits k).length ≤ bits.length+SemiprimeD1StackRootParameters.runBound bits := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootParametersExecution.source_run bits hc hN
  have hd:=SemiprimeD1StackReturnLink.run_data_bound P.program t bits.length (P.initial bits) (P.done bits)
    (SemiprimeD1StackRootParametersBounds.initial_role_bound bits) hr
  intro k
  exact (hd k).trans (Nat.add_le_add_left ht bits.length)
/-- Every actual gate operand comes from a produced source word or a physically empty fresh role. -/
theorem gate_input_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∀k:G.Stack,((GS.initial (parentExponent bits) (values bits)).data k).length ≤
      bits.length+SemiprimeD1StackRootParameters.runBound bits := by
  intro k
  rw [←initial_projection bits hc k]
  cases he:gateStack k with
  | inl p=>exact produced_word_bound bits hc hN p
  | inr f=>exact Nat.zero_le _
/-- Generic word accounting for this actual gate, independent of all original graph enumeration. -/
theorem gate_time_of_words (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) (C:Nat)
    (h:∀k:G.Stack,((GS.initial a v).data k).length ≤ C) : GS.runBound a v ≤ 300*(5*C+1) := by
  have hl:=h (.inl .leaf)
  have hm:=h (.inl .minimum)
  have hu:=h (.inl .levels)
  have he:=h (.inl .edges)
  have ha:=h (.inr .exponent)
  change (List.replicate (v .leaf) true).length ≤ C at hl
  change (List.replicate (v .minimum) true).length ≤ C at hm
  change (List.replicate (v .levels) true).length ≤ C at hu
  change (List.replicate (v .edges) true).length ≤ C at he
  change a.length ≤ C at ha
  simp only [List.length_replicate] at hl hm hu he
  unfold SemiprimeD1StackRecursiveSchedule.runBound SemiprimeD1StackScheduleActiveExecution.volume
  omega
/-- One fixed degree-ten bound retains every actual original-input and branch operation. -/
theorem runBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    runBound bits ≤ 10^55*(bits.length+1)^10 := by
  have hp:=SemiprimeD1StackRootParametersBounds.runBound_le bits
  have hg:=gate_time_of_words (parentExponent bits) (values bits)
    (bits.length+SemiprimeD1StackRootParameters.runBound bits) (gate_input_bound bits hc hN)
  have hn:bits.length+1 ≤ (bits.length+1)^10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ bits.length+1) (by decide:1 ≤ 10)
  unfold runBound
  omega
/-- Same actual original-input execution, not merely an equal-output report. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^55*(bits.length+1)^10,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (runBound_le bits hc hN),hr⟩
/-- Genuine finite-machine root control from original binary N alone. -/
noncomputable def controlInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^55*(bits.length+1)^10) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.inl .start) program
  let h:=source_run_polynomial bits hc hN
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- Every initial role is charged to the sole original input word. -/
theorem initial_role_bound (bits:List Bool) (k:Stack) : ((initial bits).data k).length ≤ bits.length := by
  cases k with
  | inl k=>change (P.input bits k).length ≤ bits.length;rw [source_input];split <;> simp
  | inr k=>exact Nat.zero_le _
/-- Successful real prefixes cannot extend beyond this same program's actual halt. -/
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
/-- All119 physical roles and every actual return cell are included at every reached source prefix. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 120*(bits.length+runBound bits+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out
    (initial_role_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 119*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega
/-- The same complete inventory applies to every actual compiled original-input prefix. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 120*(bits.length+runBound bits+1) := by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (.inl .start) program fuel (initial bits)
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
/-- A fixed polynomial includes every actual data and real-return cell. -/
theorem polynomial_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    120*(bits.length+runBound bits+1) ≤ 10^58*(bits.length+1)^10 := by
  have hn:bits.length+1 ≤ (bits.length+1)^10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ bits.length+1) (by decide:1 ≤ 10)
  have ht:=runBound_le bits hc hN
  omega
/-- Every actual compiled step uses at most four fundamental commands. -/
theorem compile_depth (pc:Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackRootRecursiveControlBounds
