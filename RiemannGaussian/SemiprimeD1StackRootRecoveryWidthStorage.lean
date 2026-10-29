/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthBounds
/-! # Genuine binary-input initialization and every2211-tape/return prefix
The complete original-input selected-key/frequency/padding source and complete actual width
bank remain allocated. No cache, shadow or actual return cell is omitted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthStorage
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackRootRecoveryWidthEncoding
open SemiprimeD1StackRootRecoveryWidthExecution SemiprimeD1StackRootRecoveryWidthBounds
open SemiprimeD1StackCalls (run configuration)
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
/-- Exactly one original binary input word is nonempty before any actual acquisition. -/
theorem input_single (bits:List Bool) :input bits=fun k=>if k=originalInput then bits else [] :=by
  funext k
  rcases k with k|k
  · have h:=congrFun (SemiprimeD1StackRootPacketPaddingStorage.input_single bits) k
    simpa only [input,data,originalInput,rootStack,Sum.elim_inl,Sum.inl.injEq] using h
  · rfl
/-- Every actual initialized word is paid by the sole binary-N input length. -/
theorem initial_length (bits:List Bool) (k:Stack) :((initial bits).data k).length ≤bits.length :=by
  change (input bits k).length ≤bits.length
  rw [input_single]
  change (if k=originalInput then bits else []).length ≤bits.length
  split_ifs <;> simp
/-- Actual machine input is genuine Turing.initList, with no exponent/incidence count/width/template/cache advice. -/
theorem initial_eq (bits:List Bool) :Turing.initList machine bits=configuration (initial bits) :=by
  have hs:SemiprimeD1StackCalls.initial originalInput (ctl .start) bits=initial bits:=by
    apply congrArg (fun d=>(⟨some (ctl .start),none,none,d,[]⟩:C.State Stack Label))
    exact (input_single bits).symm
  exact (SemiprimeD1StackCalls.initial_correct originalInput output (ctl .start) program bits).symm.trans
    (congrArg configuration hs)
/-- Every successful actual prefix stops no later than the SAME actual source halt. -/
theorem prefix_fuel (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (initial bits)=some out) :fuel ≤runBound bits :=by
  obtain ⟨t,ht,he⟩:=source_run_bounded bits hc hN
  have hh:run program 1 (done bits hN)=none:=rfl
  have hf:fuel ≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every actually allocated role, including all retained source banks and shadows, is counted. -/
theorem word_sum (words:Stack→List Bool) (cap:Nat) (h:∀k,(words k).length ≤cap) :
    (∑k:Stack,(words k).length) ≤2211*cap :=by
  calc
    _ ≤∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=2211*cap:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Every actual original-input prefix pays all2211 Boolean words and its genuine return stack. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤2212*(bits.length+runBound bits) :=by
  have ht:=prefix_fuel bits hc hN fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (initial_length bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum out.data (bits.length+fuel) hd
  omega
/-- The genuine compiled finite source starts from binary N alone and uses its OWN whole clock. -/
noncomputable def machineOriginal (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (configuration (done bits hN))) (runBound bits) :=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (ctl .start) program
  have h:=source_run_bounded bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- The identical genuine compiled prefixes include all data words and the actual none-labelled return tape. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤2212*(bits.length+runBound bits) :=by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (ctl .start) program fuel (initial bits)
  have hh:=he.trans hr
  cases hout:run program fuel (initial bits) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hout
/-- Every instruction expands to at most four genuine fixed-machine statements. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=
  SemiprimeD1StackCalls.compile_depth (ctl .start) (program pc)
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthStorage
