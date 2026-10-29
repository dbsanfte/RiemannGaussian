/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBounds
/-! # Genuine N-only finite-machine entry and all345 words plus actual returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsStorage
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsExecution SemiprimeD1StackRootPhaseFreshRecordsBounds
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] result runBound SemiprimeD1StackRootPhaseParametersEncoding.result
/-- Only original binary N can be nonempty in all345 initial Boolean roles. -/
theorem input_eq (bits:List Bool) (k:Stack) : input bits k=(if k=originalInput then bits else []) :=by
  rcases k with k|k
  · change R.input bits k=_
    rw [SemiprimeD1StackRootPhaseParametersBounds.input_eq]
    simp only [originalInput,rootStack,Sum.inl.injEq]
  · rcases k with k|k
    · rfl
    · rfl
/-- The actual genuine finite machine begins from N alone, with no second operand/cache. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) :=by
  have hs:SemiprimeD1StackCalls.initial originalInput .start bits=initial bits:=by
    apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:C.State Stack Label))
    funext k
    exact (input_eq bits k).symm
  exact (SemiprimeD1StackCalls.initial_correct originalInput output .start program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Genuine original-N-only fixed-machine source includes the entire cache/foreach clock. -/
noncomputable def sourceInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^650*(bits.length+1)^80) :=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output .start program
  let h:=source_run_polynomial bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every initial physical word is paid by the original binary input width. -/
theorem initial_role_bound (bits:List Bool) (k:Stack) : ((initial bits).data k).length ≤ bits.length :=by
  change (input bits k).length ≤ _
  rw [input_eq]
  split <;> simp
/-- Every successful same-source prefix lies before its actual complete halt. -/
theorem prefix_fuel_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) : fuel ≤ runBound bits :=by
  obtain ⟨q,hq,hfinal⟩:=source_run bits hc hN
  have hf:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- ALL345 allocated words, retained188 source/grid roles, every heap/ordinal
byte, all143 cache/shadow fields and actual real-return cells count at every prefix. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 346*(bits.length+runBound bits+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out (initial_role_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 345*(bits.length+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega
/-- Fixed degree80 total physical storage envelope, including real returns. -/
theorem polynomial_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    346*(bits.length+runBound bits+1) ≤ 10^653*(bits.length+1)^80 :=by
  have ht:=runBound_le bits hc hN
  have hn:bits.length+1 ≤ (bits.length+1)^80:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ bits.length+1) (by decide : 1 ≤ 80)
  omega
/-- The SAME compiled machine's every reached prefix retains that complete inventory. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 346*(bits.length+runBound bits+1) :=by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct originalInput output .start program fuel (initial bits)
  have hh:(SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hrun
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsStorage
