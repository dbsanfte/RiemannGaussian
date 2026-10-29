/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersExecution
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersCaps
/-! # Own original-N polynomial clock and every188-role real-return storage prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersBounds
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersExecution SemiprimeD1StackRootPhaseParametersLoop
open SemiprimeD1StackRootPhaseParametersResources SemiprimeD1StackRootPhaseParametersUniform
open SemiprimeD1StackRootPhaseParametersCaps
open SemiprimeBitArithmetic (bitValue)
/-- The retained actual grid word is charged to the entire retained126-role mass. -/
theorem grid_bytes_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (SemiprimeD1StackRootPhaseGridEncoding.result bits G.output).length ≤ radius bits :=by
  exact (Finset.single_le_sum
    (f:=fun k:G.Stack=>(SemiprimeD1StackRootPhaseGridEncoding.result bits k).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ G.output)).trans (root_mass_le bits hc hN)
/-- The physical whole-grid loop has its own original-input polynomial bound,
including repeated heap-ordinal scans and rejected phase-bank allocations. -/
theorem sweep_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    sweepBound (SemiprimeD1StackRootPhaseGridEncoding.result bits) (exponentValue bits) (levelsValue bits)
      (edgeValue bits) (phases bits) [] (terminal bits) ≤ 10^140*(bits.length+1)^18 :=by
  obtain ⟨ha,hu,hm,hK⟩:=metadata_caps bits hc hN
  have hreader:(rowTape (phases bits) (terminal bits)).length ≤ radius bits:=by
    rw [←acquired_grid]
    exact grid_bytes_le bits hc hN
  have h:=sweepBound_le (SemiprimeD1StackRootPhaseGridEncoding.result bits)
    (exponentValue bits) (levelsValue bits) (edgeValue bits) (phases bits) [] (terminal bits)
    (phases bits).length (radius bits) (radius_pos bits) hK (root_mass_le bits hc hN)
    ha hu hm (by simp only [List.length_nil,Nat.zero_add,le_refl])
    (by intro w hw;cases hw) (phase_caps bits hc hN) hreader
  have hk:=phase_count_le bits hc
  have hx:1 ≤ (bits.length+1)^4:=one_le_pow₀ (by omega)
  have hk1:(phases bits).length+1 ≤ 2*10^30*(bits.length+1)^4:=by omega
  have hmultiply: (phases bits).length*((phases bits).length+1)*radius bits ≤
      2*10^130*(bits.length+1)^18:=by
    calc
      _ ≤ (10^30*(bits.length+1)^4)*(2*10^30*(bits.length+1)^4)*radius bits:=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hk hk1)
      _=_:=by unfold radius;ring
  have hx18:1 ≤ (bits.length+1)^18:=one_le_pow₀ (by omega)
  nlinarith
/-- The actual ordered unary-reference log is charged quadratically in phase count. -/
theorem references_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    2*(stream (references (phases bits).length)).length ≤ 10^62*(bits.length+1)^8 :=by
  have hs:=references_stream_le (phases bits).length
  have hk:=phase_count_le bits hc
  have hx:1 ≤ (bits.length+1)^4:=one_le_pow₀ (by omega)
  have hk1:(phases bits).length+1 ≤ 2*10^30*(bits.length+1)^4:=by omega
  have hmultiply: (phases bits).length*((phases bits).length+1) ≤ 2*10^60*(bits.length+1)^8:=by
    calc
      _ ≤ (10^30*(bits.length+1)^4)*(2*10^30*(bits.length+1)^4):=Nat.mul_le_mul hk hk1
      _=_:=by ring
  nlinarith
/-- WHOLE SAME fixed188-role N-only program is polynomial in original binary width.
All source acquisition, copies, p2 writes,48-word framing, heap scans and cleanup count. -/
theorem runBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    runBound bits ≤ 10^150*(bits.length+1)^20 :=by
  have hg:=SemiprimeD1StackRootPhaseGridBounds.runBound_le bits hc hN
  have hb:=grid_bytes_le bits hc hN
  have hs:=sweep_le bits hc hN
  have hr:=references_le bits hc
  have hp10:(bits.length+1)^10 ≤ (bits.length+1)^18:=Nat.pow_le_pow_right (by omega) (by decide)
  have hp8:(bits.length+1)^8 ≤ (bits.length+1)^18:=Nat.pow_le_pow_right (by omega) (by decide)
  have hg18:=hg.trans (Nat.mul_le_mul_left (10^60) hp10)
  have hb18:=hb.trans (Nat.mul_le_mul_left (10^70) hp10)
  have hr18:=hr.trans (Nat.mul_le_mul_left (10^62) hp8)
  have h1:1 ≤ (bits.length+1)^18:=one_le_pow₀ (by omega)
  have hwide:runBound bits ≤ 10^141*(bits.length+1)^18:=by
    unfold runBound
    change _ ≤ 10^70*(bits.length+1)^18 at hb18
    omega
  exact hwide.trans (Nat.mul_le_mul (by norm_num : 10^141 ≤ (10^150:Nat))
    (Nat.pow_le_pow_right (by omega) (by decide : 18 ≤ 20)))
/-- Whole same-program trace under the fixed degree-twenty original-input bit clock. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ 10^150*(bits.length+1)^20,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) :=by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (runBound_le bits hc hN),hr⟩
/-- The frozen original-input grid initializes exactly one actual binary N word. -/
theorem grid_input (bits:List Bool) (k:G.Stack) : G.input bits k=(if k=G.originalInput then bits else []) :=by
  have hi:=SemiprimeD1StackCalls.initial_correct G.originalInput G.output (.inl .start) G.program bits
  have he:=hi.trans (SemiprimeD1StackRootPhaseGridBounds.initial_eq bits)
  exact (congrArg (fun cfg:SemiprimeD1StackRootPhaseGrid.machine.Cfg=>cfg.stk (some k)) he).symm
/-- Only original binary N can be nonempty in all188 initial Boolean roles. -/
theorem input_eq (bits:List Bool) (k:Stack) : input bits k=(if k=originalInput then bits else []) :=by
  rcases k with k|k
  · change G.input bits k=_
    rw [grid_input]
    simp only [originalInput,gridStack,Sum.inl.injEq]
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
/-- Genuine N-only finite-machine certificate pays the complete actual188-role pipeline. -/
noncomputable def parametersInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^150*(bits.length+1)^20) :=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output .start program
  let h:=source_run_polynomial bits hc hN
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
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
/-- ALL188 allocated words, retained126 source/grid roles, every heap/ordinal
byte, all48 phase intermediates and actual real-return cells count at every prefix. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 189*(bits.length+runBound bits+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out (initial_role_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 188*(bits.length+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hc hN fuel out hr
  omega
/-- Fixed degree-twenty total physical storage envelope, including real returns. -/
theorem polynomial_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    189*(bits.length+runBound bits+1) ≤ 10^153*(bits.length+1)^20 :=by
  have ht:=runBound_le bits hc hN
  have hn:bits.length+1 ≤ (bits.length+1)^20:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ bits.length+1) (by decide : 1 ≤ 20)
  omega
/-- The SAME compiled machine's every reached prefix retains that complete inventory. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 189*(bits.length+runBound bits+1) :=by
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
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersBounds
