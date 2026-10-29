/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputWidthExecution

/-! # Whole original-input active-digit bound: bit time and complete storage -/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicInputWidthBounds
open SemiprimeD1StackPublicInputWidth SemiprimeD1StackPublicInputWidthExecution
/-- Original physical counters, derived from the actually executed source. -/
theorem cache_lengths (bits index : List Bool) :
    (cache bits index).width.length=bits.length ∧
      (cache bits index).radix.length=SemiprimeMacroParameters.radixBits bits.length ∧
      (cache bits index).index=index :=
  ⟨List.length_replicate, List.length_replicate,rfl⟩
/-- All child cache bytes fit the original input and physical descriptor size. -/
theorem child_input_le (bits index : List Bool) :
    SemiprimeD1StackInputWidthBounds.inputSize (cache bits index)+1≤70*(bits.length+index.length+2) := by
  obtain ⟨hw,hb,hi⟩:=cache_lengths bits index
  unfold SemiprimeD1StackInputWidthBounds.inputSize
  rw [hw,hb,hi]
  have h:=(SemiprimeD1StackTransformArithmetic.prefix_powers bits.length _ le_rfl).1
  change SemiprimeMacroParameters.transformLength bits.length≤64*bits.length+1 at h
  unfold SemiprimeMacroParameters.radixBits
  omega
/-- Fixed quadratic in original binary N and ACTUAL descriptor bytes. -/
def runBound (bits index : List Bool) : ℕ := 1000000000*(bits.length+index.length+2)^2
/-- Both source acquisitions and all actual callee/caller work are charged;
there is no report-clock transport or supplied cache-size/bound-value premise. -/
theorem timeBound_le (bits index : List Bool) : timeBound bits index≤runBound bits index := by
  let I:=bits.length+index.length+2
  have hG:=Nat.pow_le_pow_left (child_input_le bits index) 2
  rw [mul_pow] at hG
  norm_num only [Nat.reducePow] at hG
  have hP : (bits.length+1)^2≤I^2 := Nat.pow_le_pow_left (by dsimp [I];omega) 2
  have hpos : 0<I^2 := Nat.pow_pos (by dsimp [I];omega)
  unfold timeBound SemiprimeD1BinaryPublicAcquisitionExecution.timeBound SemiprimeD1StackInputWidthBounds.runBound
  change _≤1000000000*I^2
  change (SemiprimeD1StackInputWidthBounds.inputSize (cache bits index)+1)^2≤4900*I^2 at hG
  omega
/-- Complete original-input source with the fixed quadratic actual clock. -/
theorem source_run_bounded (bits index : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits index,C.run program t (initial bits index)=some (done bits index) := by
  obtain ⟨t,ht,hr⟩:=source_run bits index hb
  exact ⟨t,ht.trans (timeBound_le bits index),hr⟩
/-- Proof-only actual trace choice; the literal program has no choice opcode. -/
noncomputable def sourceBound (bits index : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits index) (some (done bits index)) (runBound bits index) := by
  let h:=source_run_bounded bits index hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- The SAME genuine fixed finite machine executes both complete acquisitions. -/
noncomputable def boundInTime (bits index : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits index))
      (some (SemiprimeD1StackCalls.configuration (done bits index))) (runBound bits index) :=
  SemiprimeD1StackCalls.evalsCorrect original output Label.start program _ _ _ (sourceBound bits index hb)
/-- Successful actual prefixes never extend past the bounded completed halt. -/
theorem prefix_fuel_le (bits index : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits index)=some out) : fuel≤runBound bits index := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits index hb
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits index)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Only original binary N and actual index occupy nonempty initial input cells. -/
theorem initial_length (bits index : List Bool) (k : Stack) :
    ((initial bits index).data k).length≤bits.length+index.length := by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp only [initial,input,P.input,SemiprimeD1BinaryPublicAcquisition.store,
          SemiprimeD1BinaryPublicAcquisition.Digits.input,SemiprimeD1BinaryDigitAcquisition.store,
          SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
      · rcases k with k|k <;> exact Nat.zero_le _
    · rcases k with k|k <;> exact Nat.zero_le _
  · change (privateInput index k).length≤bits.length+index.length
    unfold privateInput
    split
    · omega
    · exact Nat.zero_le _
/-- EVERY prefix counts all37 Boolean data roles, every acquired public field,
product/copy/minimum work, unused shadows AND the physical return labels. -/
theorem prefix_cells (bits index : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits index)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤100000000000*(bits.length+index.length+2)^2 := by
  let I:=bits.length+index.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (initial_length bits index) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤37*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits index hb fuel out hr
  change fuel≤1000000000*(I+2)^2 at ht
  have hI : I≤(I+2)^2 := by
    have h:=Nat.pow_le_pow_right (by omega : 1≤I+2) (by decide : 1≤2)
    simp only [pow_one] at h
    omega
  change _≤100000000000*(I+2)^2
  omega
/-- All-prefix complete inventory on the actual compiled finite machine. -/
theorem machine_prefix_cells (bits index : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits index)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000000000*(bits.length+index.length+2)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct original output Label.start program fuel (initial bits index)
  change (C.run program fuel (initial bits index)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits index))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial bits index) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits index hb fuel out hc
end RiemannGaussian.SemiprimeD1StackPublicInputWidthBounds
