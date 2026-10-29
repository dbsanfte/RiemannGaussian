/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputExecution

/-! # Whole actual public input checker: quadratic clock and all-prefix memory
The bound is derived from the actual SAME-source header/copy/block/branch trace,
not from the original checker report or the pure semantic specification.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicInputBounds
open SemiprimeD1StackPublicInput SemiprimeD1StackPublicInputState SemiprimeD1StackPublicInputExecution

/-- The actual original word obtained by the paid fixed-width extraction. -/
theorem word_length (bits raw : List Bool) : (M.word bits raw).length=(M.cached bits).length :=
  SemiprimeD1StackWordBlockExecution.result_length raw (M.cached bits)
/-- Actual acquired bound bytes fit within the actual retained template width. -/
theorem bound_length_le (bits indexWord : List Bool) :
    (M.actualBound bits indexWord).length≤(M.cached bits).length := by
  have h:=SemiprimeD1StackInputWidthBounds.width_le_radix (SemiprimeD1StackPublicInputWidthExecution.cache bits indexWord)
  have hb:=SemiprimeD1StackPublicInputWidthBounds.cache_lengths bits indexWord
  rw [hb.2.1] at h
  rw [SemiprimeD1StackPublicInputMeaning.actualBound,SemiprimeD1StackInputWidthBounds.bound_length,
    SemiprimeD1StackPublicZeroBounds.cached_length]
  unfold SemiprimeMacroParameters.radixBits at h
  omega
/-- Fixed whole-program polynomial before all original input/index/assignment bits. -/
def runBound (bits raw indexWord : List Bool) : ℕ := 1000000000000*(bits.length+raw.length+indexWord.length+2)^2
/-- EVERY actual source call, guard, flag read, data-copy/cleanup and real
return is included; canonicality and the Boolean verdict are never premises. -/
theorem timeBound_le (bits raw indexWord : List Bool) : timeBound bits raw indexWord≤runBound bits raw indexWord := by
  let I:=bits.length+raw.length+indexWord.length+2
  have hI : 1≤I := by dsimp [I];omega
  have hi : I≤I^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1≤2)
  have hh:=SemiprimeD1StackPublicInputWidthBounds.timeBound_le bits indexWord
  have hp : (bits.length+indexWord.length+2)^2≤I^2 := Nat.pow_le_pow_left (by dsimp [I];omega) 2
  unfold SemiprimeD1StackPublicInputWidthBounds.runBound at hh
  have hc : (M.cached bits).length≤66*I := by
    have h:=SemiprimeD1StackPublicZeroBounds.cached_length_le bits
    change (M.cached bits).length≤66*(bits.length+1) at h
    dsimp [I];omega
  have hb:=bound_length_le bits indexWord
  have hr : raw.length≤I := by dsimp [I];omega
  unfold timeBound bodyBound
  rw [SemiprimeD1StackWordBlockBounds.totalTime_eq,word_length]
  change _≤1000000000000*I^2
  omega
/-- Complete SAME actual source run with its fixed whole-input quadratic clock. -/
theorem source_run_bounded (bits raw indexWord : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits raw indexWord,C.run program t (initial bits raw indexWord)=some (done bits raw indexWord) := by
  obtain ⟨t,ht,hr⟩:=source_run bits raw indexWord hb
  exact ⟨t,ht.trans (timeBound_le bits raw indexWord),hr⟩
/-- Proof-only choice of an actual proved trace, never an executing cost oracle. -/
noncomputable def sourceCheck (bits raw indexWord : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits raw indexWord)
      (some (done bits raw indexWord)) (runBound bits raw indexWord) := by
  let h:=source_run_bounded bits raw indexWord hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- The genuine fixed52-role machine has the SAME complete actual input/output clock. -/
noncomputable def machineCheck (bits raw indexWord : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits raw indexWord))
      (some (SemiprimeD1StackCalls.configuration (done bits raw indexWord))) (runBound bits raw indexWord) :=
  SemiprimeD1StackCalls.evalsCorrect (.inl H.original) output Label.start program _ _ _ (sourceCheck bits raw indexWord hb)
/-- All successful actual prefixes lie before the complete bounded halt. -/
theorem prefix_fuel_le (bits raw indexWord : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw indexWord)=some out) : fuel≤runBound bits raw indexWord := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits raw indexWord hb
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits raw indexWord)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Initial storage consists only of actual original N/index/raw input bytes. -/
theorem initial_length (bits raw indexWord : List Bool) (k : Stack) :
    ((initial bits raw indexWord).data k).length≤bits.length+raw.length+indexWord.length := by
  rcases k with k|k
  · have h:=SemiprimeD1StackPublicInputWidthBounds.initial_length bits indexWord k
    change (SemiprimeD1StackPublicInputWidth.input bits indexWord k).length≤bits.length+raw.length+indexWord.length
    change (SemiprimeD1StackPublicInputWidth.input bits indexWord k).length≤bits.length+indexWord.length at h
    omega
  · rcases k with k|k
    · exact Nat.zero_le _
    · rcases k with k|k
      · exact Nat.zero_le _
      · rcases k with k|k
        · exact Nat.zero_le _
        · cases k;change raw.length≤bits.length+raw.length+indexWord.length;omega
/-- EVERY prefix includes ALL52 Boolean data roles, every actual public cache/
index/raw/suffix, all guard/flag/word work AND every actual return-label cell. -/
theorem prefix_cells (bits raw indexWord : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw indexWord)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤100000000000000*(bits.length+raw.length+indexWord.length+2)^2 := by
  let I:=bits.length+raw.length+indexWord.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (initial_length bits raw indexWord) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤52*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits raw indexWord hb fuel out hr
  change fuel≤1000000000000*(I+2)^2 at ht
  have hI : I≤(I+2)^2 := by
    have h:=Nat.pow_le_pow_right (by omega : 1≤I+2) (by decide : 1≤2)
    simp only [pow_one] at h
    omega
  change _≤100000000000000*(I+2)^2
  omega
/-- The SAME all-prefix physical inventory on the actual compiled bit machine. -/
theorem machine_prefix_cells (bits raw indexWord : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw indexWord)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      100000000000000*(bits.length+raw.length+indexWord.length+2)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct (.inl H.original) output Label.start program fuel (initial bits raw indexWord)
  change (C.run program fuel (initial bits raw indexWord)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw indexWord))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial bits raw indexWord) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits raw indexWord hb fuel out hc
end RiemannGaussian.SemiprimeD1StackPublicInputBounds
