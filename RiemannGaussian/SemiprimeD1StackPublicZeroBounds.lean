/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicZeroExecution
import RiemannGaussian.SemiprimeD1StackRootSourceOriginal

/-! # Whole actual zero-word checker: original-input time and all-prefix storage -/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicZeroBounds
open SemiprimeD1StackPublicZero SemiprimeD1StackPublicZeroExecution
/-- Actual acquired modulus-word cell count, derived from original preprocessing. -/
theorem cached_length (bits : List Bool) : (cached bits).length=SemiprimeMacroParameters.transformLength bits.length+1 :=
  SemiprimeD1StackRootSourceOriginal.modulus_length bits
/-- The actual binary cache has linearly many cells in original physical width. -/
theorem cached_length_le (bits : List Bool) : (cached bits).length≤66*(bits.length+1) := by
  rw [cached_length]
  have h:=(SemiprimeD1StackTransformArithmetic.prefix_powers bits.length _ le_rfl).1
  change SemiprimeMacroParameters.transformLength bits.length≤64*bits.length+1 at h
  omega
/-- The actual extracted word includes every original fixed-width padding bit. -/
theorem word_length (bits raw : List Bool) : (word bits raw).length=(cached bits).length :=
  SemiprimeD1StackWordBlockExecution.result_length raw (cached bits)
/-- Fixed whole-program quadratic in original binary N and actual raw assignment. -/
def runBound (bits raw : List Bool) : ℕ := 1000000000*(bits.length+raw.length+2)^2
/-- All actual preprocessing, input copying, extraction, comparison and caller
instructions fit this bound on the SAME program, including rejected raw words. -/
theorem timeBound_le (bits raw : List Bool) : timeBound bits raw≤runBound bits raw := by
  let I:=bits.length+raw.length+2
  have hI : 1≤I := by dsimp [I];omega
  have hi : I≤I^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1≤2)
  have hc : (cached bits).length≤66*I := by have h:=cached_length_le bits;dsimp [I];omega
  have hr : raw.length≤I := by dsimp [I];omega
  have hP : (bits.length+1)^2≤I^2 := Nat.pow_le_pow_left (by dsimp [I];omega) 2
  have he:=SemiprimeD1StackWordEqualExecution.executionTime_le (word bits raw) []
  simp only [List.length_nil,Nat.add_zero,word_length] at he
  have hpos : 0<I^2 := Nat.pow_pos (by omega)
  unfold timeBound SemiprimeD1BinaryPublicAcquisitionExecution.timeBound
  rw [SemiprimeD1StackWordBlockBounds.totalTime_eq]
  change _≤1000000000*I^2
  omega
/-- Complete same-source execution with fixed original-input polynomial clock. -/
theorem source_run_bounded (bits raw : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits raw,C.run program t (initial bits raw)=some (done bits raw) := by
  obtain ⟨t,ht,hr⟩:=source_run bits raw hb
  exact ⟨t,ht.trans (timeBound_le bits raw),hr⟩
/-- Proof-only actual trace choice, absent from the executing instruction table. -/
noncomputable def sourceCheck (bits raw : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits raw) (some (done bits raw)) (runBound bits raw) := by
  let h:=source_run_bounded bits raw hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine fixed finite-machine certificate, with the same actual source clock. -/
noncomputable def checkInTime (bits raw : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits raw))
      (some (SemiprimeD1StackCalls.configuration (done bits raw))) (runBound bits raw) :=
  SemiprimeD1StackCalls.evalsCorrect original output Label.start program _ _ _ (sourceCheck bits raw hb)
/-- All successful prefixes occur before the proved complete actual halt. -/
theorem prefix_fuel_le (bits raw : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw)=some out) : fuel≤runBound bits raw := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits raw hb
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits raw)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Only original binary N and actual assignment bytes occupy initial cells. -/
theorem initial_length (bits raw : List Bool) (k : Stack) :
    ((initial bits raw).data k).length≤bits.length+raw.length := by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp only [initial,store,P.input,SemiprimeD1BinaryPublicAcquisition.store,
          SemiprimeD1BinaryPublicAcquisition.Digits.input,SemiprimeD1BinaryDigitAcquisition.store,
          SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
      · rcases k with k|k <;> exact Nat.zero_le _
    · rcases k with k|k <;> exact Nat.zero_le _
  · rcases k with k|k
    · fin_cases k <;> exact Nat.zero_le _
    · rcases k with k|k
      · cases k <;> exact Nat.zero_le _
      · cases k;change raw.length≤bits.length+raw.length;omega
/-- EVERY actual prefix counts all38 data roles, original caches/raw/suffix,
every parser/comparison shadow/work cell AND real finite-label return cells. -/
theorem prefix_cells (bits raw : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤100000000000*(bits.length+raw.length+2)^2 := by
  let I:=bits.length+raw.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (initial_length bits raw) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤38*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits raw hb fuel out hr
  change fuel≤1000000000*(I+2)^2 at ht
  have hI : I≤(I+2)^2 := by
    have h:=Nat.pow_le_pow_right (by omega : 1≤I+2) (by decide : 1≤2)
    simp only [pow_one] at h
    omega
  change _≤100000000000*(I+2)^2
  omega
/-- Identical complete all-prefix inventory on the compiled finite machine. -/
theorem machine_prefix_cells (bits raw : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000000000*(bits.length+raw.length+2)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct original output Label.start program fuel (initial bits raw)
  change (C.run program fuel (initial bits raw)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial bits raw) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits raw hb fuel out hc
end RiemannGaussian.SemiprimeD1StackPublicZeroBounds
