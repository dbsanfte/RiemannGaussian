/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTargetExecution
/-! # Closed acquisition/read polynomial, without a supplied target or cache
The physical unary index remains a declared caller input, not a decoded control
register. All original N preprocessing, cache copying and field scans are paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicTargetBounds
open SemiprimeD1StackPublicTarget SemiprimeD1StackPublicTargetExecution
attribute [local irreducible] SemiprimeD1BinaryPublicAcquisitionComponents.result
/-- Intrinsic bound on the ACTUAL original streaming block producer. The
cached digit catalogue is neither supplied nor replaced by a desired size. -/
theorem bank_length (bits : List Bool) :
    (SemiprimeD1TensorTapeCodec.vectorBits (digits bits)).length ≤ 24000000*(bits.length+1)^2 := by
  have he:=SemiprimeD1StackDigitBankSpec.entries_blocks_length
    (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) bits.length bits
  have hr:=SemiprimeD1BinaryDigitAcquisitionComponents.radix_length bits
  have hb:=SemiprimeD1StackTransformArithmetic.radix_bound bits.length
  rw [hr] at he
  rw [←SemiprimeD1StackDigitBankSpec.entries_vectorBits]
  change (SemiprimeD1StackDigitBankSpec.entries
    (SemiprimeD1StackDigitBankSpec.blocks (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) bits.length bits)++[false]).length ≤ _
  simp only [List.length_append,List.length_cons,List.length_nil]
  nlinarith [Nat.zero_le (bits.length^2)]
/-- One fixed quadratic allowance in original BINARY input and actual query bytes. -/
def timeBound (bits index : List Bool) : ℕ := 1000000000*(bits.length+index.length+2)^2
/-- Actual original-binary public acquisition/read trace with no supplied bank,
parameter, digit, default-zero result or execution clock. -/
theorem source_run_bounded (bits index : List Bool) (hb : bits≠[]) :
    ∃time ≤ timeBound bits index,C.run program time (initial bits index)=some (done bits index) := by
  obtain ⟨t,ht,hr⟩:=source_run bits index hb
  refine ⟨t,ht.trans ?_,hr⟩
  have hB:=bank_length bits
  have hp : (bits.length+1)^2 ≤ (bits.length+index.length+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hi : index.length ≤ (bits.length+index.length+2)^2 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1 ≤ bits.length+index.length+2) (by decide : 1 ≤ 2)
    simp only [pow_one] at hh
    omega
  have hpos : 0 < (bits.length+index.length+2)^2 := by positivity
  unfold SemiprimeD1BinaryPublicAcquisitionExecution.timeBound SemiprimeD1StackJetReadExecution.timeBound timeBound
  omega
/-- Proof-side choice of an ACTUALLY PROVED trace; no choice/evaluator occurs in code. -/
noncomputable def sourceRead (bits index : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits index) (some (done bits index))
      (timeBound bits index) := by
  let h:=source_run_bounded bits index hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine fixed finite machine from original binary N PLUS physical query index. -/
noncomputable def machineRead (bits index : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits index))
      (some (SemiprimeD1StackCalls.configuration (done bits index))) (timeBound bits index) :=
  SemiprimeD1StackCalls.evalsCorrect
    (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) (.inr .output)
    Label.start program _ _ _ (sourceRead bits index hb)
/-- A successful actual prefix cannot occur beyond the bounded completed halt. -/
theorem prefix_fuel_le (bits index : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits index)=some out) : fuel ≤ timeBound bits index := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits index hb
  have hf : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits index)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL thirty-six physical data stacks and real return-label cells at EVERY
actual prefix, including original acquisition plus repeated cache scan/copy. -/
theorem prefix_cells (bits index : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits index)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      100000000000*(bits.length+index.length+2)^2 := by
  let inv:=bits.length+index.length
  have hdata : ∀k,((initial bits index).data k).length ≤ inv := by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp only [initial,input,store,P.input,SemiprimeD1BinaryPublicAcquisition.store,
            SemiprimeD1BinaryPublicAcquisition.Digits.input,SemiprimeD1BinaryDigitAcquisition.store,
            SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> dsimp [inv] <;> omega
        · rcases k with k|k <;> exact Nat.zero_le _
      · rcases k with k|k <;> exact Nat.zero_le _
    · cases k <;> simp only [initial,input,store,R.store,Sum.elim_inr,List.length_nil] <;> dsimp [inv] <;> omega
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 36*(inv+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits index hb fuel out hr
  change fuel ≤ 1000000000*(inv+2)^2 at ht
  have hi : inv ≤ (inv+2)^2 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1 ≤ inv+2) (by decide : 1 ≤ 2)
    simp only [pow_one] at hh
    omega
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000000000*(inv+2)^2
  omega
/-- The same full inventory for EVERY reached genuine FinTM2 prefix. -/
theorem machine_prefix_cells (bits index : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits index)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      100000000000*(bits.length+index.length+2)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct
    (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) (.inr .output)
    Label.start program fuel (initial bits index)
  have hh:=he.trans hr
  cases hc : C.run program fuel (initial bits index) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits index hb fuel out hc
end RiemannGaussian.SemiprimeD1StackPublicTargetBounds
