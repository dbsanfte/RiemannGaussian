/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputBounds
/-! # All2505 words and real returns from genuine original-input initialization -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputStorage
open scoped BigOperators
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackPackedRootInputBounds
open SemiprimeD1StackCalls (run configuration)
open SemiprimeBitArithmetic (bitValue)
/-- Every non-input role really starts empty. -/
theorem input_single (bits : List Bool) : input bits=fun k => if k=originalInput then bits else [] := by
  funext k
  rcases k with k|k
  · have h:=congrFun (SemiprimeD1StackRootPacketInventoryStorage.input_single bits) k
    simpa only [input,bank,rootStack,originalInput,Sum.elim_inl,Sum.inl.injEq] using h
  · rcases k with k|k <;> rfl
/-- Genuine Turing.initList is exactly the new source's sole-binary-input initial state. -/
theorem initial_eq (bits : List Bool) : Turing.initList machine bits=configuration (initial bits) := by
  have hs : SemiprimeD1StackCalls.initial originalInput (Label.local .start) bits=initial bits := by
    apply congrArg (fun d => (⟨some (Label.local .start),none,none,d,[]⟩ : C.State Stack Label))
    exact (input_single bits).symm
  exact (SemiprimeD1StackCalls.initial_correct originalInput output (.local .start) program bits).symm.trans
    (congrArg configuration hs)
/-- Every initial word is paid by actual original binary input bytes. -/
theorem initial_length (bits : List Bool) (k : Stack) : ((initial bits).data k).length ≤ bits.length := by
  change (input bits k).length ≤ bits.length
  rw [input_single]
  change (if k=originalInput then bits else []).length ≤ bits.length
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _
/-- Every complete actual machine prefix is before the SAME program's proved halt. -/
theorem prefix_clock (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (fuel : ℕ) (out : C.State Stack Label) (hr : run program fuel (initial bits)=some out) : fuel ≤ runBound bits := by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded bits hc hN
  have hh : run program 1 (done bits hN)=none := rfl
  have hf : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All2505 allocations, including every retained and unused shadow, are counted. -/
theorem word_sum (d : Stack→List Bool) (cap : ℕ) (h : ∀k,(d k).length ≤ cap) :
    (∑k : Stack,(d k).length) ≤ 2505*cap := by
  calc
    _ ≤ ∑_k : Stack,cap := Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- SAME actual finite-source prefix data and all real saved-return cells. -/
theorem prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (fuel : ℕ) (out : C.State Stack Label) (hr : run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 2506*(bits.length+runBound bits) := by
  have hf:=prefix_clock bits hc hN fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out
    (initial_length bits) hr
  have hs:=word_sum out.data (bits.length+fuel) hd
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length ≤ 0+fuel at hframes
  omega
/-- Genuine compiled whole original-input machine certificate, with its SAME own total clock. -/
noncomputable def machineSource (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (configuration (done bits hN))) (runBound bits) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.local .start) program
  let h:=source_run_bounded bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every compiled original-input prefix includes all2505 data words and the real return stack. -/
theorem machine_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 2506*(bits.length+runBound bits) := by
  rw [initial_eq] at hp
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (.local .start) program fuel (initial bits)
  have hh:=he.trans hp
  cases hout : run program fuel (initial bits) with
  | none => rw [hout] at hh;cases hh
  | some out =>
    rw [hout] at hh
    have hcfg : cfg=configuration out := (Option.some.inj hh).symm
    subst cfg
    exact prefix_cells bits hc hN fuel out hout
end RiemannGaussian.SemiprimeD1StackPackedRootInputStorage
