/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformBounds
/-! # Whole finite-machine time and every-prefix data/return storage -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformResources
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformMachine
open SemiprimeD1StackPublicTransformBounds SemiprimeBitArithmetic
/-- Real original input location in the fixed finite stack catalogue. -/
def inputRole : Stack := .roots (.inl (SemiprimeD1BinaryPublicAcquisition.digitStack
  (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input)))
/-- Own completed source execution under the original-tape polynomial. -/
theorem source_run_bounded (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t ≤ runBound bits raw,C.run program t (initial bits raw second inverse)=some (done bits raw second inverse) := by
  obtain ⟨t,ht,hr⟩:=source_run bits raw second inverse hc hN
  exact ⟨t,ht.trans (runBound_le bits raw second inverse hc hN),hr⟩
/-- Genuine whole FinTM2 execution with no component/time/verdict advice. -/
noncomputable def machineCheck (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits raw second inverse))
      (some (SemiprimeD1StackCalls.configuration (done bits raw second inverse))) (runBound bits raw) := by
  have h:=SemiprimeD1StackPublicTransformMachine.machineCheck bits raw second inverse hc hN
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (runBound_le bits raw second inverse hc hN)⟩
/-- Every successful actual prefix precedes this actual completed halt. -/
theorem prefix_fuel_le (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw second inverse)=some out) : fuel ≤ runBound bits raw := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits raw second inverse hc hN
  have hf : fuel ≤ t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits raw second inverse)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All original data-role input bounds, including the actual N source cache. -/
theorem initial_bound (bits raw : List Bool) (second inverse : Bool) (q : Stack) :
    ((initial bits raw second inverse).data q).length ≤ bits.length+raw.length+1 := by
  cases q with
  | roots k=>exact (SemiprimeD1StackPublicScaleBounds.root_initial_bound bits k).trans (by omega)
  | aux q=>cases q <;> simp only [initial,List.length_nil,List.length_cons] <;> omega
  | dot k=>exact Nat.zero_le _
  | multiply k=>exact Nat.zero_le _
  | inputVector k=>exact Nat.zero_le _
  | outputVector k=>exact Nat.zero_le _
  | guard k=>exact Nat.zero_le _
  | read k=>exact Nat.zero_le _
  | equal k=>exact Nat.zero_le _
/-- Every actual data cell and finite return label is counted at every prefix. -/
def spaceBound (bits raw : List Bool) : ℕ :=10^94*(bits.length+raw.length+1)^18
/-- ALL204 physical Boolean stacks plus actual return frames, with no assumed
intermediate width or elapsed-free-space reinterpretation. -/
theorem prefix_cells (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw second inverse)=some out) :
    (∑q : Stack,(out.data q).length)+out.frames.length ≤ spaceBound bits raw := by
  let S:=bits.length+raw.length+1
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ out (initial_bound bits raw second inverse) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hsum : (∑q : Stack,(out.data q).length) ≤ 204*(S+fuel) := by
    calc
      _ ≤ ∑_q : Stack,(S+fuel) := Finset.sum_le_sum (fun q _=>hd q)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits raw second inverse hc hN fuel out hr
  have hS : 1 ≤ S := by dsimp [S];omega
  have hp : S ≤ S^18 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (by decide : 1 ≤ 18)
  change fuel ≤ 10^90*S^18 at ht
  change _ ≤ 10^94*S^18
  norm_num only at ht ⊢
  omega
/-- Same bound on ALL204 data stacks and real returns of genuine FinTM2. -/
theorem machine_prefix_cells (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw second inverse)))=some cfg) :
    (∑q : Stack,(cfg.stk (some q)).length)+(cfg.stk none).length ≤ spaceBound bits raw := by
  have he:=SemiprimeD1StackCalls.run_correct inputRole (.aux .output) Label.start program fuel
    (initial bits raw second inverse)
  have hh:=he.trans hr
  cases ho : C.run program fuel (initial bits raw second inverse) with
  | none=>rw [ho] at hh;cases hh
  | some out=>
    rw [ho] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits raw second inverse hc hN fuel out ho
end RiemannGaussian.SemiprimeD1StackPublicTransformResources
