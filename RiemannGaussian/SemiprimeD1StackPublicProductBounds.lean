/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicProductExecution
import RiemannGaussian.SemiprimeD1StackRootSourceOriginal

/-! # Whole original-input public product clock and every-prefix inventory -/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPublicProductBounds
open SemiprimeD1StackPublicProduct SemiprimeD1StackPublicProductExecution
/-- Exact actual modulus word width from the original preprocessing trace. -/
theorem cached_length (bits : List Bool) :
    (cached bits).length=SemiprimeMacroParameters.transformLength bits.length+1 :=
  SemiprimeD1StackRootSourceOriginal.modulus_length bits
/-- The actual cached modulus has linearly many cells in ORIGINAL binary N. -/
theorem cached_length_le (bits : List Bool) : (cached bits).length≤66*(bits.length+1) := by
  rw [cached_length]
  have h:=(SemiprimeD1StackTransformArithmetic.prefix_powers bits.length _ le_rfl).1
  change SemiprimeMacroParameters.transformLength bits.length≤64*bits.length+1 at h
  omega
/-- A fixed original-input cubic allowance for the complete actual program. -/
def runBound (bits raw : List Bool) : ℕ := 1000000000000*(bits.length+raw.length+2)^3
/-- Acquisition and arithmetic are charged on this SAME program and original
physical input; no mixed/native report or supplied-size transport is used. -/
theorem timeBound_le (bits raw : List Bool) : timeBound bits raw≤runBound bits raw := by
  let I:=bits.length+raw.length+2
  have hI : 1≤I := by dsimp [I];omega
  have hc:=cached_length_le bits
  have hp : raw.length+(cached bits).length+3≤70*I := by dsimp [I];omega
  have hProd : SemiprimeD1StackProductCheckBounds.runBound raw (cached bits)≤343000000000*I^3 := by
    unfold SemiprimeD1StackProductCheckBounds.runBound
    calc
      _ ≤ 1000000*(70*I)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 3)
      _ = _ := by ring
  have hAcq : (bits.length+1)^2≤I^3 :=
    (Nat.pow_le_pow_left (by dsimp [I];omega) 2).trans (Nat.pow_le_pow_right hI (by decide : 2≤3))
  have hpos : 0<I^3 := Nat.pow_pos (by omega)
  change _≤1000000000000*I^3
  unfold timeBound SemiprimeD1BinaryPublicAcquisitionExecution.timeBound
  omega
/-- Complete actual source with its original-input cubic clock. -/
theorem source_run_bounded (bits raw : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits raw,C.run program t (initial bits raw)=some (done bits raw) := by
  obtain ⟨t,ht,hr⟩:=source_run bits raw hb
  exact ⟨t,ht.trans (timeBound_le bits raw),hr⟩
/-- Proof-side trace choice, never a runtime result or clock opcode. -/
noncomputable def sourceCheck (bits raw : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits raw) (some (done bits raw)) (runBound bits raw) := by
  let h:=source_run_bounded bits raw hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine finite-machine original N+raw assignment certificate. -/
noncomputable def machineCheck (bits raw : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits raw))
      (some (SemiprimeD1StackCalls.configuration (done bits raw))) (runBound bits raw) :=
  SemiprimeD1StackCalls.evalsCorrect original output Label.start program _ _ _ (sourceCheck bits raw hb)
/-- No successful execution prefix continues beyond its bounded complete halt. -/
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
/-- Initial inputs consist of actual original N and actual assignment bytes. -/
theorem initial_length (bits raw : List Bool) (k : Stack) :
    ((initial bits raw).data k).length≤bits.length+raw.length := by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp only [initial,input,P.input,SemiprimeD1BinaryPublicAcquisition.store,
          SemiprimeD1BinaryPublicAcquisition.Digits.input,SemiprimeD1BinaryDigitAcquisition.store,
          SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
      · rcases k with k|k <;> exact Nat.zero_le _
    · rcases k with k|k <;> exact Nat.zero_le _
  · change (V.input raw [] k).length≤bits.length+raw.length
    unfold SemiprimeD1StackProductCheck.input
    split
    · omega
    · split <;> exact Nat.zero_le _
/-- EVERY prefix counts ALL76 physical Boolean stack roles, retained caches,
unused shadows, parse/arithmetic workspace AND actual return-label cells. -/
theorem prefix_cells (bits raw : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤
      100000000000000*(bits.length+raw.length+2)^3 := by
  let I:=bits.length+raw.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (initial_length bits raw) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤76*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits raw hb fuel out hr
  change fuel≤1000000000000*(I+2)^3 at ht
  have hI : I≤(I+2)^3 := by
    have h:=Nat.pow_le_pow_right (by omega : 1≤I+2) (by decide : 1≤3)
    simp only [pow_one] at h
    omega
  change _≤100000000000000*(I+2)^3
  omega
/-- Identical all-prefix inventory for the SAME genuine finite machine. -/
theorem machine_prefix_cells (bits raw : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      100000000000000*(bits.length+raw.length+2)^3 := by
  have he:=SemiprimeD1StackCalls.run_correct original output Label.start program fuel (initial bits raw)
  change (C.run program fuel (initial bits raw)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial bits raw) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits raw hb fuel out hc
end RiemannGaussian.SemiprimeD1StackPublicProductBounds
