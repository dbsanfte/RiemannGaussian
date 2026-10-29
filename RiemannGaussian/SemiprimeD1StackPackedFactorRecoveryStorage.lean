/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryFamily
/-! # All59 actual words and saved returns at every prepared recovery prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryStorage
open scoped BigOperators
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryMeaning
open SemiprimeD1StackPackedFactorRecoveryClock SemiprimeD1StackPackedFactorRecoveryFamily
open SemiprimeD1StackPackedFactorRecoveryWidths SemiprimeBitArithmetic SemiprimeSourceCompactBits
/-- The two physical inputs, including arbitrary scalar padding, bound every original source word. -/
theorem initial_length (bits scalar : List Bool) (k : Stack) :
    ((initial bits scalar).data k).length≤3*inputSize bits scalar := by
  rcases k with k|k|k
  · exact SemiprimeD1StackPackedMomentReadoutStorage.initial_length bits scalar k
  · exact Nat.zero_le _
  · exact Nat.zero_le _
/-- No physical word or unused source role is omitted from the total storage count. -/
theorem word_sum (data : Stack→List Bool) (cap : ℕ) (h : ∀k,(data k).length≤cap) :
    (∑k : Stack,(data k).length)≤59*cap := by
  calc
    _ ≤ ∑_k : Stack,cap := Finset.sum_le_sum (fun k _=>h k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Fixed storage coefficient and degree precede every physical input and semiprime family. -/
def cellsPolynomial (bits scalar : List Bool) : ℕ := 1000000000000000000*(inputSize bits scalar)^4
/-- Every actual source prefix counts all59 data words plus its real finite-label return stack. -/
theorem prefix_cells (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits scalar)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤cellsPolynomial bits scalar := by
  obtain ⟨t,ht,hs⟩:=source_run_bounded bits scalar hc p q hp hq hN hscalar
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hs,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh : SemiprimeD1StackCalls.run program 1 (done bits scalar)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (3*inputSize bits scalar)
    (initial bits scalar) out (initial_length bits scalar) hr
  have hsum:=word_sum out.data (3*inputSize bits scalar+fuel) hd
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits scalar) out hr
  change out.frames.length≤0+fuel at hframes
  have hl : inputSize bits scalar≤(inputSize bits scalar)^4 := Nat.le_self_pow (by decide : 4≠0) _
  unfold cellsPolynomial polynomial at *
  nlinarith
/-- Actual finite two-word prepared machine certificate; scalar acquisition is NOT claimed. -/
noncomputable def machinePrepared (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits scalar))
      (some (SemiprimeD1StackCalls.configuration (done bits scalar))) (polynomial bits scalar) := by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .small) (ctl .start) program
  let h:=source_run_bounded bits scalar hc p q hp hq hN hscalar
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every compiled prefix counts the SAME59 data words AND the actual saved-return word. -/
theorem machine_prefix_cells (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun z=>z.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits scalar)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤cellsPolynomial bits scalar := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput (aux .small) (ctl .start) program fuel (initial bits scalar)
  have hh:=he.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel (initial bits scalar) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have heq : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits scalar hc p q hp hq hN hscalar fuel out hout
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryStorage
