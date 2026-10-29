/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryStorage
/-! # Entire physical packed-scalar factor recovery for every original semiprime
This fixed prepared source takes ONLY original binary N and the ACTUALLY
acquired packed scalar. It supplies its own count, sum, discriminant, binary
square root, factors and physical validation. The N-only scalar-producing
recursive counter and its literal caller join remain OPEN.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryOriginal
open scoped BigOperators
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryMeaning
open SemiprimeD1StackPackedFactorRecoveryClock SemiprimeD1StackPackedFactorRecoveryFamily
open SemiprimeD1StackPackedFactorRecoveryStorage SemiprimeD1StackPackedFactorRecoveryWidths
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
/-- BOTH original physical input words remain present after every actual recovery call. -/
theorem inputs_retained (bits scalar : List Bool) :
    (done bits scalar).data originalInput=bits ∧ (done bits scalar).data scalarInput=scalar := by
  constructor
  · change (done bits scalar).data (readout R.originalInput)=bits
    rw [readout_retained]
    rfl
  · change (done bits scalar).data (readout R.scalarInput)=scalar
    rw [readout_retained]
    rfl
/-- Every actual readout cache/metadata/scalar/moment/radix word is retained literally. -/
theorem all_readout_retained (bits scalar : List Bool) (k : R.Stack) :
    (done bits scalar).data (readout k)=SemiprimeD1StackPackedMomentReadoutEncoding.result bits scalar k :=
  readout_retained bits scalar k
/-- All18 physically borrowed arithmetic work roles are empty after actual validation. -/
theorem arithmetic_empty (bits scalar : List Bool) (k : Fin 18) :
    (done bits scalar).data (squareRoot (S.clearStack k))=[] := by
  unfold done result
  split_ifs <;> fin_cases k <;> rfl
/-- The explicit restoring scratch is physically empty and counted among all59 roles. -/
theorem scratch_empty (bits scalar : List Bool) : (done bits scalar).data (aux .scratch)=[] := by
  unfold done result;split_ifs <;> rfl
/-- Outputs are the actual compact binary factor words, including the square branch. -/
theorem compact_outputs (bits scalar : List Bool) :
    Compact ((done bits scalar).data (aux .small)) ∧ Compact ((done bits scalar).data (aux .large)) :=
  outputs_compact bits scalar
/-- SAME entire prepared source returns a verified nontrivial factor pair for EVERY semiprime. -/
theorem source_original (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    ∃t ≤ polynomial bits scalar,SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) ∧
      2≤bitValue ((done bits scalar).data (aux .small)) ∧ 2≤bitValue ((done bits scalar).data (aux .large)) ∧
      bitValue ((done bits scalar).data (aux .small))*bitValue ((done bits scalar).data (aux .large))=bitValue bits ∧
      Compact ((done bits scalar).data (aux .small)) ∧ Compact ((done bits scalar).data (aux .large)) ∧
      (done bits scalar).data (aux .status)=[true] := by
  obtain ⟨t,ht,hr,hs,hl,hprod⟩:=source_factorization bits scalar hc p q hp hq hN hscalar
  exact ⟨t,ht,hr,hs,hl,hprod,(outputs_compact bits scalar).1,(outputs_compact bits scalar).2,status_true bits scalar⟩
/-- A compact actual scalar has at most2ell bits by the proved packed moment range. -/
theorem scalar_length (bits scalar : List Bool) (hc : Compact bits) (hcs : Compact scalar) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    scalar.length≤2*bits.length :=
  SemiprimeD1StackPackedMomentReadoutOriginal.scalar_length bits scalar hc hcs p q hp hq hN hscalar
/-- The same actual whole source is quartic in canonical original N bits when its acquired scalar is compact. -/
theorem source_compact (bits scalar : List Bool) (hc : Compact bits) (hcs : Compact scalar) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    ∃t ≤ 100000000000000000*(bits.length+1)^4,
      SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) ∧
      2≤bitValue ((done bits scalar).data (aux .small)) ∧ 2≤bitValue ((done bits scalar).data (aux .large)) ∧
      bitValue ((done bits scalar).data (aux .small))*bitValue ((done bits scalar).data (aux .large))=bitValue bits := by
  obtain ⟨t,ht,hr,hs,hl,hprod⟩:=source_factorization bits scalar hc p q hp hq hN hscalar
  have hlen:=scalar_length bits scalar hc hcs p q hp hq hN hscalar
  have hpow:=Nat.pow_le_pow_left (show inputSize bits scalar≤3*(bits.length+1) by unfold inputSize;omega) 4
  rw [mul_pow] at hpow
  unfold polynomial at ht
  exact ⟨t,by nlinarith,hr,hs,hl,hprod⟩
/-- Genuine compiled TWO-word prepared certificate; it does not assert a missing N-only scalar acquisition. -/
noncomputable def machineOriginal (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits scalar))
      (some (SemiprimeD1StackCalls.configuration (done bits scalar))) (1000000000000000*(bits.length+scalar.length+1)^4) :=
  machinePrepared bits scalar hc p q hp hq hN hscalar
/-- ALL59 actual data words plus real returns are paid at EVERY actual compiled prefix. -/
theorem original_prefix_cells (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun z=>z.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits scalar)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤1000000000000000000*(bits.length+scalar.length+1)^4 :=
  machine_prefix_cells bits scalar hc p q hp hq hN hscalar fuel cfg hr
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryOriginal
