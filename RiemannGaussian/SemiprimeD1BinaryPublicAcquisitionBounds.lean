/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionExecution

/-! # Actual public preprocessing space and original configuration semantics
Every real data/return stack is counted. The parameter equalities refer to the
same original public configuration and digit definitions, including square inputs.
This is a preprocessing result; graph, coefficient and factor-controller joins
remain separate obligations for the complete factoring bit-machine theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds
open SemiprimeD1BinaryPublicAcquisition SemiprimeD1BinaryPublicAcquisitionComponents
open SemiprimeD1BinaryPublicAcquisitionExecution SemiprimeBitArithmetic SemiprimeMacroParameters

/-- An actual successful source prefix cannot pass the proved final halt. -/
theorem prefix_fuel_le (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) : fuel ≤ timeBound bits := by
  obtain ⟨time,ht,hexe⟩:=source_run bits hb
  have hf : fuel ≤ time := by
    by_contra hn
    have he : fuel=time+(1+(fuel-(time+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hexe,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (⟨none,none,none,result bits,[]⟩:C.State Stack Label)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht

/-- All twenty-eight Boolean data stacks and the physical finite-label return
stack fit a fixed quadratic bound at EVERY successful executed prefix. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 24000000*(bits.length+1)^2 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp only [initial,input,store,Digits.input,SemiprimeD1BinaryDigitAcquisition.store,
          SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
      · rcases k with k|k <;> exact Nat.zero_le _
    · rcases k with k|k <;> exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 28*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  unfold timeBound at ht
  nlinarith [Nat.zero_le (bits.length^2)]

/-- Compiled-machine storage, from initList of ONLY original binary N, counts
every data and return cell with no supplied live-state/resource premise. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 24000000*(bits.length+1)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct
    (digitStack (Digits.metaStack .input))
    (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output)) (mainLabel .start)
    program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh : (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start : machine.Cfg=>
      (fun q : Option machine.Cfg=>q.bind machine.step)^[fuel] (some start))
        (initial_configuration bits)).trans hr)
  cases hc:C.run program fuel (initial bits) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc

/-- Original binary N is retained, without conversion to unary numeric N. -/
theorem retained_input (bits : List Bool) :
    result bits (digitStack (Digits.metaStack .input))=bits := rfl

/-- The WHOLE actual original digit cache survives both subsequent stages. -/
theorem retained_digits (bits : List Bool) :
    result bits (digitStack (Digits.bankStack SemiprimeD1StackDigitBank.output))=
      SemiprimeD1TensorTapeCodec.vectorBits
        (SemiprimeD1StackDigitBankSpec.blocks
          (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) bits.length bits) := rfl

/-- The two unary axes and depth are the actual original public configuration. -/
theorem public_dimensions (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    let config:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
    (result bits (axesStack (.inr 0))).length=config.r ∧
    (result bits (axesStack (.inr 1))).length=config.t ∧
    (result bits (axesStack (.inr 2))).length=config.depth :=
  SemiprimeD1StackAxesBounds.public_original_dimensions bits hc hN

/-- The normalizer word is exactly the original public normalizer value. -/
theorem public_normalizer (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    bitValue (result bits (fermatStack (.inr true)))=
      (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN).normalizer.val :=
  SemiprimeD1StackFermatBounds.public_normalizer bits hc hN

/-- The modulus word equals the original positive-width macro modulus. -/
theorem public_modulus (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    bitValue (result bits (fermatStack (.inr false)))=
      2^(SemiprimeMacroFermatNetwork.macroLength
        (macroDepth (bitLength (bitValue bits))))+1 := by
  have hw : bits.length=bitLength (bitValue bits) :=
    SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  have hn : 0 < bits.length := by rw [hw];exact bitLength_pos hN
  change bitValue (SemiprimeD1StackFermatExecution.result bits (.inr false))=_
  rw [←hw]
  exact SemiprimeD1StackFermatBounds.original_modulus bits hn

/-- The acquired cache contains exactly the original number of radix digits. -/
theorem original_count (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    (SemiprimeD1StackDigitBankSpec.blocks (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits)
      bits.length bits).length=digitCount (bitLength (bitValue bits)) :=
  SemiprimeD1BinaryDigitAcquisitionBounds.original_count bits hc hN

/-- Every cache digit has the exact original targetDigit value. -/
theorem original_digit (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (i : ℕ) (hi : i < digitCount (bitLength (bitValue bits))) :
    ∃digit,(SemiprimeD1StackDigitBankSpec.blocks (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits)
      bits.length bits)[i]?=some digit ∧
        bitValue digit=targetDigit (bitLength (bitValue bits)) (bitValue bits) i :=
  SemiprimeD1BinaryDigitAcquisitionBounds.original_digit bits hc hN i hi

/-- Canonical positive original inputs run this SAME single preprocessing
machine in a fixed quadratic number of actual finite-machine transitions. -/
noncomputable def originalInTime (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label)))
      (800000*(bitLength (bitValue bits)+1)^2) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  simpa only [timeBound,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] using acquireInTime bits hb

/-- Every actual original-input prefix has the same whole-store quadratic bound. -/
theorem original_space (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      24000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  simpa only [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] using machine_prefix_cells bits hb fuel cfg hr

end RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds
