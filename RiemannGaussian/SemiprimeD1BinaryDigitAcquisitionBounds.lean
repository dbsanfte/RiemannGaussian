/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionExecution

/-! # Actual original-input acquisition storage and public semantics
Every visited metadata, input, bank, temporary and return cell is counted.
Canonical encoding connects the physical input length to the SAME original
bitLength used in the semiprime algorithm, rather than to the numeric value N.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionBounds
open SemiprimeD1BinaryDigitAcquisition SemiprimeD1BinaryDigitAcquisitionComponents
open SemiprimeD1BinaryDigitAcquisitionExecution SemiprimeBitArithmetic SemiprimeMacroParameters

/-- A successful prefix cannot extend past the actual complete acquisition halt. -/
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

/-- ALL actual source prefixes count the twenty-three Boolean data stacks and
the physically executed return stack, without a supplied maximum-live promise. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 4000000*(bits.length+1)^2 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    rcases k with k|k
    · cases k <;> simp only [initial,SemiprimeD1BinaryDigitAcquisition.input,store,
        Meta.input,Sum.elim_inl,List.length_nil] <;> omega
    · rcases k with k|k <;> exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 23*(bits.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=23 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  unfold timeBound at ht
  nlinarith [Nat.zero_le (bits.length^2)]

/-- All actual compiled-machine prefixes, starting from original N alone, have
the same complete storage bound, with no fuel or intermediate-state advice. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 4000000*(bits.length+1)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct (metaStack .input) (bankStack Bank.output) (mainLabel .start)
    program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hs : (SemiprimeD1StackCalls.configuration (initial bits) : machine.Cfg)=Turing.initList machine bits :=
    initial_configuration bits
  have hh : (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start : machine.Cfg=>
      (fun q : Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) hs).trans hr)
  cases hc:C.run program fuel (initial bits) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc

/-- Original binary input is physically retained in the metadata cache. -/
theorem retained_input (bits : List Bool) : (result bits) (metaStack .input)=bits := rfl

/-- The final vector contains only the ACTUALLY acquired digit words. -/
theorem encoded_digits (bits : List Bool) :
    (result bits) (bankStack Bank.output)=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1StackDigitBankSpec.blocks (radix bits) bits.length bits) := rfl

/-- Canonical original input ties every physical width formula to the original public parameter. -/
theorem canonical_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    bits.length=bitLength (bitValue bits) := SemiprimeD1BinaryBootstrap.canonical_width bits hc

/-- The actual acquired bank has exactly the native original digitCount, now
as physically emitted framed records rather than a supplied count or list. -/
theorem original_count (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    (SemiprimeD1StackDigitBankSpec.blocks (radix bits) bits.length bits).length=
      digitCount (bitLength (bitValue bits)) := by
  have hw:=canonical_width bits hc
  have hell : 0 < bitLength (bitValue bits) := bitLength_pos hN
  have hrad : (radix bits).length=radixBits (bitLength (bitValue bits)) := by rw [radix_length,hw]
  exact SemiprimeD1StackDigitBankSpec.original_count _ hell bits (radix bits) hw hrad

/-- Every actual original digit, including zero digits, has the EXACT frozen
targetDigit value. Large powers/division appear only in that specification. -/
theorem original_digit (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (i : ℕ) (hi : i<digitCount (bitLength (bitValue bits))) :
    ∃digit,(SemiprimeD1StackDigitBankSpec.blocks (radix bits) bits.length bits)[i]?=some digit ∧
      bitValue digit=targetDigit (bitLength (bitValue bits)) (bitValue bits) i := by
  have hw:=canonical_width bits hc
  have hrad : (radix bits).length=radixBits (bitLength (bitValue bits)) := by rw [radix_length,hw]
  apply SemiprimeD1StackDigitBankSpec.original_digit _ bits (radix bits) hrad i
  rw [original_count bits hc hN]
  exact hi

/-- Canonical positive original inputs run the same ONE finite machine within
the original public input-length budget, with all acquisition/copies paid. -/
noncomputable def originalInTime (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (⟨none,none,none,result bits,[]⟩:C.State Stack Label)))
      (150000*(bitLength (bitValue bits)+1)^2) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  have h:=acquireInTime bits hb
  simpa only [timeBound,canonical_width bits hc] using h

/-- Every actual original-input prefix also has a fixed quadratic bit-cell bound. -/
theorem original_space (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0 < bitValue bits) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 4000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0 hN)
  simpa only [canonical_width bits hc] using machine_prefix_cells bits hb fuel cfg hr

end RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionBounds
