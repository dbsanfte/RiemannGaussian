/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFermatExecution
import RiemannGaussian.SemiprimeD1StackTransformBounds

/-! # Actual prefix storage and positive-input public constant agreement
Zero-width execution produces its own local E=0/R=1 words; the legacy macro
normalizer equality is deliberately restricted to positive original input width.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatBounds
open SemiprimeD1StackFermatConstants SemiprimeD1StackFermatComponents SemiprimeD1StackFermatExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Every actual data stack has at most original width plus executed pushes. -/
theorem prefix_data_bound (bits:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    ∀k,(out.data k).length≤bits.length+fuel := by
  apply SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out ?_ hr
  intro k
  cases k with
  | inl k => cases k <;> simp [initial,input,Meta.input]
  | inr bit => cases bit <;> simp [initial,input]

/-- Pure scalar substitution independent of executable projection contexts. -/
theorem numeric_space (n fuel cells frames time:ℕ)
    (hc:cells≤13*(n+fuel)) (hf:frames≤fuel) (ht:fuel≤time)
    (hb:time≤150000*(n+1)^2) : cells+frames≤2200000*(n+1)^2 := by
  nlinarith

/-- All thirteen Boolean stacks and the real return stack are included. -/
theorem machine_space (bits:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk (some (.inl .input))).length+(cfg.stk (some (.inl .width))).length+(cfg.stk (some (.inl .nonzero))).length+(cfg.stk (some (.inl .threshold))).length+(cfg.stk (some (.inl .radius))).length+(cfg.stk (some (.inl .square))).length+(cfg.stk (some (.inl .exponent))).length+(cfg.stk (some (.inl .squareWork))).length+(cfg.stk (some (.inl .thresholdWork))).length+(cfg.stk (some (.inl .temporary))).length+(cfg.stk (some (.inl .radix))).length+(cfg.stk (some (.inr false))).length+(cfg.stk (some (.inr true))).length+(cfg.stk none).length≤2200000*(bits.length+1)^2 := by
  rw [initial_eq] at hr
  let state:=initial bits
  change (fun cfg=>cfg.bind machine.step)^[fuel]
    (some (SemiprimeD1StackCalls.configuration state))=some cfg at hr
  have he:=SemiprimeD1StackCalls.run_correct (.inl .input) (.inr true) (.inl .start) program fuel state
  change (C.run program fuel state).map SemiprimeD1StackCalls.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration state)) at he
  cases hc:C.run program fuel state with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have hbound:=prefix_data_bound bits fuel out hc
    have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel state out hc
    have htime:fuel≤totalTime bits.length:=by
      by_contra hn
      have ht:fuel=totalTime bits.length+((fuel-totalTime bits.length-1)+1):=by omega
      rw [ht,SemiprimeD1StackReturnLink.run_add,acquire_run bits,Option.bind_some] at hc
      have hh:C.run program ((fuel-totalTime bits.length-1)+1) (done bits)=none:=by
        unfold C.run
        rw [Function.iterate_succ_apply]
        have hs:C.step program (done bits)=none:=by
          simp [C.step,SemiprimeD1StackCalls.step,done]
        simp only [Option.bind_some,hs]
        exact Function.iterate_fixed rfl _
      rw [hh] at hc;cases hc
    have h0:=hbound (.inl .input)
    have h1:=hbound (.inl .width)
    have h2:=hbound (.inl .nonzero)
    have h3:=hbound (.inl .threshold)
    have h4:=hbound (.inl .radius)
    have h5:=hbound (.inl .square)
    have h6:=hbound (.inl .exponent)
    have h7:=hbound (.inl .squareWork)
    have h8:=hbound (.inl .thresholdWork)
    have h9:=hbound (.inl .temporary)
    have h10:=hbound (.inl .radix)
    have h11:=hbound (.inr false)
    have h12:=hbound (.inr true)
    change out.frames.length≤0+fuel at hf
    have hs:(out.data (.inl .input)).length+(out.data (.inl .width)).length+(out.data (.inl .nonzero)).length+(out.data (.inl .threshold)).length+(out.data (.inl .radius)).length+(out.data (.inl .square)).length+(out.data (.inl .exponent)).length+(out.data (.inl .squareWork)).length+(out.data (.inl .thresholdWork)).length+(out.data (.inl .temporary)).length+(out.data (.inl .radix)).length+(out.data (.inr false)).length+(out.data (.inr true)).length≤13*(bits.length+fuel):=by omega
    change (out.data (.inl .input)).length+(out.data (.inl .width)).length+(out.data (.inl .nonzero)).length+(out.data (.inl .threshold)).length+(out.data (.inl .radius)).length+(out.data (.inl .square)).length+(out.data (.inl .exponent)).length+(out.data (.inl .squareWork)).length+(out.data (.inl .thresholdWork)).length+(out.data (.inl .temporary)).length+(out.data (.inl .radix)).length+(out.data (.inr false)).length+(out.data (.inr true)).length+out.frames.length≤_
    exact numeric_space bits.length fuel _ _ _ hs (by simpa only [Nat.zero_add] using hf) htime (totalTime_le bits.length)

/-- The original binary input and actual nonzero flag remain physically retained. -/
theorem retained (bits:List Bool) :
    result bits (.inl .input)=bits ∧
      result bits (.inl .nonzero)=[SemiprimeD1BinaryBootstrap.seenOne bits] := by
  exact ⟨rfl,rfl⟩

/-- On positive physical width, the returned normalizer is the existing original macro normalizer. -/
theorem original_normalizer (bits:List Bool) (hL:0<bits.length) :
    bitValue (result bits (.inr true))=
      (SemiprimeMacroEntryExecution.explicitNormalizer (macroDepth bits.length)).val := by
  exact SemiprimeD1StackFermatWords.original_normalizer bits.length hL

/-- The returned modulus agrees with the legacy positive-width macro modulus. -/
theorem original_modulus (bits:List Bool) (hL:0<bits.length) :
    bitValue (result bits (.inr false))=2^(SemiprimeMacroFermatNetwork.macroLength (macroDepth bits.length))+1 := by
  change bitValue (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length))=_
  rw [transform_eq_macroLength hL]
  exact SemiprimeD1StackFermatWords.modulus_value _ (by unfold SemiprimeMacroFermatNetwork.macroLength; positivity)

/-- The actual returned word agrees with the full existing positive public configuration. -/
theorem public_normalizer (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) :
    bitValue (result bits (.inr true))=
      (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN).normalizer.val := by
  rw [SemiprimeMacroEntryExecution.normalizer_eq_explicit]
  have hw:bits.length=bitLength (bitValue bits):=
    SemiprimeD1BinaryBootstrap.canonical_width bits hc
  have hL:0<bits.length:=by
    rw [hw]
    exact Nat.size_pos.mpr hN
  change bitValue (result bits (.inr true))=
    (SemiprimeMacroEntryExecution.explicitNormalizer (macroDepth (bitLength (bitValue bits)))).val
  rw [←hw]
  exact original_normalizer bits hL

/-- Canonical original input ties physical width to the public bitLength. -/
def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (150000*(bitLength (bitValue bits)+1)^2) := by
  have hw:=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  simpa only [hw,bitLength] using acquireInTime bits
end RiemannGaussian.SemiprimeD1StackFermatBounds
