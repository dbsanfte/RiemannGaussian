/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackGraphIndicesExecution
import RiemannGaussian.SemiprimeD1StackTransformBounds
import RiemannGaussian.SemiprimeMacroFiniteEnumerations

/-! # Original graph word-slot catalogue and actual prefix storage
This is the literal Fin(R+1) word-bit block of the real graph. Tagged Cartesian
vertex/factor and port-owner assembly remain separate, not an input oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackGraphIndicesBounds
open SemiprimeD1StackGraphIndices SemiprimeD1StackGraphIndicesComponents SemiprimeD1StackGraphIndicesExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackGraphIndicesLoop
open SemiprimeSourceHistogramKeyBits (frame)

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
    (hb:time≤200000*(n+1)^2) : cells+frames≤3000000*(n+1)^2 := by
  nlinarith

/-- All thirteen Boolean stacks and the real return stack are included. -/
theorem machine_space (bits:List Bool) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (cfg.stk (some (.inl .input))).length+(cfg.stk (some (.inl .width))).length+(cfg.stk (some (.inl .nonzero))).length+(cfg.stk (some (.inl .threshold))).length+(cfg.stk (some (.inl .radius))).length+(cfg.stk (some (.inl .square))).length+(cfg.stk (some (.inl .exponent))).length+(cfg.stk (some (.inl .squareWork))).length+(cfg.stk (some (.inl .thresholdWork))).length+(cfg.stk (some (.inl .temporary))).length+(cfg.stk (some (.inl .radix))).length+(cfg.stk (some (.inr false))).length+(cfg.stk (some (.inr true))).length+(cfg.stk none).length≤3000000*(bits.length+1)^2 := by
  rw [initial_eq] at hr
  let state:=initial bits
  change (fun cfg=>cfg.bind machine.step)^[fuel]
    (some (SemiprimeD1StackCalls.configuration state))=some cfg at hr
  have he:=SemiprimeD1StackCalls.run_correct (.inl .input) (.inr false) (.inl .start) program fuel state
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

/-- The exact original finite index enumeration retains ascending order and multiplicity. -/
theorem fin_values (n:ℕ) : (SemiprimeFiniteEnumerations.fin n).values.map Fin.val=List.range n := by
  change (List.finRange n).map Fin.val=List.range n
  apply List.ext_getElem <;> simp

/-- The executed catalogue is precisely the original Fin enumeration's framed index data. -/
theorem catalogue_fin (n:ℕ) (tail:List Bool) :
    catalogue n tail=(SemiprimeFiniteEnumerations.fin n).values.foldr
      (fun i rest=>frame (List.replicate i.val true) rest) tail := by
  rw [catalogue_range,←fin_values]
  simp only [List.foldr_map]

/-- Actual output allocation is the full literal catalogue size, not a cardinality answer. -/
theorem output_length (bits:List Bool) :
    (result bits (.inr false)).length=(transformLength bits.length+1)^2 := by
  change (catalogue (transformLength bits.length+1) []).length=_
  simpa only [List.length_nil,Nat.add_zero] using catalogue_length (transformLength bits.length+1) []

/-- The N-only output equals the SAME word-bit Fin(r*t+1) list used in the actual original graph. -/
theorem original_word_indices (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    let ell:=bitLength (bitValue bits)
    result bits (.inr false)=(SemiprimeFiniteEnumerations.fin (firstAxis ell*secondAxis ell+1)).values.foldr
      (fun i rest=>frame (List.replicate i.val true) rest) [] := by
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  change catalogue (transformLength bits.length+1) []=_
  rw [hw,←axes_product]
  exact catalogue_fin _ []

/-- The original input vertex places its word-bit slots first, at their literal numerical indices. -/
theorem input_word_slot {r t digits:ℕ} (side:Fin 2) (i:Fin (r*t)) (bit:Fin (r*t+1)) :
    ((SemiprimeMacroGraph.localSlotFinEquiv (SemiprimeMacroGraph.Vertex.input (digits:=digits) side i)) (Sum.inl bit)).val=bit.val := by
  rfl

/-- Consequently the physical catalogue is also the exact ordered word-prefix port indices
of EVERY actual input vertex; the optional source flag is not claimed as part of this block. -/
theorem original_input_word_ports (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (side:Fin 2)
    (i:Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits)))) :
    let ell:=bitLength (bitValue bits)
    result bits (.inr false)=(SemiprimeFiniteEnumerations.fin (firstAxis ell*secondAxis ell+1)).values.foldr
      (fun bit rest=>frame (List.replicate
        (((SemiprimeMacroGraph.localSlotFinEquiv
          (SemiprimeMacroGraph.Vertex.input (digits:=digitCount ell) side i)) (Sum.inl bit)).val) true) rest) [] := by
  change result bits (.inr false)=
    (SemiprimeFiniteEnumerations.fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1)).values.foldr
      (fun bit rest=>frame (List.replicate bit.val true) rest) []
  exact original_word_indices bits hc

/-- Canonical original input ties physical width to the public bitLength. -/
def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (200000*(bitLength (bitValue bits)+1)^2) := by
  have hw:=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  simpa only [hw,bitLength] using acquireInTime bits
end RiemannGaussian.SemiprimeD1StackGraphIndicesBounds
