/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputExecution
import RiemannGaussian.SemiprimeD1PackedMomentPrecision
/-! # Exact original local marked coefficient, for every finite input row
No satisfying global assignment or unknown factor value is a premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputMeaning
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputMetadata SemiprimeD1StackMarkedPublicInputFirst
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeMacroEntryBitCheck SemiprimeD1PackedMomentDigits
namespace M
export SemiprimeD1PackedMomentPrecision (coefficient precision coefficient_fits)
end M
/-- The actual positional shift uses the TRUE radix and the actual descriptor index. -/
theorem shift_original (bits raw indexWord : List Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (i : Nat) (hi : indexWord.length=i) :
    shiftCount bits raw indexWord=
      bitLength (bitValue bits)+i*radixBits (bitLength (bitValue bits)) := by
  simp only [shiftCount,ell_word,radix_word,List.length_replicate,hi,
    SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
/-- Before fitting, every actual branch already has the exact nonnegative
integer coefficient; both inactive inputs and second-side inputs are included. -/
theorem operand_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits))))) → Bool) :
    bitValue (operand bits (List.ofFn input) indexWord (decide (side=1)))=
      M.coefficient (bitValue bits) hN (.inl (.input side i)) input := by
  let p := SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  have he : SemiprimeD1StackPublicInputMeaning.expected bits (List.ofFn input) indexWord=
      subdividedTable p (.inl (.input side i)) input :=
    (SemiprimeD1StackPublicInputMeaning.expected_original bits hc hN side i indexWord hi input).trans
      (publicBitEntry_correct (bitValue bits) hN (.input side i) input)
  have hw : bitValue (SemiprimeD1StackPublicInputMeaning.word bits (List.ofFn input))=
      readWord (p.r*p.t+1) (fun bit => input (localSlotFinEquiv (.input side i) (.inl bit))) := by
    rw [SemiprimeD1StackPublicInputMeaning.word_slots bits hc side i input,localWord_value]
    rfl
  have hs := shift_original bits (List.ofFn input) indexWord hc i.val hi
  have hp := shift_positive bits (List.ofFn input) indexWord hb
  unfold M.coefficient
  rw [←he]
  cases ha : SemiprimeD1StackPublicInputMeaning.expected bits (List.ofFn input) indexWord with
  | false =>
    simp only [operand,ha,Bool.false_eq_true,ite_false,bitValue]
  | true =>
    simp only [operand,ha,ite_true]
    fin_cases side
    · have hv := marked_value (shiftCount bits (List.ofFn input) indexWord) hp
        (SemiprimeD1StackPublicInputMeaning.word bits (List.ofFn input))
      change bitValue (marked (shiftCount bits (List.ofFn input) indexWord)
        (SemiprimeD1StackPublicInputMeaning.word bits (List.ofFn input)))=_
      rw [hv,hs,hw]
      change 1+2^(bitLength (bitValue bits)+i.val*radixBits (bitLength (bitValue bits)))*
        readWord (p.r*p.t+1) (fun bit => input (localSlotFinEquiv (.input 0 i) (.inl bit)))=
          1+2^bitLength (bitValue bits)*
            (readWord (p.r*p.t+1) (fun bit => input (localSlotFinEquiv (.input 0 i) (.inl bit)))*
              (2^radixBits (bitLength (bitValue bits)))^i.val)
      rw [pow_add,Nat.mul_comm i.val (radixBits (bitLength (bitValue bits))),pow_mul]
      ring
    · rfl
/-- Fitting loses NO coefficient information: the new root precision bound
holds for each valid LOCAL row, with no extendability or model hypothesis. -/
theorem coefficient_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits))))) → Bool) :
    bitValue (coefficient bits (List.ofFn input) indexWord (decide (side=1)))=
      M.coefficient (bitValue bits) hN (.inl (.input side i)) input := by
  have hv := operand_original bits hc hN side i indexWord hi input
  have hf := M.coefficient_fits (bitValue bits) hN (.inl (.input side i)) input
  have hw : bitValue (operand bits (List.ofFn input) indexWord (decide (side=1)))<
      2^(template bits (List.ofFn input) indexWord).length := by
    rw [hv,template_length,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
    exact hf
  exact (SemiprimeBitDivision.fitBits_value hw).trans hv
/-- Uniform literal output width is exactly the original public marked precision. -/
theorem coefficient_width (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (raw indexWord : List Bool) (side : Bool) :
    (coefficient bits raw indexWord side).length=M.precision (bitValue bits) := by
  rw [coefficient_length,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
  rfl
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputMeaning

