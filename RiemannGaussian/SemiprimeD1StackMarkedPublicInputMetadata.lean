/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputEncoding
/-! # Exact retained metadata and binary shift identities -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputMetadata
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeBitArithmetic
/-- The retained width is the actual bootstrap bit count, with unary markers. -/
theorem ell_word (bits raw indexWord : List Bool) :
    ellWord bits raw indexWord=List.replicate bits.length true := rfl
/-- The radix cache is the true original radix, rather than the signal width. -/
theorem radix_word (bits raw indexWord : List Bool) :
    radixWord bits raw indexWord=List.replicate (SemiprimeMacroParameters.radixBits bits.length) true := rfl
/-- The shared extraction template is the same actual whole signal-width word. -/
theorem modulus_word (bits raw indexWord : List Bool) :
    acquired bits raw indexWord (.inl P.modulusKey)=SemiprimeD1StackPublicInputMeaning.cached bits := rfl
/-- Reacquisition decodes exactly the same original raw word as the checker. -/
theorem extracted_word (bits raw indexWord : List Bool) :
    SemiprimeD1StackWordBlockExecution.result raw
      (acquired bits raw indexWord (.inl P.modulusKey)) =
      SemiprimeD1StackPublicInputMeaning.word bits raw := rfl
/-- The actual retained raw assignment remains the complete original word. -/
theorem raw_word (bits raw indexWord : List Bool) :
    acquired bits raw indexWord P.assignment=raw := rfl
/-- The physical query index is retained without any normalization or replacement. -/
theorem index_word (bits raw indexWord : List Bool) :
    acquired bits raw indexWord P.index=indexWord := rfl
/-- The verdict inspected by the caller is the actual completed checker output. -/
theorem verdict_word (bits raw indexWord : List Bool) :
    acquired bits raw indexWord P.output=
      [SemiprimeD1StackPublicInputMeaning.expected bits raw indexWord] := rfl
/-- Two physical copies, rather than a supplied precision operand, give2ell cells. -/
theorem template_length (bits raw indexWord : List Bool) :
    (template bits raw indexWord).length=2*bits.length := by
  simp only [template,ell_word,List.length_append,List.length_replicate]
  omega
/-- Every branch has exactly the same full coefficient width. -/
theorem coefficient_length (bits raw indexWord : List Bool) (side : Bool) :
    (coefficient bits raw indexWord side).length=2*bits.length := by
  rw [coefficient,SemiprimeD1StackWordFitExecution.result_length,template_length]
/-- Canonical positive input supplies a physically positive shift before the
literal low-false pop/true push. No positivity answer is a runtime operand. -/
theorem shift_positive (bits raw indexWord : List Bool) (hb : bits≠[]) :
    0 < (ellWord bits raw indexWord).length+
      indexWord.length*(radixWord bits raw indexWord).length := by
  rw [ell_word,List.length_replicate]
  have hn : 0<bits.length := by
    have hz : bits.length≠0 := by intro hz; exact hb (List.length_eq_zero_iff.mp hz)
    omega
  omega
/-- Each physical false prepend shifts a binary word, including all padding. -/
theorem shift_value (n : Nat) (word : List Bool) :
    bitValue (List.replicate n false++word)=2^n*bitValue word := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,bitValue,bitNat,
      Bool.false_eq_true,ite_false,Nat.zero_add,ih,pow_succ]
    ring
/-- Changing the genuinely low false bit to true is exactly addition of one. -/
theorem marked_value (n : Nat) (hn : 0<n) (word : List Bool) :
    bitValue (marked n word)=1+2^n*bitValue word := by
  unfold marked
  change 1+2*bitValue (List.replicate (n-1) false++word)=_
  rw [shift_value]
  have he : n-1+1=n := by omega
  rw [←Nat.mul_assoc,show 2*2^(n-1)=(2:Nat)^n by rw [←pow_succ',he]]
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputMetadata

