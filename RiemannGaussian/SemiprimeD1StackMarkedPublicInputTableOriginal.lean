/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableBounds
import RiemannGaussian.SemiprimeD1ZeroBoundaryTables
import RiemannGaussian.SemiprimeSourceHistogramPortKeys
/-! # Exact whole original marked input table and canonical root shape
The reference is proof-side old ordered materialization with the new LOCAL
nonnegative integer coefficients. Its report component is never used as a
machine clock. Every actual leaf is acquired by the fixed physical144 source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableOriginal
open SemiprimeD1StackMarkedPublicInputTable SemiprimeD1StackMarkedPublicInputTableTrace
open SemiprimeD1StackMarkedPublicInputTableExecution SemiprimeD1StackMarkedPublicInputTableBounds
open SemiprimeD1StackStaticWordTableSpec (tree leafWords tree_entry)
open SemiprimeD1TensorTables SemiprimeD1TensorTapeCodec
open SemiprimeMacroGraph SemiprimeMacroParameters SemiprimeBitArithmetic
/-- Canonical mathematical integer encoding, used ONLY in the reference table. -/
def wordOf (n : Nat) : List Bool := (SemiprimeSourceHistogramPortKeys.encodeKey n).bits
/-- Exact original ordered input arity; proof-side descriptor notation only. -/
def inputArity (N : Nat) (side : Fin 2) (i : Fin (firstAxis (bitLength N)*secondAxis (bitLength N))) : Nat :=
  arity (.input side i : Vertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
/-- Original ordered materializer at the marked LOCAL integer coefficient.
This logical reference is never invoked by the physical source. -/
noncomputable def reference (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N) :
    Table (subdividedArity v) :=
  (build (subdividedArity v) (fun raw =>
    ⟨[wordOf (SemiprimeD1PackedMomentPrecision.coefficient N hN v
      (fun j => (raw.toArray[j.val]?).getD false))],0⟩)).table
/-- Original materialization reads the exact ordered finite assignment.
This generic lemma precedes concrete descriptor/configuration instantiation. -/
theorem reference_entry (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (input : Fin (subdividedArity v) → Bool) :
    valueAt (reference N hN v) input=[wordOf (SemiprimeD1PackedMomentPrecision.coefficient N hN v input)] := by
  unfold reference
  rw [SemiprimeD1ZeroBoundaryTables.build_entry]
  have hget : (fun j : Fin (subdividedArity v) =>
      ((List.ofFn input).toArray[j.val]?).getD false)=input := by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  exact congrArg (fun f => [wordOf (SemiprimeD1PackedMomentPrecision.coefficient N hN v f)]) hget
/-- The compact source word is literally the unique canonical original integer
coefficient, on ALL finite local assignments and both original input sides. -/
theorem word_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits))))) → Bool) :
    answer bits indexWord (decide (side=1)) (List.ofFn input)=
      wordOf (SemiprimeD1PackedMomentPrecision.coefficient (bitValue bits) hN (.inl (.input side i)) input) := by
  apply SemiprimeSourceCompactWordIds.compact_value_injective
  · exact SemiprimeD1StackMarkedPublicInputCompactBounds.coefficient_compact _ _ _ _
  · exact SemiprimeSourceHistogramPortKeys.encodeKey_compact _
  · rw [show bitValue (answer bits indexWord (decide (side=1)) (List.ofFn input))=
        bitValue (SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits (List.ofFn input) indexWord (decide (side=1))) from
      SemiprimeD1StackMarkedPublicInputCompactBounds.coefficient_value _ _ _ _]
    rw [SemiprimeD1StackMarkedPublicInputMeaning.coefficient_original bits hc hN side i indexWord hi input]
    exact (SemiprimeSourceHistogramPortKeys.encodeKey_value _).symm
/-- WHOLE exact table equality in original first-port-outermost false-first order,
rather than an entrywise value or a permutation of the input ports. -/
theorem table_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val) :
    tree (answer bits indexWord (decide (side=1))) [] (inputArity (bitValue bits) side i)=
      reference (bitValue bits) hN (.inl (.input side i)) := by
  apply SemiprimeD1ZeroBoundaryTables.table_ext
  intro input
  have ht := tree_entry (answer bits indexWord (decide (side=1))) []
    (inputArity (bitValue bits) side i) input
  simp only [List.nil_append,leafWords] at ht
  exact ht.trans ((congrArg (fun w => [w]) (word_original bits hc hN side i indexWord hi input)).trans
    (reference_entry (bitValue bits) hN (.inl (.input side i)) input).symm)
/-- Actual generated words satisfy BOTH compactness and width, including
zero[], first/second sides, inactive rows and arbitrary physical assignment padding. -/
theorem tree_good (bits indexWord : List Bool) (side : Bool) (front : List Bool) (n : Nat) :
    Good ⟨[],2*bits.length⟩ (tree (answer bits indexWord side) front n) := by
  induction n generalizing front with
  | zero =>
    refine ⟨rfl,?_⟩
    intro word hw
    have he : word=answer bits indexWord side front := List.mem_singleton.mp hw
    subst word
    exact ⟨SemiprimeD1StackMarkedPublicInputCompactBounds.coefficient_compact _ _ _ _,
      SemiprimeD1StackMarkedPublicInputCompactBounds.coefficient_length _ _ _ _⟩
  | succ n ih => exact ⟨ih (front++[false]),ih (front++[true])⟩
/-- ENTIRE actual tape matches the original marked table when the physically
counted scope has the original arity; actual scope routing remains caller work. -/
theorem tape_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val) (words : List (List Bool))
    (ha : words.length=inputArity (bitValue bits) side i) :
    outputTape bits indexWord (decide (side=1)) words=
      tape (reference (bitValue bits) hN (.inl (.input side i))) := by
  unfold outputTape SemiprimeD1StackStaticWordTableExecution.outputTape
  rw [ha]
  exact congrArg (fun t => tape t) (table_original bits hc hN side i indexWord hi)
/-- The original materialized table is Good at the NEW public2ell scalar root;
old precision2 is never substituted for it. -/
theorem reference_good (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val) :
    Good ⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩
      (reference (bitValue bits) hN (.inl (.input side i))) := by
  rw [←table_original bits hc hN side i indexWord hi]
  have hh := tree_good bits indexWord (decide (side=1)) [] (inputArity (bitValue bits) side i)
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc] at hh
  exact hh
/-- SAME actual whole144 source, exact original marked bytes and Good2ell,
with its own polynomial-per-actual-assignment clock; no source result is advised. -/
theorem source_run_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val) (words : List (List Bool))
    (ha : words.length=inputArity (bitValue bits) side i) :
    ∃ t ≤ polynomial bits indexWord words,
      SemiprimeD1StackCalls.run program t (initial bits indexWord (decide (side=1)) (vectorBits words))=
        some (done bits indexWord (decide (side=1)) words) ∧
      (done bits indexWord (decide (side=1)) words).data (SemiprimeD1StackStaticWordTable.aux .output)=
        tape (reference (bitValue bits) hN (.inl (.input side i))) ∧
      Good ⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩
        (reference (bitValue bits) hN (.inl (.input side i))) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  obtain ⟨t,ht,hr⟩ := source_run_bounded bits indexWord (decide (side=1)) words hb
  exact ⟨t,ht,hr,(output_bytes _ _ _ _).trans (tape_original bits hc hN side i indexWord hi words ha),
    reference_good bits hc hN side i indexWord hi⟩
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableOriginal

