/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds
import RiemannGaussian.SemiprimePaidFiniteEnumerationLists

/-! # Original-dimension physical coordinate-bank construction
Rows contain physical rational words, never closures encoding source words.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordBankRows
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeSourceScorePredicateBits SemiprimeRationalBits
open SemiprimeSourceOffsetInputsCore SemiprimeMaterializedSourceUniversal

/-- Acquire each original colour by actual Boolean increment encoding. -/
def colours (r : ℕ) : Run (List RationalWord) :=
  let indices := SemiprimePaidFiniteEnumerationLists.fin r
  let out := collect (fun i : Fin r =>
    let encoded := encodeNat i.val
    (⟨encoded.word,encoded.clock+2⟩:Run RationalWord)) indices.value
  ⟨out.value,indices.work+out.work+3⟩

/-- Copy every physical tail cell and head payload before constructing a new row. -/
def prepend (head : RationalWord) (tail : Row) : Run Row :=
  let h := SemiprimeSourceMemoryBits.copyWord head
  let t := copyRow tail
  ⟨h.word::t.value,h.clock+t.work+3⟩

/-- Actual copied row contents. -/
theorem prepend_value (head : RationalWord) (tail : Row) :
    (prepend head tail).value=head::tail := by
  simp only [prepend,SemiprimeSourceMemoryBits.copyWord_word,copyRow_value]

/-- Head-major physical coordinate lists, with cached smaller-dimensional tails. -/
def rowsWith (colours : List RationalWord) : ℕ → Run (List Row)
  | 0 => ⟨[[]],2⟩
  | q+1 =>
    let tails := rowsWith colours q
    let pairs := SemiprimePaidFiniteEnumerationLists.product colours tails.value
    let out := collect (fun p => prepend p.1 p.2) pairs.value
    ⟨out.value,tails.work+pairs.work+out.work+4⟩

/-- Original input endpoint: colour acquisition happens once before all dimensions. -/
def rows (r Q : ℕ) : Run (List Row) :=
  let cs := colours r
  let out := rowsWith cs.value Q
  ⟨out.value,cs.work+out.work+3⟩

/-- Proof-only coordinate interpretation of a finite original word. -/
def coordinates {r Q : ℕ} (w : Word r Q) : List ℚ := List.ofFn (fun i => ((w i).val:ℚ))

/-- Colour values and order come from the original ascending finite enumeration. -/
theorem colours_values (r : ℕ) :
    (colours r).value.map RationalWord.value=(List.finRange r).map (fun i => (i.val:ℚ)) := by
  simp only [colours,collect_value,List.map_map,SemiprimePaidFiniteEnumerationLists.fin_value]
  congr 1
  funext i
  exact (encodeNat_spec i.val).1

/-- Generic coordinate-list recursion, preserving actual head-major order. -/
theorem rowsWith_values (cs : List RationalWord) (q : ℕ) :
    ((rowsWith cs (q+1)).value.map (List.map RationalWord.value))=
      ((cs.map RationalWord.value).product
        ((rowsWith cs q).value.map (List.map RationalWord.value))).map (fun p => p.1::p.2) := by
  simp only [rowsWith,collect_value,SemiprimePaidFiniteEnumerationLists.product_value,List.map_map]
  simp only [List.product,List.map_flatMap,List.flatMap_map,List.map_map]
  congr 1
  funext head
  congr 1
  funext tail
  change (prepend head tail).value.map RationalWord.value = head.value::tail.map RationalWord.value
  rw [prepend_value]
  rfl

/-- Every constructed row has exactly the original dimension. -/
theorem rowsWith_length (cs : List RationalWord) (q : ℕ) :
    ∀ row∈(rowsWith cs q).value,row.length=q := by
  induction q with
  | zero => simp [rowsWith]
  | succ q ih =>
    intro row hrow
    simp only [rowsWith,collect_value,SemiprimePaidFiniteEnumerationLists.product_value,List.mem_map] at hrow
    obtain ⟨p,hp,rfl⟩ := hrow
    have ht := (List.mem_product.mp hp).2
    simp only [prepend_value,List.length_cons,ih _ ht]

end RiemannGaussian.SemiprimeSourceWordBankRows
