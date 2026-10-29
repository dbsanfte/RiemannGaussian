/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Actual canonical rational to signed Boolean-word acquisition
Numerator/denominator extraction and division/remainder stages are scalar
operations here. This does not identify rational source production with a
physical-bit computation. Encoded arrays cache each actual coefficient once.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeRationalWordAcquisition
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeJetArrayHeight

/-- Physical payload and the retained scalar acquisition ledger. -/
structure WordRun where
  /-- Acquired signed numerator and positive denominator words. -/
  word : RationalWord
  /-- Actual scalar division/remainder digit stages. -/
  stages : ℕ
  /-- Scalar extraction, digit, sign and cell operations. -/
  work : ℕ

/-- Acquire both canonical integer parts without any supplied encoded answer. -/
def encode (bits : ℕ) (q : ℚ) : WordRun :=
  let numerator := SemiprimeEncodedRowSelection.encode bits q.num
  let denominator := SemiprimeEncodedRowSelection.digits (bits+1) q.den
  ⟨⟨numerator.word.numerator,denominator.bits⟩,
    numerator.stages+denominator.stages,numerator.work+denominator.work+8⟩

/-- Inclusive magnitude endpoints fit by using one extra emitted digit. -/
theorem magnitude_lt {x bits : ℕ} (h : x≤2^bits) : x<2^(bits+1) :=
  h.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- Exact executed acquisition stages and scalar/cell work. -/
theorem encode_work (bits : ℕ) (q : ℚ) :
    (encode bits q).stages=2*(bits+1) ∧ (encode bits q).work=8*(bits+1)+13 := by
  simp only [encode,SemiprimeEncodedRowSelection.encode_work,
    SemiprimeEncodedRowSelection.digits_stages,SemiprimeEncodedRowSelection.digits_work]
  omega

/-- No denominator truncation occurs under the original input denominator bound. -/
theorem encode_denominator (bits : ℕ) (q : ℚ) (hd : q.den≤2^bits) :
    bitValue (encode bits q).word.denominator=q.den :=
  SemiprimeEncodedRowSelection.digits_value (bits+1) q.den (magnitude_lt hd)

/-- Legality follows from the acquired rational's canonical positive denominator. -/
theorem encode_valid (bits : ℕ) (q : ℚ) (hd : q.den≤2^bits) :
    (encode bits q).word.Valid := by
  unfold RationalWord.Valid
  rw [encode_denominator bits q hd]
  exact q.den_pos

/-- Original canonical integer bounds imply exact decoded rational equality. -/
theorem encode_value (bits : ℕ) (q : ℚ) (hn : q.num.natAbs≤2^bits) (hd : q.den≤2^bits) :
    (encode bits q).word.value=q := by
  have hnZ : |q.num|≤(2^bits : ℕ) := by
    have h : (q.num.natAbs : ℤ)≤(2^bits : ℕ) := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using h
  have hnum := SemiprimeEncodedRowSelection.encode_value bits q.num hnZ
  have hnum' : ((SemiprimeEncodedRowSelection.encode bits q.num).word.numerator.value : ℚ)=q.num := by
    change ((SemiprimeEncodedRowSelection.encode bits q.num).word.numerator.value : ℚ)/1=q.num at hnum
    simpa only [div_one] using hnum
  change ((SemiprimeEncodedRowSelection.encode bits q.num).word.numerator.value : ℚ)/
    (bitValue (encode bits q).word.denominator : ℚ)=q
  rw [encode_denominator bits q hd,hnum']
  exact Rat.num_div_den q

/-- Both emitted magnitudes have literal fixed length bits+1. -/
theorem encode_width (bits : ℕ) (q : ℚ) : Width (encode bits q).word (bits+1) := by
  constructor
  · exact le_of_eq (SemiprimeEncodedRowSelection.digits_length _ _)
  · exact le_of_eq (SemiprimeEncodedRowSelection.digits_length _ _)

/-- A common representation, rather than an output Fits oracle, supplies all guards. -/
theorem encode_representation {q : ℚ} {d B : ℕ} (bits : ℕ) (hd : 0<d)
    (hq : Representation q d B) (hB : B≤2^bits) (hD : d≤2^bits) :
    (encode bits q).word.value=q ∧ (encode bits q).word.Valid ∧ Width (encode bits q).word (bits+1) := by
  have h := representation_reduced_bound hd hq
  exact ⟨encode_value bits q (h.2.trans hB) (h.1.trans hD),
    encode_valid bits q (h.1.trans hD),encode_width bits q⟩

/-- Materialized encoded coefficient array and retained scalar report. -/
structure ArrayRun where
  /-- Every requested coefficient has one stored physical word. -/
  words : Array RationalWord
  /-- Total actual scalar digit stages. -/
  stages : ℕ
  /-- Total coefficient reads, encoding and cache construction work. -/
  work : ℕ

/-- Encode exactly J cached input coefficients, including total zero defaults. -/
def encodeArray (bits J : ℕ) (values : Array ℚ) : ArrayRun :=
  let reports := Array.ofFn (fun k : Fin J => encode bits ((values[k.val]?).getD 0))
  ⟨reports.map WordRun.word,(reports.toList.map WordRun.stages).sum,
    (reports.toList.map WordRun.work).sum+12*J+5⟩

/-- Actual cache shape. -/
theorem encodeArray_size (bits J : ℕ) (values : Array ℚ) :
    (encodeArray bits J values).words.size=J := by simp [encodeArray]

/-- Every cached cell is the once-acquired encoding of the input coefficient. -/
theorem encodeArray_get (bits J : ℕ) (values : Array ℚ) (k : Fin J) :
    (encodeArray bits J values).words[k.val]'(by simp [encodeArray])=
      (encode bits ((values[k.val]?).getD 0)).word := by
  simp [encodeArray]

/-- Explicit fixed-polynomial encoding/cell ledger, without materializing any truth table. -/
theorem encodeArray_work (bits J : ℕ) (values : Array ℚ) :
    (encodeArray bits J values).work=J*(8*(bits+1)+13)+12*J+5 ∧
      (encodeArray bits J values).stages=J*(2*(bits+1)) := by
  simp only [encodeArray,Array.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn,encode_work]
  simp

/-- Every requested coefficient refines its original represented input. -/
theorem encodeArray_representation (bits J d B : ℕ) (values : Array ℚ)
    (hd : 0<d) (hB : B≤2^bits) (hD : d≤2^bits)
    (hvalues : ∀ k : Fin J, Representation ((values[k.val]?).getD 0) d B) (k : Fin J) :
    let w := (encodeArray bits J values).words[k.val]'(by simp [encodeArray])
    w.value=((values[k.val]?).getD 0) ∧ w.Valid ∧ Width w (bits+1) := by
  dsimp only
  rw [encodeArray_get]
  exact encode_representation bits hd (hvalues k) hB hD

/-- Decoding the complete physical cache gives exactly the requested input truncation. -/
theorem encodeArray_decode (bits J d B : ℕ) (values : Array ℚ)
    (hd : 0<d) (hB : B≤2^bits) (hD : d≤2^bits)
    (hvalues : ∀ k : Fin J, Representation ((values[k.val]?).getD 0) d B) :
    ((encodeArray bits J values).words.map RationalWord.value)=
      Array.ofFn (fun k : Fin J => (values[k.val]?).getD 0) := by
  simp only [encodeArray,Array.map_ofFn,Function.comp_def]
  congr 1
  funext k
  exact (encode_representation bits hd (hvalues k) hB hD).1

end RiemannGaussian.SemiprimeRationalWordAcquisition
