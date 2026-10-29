/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramRowsBounds

/-! # One-pass physical coordinate-tag keys from acquired encoded rows
Only actual split fields and acquired coordinate IDs occur in the data path.
Native rational/finite-word interpretation is used solely in theorems.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramRowKeys
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeSourceHistogramRows
open SemiprimeSourceHistogramKeyBits

/-- Physical coordinate-colour key list with all parse/frame reports retained. -/
structure Tags where
  /-- Actual compound histogram key bytes in coordinate order. -/
  keys : List (List Bool)
  /-- Actual split, copy, framing and constructor stages. -/
  clock : ℕ

/-- Parse each encoded row field once and tag it with one actual acquired ID. -/
def tag : List (List Bool) → List Bool → Tags
  | [],_ => ⟨[],1⟩
  | q::qs,encoded =>
    let field := split encoded
    if field.valid then
      let key := pair q field.first
      let tail := tag qs field.rest
      ⟨key.bits::tail.keys,field.clock+key.clock+tail.clock+5⟩
    else ⟨[],field.clock+3⟩

/-- Proof-side exact keys from actual coordinate and colour bytes. -/
def keys (qs : List (List Bool)) (row : Row) : List (List Bool) :=
  (qs.zip row).map (fun p => frame p.1
    (SemiprimeSourceCompactBits.trim p.2.numerator.magnitude).bits)

/-- Actual one-pass parser returns exactly the acquired coordinate/colour fields. -/
theorem tag_layout (qs : List (List Bool)) (row : Row) :
    (tag qs (layout row)).keys=keys qs row := by
  induction qs generalizing row with
  | nil => rfl
  | cons q qs ih =>
    cases row with
    | nil => rfl
    | cons x xs =>
      have hp := split_frame (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits
        (layout xs)
      simp only [tag,layout,hp.1,hp.2.1,hp.2.2,ite_true,pair_bits,ih,
        keys,List.zip_cons_cons,List.map_cons]

/-- Executed row bytes can be fed directly without any proof-side decoder. -/
theorem tag_encodeRow (qs : List (List Bool)) (row : Row) :
    (tag qs (encodeRow row).bits).keys=keys qs row := by
  rw [encodeRow_bits,tag_layout]

/-- Original candidate row lookup and physical parse compose without linear rereads. -/
theorem tag_original (r Q : ℕ) (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (qs : List (List Bool)) :
    (tag qs (readRow (acquire r Q) id).bits).keys =
      keys qs (SemiprimeSourceWordBank.readRow
        (SemiprimeSourceCompactWordBank.acquire r Q) id).value := by
  rw [lookup_original r Q id hi,tag_encodeRow]

/-- No coordinate tag aliases a different actual colour field or coordinate ID. -/
theorem key_eq_iff (q c q' c' : List Bool) : frame q c=frame q' c' ↔ q=q' ∧ c=c' :=
  ⟨frame_injective q c q' c',by rintro ⟨rfl,rfl⟩;rfl⟩

/-- Whole-row tagging is linear in all actual query IDs and magnitude widths. -/
theorem tag_clock (qs : List (List Bool)) (row : Row) (B C : ℕ)
    (hq : ∀ q ∈ qs, q.length ≤ B)
    (hr : ∀ x ∈ row, x.numerator.magnitude.length ≤ C) :
    (tag qs (layout row)).clock ≤ qs.length*(6*C+6*B+11)+4 := by
  induction qs generalizing row with
  | nil => simp [tag]
  | cons q qs ih =>
    cases row with
    | nil => simp [tag,layout,split]
    | cons x xs =>
      have hp := split_frame (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits
        (layout xs)
      have hc := split_frame_clock (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits
        (layout xs)
      have hx := SemiprimeSourceCompactBits.trim_length x.numerator.magnitude
      have hxl := hr x (by simp)
      have hql := hq q (by simp)
      have ht := ih xs (fun p h => hq p (List.mem_cons_of_mem q h))
        (fun p h => hr p (List.mem_cons_of_mem x h))
      simp only [tag,layout,hp.1,hp.2.1,hp.2.2,ite_true,pair_clock,List.length_cons]
      rw [hc]
      nlinarith

/-- Actual original acquired colours are unsigned integers with literal unit denominator. -/
def NaturalColour (x : RationalWord) : Prop :=
  x.numerator.negative=false ∧ bitValue x.denominator=1

private theorem colours_natural (r : ℕ) :
    ∀ x ∈ (SemiprimeSourceWordBankRows.colours r).value, NaturalColour x := by
  intro x hx
  simp only [SemiprimeSourceWordBankRows.colours,
    SemiprimeMaterializedSourceUniversal.collect_value,List.mem_map] at hx
  obtain ⟨i,_,rfl⟩ := hx
  exact ⟨rfl,rfl⟩

private theorem rowsWith_natural (cs : Row) (q : ℕ)
    (hc : ∀ x ∈ cs, NaturalColour x) :
    ∀ row ∈ (SemiprimeSourceWordBankRows.rowsWith cs q).value,
      ∀ x ∈ row, NaturalColour x := by
  induction q with
  | zero => simp [SemiprimeSourceWordBankRows.rowsWith]
  | succ q ih =>
    intro row hr x hx
    simp only [SemiprimeSourceWordBankRows.rowsWith,
      SemiprimeMaterializedSourceUniversal.collect_value,
      SemiprimePaidFiniteEnumerationLists.product_value,List.mem_map] at hr
    obtain ⟨p,hp,rfl⟩ := hr
    rw [SemiprimeSourceWordBankRows.prepend_value] at hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hc p.1 (List.mem_product.mp hp).1
    · exact ih p.2 (List.mem_product.mp hp).2 x hx

/-- No physical sign or denominator assumption is supplied at original row reads. -/
theorem original_natural (r Q : ℕ) (id : List Bool) :
    ∀ x ∈ (SemiprimeSourceWordBank.readRow
      (SemiprimeSourceCompactWordBank.acquire r Q) id).value, NaturalColour x := by
  rw [SemiprimeSourceWordBank.readRow_value]
  cases h : (SemiprimeSourceCompactWordBank.acquire r Q).rows[bitValue id]? with
  | none => simp
  | some row =>
    have hm := List.mem_of_getElem? h
    exact rowsWith_natural (SemiprimeSourceWordBankRows.colours r).value Q
      (colours_natural r) row hm

/-- Reading and trimming actual magnitude bits recovers the original colour value. -/
theorem colour_value (x : RationalWord) (hx : NaturalColour x) :
    (bitValue (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits : ℚ)=x.value := by
  simp only [SemiprimeSourceCompactBits.trim_value,RationalWord.value,
    SemiprimeBitIndexClipping.SignedWord.value,hx.1,Bool.false_eq_true,ite_false,
    hx.2,Nat.cast_one,div_one,Int.cast_natCast]

/-- Every actual encoded row colour equals the original decoded finite coordinate;
finite-word decoding occurs ONLY in this semantic theorem. -/
theorem original_colour_values (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    ((SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r Q) id).value.map
      (fun x => (bitValue (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits : ℚ)))=
      SemiprimeSourceWordBankRows.coordinates (SemiprimeSourceWordBankSemantics.decode r Q id) := by
  rw [← SemiprimeSourceCompactWordBank.readRow_coordinates r Q id hi]
  apply List.map_congr_left
  intro x hx
  exact colour_value x (original_natural r Q id x hx)

/-- One dictionary lookup and one physical all-coordinate parse. Coordinate IDs
are an internally acquired cache, not recomputed for each original vertex. -/
def readKeys (dict : Dictionary) (qs : List (List Bool)) (id : List Bool) : Tags :=
  let row := readRow dict id
  let out := tag qs row.bits
  ⟨out.keys,row.clock+out.clock+4⟩

/-- The original dictionary endpoint supplies every coordinate in one read/parse. -/
theorem readKeys_original (r Q : ℕ) (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (qs : List (List Bool)) :
    (readKeys (acquire r Q) qs id).keys =
      keys qs (SemiprimeSourceWordBank.readRow
        (SemiprimeSourceCompactWordBank.acquire r Q) id).value :=
  tag_original r Q id hi qs

/-- Exact output cardinality when the actual acquired coordinate menu is used. -/
theorem readKeys_length (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (readKeys (acquire r Q) (SemiprimeSourceCompactWordIds.acquire Q).value id).keys.length=Q := by
  rw [readKeys_original r Q id hi]
  simp only [keys,List.length_map,List.length_zip,
    SemiprimeSourceCompactWordIds.acquire_length,
    SemiprimeSourceCompactWordBank.readRow_length r Q id hi,Nat.min_self]

/-- Framing and canonical actual magnitude fields preserve colour equality exactly. -/
theorem colour_key_eq_iff (q q' : List Bool) (x y : RationalWord) :
    frame q (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits =
      frame q' (SemiprimeSourceCompactBits.trim y.numerator.magnitude).bits ↔
    q=q' ∧ bitValue x.numerator.magnitude=bitValue y.numerator.magnitude := by
  rw [key_eq_iff]
  constructor
  · rintro ⟨hq,hc⟩
    refine ⟨hq,?_⟩
    have hv := congrArg bitValue hc
    simpa only [SemiprimeSourceCompactBits.trim_value] using hv
  · rintro ⟨hq,hc⟩
    refine ⟨hq,?_⟩
    apply SemiprimeSourceCompactWordIds.compact_value_injective
      _ _ (SemiprimeSourceCompactBits.trim_compact _) (SemiprimeSourceCompactBits.trim_compact _)
    simpa only [SemiprimeSourceCompactBits.trim_value] using hc

/-- Complete read/all-coordinate query clock from original dimensions and a single
cached coordinate-ID menu, without any bank-row scan. -/
theorem readKeys_clock (r Q : ℕ) (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (readKeys (acquire r Q) (SemiprimeSourceCompactWordIds.acquire Q).value id).clock ≤
      8*Nat.clog 2 (r^Q+1)+3*(Q*(2*(r+1)+1))+12+
      Q*(6*(r+1)+6*Nat.clog 2 (Q+1)+11)+8 := by
  have hr := SemiprimeSourceHistogramRowsBounds.readRow_clock r Q id hi
  have ht := tag_clock (SemiprimeSourceCompactWordIds.acquire Q).value
    (SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r Q) id).value
    (Nat.clog 2 (Q+1)) (r+1) (SemiprimeSourceCompactWordIds.acquire_bounded Q)
    (fun x hx => (SemiprimeSourceCompactWordBank.readRow_good r Q id x hx).2.1)
  rw [SemiprimeSourceCompactWordIds.acquire_length] at ht
  unfold readKeys
  dsimp only
  rw [lookup_original r Q id hi,encodeRow_bits]
  omega

/-- Complete original physical bank/dictionary and once-acquired coordinate menu. -/
structure QueryCache where
  /-- The same actual acquired candidate bank and row dictionary. -/
  source : Cached
  /-- Actual ascending compact coordinate-ID words. -/
  coordinates : List (List Bool)
  /-- All bank, row dictionary, coordinate acquisition and constructor reports. -/
  clock : ℕ

/-- Original-dimension query preprocessing, with no externally advised rows or IDs. -/
def acquireCaches (r Q : ℕ) : QueryCache :=
  let source := acquireWithBank r Q
  let qs := SemiprimeSourceCompactWordIds.acquire Q
  ⟨source,qs.value,source.dictionary.clock+qs.work+4⟩

/-- The same original bank is retained for candidate selection and row querying. -/
theorem acquireCaches_bank (r Q : ℕ) :
    (acquireCaches r Q).source.bank=SemiprimeSourceCompactWordBank.acquire r Q := rfl

/-- The acquired row dictionary is exactly the already proved original dictionary. -/
theorem acquireCaches_dictionary (r Q : ℕ) :
    (acquireCaches r Q).source.dictionary=acquire r Q := rfl

/-- Coordinate ID acquisition occurs once before all vertex queries. -/
theorem acquireCaches_coordinates (r Q : ℕ) :
    (acquireCaches r Q).coordinates=(SemiprimeSourceCompactWordIds.acquire Q).value := rfl

/-- Combined setup retains both actual acquisitions without changing the query path. -/
theorem acquireCaches_clock (r Q : ℕ) (hr : 0 < r) :
    (acquireCaches r Q).clock ≤ SemiprimeSourceHistogramRowsBounds.budget r Q (r^Q)+
      Q*(30*(Nat.clog 2 (Q+1)+2)+20)+1+4 := by
  have hs := SemiprimeSourceHistogramRowsBounds.acquire_clock r Q hr
  have hq := SemiprimeSourceCompactWordIds.acquire_clock Q
  change (acquire r Q).clock + (SemiprimeSourceCompactWordIds.acquire Q).work+4 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add hs hq) 4

end RiemannGaussian.SemiprimeSourceHistogramRowKeys
