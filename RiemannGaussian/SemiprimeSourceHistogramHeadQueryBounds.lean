/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramHeadRefinement

/-! # Logarithmic acquired-colour field bounds for actual fixed-head queries
Encoding setup still pays the original raw colour acquisition and trim. Once
cached, each actual selected row query reads compact framed fields only.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramHeadQueryBounds
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceHistogramRows SemiprimeSourceHistogramRowKeys
open SemiprimeSourceHistogramHeadRefinement
open SemiprimeSourceHistogramKeyBits

/-- Actual selected colour fields have logarithmic original-colour width. -/
theorem original_field_length (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    ∀ x∈(SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r Q) id).value,
      (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits.length ≤ Nat.clog 2 (r+1) := by
  intro x hx
  have hm : (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits ∈
      (SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r Q) id).value.map
        (fun y => (SemiprimeSourceCompactBits.trim y.numerator.magnitude).bits) :=
    List.mem_map.mpr ⟨x,hx,rfl⟩
  rw [row_fields r Q id hi] at hm
  obtain ⟨q,_,he⟩ := List.mem_map.mp hm
  rw [← he]
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (numberKey_compact _)
  rw [numberKey_value]
  have hp := Nat.le_pow_clog (by decide : 1 < (2:ℕ)) (r+1)
  have hq := (SemiprimeSourceWordBankSemantics.decode r Q id q).isLt
  omega

/-- The encoded payload size is governed by actual compact colour fields. -/
theorem layout_field_length (row : Row) (C : ℕ)
    (hc : ∀ x∈row,(SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits.length ≤ C) :
    (layout row).length ≤ row.length*(2*C+1) := by
  induction row with
  | nil => simp [layout]
  | cons x xs ih =>
    have hx := hc x (by simp)
    have ht := ih (fun y hy => hc y (List.mem_cons_of_mem x hy))
    simp only [layout,frame_length,List.length_cons]
    nlinarith

/-- Actual parsing/framing work uses compact cached fields, not raw numerator width. -/
theorem tag_field_clock (qs : List (List Bool)) (row : Row) (B C : ℕ)
    (hq : ∀ q∈qs,q.length ≤ B)
    (hc : ∀ x∈row,(SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits.length ≤ C) :
    (tag qs (layout row)).clock ≤ qs.length*(6*C+6*B+11)+4 := by
  induction qs generalizing row with
  | nil => simp [tag]
  | cons q qs ih => cases row with
    | nil => simp [tag,layout,split]
    | cons x xs =>
      have hp := split_frame (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits (layout xs)
      have ht := ih xs (fun y hy => hq y (List.mem_cons_of_mem q hy))
        (fun y hy => hc y (List.mem_cons_of_mem x hy))
      have hx := hc x (by simp)
      have hq' := hq q (by simp)
      simp only [tag,layout,hp.1,hp.2.1,hp.2.2,ite_true,pair_clock,
        split_frame_clock,List.length_cons]
      nlinarith

/-- Every returned coordinate-colour key has its actual framed compact width. -/
theorem keys_field_width (qs : List (List Bool)) (row : Row) (B C : ℕ)
    (hq : ∀ q∈qs,q.length ≤ B)
    (hc : ∀ x∈row,(SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits.length ≤ C) :
    ∀ key∈keys qs row,key.length ≤ 2*B+C+1 := by
  induction qs generalizing row with
  | nil => simp [keys]
  | cons q qs ih => cases row with
    | nil => simp [keys]
    | cons x xs =>
      intro key hk
      simp only [keys,List.zip_cons_cons,List.map_cons,List.mem_cons] at hk
      rcases hk with rfl|hk
      · have hx := hc x (by simp)
        have hq' := hq q (by simp)
        rw [frame_length]
        omega
      · exact ih xs (fun y hy => hq y (List.mem_cons_of_mem q hy))
          (fun y hy => hc y (List.mem_cons_of_mem x hy)) key hk

/-- Literal uniform budget for one dictionary read and all Q compact colour tags. -/
def rowQueryBudget (r Q : ℕ) : ℕ :=
  8*Nat.clog 2 (r^Q+1)+3*(Q*(2*Nat.clog 2 (r+1)+1))+12+
    Q*(6*Nat.clog 2 (r+1)+6*Nat.clog 2 (Q+1)+11)+8

/-- Original input data discharges the tighter actual selected-payload clock. -/
theorem readKeys_clock (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (readKeys (SemiprimeSourceHistogramRows.acquire r Q)
      (SemiprimeSourceCompactWordIds.acquire Q).value id).clock ≤ rowQueryBudget r Q := by
  have fields := original_field_length r Q id hi
  have hlen := SemiprimeSourceCompactWordBank.readRow_length r Q id hi
  have hstored := SemiprimeSourceHistogramRows.lookup_original r Q id hi
  simp only [SemiprimeSourceHistogramRows.readRow,SemiprimeSourceHistogramTrie.lookup_bits,
    encodeRow_bits] at hstored
  have hsize := layout_field_length _ (Nat.clog 2 (r+1)) fields
  rw [hlen] at hsize
  have hlookup := SemiprimeSourceHistogramTrieBounds.lookup_clock
    (SemiprimeSourceHistogramRows.acquire r Q).trie id (Q*(2*Nat.clog 2 (r+1)+1))
      (hstored ▸ hsize)
  have hid := SemiprimeSourceCompactWordBank.ids_bounded r Q id hi
  have ht := tag_field_clock (SemiprimeSourceCompactWordIds.acquire Q).value _
    (Nat.clog 2 (Q+1)) (Nat.clog 2 (r+1))
    (SemiprimeSourceCompactWordIds.acquire_bounded Q) fields
  rw [SemiprimeSourceCompactWordIds.acquire_length] at ht
  unfold readKeys rowQueryBudget
  dsimp only
  rw [SemiprimeSourceHistogramRows.lookup_original r Q id hi,encodeRow_bits]
  change (SemiprimeSourceHistogramTrie.lookup (SemiprimeSourceHistogramRows.acquire r Q).trie id).clock + _ + 4 ≤ _
  omega

/-- Actual physical key width for the fixed-head histogram. -/
def keyWidth (r Q : ℕ) : ℕ := 2*Nat.clog 2 (Q+1)+Nat.clog 2 (r+1)+1

/-- No externally supplied key-width answer is used at the original endpoint. -/
theorem readKeys_width (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    ∀ key∈(readKeys (SemiprimeSourceHistogramRows.acquire r Q)
      (SemiprimeSourceCompactWordIds.acquire Q).value id).keys,key.length ≤ keyWidth r Q := by
  rw [readKeys_original r Q id hi]
  exact keys_field_width _ _ _ _ (SemiprimeSourceCompactWordIds.acquire_bounded Q)
    (original_field_length r Q id hi)

end RiemannGaussian.SemiprimeSourceHistogramHeadQueryBounds
