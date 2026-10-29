/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationBits

/-! # Actual colour-row scan and framing report bounds
Only original input field lengths appear; execution accepts no width template,
intermediate Fits, semantic colour, comparison answer or packet-key advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1OrientationBounds
open SemiprimeD1OrientationBits SemiprimeBitIndexClipping
open SemiprimeSourceHistogramKeyBits (frame)

/-- Copied low/high fields inherit actual original input lengths. -/
theorem coordinate_lengths (left right j : List Bool) (B : ℕ)
    (hl : left.length≤B) (hr : right.length≤B) :
    (coordinate left right j).low.length≤B ∧ (coordinate left right j).high.length≤B := by
  rw [(coordinate_fields left right j).1,(coordinate_fields left right j).2]
  split_ifs <;> exact ⟨by assumption,by assumption⟩

/-- The actual acquired unordered field has derived linear payload size. -/
theorem coordinate_field_length (left right j : List Bool) (B : ℕ)
    (hl : left.length≤B) (hr : right.length≤B) :
    (coordinate left right j).field.length≤3*B+1 := by
  have hc := coordinate_lengths left right j B hl hr
  rw [coordinate_field,SemiprimeSourceHistogramKeyBits.frame_length]
  omega

/-- Both borrows, full zero scans, original field copies and framing are retained. -/
theorem coordinate_clock (left right j : List Bool) (B : ℕ)
    (hl : left.length≤B) (hr : right.length≤B) :
    (coordinate left right j).clock≤80*(B+1) := by
  have ho := leSignedBits_cost (left:=⟨false,left⟩) (right:=⟨false,right⟩) hl hr
  have ha : (if (leSignedBits ⟨false,left⟩ ⟨false,right⟩).le then left else right).length≤B := by
    split_ifs <;> assumption
  have hb : (if (leSignedBits ⟨false,left⟩ ⟨false,right⟩).le then right else left).length≤B := by
    split_ifs <;> assumption
  simp only [coordinate,SemiprimeSourceCompactBits.copy_clock,SemiprimeSourceCompactBits.copy_bits,
    SemiprimeSourceHistogramKeyBits.pair_clock]
  omega

/-- Actual padding is only retained or consumed by one low bit. -/
theorem coordinate_next_length (left right j : List Bool) :
    (coordinate left right j).next.length≤j.length := by
  rw [coordinate_next]
  split_ifs
  · simp only [List.length_tail];omega
  · exact le_rfl

/-- Full executed key/slot acquisition has linear retained primitive/list work.
This does not assert a complete address/tape or external row-acquisition clock. -/
theorem acquire_clock (left right : List (List Bool)) (j : List Bool) (B : ℕ)
    (hl : ∀x∈left,x.length≤B) (hr : ∀y∈right,y.length≤B) :
    (acquire left right j).clock≤100*left.length*(B+1)+3*j.length+4 := by
  induction left generalizing right j with
  | nil => cases right <;> simp [acquire,SemiprimeSourceCompactBits.copy_clock]
  | cons x xs ih =>
    cases right with
    | nil => simp only [acquire,SemiprimeSourceCompactBits.copy_clock,List.length_cons];omega
    | cons y ys =>
      have hx := hl x (by simp)
      have hy := hr y (by simp)
      have hc := coordinate_clock x y j B hx hy
      have hf := coordinate_field_length x y j B hx hy
      have hn := coordinate_next_length x y j
      have ht := ih ys (coordinate x y j).next
        (fun z hz => hl z (by simp [hz])) (fun z hz => hr z (by simp [hz]))
      simp only [acquire,SemiprimeSourceHistogramKeyBits.pair_clock,List.length_cons]
      nlinarith

/-- Every coordinate contributes only its framed acquired colour fields. -/
theorem acquire_key_length (left right : List (List Bool)) (j : List Bool) (B : ℕ)
    (hl : ∀x∈left,x.length≤B) (hr : ∀y∈right,y.length≤B) :
    (acquire left right j).key.length≤left.length*(6*B+3)+j.length := by
  induction left generalizing right j with
  | nil => cases right <;> simp [acquire,SemiprimeSourceCompactBits.copy_bits]
  | cons x xs ih =>
    cases right with
    | nil => simp only [acquire,SemiprimeSourceCompactBits.copy_bits,List.length_cons];omega
    | cons y ys =>
      have hf := coordinate_field_length x y j B (hl x (by simp)) (hr y (by simp))
      have hn := coordinate_next_length x y j
      have ht := ih ys (coordinate x y j).next
        (fun z hz => hl z (by simp [hz])) (fun z hz => hr z (by simp [hz]))
      simp only [acquire,SemiprimeSourceHistogramKeyBits.pair_bits,
        SemiprimeSourceHistogramKeyBits.frame_length,List.length_cons]
      nlinarith

end RiemannGaussian.SemiprimeD1OrientationBounds
