/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingBits

/-! # Exact physical class/slot colour reconstruction
Canonical compact unordered fields imply that a slot bit swaps the two recovered
colours. The actual zero-slot inverse therefore acquires the class representatives.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1ModeRoutingColours
open SemiprimeD1OrientationBits SemiprimeD1OrientationInverse
open SemiprimeD1OrientationComplete SemiprimeD1ModeRoutingBits
open SemiprimeBitArithmetic

/-- The actual zero-slot inverse reads the two literal unordered class rows. -/
theorem recover_zero (lows highs : List (List Bool)) (high : List Bool)
    (hl : lows.length=highs.length) :
    (recover (packetKey lows highs high) (List.replicate lows.length false)).left=lows ∧
    (recover (packetKey lows highs high) (List.replicate lows.length false)).right=highs := by
  induction lows generalizing highs with
  | nil =>
    cases highs with
    | nil => exact ⟨rfl,rfl⟩
    | cons h hs => simp at hl
  | cons low lows ih =>
    cases highs with
    | nil => simp at hl
    | cons hi highs =>
      have ht := ih highs (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl)
      have hf := recover_frame low hi (packetKey lows highs high) false (List.replicate lows.length false)
      have hleft := congrArg Prod.fst hf
      have hright := congrArg (fun x => x.2.1) hf
      simp only [value,Bool.false_eq_true,ite_false,ite_self] at hleft hright
      change (recover (SemiprimeSourceHistogramKeyBits.frame _ _) (false::_)).left=low::lows ∧
        (recover (SemiprimeSourceHistogramKeyBits.frame _ _) (false::_)).right=hi::highs
      exact ⟨hleft.trans (congrArg (List.cons low) ht.1),hright.trans (congrArg (List.cons hi) ht.2)⟩

/-- Canonical equal-colour fields have identical bytes, not just equal values. -/
theorem choice_colours (low high : List Bool) (bit : Bool)
    (hl : SemiprimeSourceCompactBits.Compact low) (hh : SemiprimeSourceCompactBits.Compact high) :
    placeLeft low high bit=(if bit then high else low) ∧
    placeRight low high bit=(if bit then low else high) := by
  by_cases he : equality (SemiprimeBitIndexClipping.leSignedBits ⟨false,low⟩ ⟨false,high⟩)=true
  · have hv := (equality_exact low high).mp he
    have hc := SemiprimeSourceCompactWordIds.compact_value_injective low high hl hh hv
    simp [placeLeft,placeRight,hc]
  · simp [placeLeft,placeRight,he]

/-- Exact recovered owner/factor colours at every coordinate of every slot. -/
theorem recover_colours (lows highs : List (List Bool)) (high : List Bool) (slots : List Bool)
    (hc : Canonical lows highs) (hs : slots.length=lows.length) (i : ℕ) (hi : i<lows.length) :
    ((recover (packetKey lows highs high) slots).left[i]?).getD []=
      (if (slots[i]?).getD false then (highs[i]?).getD [] else (lows[i]?).getD []) ∧
    ((recover (packetKey lows highs high) slots).right[i]?).getD []=
      (if (slots[i]?).getD false then (lows[i]?).getD [] else (highs[i]?).getD []) := by
  induction lows generalizing highs slots i with
  | nil => simp at hi
  | cons low lows ih =>
    cases highs with
    | nil => simp [Canonical] at hc
    | cons upper highs =>
      cases slots with
      | nil => simp at hs
      | cons bit slots =>
        have htail : Canonical lows highs := hc.2.2.2
        have hlen : slots.length=lows.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hs
        have hchoice := choice_colours low upper bit hc.1 hc.2.1
        have hf := recover_frame low upper (packetKey lows highs high) bit slots
        have hlr := congrArg Prod.fst hf
        have hrr := congrArg (fun x => x.2.1) hf
        change (recover _ _).left=placeLeft low upper bit::_ at hlr
        change (recover _ _).right=placeRight low upper bit::_ at hrr
        rw [hchoice.1] at hlr
        rw [hchoice.2] at hrr
        change ((recover (SemiprimeSourceHistogramKeyBits.frame _ _) (bit::slots)).left[i]?).getD []=_ ∧
          ((recover (SemiprimeSourceHistogramKeyBits.frame _ _) (bit::slots)).right[i]?).getD []=_
        rw [hlr,hrr]
        cases i with
        | zero => exact ⟨rfl,rfl⟩
        | succ i =>
          simpa only [List.getElem?_cons_succ] using ih highs slots htail hlen i (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi)

/-- Actual acquired coordinate fields are the literal class low/high bytes. -/
theorem acquire_fields (a : ℕ) (lows highs : List (List Bool)) (high : List Bool)
    (hl : lows.length=a) (hh : highs.length=a) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).low=(lows[i.val]?).getD [] ∧
    (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).high=(highs[i.val]?).getD [] := by
  have hz := recover_zero lows highs high (hl.trans hh.symm)
  rw [hl] at hz
  simp only [SemiprimeD1ModeRoutingBits.acquire,zeros_bits,hz.1,hz.2,
    SemiprimeD1ChildGraph.readCoordinate_bits]
  simp

end RiemannGaussian.SemiprimeD1ModeRoutingColours
