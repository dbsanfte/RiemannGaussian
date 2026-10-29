/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationInverse

/-! # Every slot has an explicit physical preimage in a canonical packet
Canonical coordinate fields are acquired compact sorted colours, not semantic
Word functions. The actual inverse reconstructs rows/index for each slot word.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1OrientationComplete
open SemiprimeD1OrientationBits SemiprimeD1OrientationInverse
open SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeSourceCompactBits (Compact)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Field choice already implemented by the physical inverse, proof specification. -/
def placeLeft (low high : List Bool) (bit : Bool) : List Bool :=
  if equality (leSignedBits ⟨false,low⟩ ⟨false,high⟩) then low else if bit then high else low

/-- Second recovered field choice, with no supplied orientation answer. -/
def placeRight (low high : List Bool) (bit : Bool) : List Bool :=
  if equality (leSignedBits ⟨false,low⟩ ⟨false,high⟩) then high else if bit then low else high

/-- Actual inverse padding update, proof specification of the computed bits. -/
def placeIndex (low high : List Bool) (bit : Bool) (j : List Bool) : List Bool :=
  if equality (leSignedBits ⟨false,low⟩ ⟨false,high⟩) then
    (SemiprimeSourceCompactBits.trim (bit::j)).bits else j

/-- Reconstructed padding is compact from the original compact tail. -/
theorem placeIndex_compact (low high : List Bool) (bit : Bool) (j : List Bool) (hj : Compact j) :
    Compact (placeIndex low high bit j) := by
  unfold placeIndex
  split_ifs
  · exact SemiprimeSourceCompactBits.trim_compact _
  · exact hj

/-- Trimming the inserted low bit preserves its exact value and compact tail. -/
theorem inserted_low (bit : Bool) (j : List Bool) (hj : Compact j) :
    (SemiprimeSourceCompactBits.trim (bit::j)).bits.headD false=bit ∧
    (SemiprimeSourceCompactBits.trim (bit::j)).bits.tail=j := by
  cases j with
  | nil => cases bit <;> simp [SemiprimeSourceCompactBits.trim]
  | cons b bs =>
    have hc : Compact (bit::b::bs) := ⟨hj,by intro h;cases h⟩
    rw [trim_eq _ hc]
    exact ⟨rfl,rfl⟩

/-- Every chosen slot bit has an actual preimage at a canonical coordinate.
Equality cases consume it from compact padding; inequality cases orient colours. -/
theorem coordinate_complete (low high : List Bool) (bit : Bool) (j : List Bool)
    (hl : Compact low) (hh : Compact high) (hle : bitValue low≤bitValue high) (hj : Compact j) :
    let here := coordinate (placeLeft low high bit) (placeRight low high bit) (placeIndex low high bit j)
    (here.field,here.slot,here.next)=(frame low high,bit,j) := by
  have ho : (leSignedBits ⟨false,low⟩ ⟨false,high⟩).le=true :=
    (SemiprimeD1CounterMaximum.unsigned_order low high).mpr hle
  by_cases he : bitValue low=bitValue high
  · have hb : low=high := SemiprimeSourceCompactWordIds.compact_value_injective low high hl hh he
    subst high
    have heq : equality (leSignedBits ⟨false,low⟩ ⟨false,low⟩)=true := (equality_exact low low).mpr rfl
    have hp := inserted_low bit j hj
    simp only [placeLeft,placeRight,placeIndex,heq,ite_true]
    simp only [coordinate,heq,ho,ite_true,SemiprimeSourceCompactBits.copy_bits,
      SemiprimeSourceHistogramKeyBits.pair_bits,hp.1,hp.2]
  · have heq : equality (leSignedBits ⟨false,low⟩ ⟨false,high⟩)=false :=
      Bool.eq_false_iff.mpr (fun h => he ((equality_exact low high).mp h))
    have hrev : (leSignedBits ⟨false,high⟩ ⟨false,low⟩).le=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have hv := (SemiprimeD1CounterMaximum.unsigned_order high low).mp h
      exact he (Nat.le_antisymm hle hv)
    have hreq : equality (leSignedBits ⟨false,high⟩ ⟨false,low⟩)=false :=
      Bool.eq_false_iff.mpr (fun h => he ((equality_exact high low).mp h).symm)
    cases bit <;>
      simp [placeLeft,placeRight,placeIndex,heq,coordinate,ho,hrev,hreq,
        SemiprimeSourceCompactBits.copy_bits,SemiprimeSourceHistogramKeyBits.pair_bits]

/-- Canonical original unordered row fields, with no alternate zero encodings. -/
def Canonical : List (List Bool) → List (List Bool) → Prop
  | [],[] => True
  | low::lows,high::highs => Compact low ∧ Compact high ∧ bitValue low≤bitValue high ∧ Canonical lows highs
  | _,_ => False

/-- Mathematical specification of the actual nested packet-key field layout. -/
def packetKey : List (List Bool) → List (List Bool) → List Bool → List Bool
  | low::lows,high::highs,j => frame (frame low high) (packetKey lows highs j)
  | _,_,j => j

/-- Non-report data returned by the actual forward packet acquisition. -/
def packetValue (out : Packet) : List Bool × List Bool × List Bool × Bool :=
  (out.key,out.slots,out.high,out.valid)

/-- Canonical fields have the same original coordinate count. -/
theorem canonical_length {lows highs : List (List Bool)} (h : Canonical lows highs) : lows.length=highs.length := by
  induction lows generalizing highs with
  | nil => cases highs <;> simp_all [Canonical]
  | cons x xs ih =>
    cases highs with
    | nil => cases h
    | cons y ys => exact congrArg Nat.succ (ih h.2.2.2)

/-- Every coordinate-length slot word is realized by the actual physical inverse.
The high padding tail is fixed; original finite Hpad bounds are attached separately. -/
theorem all_slots (lows highs : List (List Bool)) (high : List Bool) (slots : List Bool)
    (hc : Canonical lows highs) (hh : Compact high) (hs : slots.length=lows.length) :
    let back := recover (packetKey lows highs high) slots
    Compact back.index ∧ back.valid=true ∧
      packetValue (acquire back.left back.right back.index)=(packetKey lows highs high,slots,high,true) := by
  induction lows generalizing highs slots with
  | nil =>
    cases highs with
    | nil =>
      have hz : slots=[] := List.eq_nil_of_length_eq_zero hs
      subst slots
      simpa [packetKey,recover,acquire,packetValue,SemiprimeSourceCompactBits.copy_bits] using hh
    | cons y ys => cases hc
  | cons low lows ih =>
    cases highs with
    | nil => cases hc
    | cons hi highs =>
      cases slots with
      | nil => simp at hs
      | cons bit slots =>
        obtain ⟨hlo,hhi,hle,hcanon⟩ := hc
        have ht := ih highs slots hcanon (by simpa using hs)
        let key := packetKey lows highs high
        let tail := recover key slots
        obtain ⟨hindex,hvalid,hforward⟩ := ht
        have hfk : (acquire tail.left tail.right tail.index).key=key := congrArg Prod.fst hforward
        have hfs : (acquire tail.left tail.right tail.index).slots=slots := congrArg (fun z => z.2.1) hforward
        have hfh : (acquire tail.left tail.right tail.index).high=high := congrArg (fun z => z.2.2.1) hforward
        have hfv : (acquire tail.left tail.right tail.index).valid=true := congrArg (fun z => z.2.2.2) hforward
        have hdecode := recover_frame low hi key bit slots
        have hleft : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).left=
            placeLeft low hi bit::tail.left := congrArg Prod.fst hdecode
        have hright : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).right=
            placeRight low hi bit::tail.right := congrArg (fun z => z.2.1) hdecode
        have hj : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).index=
            placeIndex low hi bit tail.index := congrArg (fun z => z.2.2.1) hdecode
        have ho : (leSignedBits ⟨false,low⟩ ⟨false,hi⟩).le=true :=
          (SemiprimeD1CounterMaximum.unsigned_order low hi).mpr hle
        have hv : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).valid=true := by
          have h : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).valid=
              ((recover key slots).valid && (leSignedBits ⟨false,low⟩ ⟨false,hi⟩).le) :=
            congrArg (fun z => z.2.2.2) hdecode
          rw [ho,show (recover key slots).valid=true from hvalid] at h
          exact h
        dsimp only
        rw [hj,hleft,hright]
        refine ⟨placeIndex_compact low hi bit tail.index hindex,hv,?_⟩
        have hc := coordinate_complete low hi bit tail.index hlo hhi hle hindex
        let here := coordinate (placeLeft low hi bit) (placeRight low hi bit) (placeIndex low hi bit tail.index)
        have hfield : here.field=frame low hi := congrArg Prod.fst hc
        have hslot : here.slot=bit := congrArg (fun z => z.2.1) hc
        have hnext : here.next=tail.index := congrArg (fun z => z.2.2) hc
        simp only [packetValue,acquire]
        rw [hnext,hfield,SemiprimeSourceHistogramKeyBits.pair_bits,hfk,hfs,hfh,hfv,hslot]
        rfl

/-- Number of actual equal-coordinate padding-bit consumptions, specification only. -/
def equalCount : List (List Bool) → List (List Bool) → ℕ
  | low::lows,high::highs =>
    if equality (leSignedBits ⟨false,low⟩ ⟨false,high⟩) then equalCount lows highs+1
      else equalCount lows highs
  | _,_ => 0

/-- At most one original padding bit is consumed at each actual coordinate. -/
theorem equalCount_le (lows highs : List (List Bool)) : equalCount lows highs≤lows.length := by
  induction lows generalizing highs with
  | nil => simp [equalCount]
  | cons x xs ih =>
    cases highs with
    | nil => simp [equalCount]
    | cons y ys =>
      have ht := ih ys
      simp only [equalCount,List.length_cons]
      split_ifs <;> omega

/-- The actual inverse index stays within the complete low-bit range at fixed high tail. -/
theorem index_lt (lows highs : List (List Bool)) (high slots : List Bool)
    (hc : Canonical lows highs) (hs : slots.length=lows.length) :
    bitValue (recover (packetKey lows highs high) slots).index<
      (bitValue high+1)*2^(equalCount lows highs) := by
  induction lows generalizing highs slots with
  | nil =>
    cases highs with
    | nil =>
      have hz : slots=[] := List.eq_nil_of_length_eq_zero hs
      subst slots
      simp [packetKey,recover,SemiprimeSourceCompactBits.copy_bits,equalCount]
    | cons y ys => cases hc
  | cons low lows ih =>
    cases highs with
    | nil => cases hc
    | cons hi highs =>
      cases slots with
      | nil => simp at hs
      | cons bit slots =>
        have ht := ih highs slots hc.2.2.2 (by simpa using hs)
        have h := recover_frame low hi (packetKey lows highs high) bit slots
        have hx : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).index=
            placeIndex low hi bit (recover (packetKey lows highs high) slots).index :=
          congrArg (fun z => z.2.2.1) h
        rw [hx]
        by_cases he : equality (leSignedBits ⟨false,low⟩ ⟨false,hi⟩)=true
        · simp only [placeIndex,equalCount,he,ite_true,
            SemiprimeSourceCompactBits.trim_value,bitValue,pow_succ]
          have hb : bitNat bit≤1 := by cases bit <;> decide
          nlinarith
        · simp only [placeIndex,equalCount,he]
          exact ht

/-- Finite full-slot coverage under original dyadic Hpad divisibility.
Every actual a-bit slot reconstructs an index below Hpad; no slot catalogue or
inverse answer is supplied. Original palette/bank realization remains a separate join. -/
theorem finite_slots (lows highs : List (List Bool)) (high slots : List Bool) (Hpad : ℕ)
    (hc : Canonical lows highs) (hh : Compact high) (hs : slots.length=lows.length)
    (hdiv : 2^lows.length∣Hpad)
    (hhigh : bitValue high<Hpad/2^(equalCount lows highs)) :
    let back := recover (packetKey lows highs high) slots
    Compact back.index ∧ back.valid=true ∧ bitValue back.index<Hpad ∧
      packetValue (acquire back.left back.right back.index)=(packetKey lows highs high,slots,high,true) := by
  obtain ⟨hj,hv,hf⟩ := all_slots lows highs high slots hc hh hs
  have hp : 2^(equalCount lows highs)∣Hpad :=
    (pow_dvd_pow 2 (equalCount_le lows highs)).trans hdiv
  have hb : (bitValue high+1)*2^(equalCount lows highs)≤Hpad := by
    calc
      _ ≤ (Hpad/2^(equalCount lows highs))*2^(equalCount lows highs) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhigh)
      _ = Hpad := Nat.div_mul_cancel hp
  exact ⟨hj,hv,(index_lt lows highs high slots hc hs).trans_le hb,hf⟩

end RiemannGaussian.SemiprimeD1OrientationComplete
