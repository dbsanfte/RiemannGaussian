/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationComplete
import RiemannGaussian.SemiprimeSourceHistogramHeadRefinement

/-! # Actual finite palette coverage for physical orientation preimages
Semantic Word functions occur only in erased coverage proofs. The executed
forward/inverse row and padding paths remain entirely Boolean-list operations.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1OrientationPalette
open SemiprimeD1OrientationBits SemiprimeD1OrientationInverse SemiprimeD1OrientationComplete
open SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact)
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Mathematical canonical fields of an original palette word, proof use only. -/
def fields {r a : ℕ} (word : Word r a) : List (List Bool) :=
  List.ofFn fun q => SemiprimeSourceHistogramHeadRefinement.numberKey (word q).val

/-- Exactly the original finite colour palette, with no alternate zero bytes. -/
def Allowed (r : ℕ) (rows : List (List Bool)) : Prop :=
  ∀c∈rows,Compact c ∧ bitValue c<r

/-- Every bounded compact physical row is realized by an ACTUALLY acquired ID.
No supplied palette catalogue or coverage premise is accepted. -/
theorem palette_complete (r a : ℕ) [NeZero r] (rows : List (List Bool))
    (hlen : rows.length=a) (hrows : Allowed r rows) :
    ∃ id∈(SemiprimeSourceCompactWordBank.acquire r a).ids,
      fields (SemiprimeSourceWordBankSemantics.decode r a id)=rows := by
  let word : Word r a := fun q =>
    ⟨bitValue (rows[q.val]'(by omega)),(hrows _ (List.getElem_mem (by omega))).2⟩
  have hm := (SemiprimeFiniteEnumerations.words r a).complete word
  rw [←SemiprimeSourceCompactWordBank.ids_decode r a] at hm
  obtain ⟨id,hid,hdecode⟩ := List.mem_map.mp hm
  refine ⟨id,hid,?_⟩
  rw [hdecode]
  apply List.ext_getElem
  · simp only [fields,List.length_ofFn,hlen]
  · intro i hi hj
    simp only [fields,List.getElem_ofFn]
    apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
      (SemiprimeSourceHistogramHeadRefinement.numberKey_compact _) (hrows _ (List.getElem_mem hj)).1
    rw [SemiprimeSourceHistogramHeadRefinement.numberKey_value]

/-- Actual inverse field choices never leave their two acquired original colours. -/
theorem place_allowed (r : ℕ) (low high : List Bool) (bit : Bool)
    (hl : Compact low ∧ bitValue low<r) (hh : Compact high ∧ bitValue high<r) :
    (Compact (placeLeft low high bit) ∧ bitValue (placeLeft low high bit)<r) ∧
    (Compact (placeRight low high bit) ∧ bitValue (placeRight low high bit)<r) := by
  unfold placeLeft placeRight
  split_ifs <;> exact ⟨by assumption,by assumption⟩

/-- Recovered physical rows remain in the original finite colour alphabet. -/
theorem recover_allowed (r : ℕ) (lows highs : List (List Bool)) (high slots : List Bool)
    (hlen : lows.length=highs.length) (hs : slots.length=lows.length)
    (hl : Allowed r lows) (hh : Allowed r highs) :
    let out := recover (packetKey lows highs high) slots
    Allowed r out.left ∧ Allowed r out.right := by
  induction lows generalizing highs slots with
  | nil =>
    have hz : highs=[] := List.eq_nil_of_length_eq_zero (show highs.length=0 from hlen.symm)
    have hs' : slots=[] := List.eq_nil_of_length_eq_zero hs
    subst highs
    subst slots
    simp [packetKey,recover,Allowed]
  | cons low lows ih =>
    cases highs with
    | nil => simp at hlen
    | cons hi highs =>
      cases slots with
      | nil => simp at hs
      | cons bit slots =>
        have ht := ih highs slots (by simpa using hlen) (by simpa using hs)
          (fun c hc => hl c (by simp [hc])) (fun c hc => hh c (by simp [hc]))
        have hp := place_allowed r low hi bit (hl low (by simp)) (hh hi (by simp))
        have hd := recover_frame low hi (packetKey lows highs high) bit slots
        have hleft : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).left=
            placeLeft low hi bit::(recover (packetKey lows highs high) slots).left :=
          congrArg Prod.fst hd
        have hright : (recover (packetKey (low::lows) (hi::highs) high) (bit::slots)).right=
            placeRight low hi bit::(recover (packetKey lows highs high) slots).right :=
          congrArg (fun z => z.2.1) hd
        dsimp only
        rw [hleft,hright]
        constructor
        · intro c hc
          rcases List.mem_cons.mp hc with h|h
          · subst c;exact hp.1
          · exact ht.1 c h
        · intro c hc
          rcases List.mem_cons.mp hc with h|h
          · subst c;exact hp.2
          · exact ht.2 c h

/-- Every finite slot preimage is realized by two actual palette IDs and j<Hpad.
The returned bytes/index are computed by recover; IDs are erased coverage witnesses,
not a runtime NativeWord or a reverse-dictionary oracle. -/
theorem finite_palette_slots (r a : ℕ) [NeZero r] (lows highs : List (List Bool))
    (high slots : List Bool) (Hpad : ℕ)
    (hc : Canonical lows highs) (hlen : lows.length=a)
    (hl : Allowed r lows) (hr : Allowed r highs) (hh : Compact high)
    (hs : slots.length=a) (hdiv : 2^a∣Hpad)
    (hhigh : bitValue high<Hpad/2^(equalCount lows highs)) :
    let back := recover (packetKey lows highs high) slots
    Compact back.index ∧ bitValue back.index<Hpad ∧
      packetValue (acquire back.left back.right back.index)=(packetKey lows highs high,slots,high,true) ∧
      (∃ leftID∈(SemiprimeSourceCompactWordBank.acquire r a).ids,
        fields (SemiprimeSourceWordBankSemantics.decode r a leftID)=back.left) ∧
      (∃ rightID∈(SemiprimeSourceCompactWordBank.acquire r a).ids,
        fields (SemiprimeSourceWordBankSemantics.decode r a rightID)=back.right) := by
  let back := recover (packetKey lows highs high) slots
  have hs' : slots.length=lows.length := hs.trans hlen.symm
  obtain ⟨hj,hv,hbound,hforward⟩ := finite_slots lows highs high slots Hpad hc hh hs'
    (by simpa only [hlen] using hdiv) hhigh
  have hallowed := recover_allowed r lows highs high slots (canonical_length hc) hs' hl hr
  have hfvalid : (acquire back.left back.right back.index).valid=true := congrArg (fun z => z.2.2.2) hforward
  have hflength := (acquire_valid back.left back.right back.index).mp hfvalid
  have hfl := acquire_slots_length back.left back.right back.index hflength
  have hfslots : (acquire back.left back.right back.index).slots=slots := congrArg (fun z => z.2.1) hforward
  rw [hfslots,hs] at hfl
  refine ⟨hj,hbound,hforward,palette_complete r a back.left hfl.symm hallowed.1,?_⟩
  exact palette_complete r a back.right (hflength.symm.trans hfl.symm) hallowed.2

end RiemannGaussian.SemiprimeD1OrientationPalette
