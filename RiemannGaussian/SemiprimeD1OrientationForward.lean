/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationPalette

/-! # Full-slot coverage of every actually generated orientation packet
The class fields and high-index guard are derived from actual original physical
rows/index, not supplied as a desired packet key or class-coverage certificate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1OrientationForward
open SemiprimeD1OrientationBits SemiprimeD1OrientationInverse
open SemiprimeD1OrientationComplete SemiprimeD1OrientationPalette
open SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeSourceCompactBits (Compact)

/-- Erased view of acquired sorted coordinate fields, independent of padding bits. -/
noncomputable def sortedRows : List (List Bool) → List (List Bool) → List (List Bool) × List (List Bool)
  | x::xs,y::ys =>
    let here := coordinate x y []
    let rest := sortedRows xs ys
    (here.low::rest.1,here.high::rest.2)
  | _,_ => ([],[])

/-- Each actually acquired sorted field stays in the original colour palette. -/
theorem coordinate_allowed (r : ℕ) (x y : List Bool)
    (hx : Compact x ∧ bitValue x<r) (hy : Compact y ∧ bitValue y<r) :
    (Compact (coordinate x y []).low ∧ bitValue (coordinate x y []).low<r) ∧
    (Compact (coordinate x y []).high ∧ bitValue (coordinate x y []).high<r) ∧
    bitValue (coordinate x y []).low≤bitValue (coordinate x y []).high := by
  rw [(coordinate_fields x y []).1,(coordinate_fields x y []).2]
  by_cases ho : (leSignedBits ⟨false,x⟩ ⟨false,y⟩).le=true
  · simp only [ho,ite_true]
    exact ⟨hx,hy,(SemiprimeD1CounterMaximum.unsigned_order x y).mp ho⟩
  · simp only [ho,Bool.false_eq_true,ite_false]
    have hnot := (SemiprimeD1CounterMaximum.unsigned_order x y).not.mp ho
    exact ⟨hy,hx,by omega⟩

/-- Original input rows supply all canonical class/palette/length properties. -/
theorem sorted_properties (r : ℕ) (left right : List (List Bool))
    (hlen : left.length=right.length) (hl : Allowed r left) (hr : Allowed r right) :
    Canonical (sortedRows left right).1 (sortedRows left right).2 ∧
    Allowed r (sortedRows left right).1 ∧ Allowed r (sortedRows left right).2 ∧
    (sortedRows left right).1.length=left.length := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [sortedRows,Canonical,Allowed]
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨hcanon,hlo,hhi,hlength⟩ := ih ys (by simpa using hlen)
        (fun z hz => hl z (by simp [hz])) (fun z hz => hr z (by simp [hz]))
      have hp := coordinate_allowed r x y (hl x (by simp)) (hr y (by simp))
      simp only [sortedRows]
      refine ⟨⟨hp.1.1,hp.2.1.1,hp.2.2,hcanon⟩,?_,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with h|h
        · subst z;exact hp.1
        · exact hlo z h
      · intro z hz
        rcases List.mem_cons.mp hz with h|h
        · subst z;exact hp.2.1
        · exact hhi z h
      · simpa only [List.length_cons] using congrArg Nat.succ hlength

/-- Sorting does not change the already acquired equality flag. -/
theorem sorted_equality (x y : List Bool) :
    equality (leSignedBits ⟨false,(coordinate x y []).low⟩ ⟨false,(coordinate x y []).high⟩)=
      equality (leSignedBits ⟨false,x⟩ ⟨false,y⟩) := by
  apply Bool.eq_iff_iff.mpr
  rw [equality_exact,equality_exact,(coordinate_fields x y []).1,(coordinate_fields x y []).2]
  split_ifs
  · rfl
  · exact eq_comm

/-- The original count of consumed index bits agrees with the sorted class fields. -/
theorem sorted_equalCount (left right : List (List Bool)) :
    equalCount (sortedRows left right).1 (sortedRows left right).2=equalCount left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons x xs ih =>
    cases right with
    | nil => rfl
    | cons y ys => simp only [sortedRows,equalCount,sorted_equality,ih]

/-- Actual generated key is its sorted physical class fields followed by actual high bits. -/
theorem key_decomposition (left right : List (List Bool)) (j : List Bool)
    (hlen : left.length=right.length) :
    (acquire left right j).key=packetKey (sortedRows left right).1 (sortedRows left right).2
      (acquire left right j).high := by
  induction left generalizing right j with
  | nil => cases right <;> simp_all [acquire,sortedRows,packetKey,SemiprimeSourceCompactBits.copy_bits]
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      have ht := ih ys (coordinate x y j).next (by simpa using hlen)
      have hf : (coordinate x y j).field=(coordinate x y []).field := rfl
      simp only [acquire,SemiprimeSourceHistogramKeyBits.pair_bits,sortedRows,packetKey]
      rw [hf,coordinate_field,ht]

/-- Actual remaining index high bits retain original compactness. -/
theorem high_compact (left right : List (List Bool)) (j : List Bool) (hj : Compact j) :
    Compact (acquire left right j).high := by
  induction left generalizing right j with
  | nil => cases right <;> simpa only [acquire,SemiprimeSourceCompactBits.copy_bits] using hj
  | cons x xs ih =>
    cases right with
    | nil => simpa only [acquire,SemiprimeSourceCompactBits.copy_bits] using hj
    | cons y ys => exact ih ys (coordinate x y j).next (coordinate_next_compact x y j hj)

/-- A physical little-endian tail is exactly one integer right shift. -/
theorem tail_value (j : List Bool) : bitValue j.tail=bitValue j/2 := by
  cases j with
  | nil => rfl
  | cons b bs => cases b <;> simp [bitValue,bitNat]; omega

/-- Actual generated high padding is j shifted by the ACTUAL equal-coordinate count. -/
theorem high_value (left right : List (List Bool)) (j : List Bool) :
    bitValue (acquire left right j).high=bitValue j/2^(equalCount left right) := by
  induction left generalizing right j with
  | nil => cases right <;> simp [acquire,equalCount,SemiprimeSourceCompactBits.copy_bits]
  | cons x xs ih =>
    cases right with
    | nil => simp [acquire,equalCount,SemiprimeSourceCompactBits.copy_bits]
    | cons y ys =>
      change bitValue (acquire xs ys (coordinate x y j).next).high=_
      rw [ih,coordinate_next]
      by_cases he : equality (leSignedBits ⟨false,x⟩ ⟨false,y⟩)=true
      · have he' : (coordinate x y j).equal=true := he
        rw [he']
        simp only [ite_true,equalCount,he,pow_succ,tail_value,Nat.div_div_eq_div_mul]
        congr 1
        omega
      · have he' : ¬(coordinate x y j).equal=true := he
        simp only [he',Bool.false_eq_true,ite_false,equalCount,he]

/-- Every packet actually generated below Hpad has its own high index in range. -/
theorem generated_high_lt (left right : List (List Bool)) (j : List Bool) (Hpad : ℕ)
    (hdiv : 2^left.length∣Hpad) (hj : bitValue j<Hpad) :
    bitValue (acquire left right j).high<Hpad/2^(equalCount (sortedRows left right).1 (sortedRows left right).2) := by
  rw [sorted_equalCount,high_value]
  have hd : 2^(equalCount left right)∣Hpad :=
    (pow_dvd_pow 2 (equalCount_le left right)).trans hdiv
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^(equalCount left right))).mpr
  simpa only [Nat.div_mul_cancel hd] using hj

/-- Every a-slot word occurs in EVERY actually generated original-palette packet.
No desired class, high-index guard, palette witness or inverse answer is supplied. -/
theorem generated_full_slots (r a : ℕ) [NeZero r] (left right : List (List Bool))
    (j slots : List Bool) (Hpad : ℕ)
    (hlen : left.length=right.length) (ha : left.length=a)
    (hl : Allowed r left) (hr : Allowed r right) (hj : Compact j)
    (hindex : bitValue j<Hpad) (hdiv : 2^a∣Hpad) (hs : slots.length=a) :
    let out := acquire left right j
    let back := recover out.key slots
    Compact back.index ∧ bitValue back.index<Hpad ∧
      packetValue (acquire back.left back.right back.index)=(out.key,slots,out.high,true) ∧
      (∃ leftID∈(SemiprimeSourceCompactWordBank.acquire r a).ids,
        fields (SemiprimeSourceWordBankSemantics.decode r a leftID)=back.left) ∧
      (∃ rightID∈(SemiprimeSourceCompactWordBank.acquire r a).ids,
        fields (SemiprimeSourceWordBankSemantics.decode r a rightID)=back.right) := by
  obtain ⟨hc,hlo,hhi,hshape⟩ := sorted_properties r left right hlen hl hr
  have hp := high_compact left right j hj
  have hb := generated_high_lt left right j Hpad (by simpa only [ha] using hdiv) hindex
  have h := finite_palette_slots r a (sortedRows left right).1 (sortedRows left right).2
    (acquire left right j).high slots Hpad hc (hshape.trans ha) hlo hhi hp hs hdiv hb
  rw [←key_decomposition left right j hlen] at h
  exact h

end RiemannGaussian.SemiprimeD1OrientationForward
