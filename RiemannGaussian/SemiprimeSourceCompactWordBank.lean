/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeSourceWordBankIndexed
import RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget

/-! # Original physical coordinate bank with directly acquired compact IDs
The old padded ascending ID constructor never occurs in the runtime path.
The established canonical decoder occurs only in semantic theorems.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceCompactWordBank
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceWordBankSemantics (decode rows_length)

/-- Acquire actual rows once and directly acquire compact IDs for their actual count. -/
def acquire (r Q : ℕ) : SemiprimeSourceWordBank.Bank :=
  let table := SemiprimeSourceWordBankRows.rows r Q
  let ids := SemiprimeSourceCompactWordIds.acquire table.value.length
  ⟨table.value,ids.value,table.work+ids.work+table.value.length+4⟩

/-- New and old banks have the same physical rows; this is a proof-side equality. -/
theorem rows_eq (r Q : ℕ) : (acquire r Q).rows=(SemiprimeSourceWordBank.acquire r Q).rows := rfl

/-- Actual row count is the original complete function-alphabet cardinality. -/
theorem acquire_length (r Q : ℕ) : (acquire r Q).rows.length=r^Q := rows_length r Q

/-- Direct compact IDs cover exactly the original ascending row range. -/
theorem ids_values (r Q : ℕ) :
    (acquire r Q).ids.map bitValue=List.range (r^Q) := by
  simp only [acquire,SemiprimeSourceCompactWordIds.acquire_values,rows_length]

/-- Each actually acquired ID has logarithmic width rather than linear padding. -/
theorem ids_bounded (r Q : ℕ) : ∀ id∈(acquire r Q).ids,id.length ≤ Nat.clog 2 (r^Q+1) := by
  intro id hi
  exact (SemiprimeSourceCompactWordIds.acquire_bounded _ id hi).trans (by rw [rows_length])

/-- All acquired IDs are intrinsically canonical physical counter words. -/
theorem ids_compact (r Q : ℕ) :
    ∀ id∈(acquire r Q).ids,SemiprimeSourceCompactBits.Compact id :=
  SemiprimeSourceCompactWordIds.acquire_compact _

/-- No physical candidate ID is duplicated. -/
theorem ids_nodup (r Q : ℕ) : (acquire r Q).ids.Nodup :=
  SemiprimeSourceCompactWordIds.acquire_nodup _

/-- Acquired IDs and rows have the same actual cardinality. -/
theorem ids_length (r Q : ℕ) : (acquire r Q).ids.length=(acquire r Q).rows.length :=
  SemiprimeSourceCompactWordIds.acquire_length _

/-- Every actual new ID is numerically in the physical row range. -/
theorem id_lt (r Q : ℕ) (id : List Bool) (hi : id∈(acquire r Q).ids) : bitValue id<r^Q := by
  have h : bitValue id∈(acquire r Q).ids.map bitValue := List.mem_map.mpr ⟨id,hi,rfl⟩
  rw [ids_values] at h
  exact List.mem_range.mp h

/-- New IDs decode to exactly the original canonical words in their original order. -/
theorem ids_decode (r Q : ℕ) [NeZero r] :
    (acquire r Q).ids.map (decode r Q)=(SemiprimeFiniteEnumerations.words r Q).values := by
  have h := congrArg (List.map (fun i =>
    ((SemiprimeFiniteEnumerations.words r Q).values[i]?).getD (fun _ => 0))) (ids_values r Q)
  simp only [List.map_map] at h
  change (acquire r Q).ids.map (decode r Q)=_ at h
  rw [← SemiprimeFiniteEnumerations.words_length r Q] at h
  exact h.trans (SemiprimeSourceWordBankSemantics.map_range_lookup _ _)

/-- Exact original indexed zero-first/filter-tail candidate menu, not a permutation. -/
theorem ids_indexed (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (acquire r Q).ids.map (decode r Q)=
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst::
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail := by
  rw [ids_decode]
  exact (SemiprimeSourceWordMenuOrder.indexed_menu n F r Q arity).symm

/-- Numeric/word equality implies physical-ID equality inside the actual new menu. -/
theorem decode_injective (r Q : ℕ) [NeZero r] :
    Set.InjOn (decode r Q) {id | id∈(acquire r Q).ids} := by
  apply List.inj_on_of_nodup_map
  rw [ids_decode]
  exact (SemiprimeFiniteEnumerations.words r Q).nodup

/-- Literal compact zero is the first acquired physical candidate. -/
theorem default_head (r Q : ℕ) [NeZero r] :
    (acquire r Q).ids=[]::(acquire r Q).ids.tail := by
  apply SemiprimeSourceCompactWordIds.acquire_head
  rw [rows_length]
  exact pow_pos (NeZero.pos r) Q

/-- Literal default zero belongs to the actual bank. -/
theorem default_mem (r Q : ℕ) [NeZero r] : []∈(acquire r Q).ids := by
  rw [default_head]
  exact List.mem_cons_self

/-- The actual compact default has the original zero-first decoded value. -/
theorem decode_default (r Q : ℕ) [NeZero r] : decode r Q []=(fun _ => 0) :=
  SemiprimeSourceWordBankIndexed.decode_default r Q

/-- The actual candidate list is nonempty, including Q=0. -/
theorem ids_nonempty (r Q : ℕ) [NeZero r] : (acquire r Q).ids≠[] := by
  intro h
  have hm := default_mem r Q
  rw [h] at hm
  exact List.not_mem_nil hm

/-- Identical physical rows give identical reader reports for the SAME input bits.
This does not equate differently padded-ID clocks or bank acquisition work. -/
theorem readRow_eq (r Q : ℕ) (id : List Bool) :
    SemiprimeSourceWordBank.readRow (acquire r Q) id=
      SemiprimeSourceWordBank.readRow (SemiprimeSourceWordBank.acquire r Q) id := rfl

/-- Valid new IDs read their exact original decoded coordinate rows. -/
theorem readRow_coordinates (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(acquire r Q).ids) :
    (SemiprimeSourceWordBank.readRow (acquire r Q) id).value.map RationalWord.value=
      SemiprimeSourceWordBankRows.coordinates (decode r Q id) := by
  have hn := id_lt r Q id hi
  have hr : bitValue id<(SemiprimeSourceWordBankRows.rows r Q).value.length := by
    simpa only [rows_length] using hn
  have hc : bitValue id<(SemiprimeFiniteEnumerations.words r Q).values.length := by
    simpa only [SemiprimeFiniteEnumerations.words_length] using hn
  have h := congrArg (fun rs : List (List ℚ) => (rs[bitValue id]?).getD [])
    (SemiprimeSourceWordBankSemantics.rows_values r Q)
  rw [SemiprimeSourceWordBank.readRow_value]
  change (((SemiprimeSourceWordBankRows.rows r Q).value[bitValue id]?).getD []).map RationalWord.value=_
  simp only [List.getElem?_map,List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hc,
    Option.map_some,Option.getD_some] at h
  simpa only [decode,List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hc,Option.getD_some] using h

/-- Every returned row payload is valid with original r-derived physical width. -/
theorem readRow_good (r Q : ℕ) (id : List Bool) :
    ∀ x∈(SemiprimeSourceWordBank.readRow (acquire r Q) id).value,x.Valid ∧ Width x (r+1) := by
  rw [readRow_eq]
  exact SemiprimeSourceWordBankBounds.readRow_good r Q id

/-- Valid candidate coordinate count is exactly Q. -/
theorem readRow_length (r Q : ℕ) [NeZero r] (id : List Bool) (hi : id∈(acquire r Q).ids) :
    (SemiprimeSourceWordBank.readRow (acquire r Q) id).value.length=Q := by
  have h := congrArg List.length (readRow_coordinates r Q id hi)
  simpa only [List.length_map,SemiprimeSourceWordBankRows.coordinates,List.length_ofFn] using h

/-- Actual row-reader clock uses the NEW logarithmic address payload width.
The row scan remains explicit; this is not a constant-time lookup assertion. -/
theorem readRow_clock (r Q : ℕ) (id : List Bool) (hi : id∈(acquire r Q).ids) :
    (SemiprimeSourceWordBank.readRow (acquire r Q) id).work ≤
      (r^Q+1)*(SemiprimeSourceScorePredicateBitsBounds.copyBudget (r+1) Q+
        15*(Nat.clog 2 (r^Q+1)+1)+30) := by
  rw [readRow_eq]
  apply SemiprimeSourceWordBankBounds.readRow_clock r Q id
    (Nat.clog 2 (r^Q+1)+1) (by omega)
  exact (ids_bounded r Q id hi).trans (by omega)

/-- Original bank setup with linear-count/logarithmic-ID cost, no padded old IDs. -/
def budget (r Q L : ℕ) : ℕ :=
  SemiprimeSourceWordBankAcquisitionBudget.colourBudget r+2+
    Q*SemiprimeSourceWordBankAcquisitionBudget.rowStage r Q L+3+
    L*SemiprimeSourceCompactWordIds.stepBudget L+1+L+4

/-- Actual bank acquisition pays rows and direct compact IDs from original dimensions. -/
theorem acquire_clock (r Q : ℕ) (hr : 0<r) : (acquire r Q).clock ≤ budget r Q (r^Q) := by
  have hc := SemiprimeSourceWordBankAcquisitionBudget.colours_clock r
  have hrows := SemiprimeSourceWordBankAcquisitionBudget.rowsWith_clock r Q hr Q le_rfl
  have hi := SemiprimeSourceCompactWordIds.acquire_clock
    (SemiprimeSourceWordBankRows.rows r Q).value.length
  rw [rows_length] at hi
  unfold acquire budget
  dsimp only
  have hlen := rows_length r Q
  dsimp only [SemiprimeSourceWordBankRows.rows] at hlen
  dsimp only [SemiprimeSourceWordBankRows.rows]
  rw [hlen]
  omega

end RiemannGaussian.SemiprimeSourceCompactWordBank
