/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowSelectionBits

/-! # Original integer rows to the actual physical selector

Integer digit extraction executes explicitly and is reported separately from
physical rational-word arithmetic. No encoded matrix or template is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeEncodedRowSelection
open scoped BigOperators
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeMaterializedSelectionTemporaries
open SemiprimeRowSelectionExecution (originalRow selectedIndices)

/-- Paid original integer access. The caller retains responsibility for its
actual cached-read implementation and representation cost. -/
structure IntRun where
  /-- The actually acquired original integer. -/
  value : ℤ
  /-- Retained source-access work. -/
  work : ℕ

/-- Executed fixed-length scalar digit extraction. -/
structure DigitsRun where
  /-- The actual little-endian output bits. -/
  bits : List Bool
  /-- Actual successive division/remainder digit stages. -/
  stages : ℕ
  /-- Scalar digit operations and bit-cell/list construction ledger. -/
  work : ℕ

/-- The data path performs actual remainder/division by two at every digit;
it does not call a mathematical bit-value inverse or receive the answer. -/
def digits : ℕ → ℕ → DigitsRun
  | 0,_ => ⟨[],0,1⟩
  | width+1,value =>
      let next := digits width (value/2)
      ⟨decide (value%2=1)::next.bits,next.stages+1,next.work+4⟩

/-- Every requested digit cell is allocated, including high zero padding. -/
theorem digits_length (width value : ℕ) : (digits width value).bits.length=width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [digits,ih]

/-- Exactly width scalar digit stages execute. -/
theorem digits_stages (width value : ℕ) : (digits width value).stages=width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [digits,ih]

/-- Scalar digit/cell work is acquired from the actual recursive program. -/
theorem digits_work (width value : ℕ) : (digits width value).work=4*width+1 := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [digits,ih]; omega

/-- The actual remainder Boolean has the exact low-bit natural meaning. -/
theorem remainder_bit (value : ℕ) : bitNat (decide (value%2=1))=value%2 := by
  have h := Nat.mod_lt value (by decide : 0<2)
  by_cases he : value%2=1
  · simp [bitNat,he]
  · have hz : value%2=0 := by omega
    simp [bitNat,hz]

/-- All ORIGINAL values below the acquired width are represented exactly. -/
theorem digits_value (width value : ℕ) (hv : value<2^width) :
    bitValue (digits width value).bits=value := by
  induction width generalizing value with
  | zero =>
    have hz : value=0 := by simpa using hv
    subst value
    rfl
  | succ width ih =>
    have hd : value/2<2^width := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      simpa only [pow_succ] using hv
    simp only [digits,bitValue,remainder_bit,ih _ hd]
    omega

/-- Physical rational word emitted from one acquired original integer. -/
structure IntegerWordRun where
  /-- Signed magnitude with literal denominator one. -/
  word : RationalWord
  /-- Number of scalar digit extraction stages. -/
  stages : ℕ
  /-- Scalar digit/sign/cell construction work, NOT a literal integer TM clock. -/
  work : ℕ

/-- Encode bits+1 digits so the allowed endpoint |z|=2^bits is retained. -/
def encode (bits : ℕ) (z : ℤ) : IntegerWordRun :=
  let magnitude := digits (bits+1) z.natAbs
  ⟨⟨⟨decide (z<0),magnitude.bits⟩,[true]⟩,magnitude.stages,magnitude.work+3⟩

/-- The acquired scalar encoder reports its actual finite work and stage count. -/
theorem encode_work (bits : ℕ) (z : ℤ) :
    (encode bits z).work=4*(bits+1)+4 ∧ (encode bits z).stages=bits+1 := by
  constructor
  · change (digits (bits+1) z.natAbs).work+3=4*(bits+1)+4
    rw [digits_work]
  · exact digits_stages _ _

/-- Denominator one makes every emitted word legal, without a fit oracle. -/
theorem encode_valid (bits : ℕ) (z : ℤ) : (encode bits z).word.Valid := by
  change 0<1
  decide

/-- The emitted signed physical word equals the ORIGINAL integer exactly. -/
theorem encode_value (bits : ℕ) (z : ℤ) (hz : |z| ≤ (2^bits : ℕ)) :
    (encode bits z).word.value=(z : ℚ) := by
  have hb : z.natAbs<2^(bits+1) := by
    have h : z.natAbs ≤ 2^bits := by
      exact_mod_cast (show (z.natAbs : ℤ) ≤ (2^bits : ℕ) by simpa only [Int.natCast_natAbs] using hz)
    exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have he := digits_value (bits+1) z.natAbs hb
  have hs : (encode bits z).word.numerator.value=z := by
    change (if decide (z<0)=true then -((bitValue (digits (bits+1) z.natAbs).bits : ℕ) : ℤ)
      else ((bitValue (digits (bits+1) z.natAbs).bits : ℕ) : ℤ))=z
    rw [he,Int.natCast_natAbs]
    by_cases h : z<0
    · simp [h,abs_of_neg h]
    · simp [h,abs_of_nonneg (by omega : 0 ≤ z)]
  change ((encode bits z).word.numerator.value : ℚ)/1=(z : ℚ)
  rw [hs,div_one]

/-- Initial physical padding fits the selector's DERIVED polynomial width. -/
theorem encode_width (n bits : ℕ) (z : ℤ) :
    Width (encode bits z).word (selectorWidth n bits) := by
  have h : bits+1 ≤ selectorWidth n bits := by
    unfold selectorWidth leafBits
    omega
  constructor
  · change (digits (bits+1) z.natAbs).bits.length ≤ selectorWidth n bits
    rw [digits_length]
    exact h
  · change 1 ≤ selectorWidth n bits
    omega

/-- One retained original-cell access and actual scalar encoding. -/
structure CellRun where
  /-- Actual encoded word payload. -/
  word : RationalWord
  /-- The SAME acquired original integer, retained for later selected rows. -/
  original : ℤ
  /-- Number of original source accesses. -/
  calls : ℕ
  /-- Work returned by the source read. -/
  sourceWork : ℕ
  /-- Actual digit/sign/cell work. -/
  digitWork : ℕ

/-- The source callback is evaluated once before encoding and its report cached. -/
def acquireCell (source : IntRun) (bits : ℕ) : CellRun :=
  let encoded := encode bits source.value
  ⟨encoded.word,source.value,1,source.work,encoded.work⟩

/-- Complete acquired physical input matrix with separated work categories. -/
structure MatrixRun where
  /-- Cached original word rows. -/
  words : List (List RationalWord)
  /-- Original integers from the SAME acquired cell reports. -/
  integers : List (List ℤ)
  /-- Exactly one callback per original coefficient. -/
  sourceCalls : ℕ
  /-- Retained original read costs. -/
  sourceWork : ℕ
  /-- Retained actual scalar digit extraction costs. -/
  digitWork : ℕ
  /-- Finite cache allocation/map/fold control allowance. -/
  cacheWork : ℕ

/-- Materialize every report ONCE, then form all physical rows and work totals. -/
def acquire {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) : MatrixRun :=
  let reports := List.ofFn (fun j : Fin m => List.ofFn (fun v : Fin n => acquireCell (source j v) bits))
  ⟨reports.map (fun row => row.map CellRun.word),
    reports.map (fun row => row.map CellRun.original),
    (reports.map (fun row => (row.map CellRun.calls).sum)).sum,
    (reports.map (fun row => (row.map CellRun.sourceWork).sum)).sum,
    (reports.map (fun row => (row.map CellRun.digitWork).sum)).sum,
    20*m*n+20*m+5⟩

/-- Actual immutable rows have the exact original matrix shape. -/
theorem acquire_words {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (acquire source bits).words=List.ofFn (fun j => List.ofFn (fun v => (encode bits (source j v).value).word)) := by
  simp only [acquire,List.map_ofFn,Function.comp_def,acquireCell]

/-- The original integer cache uses precisely the same once-acquired reports. -/
theorem acquire_integers {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (acquire source bits).integers=List.ofFn (fun j => List.ofFn (fun v => (source j v).value)) := by
  simp only [acquire,List.map_ofFn,Function.comp_def,acquireCell]

/-- Every original coefficient is acquired once, rather than a closure being
re-evaluated separately for value and work projections. -/
theorem acquire_sourceCalls {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (acquire source bits).sourceCalls=m*n := by
  simp [acquire,List.map_ofFn,Function.comp_def,acquireCell,List.sum_ofFn]

/-- The actual source read costs are retained EXACTLY. -/
theorem acquire_sourceWork {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (acquire source bits).sourceWork=∑ j,∑ v,(source j v).work := by
  simp only [acquire,List.map_ofFn,Function.comp_def,acquireCell,List.sum_ofFn]

/-- All scalar integer-digit extraction has a fixed polynomial exact ledger. -/
theorem acquire_digitWork {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (acquire source bits).digitWork=m*n*(4*(bits+1)+4) := by
  simp only [acquire,List.map_ofFn,Function.comp_def,acquireCell,List.sum_ofFn]
  simp [encode_work,Nat.mul_assoc]

/-- Actual emitted matrix rows refine ORIGINAL integer rows, with no encoded
word/template/Fits advice from the caller. -/
theorem acquire_refines {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ)
    (hC : ∀ j v,|(source j v).value| ≤ (2^bits : ℕ)) (j : Fin m) :
    SemiprimeRowSelectionBits.RowRefines
      (SemiprimeRowSelectionBitArithmetic.readAt [] (acquire source bits).words j.val).value
      (originalRow (fun j v => (source j v).value) j) (selectorWidth n bits) := by
  rw [acquire_words,SemiprimeRowSelectionBitArithmetic.readAt_ofFn]
  refine ⟨by simp,?_⟩
  intro v
  rw [SemiprimeRowSelectionBitArithmetic.readWord,SemiprimeRowSelectionBitArithmetic.readAt_ofFn]
  exact ⟨encode_valid bits _,encode_width n bits _,encode_value bits _ (hC j v)⟩

/-- Selection output with every acquisition and execution work category kept. -/
structure SelectionRun (m : ℕ) where
  /-- Actual original selected IDs. -/
  selected : List (Fin m)
  /-- Original matrix cache, acquired without any second source reads. -/
  integers : List (List ℤ)
  /-- Actual source access count. -/
  sourceCalls : ℕ
  /-- Source-access work supplied by the actual read program. -/
  sourceWork : ℕ
  /-- Scalar integer-digit extraction work. -/
  digitWork : ℕ
  /-- Matrix/template/ID allocation and finite traversal work. -/
  preparationWork : ℕ
  /-- Physical rational arithmetic and selector list/control work. -/
  selectorWork : ℕ
  /-- Sum of all retained work categories. -/
  work : ℕ

/-- Entire acquired integer-to-selector adapter: actual template, actual row
IDs, every encoded cell and ONE physical selector call, with no supplied words. -/
def select {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) : SelectionRun m :=
  let acquired := acquire source bits
  let W := selectorWidth n bits
  let template := List.replicate W false
  let ids := List.finRange m
  let out := SemiprimeRowSelectionBits.run n template acquired.words ids
  let preparation := acquired.cacheWork+(W+1)+(3*m+1)+3
  ⟨out.state.selected,acquired.integers,acquired.sourceCalls,acquired.sourceWork,acquired.digitWork,
    preparation,out.clock,acquired.sourceWork+acquired.digitWork+preparation+out.clock⟩

/-- The acquired adapter selects exactly the actual old original integer rows. -/
theorem select_correct {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ)
    (hC : ∀ j v,|(source j v).value| ≤ (2^bits : ℕ)) :
    (select source bits).selected=selectedIndices (fun j v => (source j v).value) := by
  exact SemiprimeRowSelectionBits.run_selected_eq _ (List.finRange m) bits hC
    (List.replicate (selectorWidth n bits) false) (by simp) (acquire source bits).words
    (by simpa using acquire_refines source bits hC)

/-- The adapter returns its original integer cache for selected-row assembly,
so the caller need not re-read an expensive source after choosing IDs. -/
theorem select_integers {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (select source bits).integers=List.ofFn (fun j => List.ofFn (fun v => (source j v).value)) :=
  acquire_integers source bits

/-- Original callback accesses are exposed exactly at the public adapter. -/
theorem select_sourceCalls {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (select source bits).sourceCalls=m*n := acquire_sourceCalls source bits

/-- Exact retained source-read work at the public selector adapter. -/
theorem select_sourceWork {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (select source bits).sourceWork=∑ j,∑ v,(source j v).work := acquire_sourceWork source bits

/-- Exact digit-extraction ledger, separately exposed from physical arithmetic. -/
theorem select_digitWork {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (select source bits).digitWork=m*n*(4*(bits+1)+4) := acquire_digitWork source bits

/-- Matrix cache, actual template and actual row-ID construction are attached. -/
theorem select_preparationWork {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits : ℕ) :
    (select source bits).preparationWork=
      (20*m*n+20*m+5)+(selectorWidth n bits+1)+(3*m+1)+3 := rfl

/-- Fixed polynomial acquisition/physical-selector ledger after a caller's
original cached-read bound. Its scalar-digit and memory model remains explicit. -/
def budget (m n bits readBudget : ℕ) : ℕ :=
  m*n*readBudget+m*n*(4*(bits+1)+4)+(20*m*n+20*m+5)+
    (selectorWidth n bits+1)+(3*m+1)+3+
    SemiprimeRowSelectionBits.runBudget m n (selectorWidth n bits) m

/-- Complete attached work bound: source reads, digit operations, actual cache,
template/IDs and the ENTIRE physical selector. No output/state/Fits oracle. -/
theorem select_work {m n : ℕ} (source : Fin m → Fin n → IntRun) (bits readBudget : ℕ)
    (hC : ∀ j v,|(source j v).value| ≤ (2^bits : ℕ))
    (hread : ∀ j v,(source j v).work ≤ readBudget) :
    (select source bits).work ≤ budget m n bits readBudget := by
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin m))) =>
    Finset.sum_le_sum (fun v (_ : v∈(Finset.univ : Finset (Fin n))) => hread j v))
  have hshape : (acquire source bits).words.length ≤ m := by rw [acquire_words]; simp
  have hp := SemiprimeRowSelectionBits.run_clock (fun j v => (source j v).value) (List.finRange m)
    bits hC (List.replicate (selectorWidth n bits) false) (by simp)
    (acquire source bits).words hshape (by simpa using acquire_refines source bits hC)
  rw [List.length_finRange] at hp
  simp only [List.length_replicate] at hp
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hs' : (∑ j,∑ v,(source j v).work) ≤ m*n*readBudget := by
    simpa only [Nat.mul_assoc] using hs
  unfold select budget
  dsimp only
  rw [acquire_sourceWork,acquire_digitWork]
  change (∑ j,∑ v,(source j v).work)+m*n*(4*(bits+1)+4)+
    ((20*m*n+20*m+5)+(selectorWidth n bits+1)+(3*m+1)+3)+_ ≤ _
  omega

/-- Plain original integer matrix wrapper: one logical source access per cell.
A caller needing physical read costs should use select with its actual IntRun. -/
def selectMatrix {m n : ℕ} (C : Fin m → Fin n → ℤ) (bits : ℕ) : SelectionRun m :=
  select (fun j v => ⟨C j v,1⟩) bits

/-- Plain integer input interface requires no pre-encoded data. -/
theorem selectMatrix_correct {m n : ℕ} (C : Fin m → Fin n → ℤ) (bits : ℕ)
    (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) :
    (selectMatrix C bits).selected=selectedIndices C := select_correct _ _ hC

/-- Plain-matrix logical-read wrapper inherits the full acquired ledger; its
one-unit read is explicitly not a physical lookup-cost theorem. -/
theorem selectMatrix_work {m n : ℕ} (C : Fin m → Fin n → ℤ) (bits : ℕ)
    (hC : ∀ j v,|C j v| ≤ (2^bits : ℕ)) :
    (selectMatrix C bits).work ≤ budget m n bits 1 :=
  select_work _ bits 1 hC (by intro j v; rfl)

end RiemannGaussian.SemiprimeEncodedRowSelection
