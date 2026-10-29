/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordBankBounds

/-! # Complete original physical coordinate-bank acquisition budget
The universal-cardinality parameter of the numeric envelope is an independent
resource cap; the actual execution theorem substitutes exactly r^Q.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget
open SemiprimeSourceWordBank SemiprimeSourceWordBankRows SemiprimeSourceWordBankBounds
open SemiprimeSourceWordBankSemantics SemiprimeRationalBits SemiprimeBitArithmetic
open SemiprimeBitDivision SemiprimeBitProductSort SemiprimeSourceOffsetInputsCore
open SemiprimeSourceScorePredicateBits SemiprimeSourceScorePredicateBitsBounds
open SemiprimeMaterializedSourceUniversal SemiprimeReportPolynomialGrowth

/-- Exact number of actually acquired physical colour cells. -/
theorem colours_length (r : ℕ) : (colours r).value.length=r := by
  have h := congrArg List.length (colours_values r)
  simpa only [List.length_map,List.length_finRange] using h

/-- Literal product-list cardinality at the runtime constructor head. -/
theorem product_length {α β : Type*} (xs : List α) (ys : List β) :
    (xs.product ys).length=xs.length*ys.length := List.length_product _ _

/-- Exact cardinality at every actual row-construction frame. -/
theorem rowsWith_cardinality (cs : List RationalWord) (q : ℕ) :
    (rowsWith cs q).value.length=cs.length^q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [rowsWith,collect_value,SemiprimePaidFiniteEnumerationLists.product_value,
      List.length_map,product_length,ih,pow_succ]
    ring

/-- Original colour acquisition, including finite-index construction. -/
def colourBudget (r : ℕ) : ℕ := 3*(r+1)^2+r*(20*(r+1)^2+8)+4

/-- No original-colour encoded word is supplied as an input. -/
theorem colours_clock (r : ℕ) : (colours r).work ≤ colourBudget r := by
  have hf := SemiprimePaidFiniteEnumerationLists.fin_work r
  have hc := collect_work (fun i : Fin r =>
    let encoded := encodeNat i.val
    (⟨encoded.word,encoded.clock+2⟩:Run RationalWord))
    (SemiprimePaidFiniteEnumerationLists.fin r).value (20*(r+1)^2+6) (by
      intro i _
      have h := encodeNat_clock i.val
      have hp : (i.val+1)^2 ≤ (r+1)^2 := Nat.pow_le_pow_left (by omega) 2
      dsimp only
      omega)
  simp only [SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange] at hc
  dsimp only [colours,colourBudget]
  simp only [SemiprimePaidFiniteEnumerationLists.fin_value]
  nlinarith

/-- One copied-row callback with all head and tail payload copying retained. -/
theorem prepend_clock (head : RationalWord) (tail : Row) (W Q : ℕ)
    (hh : Width head W) (ht : tail.length≤Q ∧ ∀ x∈tail,Width x W) :
    (prepend head tail).work ≤ Q*(8*W+9)+8*W+12 := by
  have h := SemiprimeSourceMemoryBits.copyWord_clock head W hh
  have t := copyRow_work tail W Q ht
  dsimp only [prepend]
  unfold copyBudget at t
  omega

/-- Single original physical row-acquisition stage with cached tail cardinality cap A. -/
def rowStage (r Q A : ℕ) : ℕ :=
  r*(4*A+3)+1+r*A*(Q*(8*(r+1)+9)+8*(r+1)+14)+1+4

/-- Every actual coordinate-recursion frame is covered by the original maximum dimensions. -/
theorem rowsWith_clock (r Q : ℕ) (hr : 0<r) :
    ∀ q≤Q,(rowsWith (colours r).value q).work≤2+q*rowStage r Q (r^Q) := by
  intro q hq
  induction q with
  | zero => simp [rowsWith]
  | succ q ih =>
    have old := ih (by omega)
    have hcard : (rowsWith (colours r).value q).value.length ≤ r^Q := by
      rw [rowsWith_cardinality,colours_length]
      exact Nat.pow_le_pow_right hr (by omega)
    have hp := SemiprimePaidFiniteEnumerationLists.product_work (colours r).value
      (rowsWith (colours r).value q).value
    rw [colours_length] at hp
    have hp' : (SemiprimePaidFiniteEnumerationLists.product (colours r).value
        (rowsWith (colours r).value q).value).work ≤ r*(4*r^Q+3)+1 := by
      apply hp.trans
      gcongr
    have hc := collect_work (fun p : RationalWord×Row => prepend p.1 p.2)
      (SemiprimePaidFiniteEnumerationLists.product (colours r).value
        (rowsWith (colours r).value q).value).value
      (Q*(8*(r+1)+9)+8*(r+1)+12) (by
        intro p h
        rw [SemiprimePaidFiniteEnumerationLists.product_value] at h
        have hmem := List.mem_product.mp h
        apply prepend_clock
        · exact (colours_good r p.1 hmem.1).2
        · exact ⟨(rowsWith_length _ q _ hmem.2).le.trans (by omega),
            fun x hx => (rowsWith_good _ _ q (colours_good r) _ hmem.2 x hx).2⟩)
    simp only [SemiprimePaidFiniteEnumerationLists.product_value,product_length,colours_length] at hc
    have hc' : (collect (fun p : RationalWord×Row => prepend p.1 p.2)
        (SemiprimePaidFiniteEnumerationLists.product (colours r).value
          (rowsWith (colours r).value q).value).value).work ≤
        r*r^Q*(Q*(8*(r+1)+9)+8*(r+1)+14)+1 := by
      rw [SemiprimePaidFiniteEnumerationLists.product_value]
      apply hc.trans
      gcongr
    simp only [rowsWith]
    unfold rowStage at old ⊢
    nlinarith

/-- All generated IDs, including high-zero padding, have original cardinality width. -/
theorem ascending_bounded (current : List Bool) (n : ℕ) :
    ∀ id∈(ascending current n).value,id.length≤current.length+2*n := by
  induction n generalizing current with
  | zero => simp [ascending]
  | succ n ih =>
    intro id hi
    simp only [ascending,List.mem_cons,fitBits_self] at hi
    rcases hi with rfl|hi
    · omega
    · have h := ih (addBits current [true] false).bits id hi
      have hl := (addBits_counts current [true] false).2.2.2.2
      simp only [List.length_cons,List.length_nil] at hl
      omega

/-- Full acquired ascending-ID circuit work, with original physical length caps. -/
theorem ascending_clock (current : List Bool) (n L : ℕ) (hL : current.length+2*n≤L) :
    (ascending current n).work≤n*(30*(L+1)+30)+1 := by
  induction n generalizing current with
  | zero => simp [ascending]
  | succ n ih =>
    have hl := (addBits_counts current [true] false).2.2.2.2
    simp only [List.length_cons,List.length_nil] at hl
    have ht := ih (addBits current [true] false).bits (by omega)
    have hc := fitBits_cost current current
    have ha := addBits_cost current [true] false
    have hm : max current.length [true].length≤L+1 := by
      simp only [List.length_cons,List.length_nil]
      apply max_le <;> omega
    simp only [ascending]
    nlinarith

/-- Numeric envelope includes actual colour, all row stages, all IDs and final lengths. -/
def budget (r Q A : ℕ) : ℕ :=
  colourBudget r+2+Q*rowStage r Q A+3+A*(30*(2*A+1)+30)+1+A+4

/-- Complete bank acquisition bound from original input only. -/
theorem acquire_clock (r Q : ℕ) (hr : 0<r) : (acquire r Q).clock≤budget r Q (r^Q) := by
  have hc := colours_clock r
  have hrw := rowsWith_clock r Q hr Q le_rfl
  have hi := ascending_clock [] (SemiprimeSourceWordBankRows.rows r Q).value.length (2*r^Q)
    (by simp only [List.length_nil,Nat.zero_add,rows_length];exact le_rfl)
  simp only [rows_length] at hi
  dsimp only [acquire,SemiprimeSourceWordBankRows.rows]
  unfold budget
  change _ ≤ colourBudget r+2+Q*rowStage r Q (r^Q)+3+
    r^Q*(30*(2*r^Q+1)+30)+1+r^Q+4
  have hlen := rows_length r Q
  dsimp only [SemiprimeSourceWordBankRows.rows] at hlen
  rw [hlen]
  omega

/-- Actual acquired ID bit lengths require no advised width. -/
theorem acquire_ids_bounded (r Q : ℕ) : ∀ id∈(acquire r Q).ids,id.length≤2*r^Q := by
  have h := ascending_bounded [] (SemiprimeSourceWordBankRows.rows r Q).value.length
  simpa only [acquire,List.length_nil,Nat.zero_add,rows_length] using h

/-- Original acquired candidate IDs discharge lookup width without advice. -/
theorem readRow_clock_original (r Q : ℕ) (id : List Bool) (hid : id∈(acquire r Q).ids) :
    (readRow (acquire r Q) id).work≤
      (r^Q+1)*(copyBudget (r+1) Q+15*(2*r^Q+1)+30) := by
  apply readRow_clock r Q id (2*r^Q+1) (by omega)
  exact (acquire_ids_bounded r Q id hid).trans (by omega)

/-- Resource-only monotonicity, with no source/bank expressions in the arithmetic context. -/
theorem budget_mono {r Q A r' Q' A' : ℕ} (hr : r≤r') (hQ : Q≤Q') (hA : A≤A') :
    budget r Q A≤budget r' Q' A' := by
  unfold budget colourBudget rowStage
  gcongr

/-- Fixed monomial growth in independent materialized original resources. -/
theorem budget_monomial : ∃ C k : ℕ,∀ S,budget S S S≤C*(S+1)^k := by
  change Bound (fun S => budget S S S)
  simp only [budget,colourBudget,rowStage]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget
