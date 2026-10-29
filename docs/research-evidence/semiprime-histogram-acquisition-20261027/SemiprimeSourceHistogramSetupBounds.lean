/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramSetup
import RiemannGaussian.SemiprimeSourceHistogramHeadBounds
import RiemannGaussian.SemiprimeSourceHistogramScalesBounds

/-! # Actual original-input histogram setup resources
The complete setup report is bounded from the actual sparse original metadata,
compact bank/row dictionary, encoded keys and acquired scales. Native finite
metadata/encoder interfaces remain explicit; no near-linear/full-TM claim is made.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramSetupBounds
open scoped BigOperators
open SemiprimeReportPolynomialGrowth

/-- Actual original bank/dictionary and once-acquired coordinate ID cache. -/
def rowsBudget (r Q L : ℕ) : ℕ := SemiprimeSourceHistogramRowsBounds.budget r Q L+
  Q*SemiprimeSourceCompactWordIds.stepBudget Q+1+4

/-- Static original variable keys, retaining every actual finite-index encoder. -/
def verticesBudget (n : ℕ) : ℕ := n*(SemiprimeSourceHistogramPortKeys.encodeBudget n+5)+1

/-- Coordinate magnitude is counted from the actual acquired coordinate list. -/
def coordinateBudget (Q : ℕ) : ℕ := Q*SemiprimeSourceHistogramCountInput.stepBudget Q+1

/-- Complete retained setup budget in original dimensions and actual M,L cardinalities. -/
def budget (n F r Q lam M L : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.budget n F Q M+rowsBudget r Q L+
  verticesBudget n+SemiprimeSourceHistogramScalesBounds.budget r Q lam M n+
  coordinateBudget Q+8

/-- Every setup producer is actually invoked and its complete report is retained.
Only the original positive group count is needed, not setup/resource/width advice. -/
theorem acquire_clock (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (hr : 0<r) :
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).clock ≤
      budget n F r Q lam (∑e,arity e) (r^Q) := by
  let data := SemiprimeSourceHistogramPortKeys.acquireOriginal n F Q arity owner
  have hd := SemiprimeSourceHistogramPortKeys.acquireOriginal_clock n F Q arity owner
  have hrows := SemiprimeSourceHistogramRowKeys.acquireCaches_clock r Q hr
  change (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).clock ≤ rowsBudget r Q (r^Q) at hrows
  have hM : data.records.length=∑e,arity e :=
    SemiprimeSourceHistogramPortKeys.acquireOriginal_length n F Q arity owner
  have hn : data.metadata.vertices.length=n := (SemiprimeSourceHistogramMetadata.sizes n F Q arity).1
  have hQ : data.metadata.coordinates.length=Q := (SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.2.1
  have hv := SemiprimeSourceHistogramHeadBounds.verticesWith_work data.metadata.vertices
  rw [hn] at hv
  change (SemiprimeSourceHistogramHeadBits.verticesWith data.metadata.vertices).work ≤ verticesBudget n at hv
  have hs := SemiprimeSourceHistogramScalesBounds.acquire_clock r Q lam data.records data.metadata.vertices
  rw [hM,hn] at hs
  have hq := SemiprimeSourceHistogramCountInput.count_clock data.metadata.coordinates
  rw [hQ] at hq
  change (SemiprimeSourceHistogramCountInput.count data.metadata.coordinates).clock ≤ coordinateBudget Q at hq
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hd hrows) hv) hs) hq) 8

/-- Conservative polynomial envelope for the original compact bank setup.
It keeps colour/native-row initialization rather than assuming it away. -/
def bankPolynomial (S : ℕ) : ℕ :=
  SemiprimeSourceWordBankAcquisitionBudget.colourBudget S+2+
  S*SemiprimeSourceWordBankAcquisitionBudget.rowStage S S S+3+
  S*(30*((S+1)+2)+20)+1+S+4

/-- Original row dictionary, using proved compact address width caps. -/
def rowsPolynomial (S : ℕ) : ℕ :=
  bankPolynomial S+4*S+1+S*SemiprimeSourceHistogramRowsBounds.rowStage (S+1) S (S+1)+1+4+
    S*(30*((S+1)+2)+20)+1+4

/-- One fixed original-resource polynomial also covers every native setup encoder. -/
def polynomialBudget (S : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.budget S S S S+rowsPolynomial S+verticesBudget S+
    SemiprimeSourceHistogramScalesBounds.polynomialBudget S+
      (S*(30*((S+1)+2)+20)+1)+8

/-- The actual row/bank cache budget has no unbound ID-width or producer parameter. -/
theorem rowsBudget_polynomial (r Q L S : ℕ) (hr : r ≤ S) (hQ : Q ≤ S) (hL : L ≤ S) :
    rowsBudget r Q L ≤ rowsPolynomial S := by
  have hl := SemiprimeSourceHistogramScalesBounds.clog_cap L S hL
  have hq := SemiprimeSourceHistogramScalesBounds.clog_cap Q S hQ
  have hcolour : SemiprimeSourceWordBankAcquisitionBudget.colourBudget r ≤
      SemiprimeSourceWordBankAcquisitionBudget.colourBudget S := by
    unfold SemiprimeSourceWordBankAcquisitionBudget.colourBudget
    gcongr
  have hstage : SemiprimeSourceWordBankAcquisitionBudget.rowStage r Q L ≤
      SemiprimeSourceWordBankAcquisitionBudget.rowStage S S S := by
    unfold SemiprimeSourceWordBankAcquisitionBudget.rowStage
    gcongr
  have hids : L*SemiprimeSourceCompactWordIds.stepBudget L ≤ S*(30*((S+1)+2)+20) := by
    unfold SemiprimeSourceCompactWordIds.stepBudget
    gcongr
  have hcoords : Q*SemiprimeSourceCompactWordIds.stepBudget Q ≤ S*(30*((S+1)+2)+20) := by
    unfold SemiprimeSourceCompactWordIds.stepBudget
    gcongr
  have hbank : SemiprimeSourceCompactWordBank.budget r Q L ≤ bankPolynomial S := by
    unfold SemiprimeSourceCompactWordBank.budget bankPolynomial
    have hs := Nat.mul_le_mul hQ hstage
    omega
  have hdictionary : SemiprimeSourceHistogramRowsBounds.rowStage (Nat.clog 2 (L+1)) Q (r+1) ≤
      SemiprimeSourceHistogramRowsBounds.rowStage (S+1) S (S+1) := by
    unfold SemiprimeSourceHistogramRowsBounds.rowStage
    gcongr
  have hdict := Nat.mul_le_mul hL hdictionary
  unfold rowsBudget SemiprimeSourceHistogramRowsBounds.budget rowsPolynomial
  omega

/-- Every original numerical cap discharges the full explicit setup envelope. -/
theorem budget_polynomial (n F r Q lam M L S : ℕ)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hl : lam ≤ S)
    (hM : M ≤ S) (hL : L ≤ S) : budget n F r Q lam M L ≤ polynomialBudget S := by
  have hrows := rowsBudget_polynomial r Q L S hr hQ hL
  have hscales := SemiprimeSourceHistogramScalesBounds.budget_polynomial r Q lam M n S hr hQ hl hM hn
  have hports : SemiprimeSourceHistogramPortKeys.budget n F Q M ≤
      SemiprimeSourceHistogramPortKeys.budget S S S S := by
    unfold SemiprimeSourceHistogramPortKeys.budget SemiprimeSourceHistogramMetadata.budget
      SemiprimeSourceHistogramPortKeys.recordBudget SemiprimeSourceHistogramPortKeys.encodeBudget
    gcongr
  have hv : verticesBudget n ≤ verticesBudget S := by
    unfold verticesBudget SemiprimeSourceHistogramPortKeys.encodeBudget
    gcongr
  have hlogQ := SemiprimeSourceHistogramScalesBounds.clog_cap Q S hQ
  have hc : coordinateBudget Q ≤ S*(30*((S+1)+2)+20)+1 := by
    unfold coordinateBudget SemiprimeSourceHistogramCountInput.stepBudget
    gcongr
  unfold budget polynomialBudget
  omega

/-- Fixed constants precede all original graphs, owner functions and resource caps.
The actual cardinalities M=Σarity and L=r^Q are never supplied count answers. -/
theorem acquire_clock_monomial : ∃ C k : ℕ,∀ n F r Q lam (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) S,
    0<r → n ≤ S → F ≤ S → r ≤ S → Q ≤ S → lam ≤ S →
      (∑e,arity e) ≤ S → r^Q ≤ S →
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).clock ≤ C*(S+1)^k := by
  have hp : Bound (fun S => polynomialBudget S) := by
    simp only [polynomialBudget,rowsPolynomial,bankPolynomial,verticesBudget,
      SemiprimeSourceHistogramPortKeys.budget,SemiprimeSourceHistogramMetadata.budget,
      SemiprimeSourceHistogramPortKeys.recordBudget,SemiprimeSourceHistogramPortKeys.encodeBudget,
      SemiprimeSourceWordBankAcquisitionBudget.colourBudget,SemiprimeSourceWordBankAcquisitionBudget.rowStage,
      SemiprimeSourceHistogramRowsBounds.rowStage,SemiprimeSourceHistogramScalesBounds.polynomialBudget,
      SemiprimeSourceHistogramScalesBounds.naturalBudget,SemiprimeSourceHistogramScalesBounds.powerBudget,
      SemiprimeSourceCountPowers.stepBudget,SemiprimeSourceHistogramScalesBounds.productBudget,
      SemiprimeSourceHistogramScalesBounds.weightsBudget,SemiprimeSourceScoreWeightBits.weightBudget,
      SemiprimeSourceScoreWeightBits.weightWidth]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro n F r Q lam arity owner S hpos hn hF hr hQ hl hM hL
  exact (acquire_clock n F r Q lam arity owner hpos).trans
    ((budget_polynomial n F r Q lam (∑e,arity e) (r^Q) S hn hF hr hQ hl hM hL).trans (h S))

end RiemannGaussian.SemiprimeSourceHistogramSetupBounds
