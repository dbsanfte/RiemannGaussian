/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramScales

/-! # Complete original-input scale-cache work with compact query operands
Only original list counts and r,Q,lambda occur in the final budget. The native
r/lambda encoding costs remain explicit; no padded M/n encoding is executed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramScalesBounds
open SemiprimeBitArithmetic SemiprimeSourceOffsetInputsCore
open SemiprimeSourceHistogramScales SemiprimeReportPolynomialGrowth

/-- Paid native encoder and immediate high-zero removal. -/
def naturalBudget (n : ℕ) : ℕ := 20*(n+1)^2+6*(n+1)+6

/-- Original native parameter setup is explicit, not a binary encoder assumption. -/
theorem natural_clock (n : ℕ) : (natural n).clock ≤ naturalBudget n := by
  have hc := natBits_clock n
  have hl := natBits_length n
  simp only [natural,SemiprimeSourceCompactBits.trim_clock,naturalBudget]
  omega

/-- Repeated physical multiplication and final trim in actual base bit width. -/
def powerBudget (A k : ℕ) : ℕ :=
  1+k*SemiprimeSourceCountPowers.stepBudget A k+6*(2*k*A+1)+6

/-- The complete power clock requires only the actual original base width. -/
theorem power_clock (base : List Bool) (k A : ℕ) (ha : base.length ≤ A) :
    (power base k).clock ≤ powerBudget A k := by
  have hc := SemiprimeSourceCountPowers.powerBits_clock base k k le_rfl
  have hl := SemiprimeSourceCountPowers.powerBits_length base k
  have hb : SemiprimeSourceCountPowers.stepBudget base.length k ≤
      SemiprimeSourceCountPowers.stepBudget A k := by
    unfold SemiprimeSourceCountPowers.stepBudget
    gcongr
  have hl' : (SemiprimeSourceCountPowers.powerBits base k).bits.length ≤ 2*k*A+1 := by
    apply hl.trans
    gcongr
  have hc' := hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k hb) 1)
  simp only [power,SemiprimeSourceCompactBits.trim_clock,powerBudget]
  omega

/-- Conservative physical width before and after the actual power trim. -/
theorem power_length (base : List Bool) (k A : ℕ) (ha : base.length ≤ A) :
    (power base k).bits.length ≤ 2*k*A+1 := by
  apply (SemiprimeSourceCompactBits.trim_length _).trans
  apply (SemiprimeSourceCountPowers.powerBits_length base k).trans
  gcongr

/-- Actual multiplier and immediate trim, polynomial in its true operand widths. -/
def productBudget (A B : ℕ) : ℕ := 12*A*(A+B+2)+1+6*(2*A+B)+6

/-- All multiplier and trim work, with no product/encoded-value advice. -/
theorem product_clock (a b : List Bool) (A B : ℕ) (ha : a.length ≤ A) (hb : b.length ≤ B) :
    (product a b).clock ≤ productBudget A B := by
  have hc := mulBits_cost a b
  have hl := mulBits_length a b
  have hc' : bitCost (mulBits a b) ≤ 12*A*(A+B+2)+1 := by
    apply hc.trans
    gcongr
  have hl' : (mulBits a b).bits.length ≤ 2*A+B := by
    apply hl.trans
    gcongr
  simp only [product,SemiprimeSourceCompactBits.trim_clock,productBudget]
  omega

/-- Actual product output width follows the multiplier and the trim scan. -/
theorem product_length (a b : List Bool) (A B : ℕ) (ha : a.length ≤ A) (hb : b.length ≤ B) :
    (product a b).bits.length ≤ 2*A+B := by
  apply (SemiprimeSourceCompactBits.trim_length _).trans
  apply (mulBits_length a b).trans
  gcongr

/-- Seven actually executed weight products and both output trims. -/
def weightsBudget (K : ℕ) : ℕ := SemiprimeSourceScoreWeightBits.weightBudget K+
  12*SemiprimeSourceScoreWeightBits.weightWidth K+7

/-- Weight construction is paid at its actual compact input widths. -/
theorem weights_clock (M n lam U : List Bool) (K : ℕ)
    (hM : M.length ≤ K) (hn : n.length ≤ K) (hl : lam.length ≤ K) (hU : U.length ≤ K) :
    (weights M n lam U).clock ≤ weightsBudget K := by
  have hc := SemiprimeSourceScoreWeightBits.weights_clock M n lam U K hM hn hl hU
  have hw := SemiprimeSourceScoreWeightBits.weights_length M n lam U K hM hn hl hU
  simp only [weights,SemiprimeSourceCompactBits.trim_clock,weightsBudget]
  omega

/-- Physical alphabet-power width from the ALREADY trimmed original base. -/
def alphabetWidth (r Q : ℕ) : ℕ := 2*Q*Nat.clog 2 (r+1)+1
/-- Conservative square width, still logarithmic in original alphabet magnitude. -/
def squareWidth (r Q : ℕ) : ℕ := 3*alphabetWidth r Q
/-- Query weight input width uses compact M,n,lambda, not their padded encodings. -/
def inputWidth (r Q lam M n : ℕ) : ℕ :=
  Nat.clog 2 (M+1)+Nat.clog 2 (n+1)+Nat.clog 2 (lam+1)+squareWidth r Q

/-- Actual compact weight operands all fit the original-derived logarithmic bound. -/
theorem acquire_weight_input_widths {A B : Type*} (r Q lam : ℕ)
    (records : List A) (vertices : List B) :
    (SemiprimeSourceHistogramCountInput.count records).bits.length ≤
        inputWidth r Q lam records.length vertices.length ∧
    (SemiprimeSourceHistogramCountInput.count vertices).bits.length ≤
        inputWidth r Q lam records.length vertices.length ∧
    (natural lam).bits.length ≤ inputWidth r Q lam records.length vertices.length ∧
    (product (power (natural r).bits Q).bits (power (natural r).bits Q).bits).bits.length ≤
        inputWidth r Q lam records.length vertices.length := by
  have hM := SemiprimeSourceHistogramCountInput.count_length records
  have hn := SemiprimeSourceHistogramCountInput.count_length vertices
  have hl := natural_length lam
  have hL := power_length (natural r).bits Q (Nat.clog 2 (r+1)) (natural_length r)
  have hU := product_length (power (natural r).bits Q).bits (power (natural r).bits Q).bits
    (alphabetWidth r Q) (alphabetWidth r Q) hL hL
  unfold inputWidth squareWidth
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- Complete original list/dimension scale-cache budget; no unary L/L⁴ appears. -/
def budget (r Q lam M n : ℕ) : ℕ :=
  M*SemiprimeSourceHistogramCountInput.stepBudget M+1+
  (n*SemiprimeSourceHistogramCountInput.stepBudget n+1)+
  naturalBudget r+naturalBudget lam+
  powerBudget (Nat.clog 2 (r+1)) Q+
  productBudget (alphabetWidth r Q) (alphabetWidth r Q)+
  productBudget (squareWidth r Q) (squareWidth r Q)+
  powerBudget (Nat.clog 2 (r+1)) (4*Q-1)+
  weightsBudget (inputWidth r Q lam M n)+20

/-- The actual original-input scale cache retains every lower acquisition report. -/
theorem acquire_clock {A B : Type*} (r Q lam : ℕ) (records : List A) (vertices : List B) :
    (acquire r Q lam records vertices).clock ≤ budget r Q lam records.length vertices.length := by
  have hM := SemiprimeSourceHistogramCountInput.count_clock records
  have hn := SemiprimeSourceHistogramCountInput.count_clock vertices
  have hr := natural_clock r
  have hl := natural_clock lam
  have hL := power_clock (natural r).bits Q (Nat.clog 2 (r+1)) (natural_length r)
  have hG := power_clock (natural r).bits (4*Q-1) (Nat.clog 2 (r+1)) (natural_length r)
  have hLl := power_length (natural r).bits Q (Nat.clog 2 (r+1)) (natural_length r)
  have hL2 := product_clock (power (natural r).bits Q).bits (power (natural r).bits Q).bits
    (alphabetWidth r Q) (alphabetWidth r Q) hLl hLl
  have hL2l : (product (power (natural r).bits Q).bits (power (natural r).bits Q).bits).bits.length ≤
      squareWidth r Q := by
    have h := product_length (power (natural r).bits Q).bits (power (natural r).bits Q).bits
      (alphabetWidth r Q) (alphabetWidth r Q) hLl hLl
    unfold squareWidth
    omega
  have hL4 := product_clock
    (product (power (natural r).bits Q).bits (power (natural r).bits Q).bits).bits
    (product (power (natural r).bits Q).bits (power (natural r).bits Q).bits).bits
    (squareWidth r Q) (squareWidth r Q) hL2l hL2l
  have hw := acquire_weight_input_widths r Q lam records vertices
  have hweights := weights_clock
    (SemiprimeSourceHistogramCountInput.count records).bits
    (SemiprimeSourceHistogramCountInput.count vertices).bits (natural lam).bits
    (product (power (natural r).bits Q).bits (power (natural r).bits Q).bits).bits
    (inputWidth r Q lam records.length vertices.length) hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
  unfold acquire budget
  dsimp only
  omega

/-- Compact-width logarithms admit an elementary conservative original-resource cap. -/
theorem clog_cap (x S : ℕ) (hx : x ≤ S) : Nat.clog 2 (x+1) ≤ S+1 := by
  apply le_trans _ (Nat.add_le_add_right hx 1)
  apply (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).2
  exact Nat.lt_two_pow_self.le

/-- Physical power setup budgets are monotone in actual operand width and exponent. -/
theorem powerBudget_mono {A k A' k' : ℕ} (hA : A ≤ A') (hk : k ≤ k') :
    powerBudget A k ≤ powerBudget A' k' := by
  unfold powerBudget SemiprimeSourceCountPowers.stepBudget
  gcongr

/-- Physical product setup budgets are monotone in actual operand widths. -/
theorem productBudget_mono {A B A' B' : ℕ} (hA : A ≤ A') (hB : B ≤ B') :
    productBudget A B ≤ productBudget A' B' := by
  unfold productBudget
  gcongr

/-- Compact-weight setup budgets are monotone in actual input-width caps. -/
theorem weightsBudget_mono {K K' : ℕ} (h : K ≤ K') : weightsBudget K ≤ weightsBudget K' := by
  unfold weightsBudget SemiprimeSourceScoreWeightBits.weightBudget SemiprimeSourceScoreWeightBits.weightWidth
  gcongr

/-- A single polynomial expression covers the entire original input family.
This conservative setup envelope does not replace the proved compact query widths. -/
def polynomialBudget (S : ℕ) : ℕ :=
  2*(S*(30*((S+1)+2)+20)+1)+2*naturalBudget S+
  powerBudget (S+1) S+
  productBudget (2*S*(S+1)+1) (2*S*(S+1)+1)+
  productBudget (3*(2*S*(S+1)+1)) (3*(2*S*(S+1)+1))+
  powerBudget (S+1) (4*S)+weightsBudget (3*(S+1)+3*(2*S*(S+1)+1))+20

/-- Every original dimension/list count discharges this conservative numeric cap. -/
theorem budget_polynomial (r Q lam M n S : ℕ)
    (hr : r ≤ S) (hQ : Q ≤ S) (hl : lam ≤ S) (hM : M ≤ S) (hn : n ≤ S) :
    budget r Q lam M n ≤ polynomialBudget S := by
  have hlogr := clog_cap r S hr
  have hlogl := clog_cap lam S hl
  have hlogM := clog_cap M S hM
  have hlogn := clog_cap n S hn
  have hMc : M*SemiprimeSourceHistogramCountInput.stepBudget M+1 ≤
      S*(30*((S+1)+2)+20)+1 := by
    unfold SemiprimeSourceHistogramCountInput.stepBudget
    gcongr
  have hnc : n*SemiprimeSourceHistogramCountInput.stepBudget n+1 ≤
      S*(30*((S+1)+2)+20)+1 := by
    unfold SemiprimeSourceHistogramCountInput.stepBudget
    gcongr
  have hrn : naturalBudget r ≤ naturalBudget S := by unfold naturalBudget;gcongr
  have hln : naturalBudget lam ≤ naturalBudget S := by unfold naturalBudget;gcongr
  have hAw : alphabetWidth r Q ≤ 2*S*(S+1)+1 := by unfold alphabetWidth;gcongr
  have hSw : squareWidth r Q ≤ 3*(2*S*(S+1)+1) := by unfold squareWidth;gcongr
  have hIw : inputWidth r Q lam M n ≤ 3*(S+1)+3*(2*S*(S+1)+1) := by
    unfold inputWidth
    omega
  have hP := powerBudget_mono hlogr hQ
  have hG := powerBudget_mono hlogr (show 4*Q-1 ≤ 4*S by omega)
  have hS := productBudget_mono hAw hAw
  have hF := productBudget_mono hSw hSw
  have hW := weightsBudget_mono hIw
  unfold budget polynomialBudget
  omega

/-- Fixed constants precede all original dimensions and actual metadata lists. -/
theorem acquire_clock_monomial : ∃ C k : ℕ,∀ {A B : Type*} (r Q lam : ℕ)
    (records : List A) (vertices : List B) (S : ℕ),
    r ≤ S → Q ≤ S → lam ≤ S → records.length ≤ S → vertices.length ≤ S →
    (acquire r Q lam records vertices).clock ≤ C*(S+1)^k := by
  have hp : SemiprimeReportPolynomialGrowth.Bound polynomialBudget := by
    change Bound (fun S => polynomialBudget S)
    simp only [polynomialBudget,naturalBudget,powerBudget,SemiprimeSourceCountPowers.stepBudget,
      productBudget,weightsBudget,SemiprimeSourceScoreWeightBits.weightBudget,
      SemiprimeSourceScoreWeightBits.weightWidth]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro A B r Q lam records vertices S hr hQ hl hM hn
  exact (acquire_clock r Q lam records vertices).trans
    ((budget_polynomial r Q lam records.length vertices.length S hr hQ hl hM hn).trans (h S))

end RiemannGaussian.SemiprimeSourceHistogramScalesBounds
