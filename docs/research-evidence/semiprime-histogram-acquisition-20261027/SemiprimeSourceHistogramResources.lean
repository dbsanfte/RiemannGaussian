/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramQueryBounds
import RiemannGaussian.SemiprimeSourceHistogramSetupBounds
import RiemannGaussian.SemiprimeSourceHistogramSearchBudget

/-! # Uniform original-resource bounds for histogram source acquisition
Only caps on the original graph dimensions and actual materialized alphabet
occur below. Logarithms are enlarged only in numerical majorants; executed
compact payloads and all acquisition reports are retained by the caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeSourceHistogramResources
open scoped BigOperators
open SemiprimeReportPolynomialGrowth
open SemiprimeSourceHistogramArithmeticBounds (grow unitBudget)
open SemiprimeSourceHistogramScalesBounds (clog_cap)

/-- Subtraction-free polynomial envelope for the acquired logarithmic operands. -/
def basePolynomial (S : ℕ) : ℕ :=
  1+(S+1)+(S^2+1)+(S^4+1)+(S^4+1)+(S^8+1)+
    (4*S^2+1)+(S^2+1)+(S^4+1)+(S+1)+(S+2)

/-- Fixed-depth binary arithmetic preserves a polynomial output width. -/
def outputPolynomial (S : ℕ) : ℕ := grow (grow (basePolynomial S) 20) 2

/-- Original dimensions and actual alphabet cardinality bound every input width. -/
theorem baseWidth_polynomial (n M r Q lam S : ℕ) (hr0 : 0<r)
    (hn : n≤S) (hM : M≤S) (hQ : Q≤S) (hlam : lam≤S) (hL : r^Q≤S) :
    SemiprimeSourceHistogramQueryBounds.baseWidth n M r Q lam≤basePolynomial S := by
  have hL2 := Nat.pow_le_pow_left hL 2
  have hL4 := Nat.pow_le_pow_left hL 4
  have hG : r^(4*Q-1)≤S^4 := by
    calc
      _ ≤ r^(4*Q) := Nat.pow_le_pow_right hr0 (Nat.sub_le _ _)
      _ = (r^Q)^4 := by rw [← pow_mul];congr 1;omega
      _ ≤ S^4 := hL4
  have hI : n^2*lam^2*(r^Q)^4≤S^8 := by
    calc
      _ ≤ S^2*S^2*S^4 := by gcongr
      _ = S^8 := by ring
  have hH : 4*M^2≤4*S^2 := by gcongr
  have hM2 := Nat.pow_le_pow_left hM 2
  have hC : (Q*n)^2≤S^4 := by
    calc
      _ ≤ (S*S)^2 := by gcongr
      _ = S^4 := by ring
  have h1 := clog_cap (r^Q) S hL
  have h2 := clog_cap ((r^Q)^2) (S^2) hL2
  have h3 := clog_cap ((r^Q)^4) (S^4) hL4
  have h4 := clog_cap (r^(4*Q-1)) (S^4) hG
  have h5 := clog_cap (n^2*lam^2*(r^Q)^4) (S^8) hI
  have h6 := clog_cap (4*M^2) (4*S^2) hH
  have h7 := clog_cap (M^2) (S^2) hM2
  have h8 := clog_cap ((Q*n)^2) (S^4) hC
  have h9 := clog_cap Q S hQ
  have h10 : Nat.clog 2 (n+2)≤S+2 := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using clog_cap (n+1) (S+1) (by omega)
  unfold SemiprimeSourceHistogramQueryBounds.baseWidth basePolynomial
  omega

/-- Every actual final score width is bounded using only original resource caps. -/
theorem outputWidth_polynomial (n M r Q lam S : ℕ) (hr0 : 0<r)
    (hn : n≤S) (hM : M≤S) (hQ : Q≤S) (hlam : lam≤S) (hL : r^Q≤S) :
    SemiprimeSourceHistogramQueryBounds.outputWidth n M r Q lam≤outputPolynomial S := by
  apply SemiprimeSourceHistogramArithmeticBounds.grow_width_mono
  apply SemiprimeSourceHistogramArithmeticBounds.grow_width_mono
  exact baseWidth_polynomial n M r Q lam S hr0 hn hM hQ hlam hL

/-- Numerical polynomial above the actual streaming square-sum budget. -/
def squaresPolynomial (B M : ℕ) : ℕ :=
  M*(100*(B+((M+1)^2+1+2)+2)+100+3)+2

/-- The logarithmic counter width is enlarged only in this cost majorant. -/
theorem squaresBudget_polynomial (B M : ℕ) :
    SemiprimeSourceHistogramSquaresBounds.budget B M ≤ squaresPolynomial B M := by
  have h := clog_cap ((M+1)^2) ((M+1)^2) le_rfl
  unfold SemiprimeSourceHistogramSquaresBounds.budget
    SemiprimeSourceHistogramSquaresBounds.stepBudget
    SemiprimeSourceHistogramSquaresBounds.width squaresPolynomial
  gcongr

/-- Original graph and alphabet key widths in one physical feature pass. -/
def featurePolynomial (S : ℕ) : ℕ :=
  S*(28*(2*S+1)+47+4)+1+squaresPolynomial (3*(2*S+1)+1) S+3

/-- One actual feature budget is polynomial in original resources, without T. -/
theorem featureBudget_polynomial (n F M L S : ℕ)
    (hn : n≤S) (hF : F≤S) (hM : M≤S) (hL : L≤S) :
    SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) L M≤featurePolynomial S := by
  have hN := clog_cap (n+F) (2*S) (by omega)
  have hLlog := clog_cap L S hL
  have hw : SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) L≤2*S+1 := by
    exact max_le hN (hLlog.trans (by omega))
  have hs := (SemiprimeSourceHistogramSquaresBounds.budget_mono
    (show 3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) L+1≤3*(2*S+1)+1 by omega) hM).trans
      (squaresBudget_polynomial (3*(2*S+1)+1) S)
  unfold SemiprimeSourceHistogramFeatureBitsBounds.budget
    SemiprimeSourceHistogramFeatureBitsBounds.oneBudget featurePolynomial
  gcongr

/-- One paid physical row read and all its coordinate/colour tags. -/
def rowPolynomial (S : ℕ) : ℕ :=
  8*(S+1)+3*(S*(2*(S+1)+1))+12+S*(6*(S+1)+6*(S+1)+11)+8

/-- Original compact colour and row address caps bound the actual row-query budget. -/
theorem rowBudget_polynomial (r Q S : ℕ) (hr : r≤S) (hQ : Q≤S) (hL : r^Q≤S) :
    SemiprimeSourceHistogramHeadQueryBounds.rowQueryBudget r Q≤rowPolynomial S := by
  have h1 := clog_cap r S hr
  have h2 := clog_cap Q S hQ
  have h3 := clog_cap (r^Q) S hL
  unfold SemiprimeSourceHistogramHeadQueryBounds.rowQueryBudget rowPolynomial
  gcongr

/-- Full original head stream and physical counter/histogram cost majorant. -/
def headPolynomial (S : ℕ) : ℕ :=
  S*(8*(S+1)+3*(S+1)+12+rowPolynomial S+3*S+1+20*((S+2)+1)+10+20)+1+
    squaresPolynomial (3*(S+1)+1) (S^2)+3

/-- The all-coordinate head budget is polynomial in original acquired resources. -/
theorem headBudget_polynomial (n r Q S : ℕ)
    (hn : n≤S) (hr : r≤S) (hQ : Q≤S) (hL : r^Q≤S) :
    SemiprimeSourceHistogramHeadBounds.budget r Q (SemiprimeSourceHistogramPortKeys.keyWidth n) n≤
      headPolynomial S := by
  have h1 := clog_cap n S hn
  have h2 := clog_cap (r^Q) S hL
  have h3 := clog_cap Q S hQ
  have h4 := clog_cap r S hr
  have h5 : Nat.clog 2 (n+2)≤S+2 := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using clog_cap (n+1) (S+1) (by omega)
  have hrow := rowBudget_polynomial r Q S hr hQ hL
  have hkeys : SemiprimeSourceHistogramHeadQueryBounds.keyWidth r Q≤3*(S+1)+1 := by
    unfold SemiprimeSourceHistogramHeadQueryBounds.keyWidth
    omega
  have hcount : Q*n≤S^2 := by simpa only [pow_two] using Nat.mul_le_mul hQ hn
  have hs := (SemiprimeSourceHistogramSquaresBounds.budget_mono hkeys hcount).trans
    (squaresBudget_polynomial (3*(S+1)+1) (S^2))
  unfold SemiprimeSourceHistogramHeadBounds.budget
    SemiprimeSourceHistogramHeadBounds.vertexStage SemiprimeSourceHistogramPortKeys.keyWidth
    SemiprimeSourceHistogramTrieBounds.clockWidth headPolynomial
  gcongr

/-- All prefix keys and actual selected-ID copies, for at most n+F positions. -/
def prefixPolynomial (S : ℕ) : ℕ := 2*S*(100*((S+1)+(2*S+2)+2))+1

/-- Original prefix length and actual alphabet cap bound the full dictionary acquisition. -/
theorem prefixBudget_polynomial (L k S : ℕ) (hL : L≤S) (hk : k≤2*S) :
    SemiprimeSourceHistogramQueryBounds.prefixBudget L k≤prefixPolynomial S := by
  have h1 := clog_cap L S hL
  have h2 := clog_cap (k+1) (2*S+1) (by omega)
  unfold SemiprimeSourceHistogramQueryBounds.prefixBudget
    SemiprimeSourceHistogramTrieBounds.clockWidth prefixPolynomial
  gcongr

/-- Complete sparse score-query majorant with every physical producer retained. -/
def queryPolynomial (S : ℕ) : ℕ :=
  prefixPolynomial S+16*featurePolynomial S+headPolynomial S+
    90*unitBudget (basePolynomial S)+3*unitBudget (grow (basePolynomial S) 20)+2*S+10

/-- Complete per-query budget from original numerical resources only. -/
theorem scoreBudget_polynomial (n F M r Q lam k S : ℕ) (hr0 : 0<r)
    (hn : n≤S) (hF : F≤S) (hM : M≤S) (hr : r≤S) (hQ : Q≤S) (hlam : lam≤S)
    (hL : r^Q≤S) (hk : k≤2*S) :
    SemiprimeSourceHistogramQueryBounds.scoreBudget n F M r Q lam k≤queryPolynomial S := by
  have hp := prefixBudget_polynomial (r^Q) k S hL hk
  have hf := featureBudget_polynomial n F M (r^Q) S hn hF hM hL
  have hh := headBudget_polynomial n r Q S hn hr hQ hL
  have hb := baseWidth_polynomial n M r Q lam S hr0 hn hM hQ hlam hL
  have hu := SemiprimeSourceHistogramArithmeticBounds.unitBudget_mono hb
  have hg := SemiprimeSourceHistogramArithmeticBounds.unitBudget_mono
    (SemiprimeSourceHistogramArithmeticBounds.grow_width_mono hb 20)
  unfold SemiprimeSourceHistogramQueryBounds.scoreBudget
    SemiprimeSourceHistogramQueryBounds.laneWidth queryPolynomial
  omega

/-- Whole actual source-selector report majorant, including setup once.
The materialized alphabet is an original resource, not a bit-width substitution. -/
def envelope (S : ℕ) : ℕ :=
  SemiprimeSourceHistogramSetupBounds.polynomialBudget S+
    SemiprimeSourceHistogramSearchBudget.controllerBudget (2*S) S (S+1)
      (queryPolynomial S) (outputPolynomial S)+2*S+4

/-- The actual original selector budget is uniformly controlled by seven
original graph/alphabet resources. There is no quadratic descriptor-count cap. -/
theorem budget_polynomial (n F r Q lam M S : ℕ) (hr0 : 0<r)
    (hn : n≤S) (hF : F≤S) (hr : r≤S) (hQ : Q≤S) (hlam : lam≤S)
    (hM : M≤S) (hL : r^Q≤S) :
    SemiprimeSourceHistogramSearchBudget.budget n F r Q lam M (r^Q)≤envelope S := by
  have hs := SemiprimeSourceHistogramSetupBounds.budget_polynomial
    n F r Q lam M (r^Q) S hn hF hr hQ hlam hM hL
  have hquery := scoreBudget_polynomial n F M r Q lam (n+F) S hr0
    hn hF hM hr hQ hlam hL (by omega)
  have hwidth := outputWidth_polynomial n M r Q lam S hr0 hn hM hQ hlam hL
  have hbits := clog_cap (r^Q) S hL
  have htail : r^Q-1≤S := (Nat.sub_le _ _).trans hL
  have hc := SemiprimeSourceHistogramSearchBudget.controllerBudget_mono
    (show n+F≤2*S by omega) htail hbits hquery hwidth
  unfold SemiprimeSourceHistogramSearchBudget.budget envelope
  omega

/-- Fixed constants precede the entire original family, including all graphs,
owner functions, prefixes and physical acquired scores. -/
theorem envelope_monomial : ∃ C k : ℕ,∀ S,envelope S≤C*(S+1)^k := by
  change Bound (fun S => envelope S)
  simp only [envelope,SemiprimeSourceHistogramSearchBudget.controllerBudget,
    queryPolynomial,outputPolynomial,basePolynomial,prefixPolynomial,featurePolynomial,
    headPolynomial,rowPolynomial,squaresPolynomial,
    SemiprimeSourceHistogramArithmeticBounds.unitBudget,SemiprimeSourceHistogramArithmeticBounds.grow,
    SemiprimeSourceHistogramSetupBounds.polynomialBudget,
    SemiprimeSourceHistogramSetupBounds.rowsPolynomial,
    SemiprimeSourceHistogramSetupBounds.bankPolynomial,
    SemiprimeSourceHistogramSetupBounds.verticesBudget,
    SemiprimeSourceHistogramPortKeys.budget,SemiprimeSourceHistogramMetadata.budget,
    SemiprimeSourceHistogramPortKeys.recordBudget,SemiprimeSourceHistogramPortKeys.encodeBudget,
    SemiprimeSourceWordBankAcquisitionBudget.colourBudget,SemiprimeSourceWordBankAcquisitionBudget.rowStage,
    SemiprimeSourceHistogramRowsBounds.rowStage,SemiprimeSourceHistogramScalesBounds.polynomialBudget,
    SemiprimeSourceHistogramScalesBounds.naturalBudget,SemiprimeSourceHistogramScalesBounds.powerBudget,
    SemiprimeSourceCountPowers.stepBudget,SemiprimeSourceHistogramScalesBounds.productBudget,
    SemiprimeSourceHistogramScalesBounds.weightsBudget,SemiprimeSourceScoreWeightBits.weightBudget,
    SemiprimeSourceScoreWeightBits.weightWidth]
  boundArithmetic

/-- Actual original-input source selection, bounded by original resource caps
with every setup/query/comparison/copy report retained. This is a mixed report,
not a complete primitive-bit/tape or public-caller clock theorem. -/
theorem run_report_actual (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (S : ℕ)
    (hn : n≤S) (hF : F≤S) (hr : r≤S) (hQ : Q≤S) (hlam : lam≤S)
    (hM : (∑ e,arity e)≤S) (hL : r^Q≤S) :
    (SemiprimeSourceHistogramSearch.run n F r Q lam arity owner).work≤envelope S := by
  exact (SemiprimeSourceHistogramSearchBudget.run_work n F r Q lam arity owner).trans
    (budget_polynomial n F r Q lam (∑ e,arity e) S (NeZero.pos r) hn hF hr hQ hlam hM hL)

end RiemannGaussian.SemiprimeSourceHistogramResources
