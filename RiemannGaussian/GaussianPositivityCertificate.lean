import RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# Soundness interface for Gaussian positivity certificates

This file connects the shape of the finite endpoint certificates to the
actual convergent arithmetic explicit formula.  A cutoff separates the
retained low prime-power channels from an honest infinite tail.  The
soundness theorem then packages exactly the four analytic obligations used by
the current certificates: a positive endpoint margin, no compact-interval
loss in the retained model, a controlled loss from the omitted tail, and a
direct large-center bound.
-/

namespace RiemannGaussian

noncomputable section

open Filter
open scoped BigOperators Topology

/-- The low prime-power channels with natural-number index below `cutoff`.
The zero terms at indices `0` and `1` make `cutoff = 6` exactly the retained
`n = 2,3,4,5` model used by the epsilon `3/50` certificate. -/
def gaussianPrimePartialSum (ε t : ℝ) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff, gaussianPrimeSummand ε t n

/-- The genuine infinite prime-power tail starting at `cutoff`. -/
def gaussianPrimeTailSum (ε t : ℝ) (cutoff : ℕ) : ℝ :=
  ∑' k : ℕ, gaussianPrimeSummand ε t (k + cutoff)

/-- Absolute convergence makes the low-channel/tail split exact. -/
theorem gaussianPrimeSum_eq_partial_add_tail
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (cutoff : ℕ) :
    gaussianPrimeSum ε t =
      gaussianPrimePartialSum ε t cutoff +
        gaussianPrimeTailSum ε t cutoff := by
  unfold gaussianPrimeSum gaussianPrimePartialSum gaussianPrimeTailSum
  exact (summable_gaussianPrimeSummand hε t).sum_add_tsum_nat_add cutoff |>.symm

/-- Prime contribution of the finitely retained channels. -/
def gaussianPrimePartialContribution
    (ε t : ℝ) (cutoff : ℕ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) * gaussianPrimePartialSum ε t cutoff

/-- Prime contribution of the infinite omitted tail. -/
def gaussianPrimeTailContribution
    (ε t : ℝ) (cutoff : ℕ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) * gaussianPrimeTailSum ε t cutoff

/-- The nonoscillatory tail envelope is the prime tail at center zero. -/
def gaussianPrimeTailEnvelope (ε : ℝ) (cutoff : ℕ) : ℝ :=
  gaussianPrimeTailContribution ε 0 cutoff

theorem summable_gaussianPrimeTailSummand
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (cutoff : ℕ) :
    Summable (fun k : ℕ => gaussianPrimeSummand ε t (k + cutoff)) := by
  exact (summable_nat_add_iff cutoff).2
    (summable_gaussianPrimeSummand hε t)

lemma abs_gaussianPrimeSummand_le_zero_center
    (ε t : ℝ) (n : ℕ) :
    |gaussianPrimeSummand ε t n| ≤ gaussianPrimeSummand ε 0 n := by
  have hcoefficient : 0 ≤
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        Real.exp (-(Real.log n) ^ 2 / (4 * ε)) := by
    positivity
  unfold gaussianPrimeSummand
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [abs_mul, abs_of_nonneg hcoefficient]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left
      (Real.abs_cos_le_one (t * Real.log n)) hcoefficient

/-- The zero-center tail is nonnegative because every one of its summands is
nonnegative. -/
theorem gaussianPrimeTailContribution_zero_nonnegative
    {ε : ℝ} (hε : 0 < ε) (cutoff : ℕ) :
    0 ≤ gaussianPrimeTailContribution ε 0 cutoff := by
  have hfactor : 0 ≤ 2 / Real.sqrt (Real.pi * ε) := by positivity
  apply mul_nonneg hfactor
  apply tsum_nonneg
  intro k
  unfold gaussianPrimeSummand
  simp only [zero_mul, Real.cos_zero, mul_one]
  positivity

/-- The absolute value of the oscillatory infinite tail at every center is
bounded by the same tail at center zero. -/
theorem abs_gaussianPrimeTailContribution_le_envelope
    {ε : ℝ} (hε : 0 < ε) (cutoff : ℕ) (t : ℝ) :
    |gaussianPrimeTailContribution ε t cutoff| ≤
      gaussianPrimeTailEnvelope ε cutoff := by
  let f : ℕ → ℝ := fun k => gaussianPrimeSummand ε t (k + cutoff)
  let g : ℕ → ℝ := fun k => gaussianPrimeSummand ε 0 (k + cutoff)
  have hf : Summable f :=
    summable_gaussianPrimeTailSummand hε t cutoff
  have hg : Summable g :=
    summable_gaussianPrimeTailSummand hε 0 cutoff
  have habs : (∑' k, |f k|) ≤ ∑' k, g k := by
    exact hf.norm.tsum_le_tsum
      (fun k => abs_gaussianPrimeSummand_le_zero_center ε t (k + cutoff)) hg
  have htsum : |∑' k, f k| ≤ ∑' k, g k := by
    calc
      |∑' k, f k| = ‖∑' k, f k‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' k, ‖f k‖ := norm_tsum_le_tsum_norm hf.norm
      _ = ∑' k, |f k| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑' k, g k := habs
  have hfactor : 0 ≤ 2 / Real.sqrt (Real.pi * ε) := by positivity
  unfold gaussianPrimeTailContribution gaussianPrimeTailEnvelope
  simp only [gaussianPrimeTailSum]
  rw [abs_mul, abs_of_nonneg hfactor]
  exact mul_le_mul_of_nonneg_left htsum hfactor

/-- In the certificate comparison, the omitted tail can lose no more than
its zero-center envelope. -/
theorem gaussianPrimeTailContribution_sub_zero_le_envelope
    {ε : ℝ} (hε : 0 < ε) (cutoff : ℕ) (t : ℝ) :
    gaussianPrimeTailContribution ε t cutoff -
        gaussianPrimeTailContribution ε 0 cutoff ≤
      gaussianPrimeTailEnvelope ε cutoff := by
  have ht := (le_abs_self
    (gaussianPrimeTailContribution ε t cutoff)).trans
      (abs_gaussianPrimeTailContribution_le_envelope hε cutoff t)
  have hzero := gaussianPrimeTailContribution_zero_nonnegative hε cutoff
  linarith

/-! ## A parameter-uniform high-prime cutoff -/

/-- Fixed summable comparison tail, independent of the Gaussian width and
center. -/
def vonMangoldtDivSqTail (cutoff : ℕ) : ℝ :=
  ∑' k : ℕ,
    ArithmeticFunction.vonMangoldt (k + cutoff) /
      ((k + cutoff : ℕ) : ℝ) ^ 2

/-- The fixed comparison tail vanishes as the cutoff tends to infinity. -/
theorem tendsto_vonMangoldtDivSqTail_atTop :
    Tendsto vonMangoldtDivSqTail atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
  have hf : Summable f := summable_vonMangoldt_div_sq
  have hpartial := hf.tendsto_sum_tsum_nat
  have hdifference : Tendsto
      (fun cutoff : ℕ => (∑' n, f n) - ∑ n ∈ Finset.range cutoff, f n)
      atTop (𝓝 0) := by
    have hconstant : Tendsto (fun _ : ℕ => ∑' n, f n) atTop
        (𝓝 (∑' n, f n)) := tendsto_const_nhds
    simpa only [sub_self] using hconstant.sub hpartial
  apply hdifference.congr'
  filter_upwards with cutoff
  have hsplit := hf.sum_add_tsum_nat_add cutoff
  dsimp only [vonMangoldtDivSqTail, f]
  linarith

lemma gaussianPrimeSummand_zero_le_vonMangoldt_div_sq
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    (hlog : 8 * ε ≤ Real.log n) :
    gaussianPrimeSummand ε 0 n ≤
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hn1
  have hweight := gaussian_log_weight_le_inv_sq hε hn0 hlog
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := by positivity
  have hcoef0 : 0 ≤
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) :=
    div_nonneg hΛ0 (Real.sqrt_nonneg _)
  unfold gaussianPrimeSummand
  simp only [zero_mul, Real.cos_zero, mul_one]
  calc
    ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
          Real.exp (-(Real.log (n : ℝ)) ^ 2 / (4 * ε)) ≤
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) *
          (1 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hweight hcoef0
    _ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
      have hdiv : ArithmeticFunction.vonMangoldt n /
          Real.sqrt (n : ℝ) ≤ ArithmeticFunction.vonMangoldt n := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_right hΛ0 (inv_le_one_of_one_le₀ hsqrt1)
      simpa [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right hdiv (inv_nonneg.mpr (sq_nonneg _))

/-- If the cutoff lies beyond the uniform threshold `log N ≥ 8 ε`, the
entire nonoscillatory Gaussian tail is bounded by a width-independent
summable tail. -/
theorem gaussianPrimeTailEnvelope_le_vonMangoldtDivSqTail
    {ε : ℝ} (hε : 0 < ε) {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hlog : 8 * ε ≤ Real.log cutoff) :
    gaussianPrimeTailEnvelope ε cutoff ≤
      2 / Real.sqrt (Real.pi * ε) * vonMangoldtDivSqTail cutoff := by
  let f : ℕ → ℝ := fun k => gaussianPrimeSummand ε 0 (k + cutoff)
  let g : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt (k + cutoff) /
      ((k + cutoff : ℕ) : ℝ) ^ 2
  have hf : Summable f :=
    summable_gaussianPrimeTailSummand hε 0 cutoff
  have hg : Summable g := by
    exact (summable_nat_add_iff cutoff).2 summable_vonMangoldt_div_sq
  have hterm : ∀ k : ℕ, f k ≤ g k := by
    intro k
    have hkn : 0 < k + cutoff := Nat.add_pos_right k hcutoff
    have hcast : (cutoff : ℝ) ≤ (k + cutoff : ℕ) := by
      exact_mod_cast Nat.le_add_left cutoff k
    have hcutoffReal : 0 < (cutoff : ℝ) := by exact_mod_cast hcutoff
    have hlogMono : Real.log cutoff ≤ Real.log (k + cutoff : ℕ) :=
      Real.log_le_log hcutoffReal hcast
    exact gaussianPrimeSummand_zero_le_vonMangoldt_div_sq hε hkn
      (hlog.trans hlogMono)
  have hsum : (∑' k, f k) ≤ ∑' k, g k :=
    hf.tsum_le_tsum hterm hg
  have hfactor : 0 ≤ 2 / Real.sqrt (Real.pi * ε) := by positivity
  unfold gaussianPrimeTailEnvelope gaussianPrimeTailContribution
  simp only [gaussianPrimeTailSum, vonMangoldtDivSqTail]
  exact mul_le_mul_of_nonneg_left hsum hfactor

/-- Every width admits a natural-number cutoff satisfying the uniform
high-prime threshold. -/
theorem exists_gaussianPrimeTailCutoff (ε : ℝ) :
    ∃ cutoff : ℕ, 0 < cutoff ∧ 8 * ε ≤ Real.log cutoff := by
  obtain ⟨cutoff, hcutoff⟩ := exists_nat_gt (Real.exp (8 * ε))
  have hcutoffReal : 0 < (cutoff : ℝ) :=
    (Real.exp_pos (8 * ε)).trans hcutoff
  have hlog : 8 * ε < Real.log (cutoff : ℝ) :=
    (Real.lt_log_iff_exp_lt hcutoffReal).2 hcutoff
  exact ⟨cutoff, by exact_mod_cast hcutoffReal, hlog.le⟩

/-- The arithmetic model obtained by retaining only the channels below the
cutoff. -/
def gaussianArithmeticRetainedFormula
    (ε : ℝ) (cutoff : ℕ) (t : ℝ) : ℝ :=
  gaussianArchimedeanContribution ε t -
    gaussianPrimePartialContribution ε t cutoff

/-- The actual arithmetic explicit formula is exactly the retained model
minus the convergent omitted prime tail. -/
theorem gaussianArithmeticExplicitFormula_eq_retained_sub_tail
    {ε : ℝ} (hε : 0 < ε) (cutoff : ℕ) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      gaussianArithmeticRetainedFormula ε cutoff t -
        gaussianPrimeTailContribution ε t cutoff := by
  rw [gaussianArithmeticExplicitFormula, gaussianPrimeContribution,
    gaussianPrimeSum_eq_partial_add_tail hε]
  simp only [gaussianArithmeticRetainedFormula,
    gaussianPrimePartialContribution, gaussianPrimeTailContribution]
  ring

/-- Analytic obligations whose discharge makes one positive Gaussian width
kernel-checked.  `endpointMargin` is a lower bound for the full formula at
zero.  On the compact interval the retained low-channel model may not fall
below its zero value, while the omitted tail may lose at most `tailLoss`.
The endpoint margin covers that loss.  Beyond `compactRadius`, a direct bound
handles the full formula.

The epsilon `3/50` research certificate is intended to instantiate this with
`cutoff = 6`, `compactRadius = 15`, endpoint margin `1/100000`, and tail loss
`74/10000000`. -/
structure GaussianArithmeticWidthCertificate (ε : ℝ) where
  width_pos : 0 < ε
  cutoff : ℕ
  compactRadius : ℝ
  compactRadius_nonneg : 0 ≤ compactRadius
  endpointMargin : ℝ
  tailLoss : ℝ
  endpoint_lower :
    endpointMargin ≤ gaussianArithmeticExplicitFormula ε 0
  compact_retained_ge_zero :
    ∀ t : ℝ, 0 ≤ t → t ≤ compactRadius →
      gaussianArithmeticRetainedFormula ε cutoff 0 ≤
        gaussianArithmeticRetainedFormula ε cutoff t
  compact_tail_loss_le :
    ∀ t : ℝ, 0 ≤ t → t ≤ compactRadius →
      gaussianPrimeTailContribution ε t cutoff -
          gaussianPrimeTailContribution ε 0 cutoff ≤ tailLoss
  tailLoss_le_endpointMargin : tailLoss ≤ endpointMargin
  large_nonnegative :
    ∀ t : ℝ, compactRadius ≤ t →
      0 ≤ gaussianArithmeticExplicitFormula ε t

/-- Build the general soundness record from the natural, center-independent
absolute tail envelope. -/
def GaussianArithmeticWidthCertificate.ofTailEnvelope
    {ε : ℝ} (hε : 0 < ε) (cutoff : ℕ) (compactRadius : ℝ)
    (hcompactRadius : 0 ≤ compactRadius) (endpointMargin : ℝ)
    (hEndpoint :
      endpointMargin ≤ gaussianArithmeticExplicitFormula ε 0)
    (hRetained :
      ∀ t : ℝ, 0 ≤ t → t ≤ compactRadius →
        gaussianArithmeticRetainedFormula ε cutoff 0 ≤
          gaussianArithmeticRetainedFormula ε cutoff t)
    (hEnvelope :
      gaussianPrimeTailEnvelope ε cutoff ≤ endpointMargin)
    (hLarge :
      ∀ t : ℝ, compactRadius ≤ t →
        0 ≤ gaussianArithmeticExplicitFormula ε t) :
    GaussianArithmeticWidthCertificate ε where
  width_pos := hε
  cutoff := cutoff
  compactRadius := compactRadius
  compactRadius_nonneg := hcompactRadius
  endpointMargin := endpointMargin
  tailLoss := gaussianPrimeTailEnvelope ε cutoff
  endpoint_lower := hEndpoint
  compact_retained_ge_zero := hRetained
  compact_tail_loss_le := fun t _ _ =>
    gaussianPrimeTailContribution_sub_zero_le_envelope hε cutoff t
  tailLoss_le_endpointMargin := hEnvelope
  large_nonnegative := hLarge

/-- Soundness of a single width certificate against the actual convergent
arithmetic expression. -/
theorem GaussianArithmeticWidthCertificate.goodWidth
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε) :
    GaussianArithmeticGoodWidth ε := by
  refine ⟨certificate.width_pos, ?_⟩
  have hnonnegative_of_nonnegative_center :
      ∀ t : ℝ, 0 ≤ t →
        0 ≤ gaussianArithmeticExplicitFormula ε t := by
    intro t ht
    by_cases htCompact : t ≤ certificate.compactRadius
    · have hsplitZero :=
        gaussianArithmeticExplicitFormula_eq_retained_sub_tail
          certificate.width_pos certificate.cutoff 0
      have hsplit :=
        gaussianArithmeticExplicitFormula_eq_retained_sub_tail
          certificate.width_pos certificate.cutoff t
      have hretained :=
        certificate.compact_retained_ge_zero t ht htCompact
      have htail := certificate.compact_tail_loss_le t ht htCompact
      linarith [certificate.endpoint_lower,
        certificate.tailLoss_le_endpointMargin]
    · exact certificate.large_nonnegative t (le_of_not_ge htCompact)
  intro t
  by_cases ht : 0 ≤ t
  · exact hnonnegative_of_nonnegative_center t ht
  · rw [← gaussianArithmeticExplicitFormula_neg_center ε t]
    exact hnonnegative_of_nonnegative_center (-t) (by linarith)

/-- The logical target exposed by the soundness layer: certificates exist at
widths arbitrarily far to the right.  The intended way to prove this is a
single parameter-uniform constructor, not an endless chain of independently
enumerated finite certificates. -/
def GaussianArithmeticWidthCertificatesUnbounded : Prop :=
  ∀ B : ℝ, ∃ ε : ℝ, ∃ _certificate : GaussianArithmeticWidthCertificate ε,
    B < ε

/-- An unbounded family of sound certificates supplies the cofinal family of
good widths required by heat propagation. -/
theorem gaussianArithmeticGoodWidthsUnbounded_of_certificates
    (hCertificates : GaussianArithmeticWidthCertificatesUnbounded) :
    GaussianArithmeticGoodWidthsUnbounded := by
  intro B
  rcases hCertificates B with ⟨ε, certificate, hBε⟩
  exact ⟨ε, hBε, certificate.goodWidth⟩

/-- Exact endpoint of this certificate program: an unbounded family of these
analytic certificates would prove Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_gaussianArithmeticWidthCertificatesUnbounded
    (hCertificates : GaussianArithmeticWidthCertificatesUnbounded) :
    RiemannHypothesis :=
  gaussianArithmeticGoodWidthsUnbounded_iff_riemannHypothesis.mp
    (gaussianArithmeticGoodWidthsUnbounded_of_certificates hCertificates)

end

end RiemannGaussian
