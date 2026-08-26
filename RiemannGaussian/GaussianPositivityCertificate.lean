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

/-- The final scalable certificate target: certificates exist at widths
arbitrarily far to the right. -/
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
