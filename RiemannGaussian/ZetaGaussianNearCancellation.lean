/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SmoothedCotangentSource
import RiemannGaussian.ZetaGaussianDistanceRemainder

/-!
# Compensation of the complete nearby Gaussian-cotangent zeta source

Every nearby zero's possible negative blended source is paid for by its
own retained shifted Poisson mass. The complete complex decomposition is
proved before taking real parts. Consequently any selected nearby zero,
or finite group of them, survives in the full signed remainder bound.
No sign hypothesis on the unselected zeros, zero simplicity, or smoothed
prime identity is assumed. This closes the nearby compensation step only.
-/

namespace RiemannGaussian.ZetaGaussianNearCancellation
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open ZetaGaussianDistanceRemainder SmoothedCotangentSource
open CotangentRegularization (frequency)

/-- Restrict an original complex divisor carrier to the complete open nearby ball. -/
def nearRestrict (η : ℝ) (s : ℂ) (f : NontrivialZetaZero → ℂ)
    (ρ : NontrivialZetaZero) : ℂ := if ‖s - ρ.1‖ < η then f ρ else 0

/-- The complete nearby Gaussian-plus-cotangent source, with analytic multiplicity. -/
def nearSource (B η : ℝ) (s : ℂ) : NontrivialZetaZero → ℂ :=
  nearRestrict η s fun ρ => (analyticZetaZeroMultiplicity ρ : ℂ) *
    source (GaussianComplexHalfMoments.transform B) η (s - ρ.1)

/-- The literal cotangent correction at every nearby actual zero. -/
def nearCotangent (η : ℝ) (s : ℂ) : NontrivialZetaZero → ℂ :=
  nearRestrict η s fun ρ => (analyticZetaZeroMultiplicity ρ : ℂ) *
    (frequency η : ℂ) * Complex.cot ((frequency η : ℂ) * (s - ρ.1))

/-- One nearby source retains exactly the Poisson reserve paid by that same zero. -/
def compensated (B η : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) : ℝ :=
  (nearSource B η s ρ).re + (24 * B / η ^ 2) * nearPoisson η s ρ

/-- Every nearby restriction has actual finite divisor support, for any carrier. -/
theorem finite_support_nearRestrict (η : ℝ) (s : ℂ) (f : NontrivialZetaZero → ℂ) :
    (Function.support (nearRestrict η s f)).Finite := by
  have hf : {ρ : NontrivialZetaZero | |ρ.1.im| ≤ |s.im| + |η|}.Finite := by
    simpa only [zetaSpectralCoordinate_re] using
      spectralZetaZeroWindowSet_finite (by positivity : 0 ≤ |s.im| + |η|)
  apply hf.subset
  intro ρ hρ
  have hd : ‖s - ρ.1‖ < η := by
    by_contra hn
    exact hρ (by simp [nearRestrict, hn])
  have hi : |s.im - ρ.1.im| ≤ ‖s - ρ.1‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s - ρ.1)
  have ht : |ρ.1.im| ≤ |s.im - ρ.1.im| + |s.im| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (ρ.1.im - s.im) s.im
  change |ρ.1.im| ≤ |s.im| + |η|
  linarith [le_abs_self η]

/-- The complete nearby blended source is genuinely summable. -/
theorem summable_nearSource (B η : ℝ) (s : ℂ) : Summable (nearSource B η s) :=
  summable_of_hasFiniteSupport (finite_support_nearRestrict η s _)

/-- The literal nearby cotangent carrier is genuinely summable. -/
theorem summable_nearCotangent (η : ℝ) (s : ℂ) : Summable (nearCotangent η s) :=
  summable_of_hasFiniteSupport (finite_support_nearRestrict η s _)

/-- Before summation or loss of phase, the original remainder plus nearby
cotangent splits exactly into the blended nearby source and the far remainder. -/
theorem term_add_nearCotangent (B : ℝ) {η : ℝ} (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) :
    ZetaGaussianPoleRemainder.term B s ρ + nearCotangent η s ρ =
      nearSource B η s ρ + farTerm B η s ρ := by
  by_cases hd : ‖s - ρ.1‖ < η
  · have hz := Complex.ne_zero_of_re_pos (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ)
    simp only [nearCotangent, nearSource, nearRestrict, hd, if_true,
      farTerm, not_le.mpr hd, if_false, add_zero]
    rw [source_eq _ hη hz (by linarith)]
    simp only [ZetaGaussianPoleRemainder.term, GaussianLaplacePoleRemainder.remainder]
    ring
  · simp [nearCotangent, nearSource, nearRestrict, farTerm, hd, le_of_not_gt hd]

/-- Absolute convergence justifies the complete complex blended-source identity. -/
theorem tsum_term_add_nearCotangent {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) :
    (∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B s ρ) +
        (∑' ρ : NontrivialZetaZero, nearCotangent η s ρ) =
      (∑' ρ : NontrivialZetaZero, nearSource B η s ρ) +
        ∑' ρ : NontrivialZetaZero, farTerm B η s ρ := by
  rw [← (ZetaGaussianPoleRemainder.summable_term hB hs).tsum_add (summable_nearCotangent η s),
    ← (summable_nearSource B η s).tsum_add (summable_farTerm hB hη hs)]
  exact tsum_congr (term_add_nearCotangent B hη hs)

/-- Every actual zero's compensated contribution is nonnegative. The cubic
nearby cost is exactly canceled by its own multiplicity-weighted Poisson reserve. -/
theorem compensated_nonneg {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) : 0 ≤ compensated B η s ρ := by
  by_cases hd : ‖s - ρ.1‖ < η
  · have hg := gaussian_source_re_lower hB hη hd.le
      (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ).le
    have hm := mul_le_mul_of_nonneg_left hg
      (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
    have hp := mul_le_mul_of_nonneg_left (nearPoisson_lower hη hs ρ hd)
      (show 0 ≤ 24 * B / η ^ 2 by positivity)
    have he : (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (2 * η)) =
        (analyticZetaZeroMultiplicity ρ : ℝ) * (12 * B / η ^ 3) := by
      field_simp
      ring
    rw [he] at hp
    simp only [compensated, nearSource, nearRestrict, hd, if_true, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    linarith
  · simp [compensated, nearSource, nearRestrict, nearPoisson, hd]

/-- The exact nonnegative compensated carrier is summable over the full divisor. -/
theorem summable_compensated {η : ℝ} (hη : 0 < η) (B : ℝ)
    {s : ℂ} (hs : 1 ≤ s.re) : Summable (compensated B η s) :=
  (Complex.reCLM.summable (summable_nearSource B η s)).add
    ((summable_nearPoisson hη hs).mul_left _)

/-- The compensated total preserves the complete signed source and exact nearby reserve. -/
theorem tsum_compensated {η : ℝ} (hη : 0 < η) (B : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    (∑' ρ : NontrivialZetaZero, compensated B η s ρ) =
      (∑' ρ : NontrivialZetaZero, nearSource B η s ρ).re +
        (24 * B / η ^ 2) * ∑' ρ : NontrivialZetaZero, nearPoisson η s ρ := by
  have hr : Summable (fun ρ : NontrivialZetaZero => (nearSource B η s ρ).re) :=
    Complex.reCLM.summable (summable_nearSource B η s)
  simp only [compensated]
  rw [hr.tsum_add ((summable_nearPoisson hη hs).mul_left _),
    Complex.re_tsum (summable_nearSource B η s), tsum_mul_left]

/-- Every selected finite set retains its full compensated source in the complete total. -/
theorem sum_compensated_le {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (S : Finset NontrivialZetaZero) :
    (∑ ρ ∈ S, compensated B η s ρ) ≤ ∑' ρ : NontrivialZetaZero, compensated B η s ρ :=
  (summable_compensated hη B hs).sum_le_tsum S (fun ρ _ => compensated_nonneg hB hη hs ρ)

/-- The complete signed Gaussian-cotangent remainder retains any finite selected
source, after all other nearby losses are paid by their own Poisson reserves. -/
theorem neg_re_tsum_le_sub_sum {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (S : Finset NontrivialZetaZero) :
    -((∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B s ρ) +
        ∑' ρ : NontrivialZetaZero, nearCotangent η s ρ).re ≤
      (24 * B / η ^ 2) * (logDeriv riemannXi (s + (η : ℂ))).re -
        ∑ ρ ∈ S, compensated B η s ρ := by
  have hselected := sum_compensated_le hB hη hs S
  rw [tsum_compensated hη B hs] at hselected
  have htail := norm_tsum_farTerm_le_reserve hB hη hs
  have hreal := (Complex.abs_re_le_norm
    (∑' ρ : NontrivialZetaZero, farTerm B η s ρ)).trans htail
  rw [tsum_term_add_nearCotangent hB hη hs, Complex.add_re]
  linarith [neg_le_abs (∑' ρ : NontrivialZetaZero, farTerm B η s ρ).re]

/-- In particular, a selected zero survives with its exact compensated contribution. -/
theorem neg_re_tsum_le_sub_selected {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) :
    -((∑' τ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B s τ) +
        ∑' τ : NontrivialZetaZero, nearCotangent η s τ).re ≤
      (24 * B / η ^ 2) * (logDeriv riemannXi (s + (η : ℂ))).re -
        compensated B η s ρ := by
  simpa using neg_re_tsum_le_sub_sum hB hη hs {ρ}

/-- The exact source of a zero at its own ordinate, including its cotangent
correction, Gaussian transform and shifted Poisson contribution. -/
def alignedSource (B η : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity ρ : ℝ) *
    (GaussianFermiLaplaceOrder.halfGaussian B (1 - ρ.1.re) +
      frequency η * Real.cot (frequency η * (1 - ρ.1.re)) - 1 / (1 - ρ.1.re)) +
    (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (1 + η - ρ.1.re))

/-- A nearby selected zero's compensated carrier is exactly the stated real source. -/
theorem compensated_at_ordinate (B : ℝ) {η : ℝ} (hη : 0 < η)
    (ρ : NontrivialZetaZero) (hρ : 1 - ρ.1.re < η) :
    compensated B η (1 + I * ρ.1.im) ρ = alignedSource B η ρ := by
  have hu : 0 < 1 - ρ.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one ρ)
  have he : 1 + I * (ρ.1.im : ℂ) - ρ.1 = ((1 - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hd : ‖1 + I * (ρ.1.im : ℂ) - ρ.1‖ < η := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    exact hρ
  have hs : 1 + I * (ρ.1.im : ℂ) + (η : ℂ) = ((1 + η : ℝ) : ℂ) + I * ρ.1.im := by
    push_cast
    ring
  simp only [compensated, nearSource, nearRestrict, hd, if_true, nearPoisson,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [he, gaussian_source_real hη B hu (by linarith), hs,
    zetaGlobalPoissonSummand_at_ordinate ρ (by linarith : 1 ≤ 1 + η)]
  rfl

/-- The selected real Gaussian-cotangent source with its own reserve is nonnegative. -/
theorem alignedSource_nonneg {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    (ρ : NontrivialZetaZero) (hρ : 1 - ρ.1.re < η) : 0 ≤ alignedSource B η ρ := by
  rw [← compensated_at_ordinate B hη ρ hρ]
  exact compensated_nonneg hB hη (by simp) ρ

/-- A selected zero keeps its full half-Gaussian source up to an explicit
linear displacement loss, as well as its exact multiplicity-weighted reserve. -/
theorem alignedSource_lower (B : ℝ) {η : ℝ} (hη : 0 < η)
    (ρ : NontrivialZetaZero) (hρ : 1 - ρ.1.re ≤ η) :
    (analyticZetaZeroMultiplicity ρ : ℝ) *
        (GaussianFermiLaplaceOrder.halfGaussian B (1 - ρ.1.re) -
          Real.pi ^ 2 * (1 - ρ.1.re) / (8 * η ^ 2)) +
      (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (1 + η - ρ.1.re)) ≤
        alignedSource B η ρ := by
  have h := CotangentRegularization.scaled_cot_real_lower hη
    (sub_pos.mpr (NontrivialZetaZero.re_lt_one ρ)) hρ
  unfold alignedSource
  apply add_le_add (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) le_rfl
  linarith

/-- At a selected zero's ordinate the complete signed remainder has a fully
elementary allowance minus that zero's exact source. Every other nearby-zero
sign and the complete far tail have been discharged unconditionally. -/
theorem neg_re_tsum_le_elementary_sub_source {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 4) (ρ : NontrivialZetaZero) (hρ : 1 - ρ.1.re < η) :
    -((∑' τ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B (1 + I * ρ.1.im) τ) +
        ∑' τ : NontrivialZetaZero, nearCotangent η (1 + I * ρ.1.im) τ).re ≤
      (24 * B / η ^ 2) * poissonAllowance η ρ.1.im - alignedSource B η ρ := by
  have h := neg_re_tsum_le_sub_selected hB hη (s := 1 + I * ρ.1.im) (by simp) ρ
  rw [compensated_at_ordinate B hη ρ hρ] at h
  have hs : 1 + I * (ρ.1.im : ℂ) + (η : ℂ) = ((1 + η : ℝ) : ℂ) + I * ρ.1.im := by
    push_cast
    ring
  rw [hs] at h
  exact h.trans (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (re_logDeriv_shift_le hη hηsmall ρ.1.im) (by positivity)) _)

/-- The full signed remainder is bounded with no unevaluated cotangent:
the selected Gaussian mass costs only a proved linear displacement loss,
while the full shifted Poisson source remains subtractive. -/
theorem neg_re_tsum_le_elementary_gaussian_source {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 4) (ρ : NontrivialZetaZero) (hρ : 1 - ρ.1.re < η) :
    -((∑' τ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B (1 + I * ρ.1.im) τ) +
        ∑' τ : NontrivialZetaZero, nearCotangent η (1 + I * ρ.1.im) τ).re ≤
      (24 * B / η ^ 2) * poissonAllowance η ρ.1.im -
        ((analyticZetaZeroMultiplicity ρ : ℝ) *
          (GaussianFermiLaplaceOrder.halfGaussian B (1 - ρ.1.re) -
            Real.pi ^ 2 * (1 - ρ.1.re) / (8 * η ^ 2)) +
          (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (1 + η - ρ.1.re))) :=
  (neg_re_tsum_le_elementary_sub_source hB hη hηsmall ρ hρ).trans
    (sub_le_sub_left (alignedSource_lower B hη ρ hρ.le) _)

end
end RiemannGaussian.ZetaGaussianNearCancellation
