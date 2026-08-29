import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceQuadraticRigidity

/-!
# Complementary eta tilts and the horizontal defect

The moment bounds obtained from the fixed positive eta measure are vertical:
they constrain the ordinate of a zero.  This module exposes the first
genuinely horizontal structure.  The zeta functional equation reflects a zero
`sigma + I*y` to another zero `(1 - sigma) + I*y`.  Consequently the same
Fourier frequency annihilates the fixed eta measure at both complementary
exponential tilts.

Subtracting the two cancellations gives a horizontal-defect weight

`exp (-(1/2+a)t) - exp (-(1/2-a)t)`.

Lean proves its exact hyperbolic-sine factorization and proves that, when
`a != 0`, multiplication by `a` makes this weight strictly negative at every
positive support point.  Thus an off-critical zero produces simultaneous
cosine and sine cancellation for an explicit fixed-sign horizontal defect.
Ruling out that arithmetic cancellation is the new rigidity problem; it is
not ruled out in this module.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Difference between the two exponential tilts symmetric about `1/2`. -/
def pairedEtaHorizontalDefectWeight (a t : ℝ) : ℝ :=
  Real.exp (-(1 / 2 + a) * t) - Real.exp (-(1 / 2 - a) * t)

/-- The complementary-tilt difference is exactly an exponentially damped
hyperbolic sine. -/
theorem pairedEtaHorizontalDefectWeight_eq_sinh (a t : ℝ) :
    pairedEtaHorizontalDefectWeight a t =
      -2 * Real.exp (-t / 2) * Real.sinh (a * t) := by
  unfold pairedEtaHorizontalDefectWeight
  rw [show -(1 / 2 + a) * t = -t / 2 + -(a * t) by ring,
    show -(1 / 2 - a) * t = -t / 2 + a * t by ring,
    Real.exp_add, Real.exp_add, Real.sinh_eq]
  ring

/-- Away from the critical line, the horizontal displacement times its
defect weight is strictly negative at every positive time. -/
theorem mul_pairedEtaHorizontalDefectWeight_neg
    {a t : ℝ} (ha : a ≠ 0) (ht : 0 < t) :
    a * pairedEtaHorizontalDefectWeight a t < 0 := by
  rw [pairedEtaHorizontalDefectWeight_eq_sinh]
  have hasinh : 0 < a * Real.sinh (a * t) := by
    rcases lt_or_gt_of_ne ha with haNeg | haPos
    · exact mul_pos_of_neg_of_neg haNeg
        ((Real.sinh_neg_iff).2 (mul_neg_of_neg_of_pos haNeg ht))
    · exact mul_pos haPos
        ((Real.sinh_pos_iff).2 (mul_pos haPos ht))
  have hpositive : 0 < 2 * Real.exp (-t / 2) *
      (a * Real.sinh (a * t)) := by positivity
  calc
    a * (-2 * Real.exp (-t / 2) * Real.sinh (a * t)) =
        -(2 * Real.exp (-t / 2) *
          (a * Real.sinh (a * t))) := by ring
    _ < 0 := neg_lt_zero.mpr hpositive

/-- Cosine moment of the complementary-tilt horizontal defect. -/
def pairedEtaHorizontalDefectCosineMoment (a y : ℝ) : ℝ :=
  ∫ t : ℝ, pairedEtaHorizontalDefectWeight a t * Real.cos (y * t)
    ∂pairedEtaLogMeasure

/-- Sine moment of the complementary-tilt horizontal defect. -/
def pairedEtaHorizontalDefectSineMoment (a y : ℝ) : ℝ :=
  ∫ t : ℝ, pairedEtaHorizontalDefectWeight a t * Real.sin (y * t)
    ∂pairedEtaLogMeasure

/-- The horizontal-defect cosine kernel is integrable whenever both
complementary tilts are positive. -/
theorem integrable_pairedEtaHorizontalDefectCosineKernel
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    Integrable (fun t : ℝ =>
      pairedEtaHorizontalDefectWeight a t * Real.cos (y * t))
      pairedEtaLogMeasure := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hp : Integrable (fun t : ℝ =>
      Real.exp (-(1 / 2 + a) * t) * Real.cos (y * t))
      pairedEtaLogMeasure :=
    integrable_pairedEtaTiltedCosineKernel (1 / 2 + a) y hplus
  have hm : Integrable (fun t : ℝ =>
      Real.exp (-(1 / 2 - a) * t) * Real.cos (y * t))
      pairedEtaLogMeasure :=
    integrable_pairedEtaTiltedCosineKernel (1 / 2 - a) y hminus
  apply (hp.sub hm).congr
  filter_upwards with t
  change Real.exp (-(1 / 2 + a) * t) * Real.cos (y * t) -
      Real.exp (-(1 / 2 - a) * t) * Real.cos (y * t) =
    pairedEtaHorizontalDefectWeight a t * Real.cos (y * t)
  unfold pairedEtaHorizontalDefectWeight
  ring

/-- The horizontal-defect sine kernel is integrable whenever both
complementary tilts are positive. -/
theorem integrable_pairedEtaHorizontalDefectSineKernel
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    Integrable (fun t : ℝ =>
      pairedEtaHorizontalDefectWeight a t * Real.sin (y * t))
      pairedEtaLogMeasure := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hp : Integrable (fun t : ℝ =>
      Real.exp (-(1 / 2 + a) * t) * Real.sin (y * t))
      pairedEtaLogMeasure :=
    integrable_pairedEtaTiltedSineKernel (1 / 2 + a) y hplus
  have hm : Integrable (fun t : ℝ =>
      Real.exp (-(1 / 2 - a) * t) * Real.sin (y * t))
      pairedEtaLogMeasure :=
    integrable_pairedEtaTiltedSineKernel (1 / 2 - a) y hminus
  apply (hp.sub hm).congr
  filter_upwards with t
  change Real.exp (-(1 / 2 + a) * t) * Real.sin (y * t) -
      Real.exp (-(1 / 2 - a) * t) * Real.sin (y * t) =
    pairedEtaHorizontalDefectWeight a t * Real.sin (y * t)
  unfold pairedEtaHorizontalDefectWeight
  ring

/-- The horizontal-defect cosine moment is exactly the difference of the two
complementary tilted cosine moments. -/
theorem pairedEtaHorizontalDefectCosineMoment_eq_sub
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    pairedEtaHorizontalDefectCosineMoment a y =
      pairedEtaTiltedCosineMoment (1 / 2 + a) y -
        pairedEtaTiltedCosineMoment (1 / 2 - a) y := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hp :=
    integrable_pairedEtaTiltedCosineKernel (1 / 2 + a) y hplus
  have hm :=
    integrable_pairedEtaTiltedCosineKernel (1 / 2 - a) y hminus
  unfold pairedEtaHorizontalDefectCosineMoment
    pairedEtaTiltedCosineMoment
  calc
    (∫ t : ℝ, pairedEtaHorizontalDefectWeight a t * Real.cos (y * t)
        ∂pairedEtaLogMeasure) =
        ∫ t : ℝ,
          Real.exp (-(1 / 2 + a) * t) * Real.cos (y * t) -
            Real.exp (-(1 / 2 - a) * t) * Real.cos (y * t)
          ∂pairedEtaLogMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      unfold pairedEtaHorizontalDefectWeight
      ring
    _ = (∫ t : ℝ,
          Real.exp (-(1 / 2 + a) * t) * Real.cos (y * t)
          ∂pairedEtaLogMeasure) -
        ∫ t : ℝ,
          Real.exp (-(1 / 2 - a) * t) * Real.cos (y * t)
          ∂pairedEtaLogMeasure := integral_sub hp hm

/-- The horizontal-defect sine moment is exactly the difference of the two
complementary tilted sine moments. -/
theorem pairedEtaHorizontalDefectSineMoment_eq_sub
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    pairedEtaHorizontalDefectSineMoment a y =
      pairedEtaTiltedSineMoment (1 / 2 + a) y -
        pairedEtaTiltedSineMoment (1 / 2 - a) y := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hp :=
    integrable_pairedEtaTiltedSineKernel (1 / 2 + a) y hplus
  have hm :=
    integrable_pairedEtaTiltedSineKernel (1 / 2 - a) y hminus
  unfold pairedEtaHorizontalDefectSineMoment pairedEtaTiltedSineMoment
  calc
    (∫ t : ℝ, pairedEtaHorizontalDefectWeight a t * Real.sin (y * t)
        ∂pairedEtaLogMeasure) =
        ∫ t : ℝ,
          Real.exp (-(1 / 2 + a) * t) * Real.sin (y * t) -
            Real.exp (-(1 / 2 - a) * t) * Real.sin (y * t)
          ∂pairedEtaLogMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      unfold pairedEtaHorizontalDefectWeight
      ring
    _ = (∫ t : ℝ,
          Real.exp (-(1 / 2 + a) * t) * Real.sin (y * t)
          ∂pairedEtaLogMeasure) -
        ∫ t : ℝ,
          Real.exp (-(1 / 2 - a) * t) * Real.sin (y * t)
          ∂pairedEtaLogMeasure := integral_sub hp hm

/-- The functional-equation reflection gives exact cosine and sine
cancellation at the complementary tilt and the same Fourier frequency. -/
theorem pairedEtaTiltedMoments_eq_zero_at_complementary_tilt
    (rho : NontrivialZetaZero) :
    pairedEtaTiltedCosineMoment (1 - rho.1.re) rho.1.im = 0 ∧
      pairedEtaTiltedSineMoment (1 - rho.1.re) rho.1.im = 0 := by
  have h := pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero
    (NontrivialZetaZero.conjugatePartner rho)
  simpa [NontrivialZetaZero.conjugatePartner_coe] using h

/-- Every zeta zero therefore gives four exact cancellations: cosine and sine
at each of the two complementary positive tilts. -/
theorem pairedEtaTiltedMoments_eq_zero_at_both_complementary_tilts
    (rho : NontrivialZetaZero) :
    (pairedEtaTiltedCosineMoment rho.1.re rho.1.im = 0 ∧
      pairedEtaTiltedSineMoment rho.1.re rho.1.im = 0) ∧
    (pairedEtaTiltedCosineMoment (1 - rho.1.re) rho.1.im = 0 ∧
      pairedEtaTiltedSineMoment (1 - rho.1.re) rho.1.im = 0) := by
  exact ⟨pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero rho,
    pairedEtaTiltedMoments_eq_zero_at_complementary_tilt rho⟩

/-- Subtracting the complementary cancellations makes both horizontal-defect
Fourier moments vanish exactly. -/
theorem pairedEtaHorizontalDefectMoments_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaHorizontalDefectCosineMoment
        (rho.1.re - 1 / 2) rho.1.im = 0 ∧
      pairedEtaHorizontalDefectSineMoment
        (rho.1.re - 1 / 2) rho.1.im = 0 := by
  have hrePos := NontrivialZetaZero.zero_lt_re rho
  have hreLt := NontrivialZetaZero.re_lt_one rho
  have ha : |rho.1.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hboth := pairedEtaTiltedMoments_eq_zero_at_both_complementary_tilts rho
  have hplus : 1 / 2 + (rho.1.re - 1 / 2) = rho.1.re := by ring
  have hminus : 1 / 2 - (rho.1.re - 1 / 2) = 1 - rho.1.re := by ring
  constructor
  · rw [pairedEtaHorizontalDefectCosineMoment_eq_sub ha, hplus, hminus,
      hboth.1.1, hboth.2.1, sub_zero]
  · rw [pairedEtaHorizontalDefectSineMoment_eq_sub ha, hplus, hminus,
      hboth.1.2, hboth.2.2, sub_zero]

/-- An off-critical zero yields a fixed-sign horizontal-defect weight whose
cosine and sine transforms nevertheless both vanish.  This is the literal
horizontal rigidity certificate left for the arithmetic argument. -/
theorem nontrivialZetaZero_offCritical_etaHorizontalDefect_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    (pairedEtaHorizontalDefectCosineMoment
        (rho.1.re - 1 / 2) rho.1.im = 0 ∧
      pairedEtaHorizontalDefectSineMoment
        (rho.1.re - 1 / 2) rho.1.im = 0) ∧
      ∀ t ∈ pairedEtaLogSupport,
        (rho.1.re - 1 / 2) *
          pairedEtaHorizontalDefectWeight (rho.1.re - 1 / 2) t < 0 := by
  refine ⟨pairedEtaHorizontalDefectMoments_eq_zero_of_nontrivialZetaZero rho,
    ?_⟩
  intro t ht
  exact mul_pairedEtaHorizontalDefectWeight_neg
    (sub_ne_zero.mpr hoff)
    (pairedEtaLogSupport_subset_Ioi_zero ht)

/-- The sign-normalized horizontal defect.  For nonzero horizontal
displacement this is strictly positive on the complete eta support. -/
def pairedEtaPositiveHorizontalDefectDensity (a t : ℝ) : ℝ :=
  -a * pairedEtaHorizontalDefectWeight a t

/-- The sign-normalized horizontal defect is strictly positive at every
positive time when the horizontal displacement is nonzero. -/
theorem pairedEtaPositiveHorizontalDefectDensity_pos
    {a t : ℝ} (ha : a ≠ 0) (ht : 0 < t) :
    0 < pairedEtaPositiveHorizontalDefectDensity a t := by
  unfold pairedEtaPositiveHorizontalDefectDensity
  rw [neg_mul]
  exact neg_pos.mpr (mul_pairedEtaHorizontalDefectWeight_neg ha ht)

/-- Cosine moment of the positive horizontal-defect density. -/
def pairedEtaPositiveHorizontalDefectCosineMoment (a y : ℝ) : ℝ :=
  ∫ t : ℝ,
    pairedEtaPositiveHorizontalDefectDensity a t * Real.cos (y * t)
    ∂pairedEtaLogMeasure

/-- Sine moment of the positive horizontal-defect density. -/
def pairedEtaPositiveHorizontalDefectSineMoment (a y : ℝ) : ℝ :=
  ∫ t : ℝ,
    pairedEtaPositiveHorizontalDefectDensity a t * Real.sin (y * t)
    ∂pairedEtaLogMeasure

/-- The positive horizontal-defect cosine moment is the sign-normalized
complementary-tilt difference. -/
theorem pairedEtaPositiveHorizontalDefectCosineMoment_eq
    (a y : ℝ) :
    pairedEtaPositiveHorizontalDefectCosineMoment a y =
      -a * pairedEtaHorizontalDefectCosineMoment a y := by
  unfold pairedEtaPositiveHorizontalDefectCosineMoment
    pairedEtaHorizontalDefectCosineMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold pairedEtaPositiveHorizontalDefectDensity
  ring

/-- The positive horizontal-defect sine moment is the sign-normalized
complementary-tilt difference. -/
theorem pairedEtaPositiveHorizontalDefectSineMoment_eq
    (a y : ℝ) :
    pairedEtaPositiveHorizontalDefectSineMoment a y =
      -a * pairedEtaHorizontalDefectSineMoment a y := by
  unfold pairedEtaPositiveHorizontalDefectSineMoment
    pairedEtaHorizontalDefectSineMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold pairedEtaPositiveHorizontalDefectDensity
  ring

/-- An off-critical zeta zero yields an explicit strictly positive density on
the complete eta support whose cosine and sine moments both vanish at the
zero's ordinate. -/
theorem nontrivialZetaZero_offCritical_etaPositiveHorizontalDefect_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    (pairedEtaPositiveHorizontalDefectCosineMoment
        (rho.1.re - 1 / 2) rho.1.im = 0 ∧
      pairedEtaPositiveHorizontalDefectSineMoment
        (rho.1.re - 1 / 2) rho.1.im = 0) ∧
      ∀ t ∈ pairedEtaLogSupport,
        0 < pairedEtaPositiveHorizontalDefectDensity
          (rho.1.re - 1 / 2) t := by
  have hzero :=
    pairedEtaHorizontalDefectMoments_eq_zero_of_nontrivialZetaZero rho
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pairedEtaPositiveHorizontalDefectCosineMoment_eq, hzero.1,
      mul_zero]
  · rw [pairedEtaPositiveHorizontalDefectSineMoment_eq, hzero.2,
      mul_zero]
  · intro t ht
    exact pairedEtaPositiveHorizontalDefectDensity_pos
      (sub_ne_zero.mpr hoff)
      (pairedEtaLogSupport_subset_Ioi_zero ht)

end

end RiemannGaussian
