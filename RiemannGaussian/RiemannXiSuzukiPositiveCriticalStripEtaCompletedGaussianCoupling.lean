import RiemannGaussian.GaussianHeat
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletedSymmetry
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure

/-!
# Completed Gaussian coupling for the positive eta Laplace measure

The raw positive eta Laplace Gram profile is not invariant under
`sigma ↔ 1 - sigma`.  This module inserts the exact completion forced by xi,
rather than postulating a symmetric normalization.

The resulting pointwise energy is the squared norm of the genuine xi
function.  Xi's functional equation and conjugation symmetry therefore give
an exact complementary-tilt identity between two explicit sums of squares of
Fourier moments of the same positive arithmetic measure.  Gaussian-weighted
finite windows inherit that identity and remain genuine nonnegative,
integrable quantities.

This is a symmetry-aware coupling interface, not a zero-location theorem.
At a zero both moment energies vanish, so an additional eta-specific
coercivity or phase estimate is still required.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The exact completion weight multiplying the squared norm of the positive
eta Laplace partition. -/
def pairedEtaCompletedLaplaceWeight (s : ℂ) : ℝ :=
  Complex.normSq (pairedEtaXiCompletionFactor s * s)

/-- The completion-weighted positive-Laplace energy. -/
def pairedEtaCompletedLaplaceEnergy (s : ℂ) : ℝ :=
  pairedEtaCompletedLaplaceWeight s *
    Complex.normSq (pairedEtaLaplacePartition s)

/-- The completed positive-Laplace energy is nonnegative at every complex
parameter. -/
theorem pairedEtaCompletedLaplaceEnergy_nonneg (s : ℂ) :
    0 ≤ pairedEtaCompletedLaplaceEnergy s := by
  exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- In the positive half-plane, the completed positive-Laplace energy is
exactly the squared norm of completed paired eta. -/
theorem pairedEtaCompletedLaplaceEnergy_eq_normSq_completedXi
    {s : ℂ} (hspos : 0 < s.re) :
    pairedEtaCompletedLaplaceEnergy s =
      Complex.normSq (pairedEtaCompletedXi s) := by
  unfold pairedEtaCompletedXi
  rw [pairedEtaCore_eq_mul_laplacePartition hspos]
  unfold pairedEtaCompletedLaplaceEnergy pairedEtaCompletedLaplaceWeight
  simp only [Complex.normSq_mul]
  ring

/-- The completed energy is literally the squared norm of the completed
factor times the transform of the fixed positive arithmetic measure. -/
theorem pairedEtaCompletedLaplaceEnergy_eq_normSq_integral
    {s : ℂ} (hspos : 0 < s.re) :
    pairedEtaCompletedLaplaceEnergy s =
      Complex.normSq
        ((pairedEtaXiCompletionFactor s * s) *
          ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) := by
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hspos]
  unfold pairedEtaCompletedLaplaceEnergy pairedEtaCompletedLaplaceWeight
  simp only [Complex.normSq_mul]

/-- Throughout the open critical strip, the completed positive-Laplace
energy is exactly the squared norm of the genuine entire xi normalization. -/
theorem pairedEtaCompletedLaplaceEnergy_eq_normSq_riemannXi
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaCompletedLaplaceEnergy s = Complex.normSq (riemannXi s) := by
  rw [pairedEtaCompletedLaplaceEnergy_eq_normSq_completedXi hspos,
    pairedEtaCompletedXi_eq_riemannXi hspos hslt]

/-- The completion weight is strictly positive throughout the open critical
strip. -/
theorem pairedEtaCompletedLaplaceWeight_pos
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    0 < pairedEtaCompletedLaplaceWeight s := by
  unfold pairedEtaCompletedLaplaceWeight
  apply Complex.normSq_pos.mpr
  exact mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero hspos hslt)
    (by
      intro hs
      subst s
      norm_num at hspos)

/-- In the open critical strip, vanishing of the positive-Laplace energy is
exactly vanishing of xi. -/
theorem pairedEtaCompletedLaplaceEnergy_eq_zero_iff_riemannXi_eq_zero
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaCompletedLaplaceEnergy s = 0 ↔ riemannXi s = 0 := by
  rw [pairedEtaCompletedLaplaceEnergy_eq_normSq_riemannXi hspos hslt,
    Complex.normSq_eq_zero]

/-- The completed energy has the exact complementary symmetry dictated by
xi's functional equation and real structure. -/
theorem pairedEtaCompletedLaplaceEnergy_one_sub_conj
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaCompletedLaplaceEnergy (1 - starRingEnd ℂ s) =
      pairedEtaCompletedLaplaceEnergy s := by
  have hpartnerPos : 0 < (1 - starRingEnd ℂ s).re := by
    simpa using (sub_pos.mpr hslt)
  have hpartnerLt : (1 - starRingEnd ℂ s).re < 1 := by
    simpa using (sub_lt_self (1 : ℝ) hspos)
  rw [pairedEtaCompletedLaplaceEnergy_eq_normSq_riemannXi
      hpartnerPos hpartnerLt,
    pairedEtaCompletedLaplaceEnergy_eq_normSq_riemannXi hspos hslt,
    riemannXi_one_sub, riemannXi_conj, Complex.normSq_conj]

/-- Reflection across the critical line preserves the ordinate in the
standard vertical-line coordinates. -/
theorem one_sub_conj_vertical (sigma y : ℝ) :
    (1 : ℂ) - starRingEnd ℂ
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
      ((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

/-- On a vertical line, the completed energy is the positive completion
weight times the sum of squares of the literal tilted cosine and sine moments
of the fixed eta measure. -/
theorem pairedEtaCompletedLaplaceEnergy_vertical_eq_tiltedMoments
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
      pairedEtaCompletedLaplaceWeight
          ((sigma : ℂ) + (y : ℂ) * Complex.I) *
        (pairedEtaTiltedCosineMoment sigma y ^ 2 +
          pairedEtaTiltedSineMoment sigma y ^ 2) := by
  unfold pairedEtaCompletedLaplaceEnergy
  rw [pairedEtaLaplacePartition_eq_cosine_sub_I_sine sigma y hsigma]
  congr 1
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The actual xi completion couples the squared tilted Fourier moments of
the same positive eta measure at `sigma` and `1 - sigma`, pointwise in the
common ordinate. -/
theorem pairedEtaCompletedTiltedMomentEnergy_complementary
    (sigma y : ℝ) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    pairedEtaCompletedLaplaceWeight
          (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
        (pairedEtaTiltedCosineMoment (1 - sigma) y ^ 2 +
          pairedEtaTiltedSineMoment (1 - sigma) y ^ 2) =
      pairedEtaCompletedLaplaceWeight
          ((sigma : ℂ) + (y : ℂ) * Complex.I) *
        (pairedEtaTiltedCosineMoment sigma y ^ 2 +
          pairedEtaTiltedSineMoment sigma y ^ 2) := by
  have hsym := pairedEtaCompletedLaplaceEnergy_one_sub_conj
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I)
    (by simpa using hsigma) (by simpa using hsigmaOne)
  rw [one_sub_conj_vertical] at hsym
  rw [pairedEtaCompletedLaplaceEnergy_vertical_eq_tiltedMoments
      (1 - sigma) y (sub_pos.mpr hsigmaOne),
    pairedEtaCompletedLaplaceEnergy_vertical_eq_tiltedMoments
      sigma y hsigma] at hsym
  exact hsym

/-- A finite Gaussian window of the completion-weighted positive eta Laplace
energy on a vertical line. -/
def pairedEtaCompletedLaplaceGaussianWindowEnergy
    (sigma tau x lower upper : ℝ) : ℝ :=
  ∫ y : ℝ in lower..upper,
    translatedGaussian tau x y *
      pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I)

/-- In the open critical strip, the completed eta Gaussian-window integrand
is genuinely interval-integrable. -/
theorem intervalIntegrable_pairedEtaCompletedLaplaceGaussianWindowEnergy
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (tau x lower upper : ℝ) :
    IntervalIntegrable (fun y : ℝ ↦
      translatedGaussian tau x y *
        pairedEtaCompletedLaplaceEnergy
          ((sigma : ℂ) + (y : ℂ) * Complex.I))
      volume lower upper := by
  have hline : Continuous (fun y : ℝ ↦
      (sigma : ℂ) + (y : ℂ) * Complex.I) := by
    fun_prop
  have hxi : Continuous (fun y : ℝ ↦
      riemannXi ((sigma : ℂ) + (y : ℂ) * Complex.I)) :=
    differentiable_riemannXi.continuous.comp hline
  have hcontinuous : Continuous (fun y : ℝ ↦
      translatedGaussian tau x y *
        Complex.normSq
          (riemannXi ((sigma : ℂ) + (y : ℂ) * Complex.I))) := by
    have hgaussian : Continuous (fun y : ℝ ↦
        translatedGaussian tau x y) := by
      unfold translatedGaussian
      fun_prop
    exact hgaussian.mul (Complex.continuous_normSq.comp hxi)
  apply (hcontinuous.intervalIntegrable lower upper).congr_ae
  filter_upwards with y
  rw [pairedEtaCompletedLaplaceEnergy_eq_normSq_riemannXi
    (by simpa using hsigma) (by simpa using hsigmaOne)]

/-- Every completed eta Gaussian window in the open strip is exactly the
corresponding finite Gaussian window of the genuine xi squared norm. -/
theorem pairedEtaCompletedLaplaceGaussianWindowEnergy_eq_riemannXi
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (tau x lower upper : ℝ) :
    pairedEtaCompletedLaplaceGaussianWindowEnergy
        sigma tau x lower upper =
      ∫ y : ℝ in lower..upper,
        translatedGaussian tau x y *
          Complex.normSq
            (riemannXi ((sigma : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold pairedEtaCompletedLaplaceGaussianWindowEnergy
  apply intervalIntegral.integral_congr
  intro y _hy
  change translatedGaussian tau x y *
      pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
    translatedGaussian tau x y *
      Complex.normSq
        (riemannXi ((sigma : ℂ) + (y : ℂ) * Complex.I))
  rw [pairedEtaCompletedLaplaceEnergy_eq_normSq_riemannXi
    (by simpa using hsigma) (by simpa using hsigmaOne)]

/-- The completed Gaussian window is also a literal Gaussian average of the
completion-weighted squared cosine and sine moments of the fixed positive eta
measure. -/
theorem pairedEtaCompletedLaplaceGaussianWindowEnergy_eq_tiltedMoments
    (sigma tau x lower upper : ℝ) (hsigma : 0 < sigma) :
    pairedEtaCompletedLaplaceGaussianWindowEnergy
        sigma tau x lower upper =
      ∫ y : ℝ in lower..upper,
        translatedGaussian tau x y *
          (pairedEtaCompletedLaplaceWeight
              ((sigma : ℂ) + (y : ℂ) * Complex.I) *
            (pairedEtaTiltedCosineMoment sigma y ^ 2 +
              pairedEtaTiltedSineMoment sigma y ^ 2)) := by
  unfold pairedEtaCompletedLaplaceGaussianWindowEnergy
  apply intervalIntegral.integral_congr
  intro y _hy
  change translatedGaussian tau x y *
      pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
    translatedGaussian tau x y *
      (pairedEtaCompletedLaplaceWeight
          ((sigma : ℂ) + (y : ℂ) * Complex.I) *
        (pairedEtaTiltedCosineMoment sigma y ^ 2 +
          pairedEtaTiltedSineMoment sigma y ^ 2))
  rw [pairedEtaCompletedLaplaceEnergy_vertical_eq_tiltedMoments
    sigma y hsigma]

/-- Every ordered finite Gaussian window of the completed positive-Laplace
energy is nonnegative. -/
theorem pairedEtaCompletedLaplaceGaussianWindowEnergy_nonneg
    (sigma tau x : ℝ) {lower upper : ℝ} (hlower : lower ≤ upper) :
    0 ≤ pairedEtaCompletedLaplaceGaussianWindowEnergy
      sigma tau x lower upper := by
  unfold pairedEtaCompletedLaplaceGaussianWindowEnergy
  apply intervalIntegral.integral_nonneg hlower
  intro y _hy
  exact mul_nonneg (Real.exp_pos _).le
    (pairedEtaCompletedLaplaceEnergy_nonneg _)

/-- The genuine completion makes every finite eta Gaussian window exactly
symmetric under `sigma ↔ 1 - sigma`. -/
theorem pairedEtaCompletedLaplaceGaussianWindowEnergy_complementary
    (sigma tau x lower upper : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    pairedEtaCompletedLaplaceGaussianWindowEnergy
        (1 - sigma) tau x lower upper =
      pairedEtaCompletedLaplaceGaussianWindowEnergy
        sigma tau x lower upper := by
  unfold pairedEtaCompletedLaplaceGaussianWindowEnergy
  apply intervalIntegral.integral_congr
  intro y _hy
  change translatedGaussian tau x y *
      pairedEtaCompletedLaplaceEnergy
        (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
    translatedGaussian tau x y *
      pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I)
  congr 1
  rw [← one_sub_conj_vertical]
  exact pairedEtaCompletedLaplaceEnergy_one_sub_conj
    (by simpa using hsigma) (by simpa using hsigmaOne)

end

end RiemannGaussian
