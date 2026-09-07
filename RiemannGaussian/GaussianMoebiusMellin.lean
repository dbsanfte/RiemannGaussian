import RiemannGaussian.GaussianMellinVertical
import RiemannGaussian.ZetaReciprocalDirichlet
import RiemannGaussian.ZetaReciprocalGaussianContour

/-!
# The exact Gaussian Möbius sum and its full reciprocal integral

Every positive heat time gives a convergent Gaussian sum of the actual
Möbius coefficients. Absolute integrals of the original complex Dirichlet
terms form a summable series, justifying the full sum--integral exchange.
The resulting identity holds at every abscissa greater than one, including
the moving line in the checked reciprocal contour.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The actual signed logarithmic Gaussian Möbius summand; its zeroth term vanishes. -/
def gaussianMoebiusSummand (a tau : ℝ) (n : ℕ) : ℝ :=
  (μ n : ℤ) * Real.exp (-(a - Real.log n) ^ 2 / (4 * tau))

/-- The full signed Gaussian sum of the original Möbius coefficients. -/
def gaussianMoebiusSum (a tau : ℝ) : ℝ := ∑' n : ℕ, gaussianMoebiusSummand a tau n

/-- Each original Dirichlet term retains its full complex phase on the vertical contour. -/
def gaussianMoebiusMellinTerm (a tau sigma : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
    (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2) *
      LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) ((sigma : ℂ) + (t : ℂ) * I) n

/-- The exact displacement phase of every Möbius Mellin term, including the vanishing zero index. -/
theorem gaussianMoebiusMellinTerm_eq_atom (a tau sigma : ℝ) (n : ℕ) (t : ℝ) :
    gaussianMoebiusMellinTerm a tau sigma n t = ((μ n : ℤ) : ℂ) *
      Complex.exp (((a - Real.log n : ℝ) : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
        (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2) := by
  by_cases hn : n = 0
  · subst n
    simp [gaussianMoebiusMellinTerm]
  rw [gaussianMoebiusMellinTerm, moebius_LSeries_term_eq_exp _ hn]
  rw [← mul_assoc, mul_comm _ (((μ n : ℤ) : ℂ)), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every actual Gaussian Dirichlet term is integrable on the entire vertical line. -/
theorem integrable_gaussianMoebiusMellinTerm (a sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    Integrable (gaussianMoebiusMellinTerm a tau sigma n) := by
  change Integrable (fun t : ℝ ↦ gaussianMoebiusMellinTerm a tau sigma n t)
  simp_rw [gaussianMoebiusMellinTerm_eq_atom]
  exact (integrable_gaussianMellin_vertical (a - Real.log n) sigma htau).const_mul _

/-- Integrating an actual complex Dirichlet term gives its signed Gaussian Möbius coefficient with exact normalization. -/
theorem integral_gaussianMoebiusMellinTerm (a sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    (∫ t : ℝ, gaussianMoebiusMellinTerm a tau sigma n t) =
      ((Real.sqrt (Real.pi / tau) * gaussianMoebiusSummand a tau n : ℝ) : ℂ) := by
  simp_rw [gaussianMoebiusMellinTerm_eq_atom]
  rw [integral_const_mul, integral_gaussianMellin_vertical _ _ htau]
  unfold gaussianMoebiusSummand
  push_cast
  ring

/-- The exact norm of a Dirichlet term separates its summable arithmetic mass and Gaussian ordinate factor. -/
theorem norm_gaussianMoebiusMellinTerm (a tau sigma : ℝ) (n : ℕ) (t : ℝ) :
    ‖gaussianMoebiusMellinTerm a tau sigma n t‖ =
      (Real.exp (a * sigma + tau * sigma ^ 2) * Real.exp (-tau * t ^ 2)) *
        ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) (sigma : ℂ) n‖ := by
  rw [gaussianMoebiusMellinTerm, norm_mul, norm_gaussianMellin_vertical,
    norm_moebius_LSeries_term_vertical]

/-- The series of evaluated norm integrals converges; positive-time integrability is established separately above. -/
theorem summable_integral_norm_gaussianMoebiusMellinTerm (a : ℝ) {tau sigma : ℝ}
    (hsigma : 1 < sigma) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖gaussianMoebiusMellinTerm a tau sigma n t‖) := by
  have h := (summable_moebiusDirichletMass hsigma).mul_left
    (Real.exp (a * sigma + tau * sigma ^ 2) * Real.sqrt (Real.pi / tau))
  refine h.congr fun n ↦ ?_
  simp_rw [norm_gaussianMoebiusMellinTerm]
  rw [integral_mul_const, integral_const_mul, integral_gaussian]

/-- The genuine reciprocal Gaussian kernel is the full complex Dirichlet sum, with no omitted terms. -/
theorem zetaReciprocalGaussianKernel_eq_tsum_moebius (a tau : ℝ) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, gaussianMoebiusMellinTerm a tau sigma n t := by
  rw [zetaReciprocalGaussianKernel,
    zetaReciprocalExtension_eq_moebius_LSeries (by simpa using hsigma)]
  exact tsum_mul_left.symm

/-- A proved integrable Gaussian envelope bounds the actual reciprocal kernel on the whole right line. -/
theorem norm_zetaReciprocalGaussianKernel_le_dirichlet (a tau : ℝ) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    ‖zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      (Real.exp (a * sigma + tau * sigma ^ 2) * Real.exp (-tau * t ^ 2)) *
        moebiusDirichletMass sigma := by
  rw [zetaReciprocalGaussianKernel, norm_mul, norm_gaussianMellin_vertical]
  exact mul_le_mul_of_nonneg_left (norm_zetaReciprocalExtension_le_moebiusDirichletMass hsigma t)
    (by positivity)

/-- The full actual reciprocal Gaussian kernel is integrable, not just its individual Dirichlet terms. -/
theorem integrable_zetaReciprocalGaussianKernel_vertical (a : ℝ) {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 1 < sigma) :
    Integrable (fun t : ℝ ↦ zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)) := by
  have hg := ((integrable_exp_neg_mul_sq htau).const_mul
    (Real.exp (a * sigma + tau * sigma ^ 2))).mul_const (moebiusDirichletMass sigma)
  refine hg.mono' ?_ (Filter.Eventually.of_forall (norm_zetaReciprocalGaussianKernel_le_dirichlet a tau hsigma))
  simp_rw [zetaReciprocalGaussianKernel_eq_tsum_moebius a tau hsigma]
  exact AEStronglyMeasurable.tsum fun n ↦ (integrable_gaussianMoebiusMellinTerm a sigma htau n).aestronglyMeasurable

/-- The actual signed Gaussian Möbius series converges absolutely for every positive heat time. -/
theorem summable_gaussianMoebiusSummand (a : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Summable (gaussianMoebiusSummand a tau) := by
  have h := (hasSum_integral_of_summable_integral_norm
    (integrable_gaussianMoebiusMellinTerm a 2 htau)
    (summable_integral_norm_gaussianMoebiusMellinTerm a (by norm_num : (1 : ℝ) < 2))).summable
  simp_rw [integral_gaussianMoebiusMellinTerm a 2 htau, Complex.ofReal_mul] at h
  have hc : (Real.sqrt (Real.pi / tau) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos Real.pi_pos htau)).ne'
  exact Complex.summable_ofReal.mp ((summable_mul_left_iff hc).mp h)

/-- The full reciprocal contour integral equals the actual convergent Gaussian Möbius sum, with every exchange justified. -/
theorem integral_zetaReciprocalGaussianKernel_eq_gaussianMoebiusSum (a : ℝ) {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 1 < sigma) :
    (∫ t : ℝ, zetaReciprocalGaussianKernel a tau ((sigma : ℂ) + (t : ℂ) * I)) =
      ((Real.sqrt (Real.pi / tau) * gaussianMoebiusSum a tau : ℝ) : ℂ) := by
  simp_rw [zetaReciprocalGaussianKernel_eq_tsum_moebius a tau hsigma]
  rw [← integral_tsum_of_summable_integral_norm
    (integrable_gaussianMoebiusMellinTerm a sigma htau)
    (summable_integral_norm_gaussianMoebiusMellinTerm a hsigma)]
  simp_rw [integral_gaussianMoebiusMellinTerm a sigma htau, Complex.ofReal_mul]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  rfl

end

end RiemannGaussian
