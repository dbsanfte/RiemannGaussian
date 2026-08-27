import RiemannGaussian.RiemannXiBoundaryHeatResidues
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The boundary heat invariant as a reflected-pair Gaussian Gram norm

The positive fixed-time boundary heat residue is not a holomorphic
one-zero statistic: it couples a spectral zero with its reflection across
the real spectral axis.  This file supplies the exact two-zero analytic
object.  The oriented kernel

`-i * (alpha - beta) * exp (-tau * (x - alpha) * (x - beta))`

is entire jointly in the two zero variables.  On the actual zeta pair
`(alpha, conj alpha)` it becomes the positive boundary heat kernel.  It also
factors into the analytic half-Gaussians already used by the one-point
Gaussian explicit formula, with an explicit transverse damping factor.

Finally, the complete boundary invariant is realized as the squared norm of
an explicit zeta-indexed `ℓ²` feature vector.  Thus the reflected-pair
correlation, the spectral-xi boundary heat residue, and a genuine Hilbert
Gram diagonal are proved to be one and the same invariant.  This identifies
the precise two-point arithmetic/Suzuki object whose independent control is
needed at the current RH frontier.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The oriented jointly entire Gaussian kernel in two spectral-zero
variables. -/
def reflectedPairGaussianKernel
    (x tau : ℝ) (alpha beta : ℂ) : ℂ :=
  -Complex.I * (alpha - beta) *
    Complex.exp (-((tau : ℂ) *
      (((x : ℂ) - alpha) * ((x : ℂ) - beta))))

/-- The reflected-pair Gaussian kernel is entire jointly in both zero
variables. -/
theorem differentiable_reflectedPairGaussianKernel
    (x tau : ℝ) :
    Differentiable ℂ (fun p : ℂ × ℂ ↦
      reflectedPairGaussianKernel x tau p.1 p.2) := by
  unfold reflectedPairGaussianKernel
  fun_prop

/-- Exchanging the two reflected slots reverses the oriented kernel. -/
theorem reflectedPairGaussianKernel_swap
    (x tau : ℝ) (alpha beta : ℂ) :
    reflectedPairGaussianKernel x tau beta alpha =
      -reflectedPairGaussianKernel x tau alpha beta := by
  unfold reflectedPairGaussianKernel
  have hexponent :
      -((tau : ℂ) * (((x : ℂ) - beta) * ((x : ℂ) - alpha))) =
        -((tau : ℂ) * (((x : ℂ) - alpha) * ((x : ℂ) - beta))) := by
    ring
  rw [hexponent]
  ring

/-- Exact factorization through the two analytic half-Gaussians used by the
one-point Gaussian explicit formula. -/
theorem reflectedPairGaussianKernel_eq_halfGaussian_product
    (x tau : ℝ) (alpha beta : ℂ) :
    reflectedPairGaussianKernel x tau alpha beta =
      (-Complex.I * (alpha - beta) *
        Complex.exp (((tau / 2 : ℝ) : ℂ) * (alpha - beta) ^ 2)) *
      complexHalfGaussian tau x alpha *
      complexHalfGaussian tau x beta := by
  rw [reflectedPairGaussianKernel, complexHalfGaussian,
    complexHalfGaussian]
  rw [show
      (-Complex.I * (alpha - beta) *
          Complex.exp (((tau / 2 : ℝ) : ℂ) * (alpha - beta) ^ 2)) *
          Complex.exp (-(((tau / 2 : ℝ) : ℂ) * (alpha - (x : ℂ)) ^ 2)) *
          Complex.exp (-(((tau / 2 : ℝ) : ℂ) * (beta - (x : ℂ)) ^ 2)) =
        -Complex.I * (alpha - beta) *
          (Complex.exp (((tau / 2 : ℝ) : ℂ) * (alpha - beta) ^ 2) *
            Complex.exp (-(((tau / 2 : ℝ) : ℂ) * (alpha - (x : ℂ)) ^ 2)) *
            Complex.exp (-(((tau / 2 : ℝ) : ℂ) * (beta - (x : ℂ)) ^ 2))) by
      ring,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- On a conjugate pair the oriented entire kernel is the positive real
boundary heat kernel. -/
theorem reflectedPairGaussianKernel_conj
    (x tau : ℝ) (alpha : ℂ) :
    reflectedPairGaussianKernel x tau alpha (starRingEnd ℂ alpha) =
      (2 * alpha.im * Real.exp (-(Complex.normSq
        ((x : ℂ) - alpha) * tau)) : ℝ) := by
  rw [reflectedPairGaussianKernel]
  have hdiff : alpha - starRingEnd ℂ alpha =
      (2 * alpha.im : ℝ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have hprod : ((x : ℂ) - alpha) *
      ((x : ℂ) - starRingEnd ℂ alpha) =
      (Complex.normSq ((x : ℂ) - alpha) : ℂ) := by
    have hconj : starRingEnd ℂ ((x : ℂ) - alpha) =
        (x : ℂ) - starRingEnd ℂ alpha := by simp
    rw [Complex.normSq_eq_conj_mul_self]
    rw [hconj, mul_comm]
  rw [hdiff, hprod]
  have hexpArg : -((tau : ℂ) *
      (Complex.normSq ((x : ℂ) - alpha) : ℂ)) =
      ((-(Complex.normSq ((x : ℂ) - alpha) * tau) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexpArg, ← Complex.ofReal_exp]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Critical-line reflection supplies a genuine second zeta zero and turns
the entire pair kernel into the boundary heat kernel. -/
theorem reflectedPairGaussianKernel_conjugatePartner
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    reflectedPairGaussianKernel x tau
        (zetaSpectralCoordinate rho.1)
        (zetaSpectralCoordinate
          (NontrivialZetaZero.conjugatePartner rho).1) =
      (2 * (zetaSpectralCoordinate rho.1).im *
        Real.exp (-(Complex.normSq
          ((x : ℂ) - zetaSpectralCoordinate rho.1) * tau)) : ℝ) := by
  rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
  exact reflectedPairGaussianKernel_conj x tau
    (zetaSpectralCoordinate rho.1)

/-- The oriented two-zero statistic over an actual zeta zero and its
critical-line-reflected zeta partner. -/
def zetaUpperReflectedPairGaussianSummand
    (x tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℂ) *
      reflectedPairGaussianKernel x tau
        (zetaSpectralCoordinate rho.1)
        (zetaSpectralCoordinate
          (NontrivialZetaZero.conjugatePartner rho).1)
  else 0

/-- The matched two-zero Gaussian statistic is exactly the complex boundary
heat residue, term by term. -/
theorem zetaUpperReflectedPairGaussianSummand_eq_boundaryHeatResidue
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperReflectedPairGaussianSummand x tau rho =
      riemannXiUpperHyperbolicBoundaryHeatResidue x tau rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperReflectedPairGaussianSummand, if_pos hupper,
      riemannXiUpperHyperbolicBoundaryHeatResidue,
      zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper,
      reflectedPairGaussianKernel_conjugatePartner]
    push_cast
    ring
  · rw [zetaUpperReflectedPairGaussianSummand, if_neg hupper,
      riemannXiUpperHyperbolicBoundaryHeatResidue,
      zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]
    rfl

/-- The complete matched reflected-pair statistic is summable at positive
proper time. -/
theorem summable_zetaUpperReflectedPairGaussianSummand
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Summable (zetaUpperReflectedPairGaussianSummand x tau) := by
  exact
    (hasSum_riemannXiUpperHyperbolicBoundaryHeatResidue x htau).summable.congr
      (fun rho ↦
        (zetaUpperReflectedPairGaussianSummand_eq_boundaryHeatResidue
          x tau rho).symm)

/-- The complete actual-zero-pair Gaussian correlation. -/
def riemannXiUpperReflectedPairGaussianTotal
    (x tau : ℝ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperReflectedPairGaussianSummand x tau rho

/-- The matched two-zero correlation is the complete complex boundary heat
residue total. -/
theorem riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal
    (x tau : ℝ) :
    riemannXiUpperReflectedPairGaussianTotal x tau =
      riemannXiUpperHyperbolicBoundaryHeatResidueTotal x tau := by
  unfold riemannXiUpperReflectedPairGaussianTotal
  apply tsum_congr
  exact zetaUpperReflectedPairGaussianSummand_eq_boundaryHeatResidue x tau

/-- Vanishing of the complete matched actual-zero-pair Gaussian correlation
is equivalent to RH. -/
theorem riemannXiUpperReflectedPairGaussianTotal_eq_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperReflectedPairGaussianTotal x tau = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal
    x tau]
  exact
    riemannXiUpperHyperbolicBoundaryHeatResidueTotal_eq_zero_iff_rh
      x htau

/-- The reflected heat factor is a transversely damped Gram diagonal of the
analytic half-Gaussian used in the one-point explicit formula. -/
theorem boundaryHeatKernel_eq_transverse_mul_normSq_halfGaussian
    (x tau : ℝ) (alpha : ℂ) :
    2 * alpha.im * Real.exp (-(Complex.normSq
        ((x : ℂ) - alpha) * tau)) =
      (2 * alpha.im * Real.exp (-2 * tau * alpha.im ^ 2)) *
        Complex.normSq (complexHalfGaussian tau x alpha) := by
  have hnormHalf :
      Complex.normSq (complexHalfGaussian tau x alpha) =
        ‖complexTranslatedGaussian tau x alpha‖ := by
    rw [Complex.normSq_eq_norm_sq,
      complexTranslatedGaussian_eq_half_mul_half, norm_mul]
    ring
  rw [hnormHalf, norm_complexTranslatedGaussian,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
    Complex.ofReal_im, zero_sub]
  rw [show
      (2 * alpha.im * Real.exp (-2 * tau * alpha.im ^ 2)) *
          Real.exp (tau * alpha.im ^ 2 - tau * (alpha.re - x) ^ 2) =
        2 * alpha.im *
          (Real.exp (-2 * tau * alpha.im ^ 2) *
            Real.exp (tau * alpha.im ^ 2 - tau * (alpha.re - x) ^ 2)) by
      ring,
    ← Real.exp_add]
  congr 1
  ring_nf

/-- Positive transverse weight multiplying the analytic half-Gaussian at one
upper spectral zero. -/
def zetaUpperBoundaryGaussianTransverseWeight
    (tau : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (2 * (zetaSpectralCoordinate rho.1).im *
        Real.exp (-2 * tau * (zetaSpectralCoordinate rho.1).im ^ 2))
  else 0

/-- Every upper-zero transverse Gaussian weight is nonnegative. -/
theorem zetaUpperBoundaryGaussianTransverseWeight_nonneg
    (tau : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperBoundaryGaussianTransverseWeight tau rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBoundaryGaussianTransverseWeight, if_pos hupper]
    positivity
  · rw [zetaUpperBoundaryGaussianTransverseWeight, if_neg hupper]

/-- The zeta-indexed half-Gaussian feature whose squared norm is one boundary
heat summand. -/
def zetaUpperBoundaryGaussianFeature
    (x tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (Real.sqrt (zetaUpperBoundaryGaussianTransverseWeight tau rho) : ℂ) *
    complexHalfGaussian tau x (zetaSpectralCoordinate rho.1)

/-- The squared modulus of one feature is exactly its positive fixed-time
boundary heat contribution. -/
theorem normSq_zetaUpperBoundaryGaussianFeature
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Complex.normSq (zetaUpperBoundaryGaussianFeature x tau rho) =
      zetaUpperHyperbolicBoundaryHeatSummand x tau rho := by
  rw [zetaUpperBoundaryGaussianFeature, Complex.normSq_mul,
    Complex.normSq_ofReal,
    Real.mul_self_sqrt
      (zetaUpperBoundaryGaussianTransverseWeight_nonneg tau rho)]
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBoundaryGaussianTransverseWeight, if_pos hupper,
      zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper,
      boundaryHeatKernel_eq_transverse_mul_normSq_halfGaussian]
    ring
  · rw [zetaUpperBoundaryGaussianTransverseWeight, if_neg hupper,
      zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]
    simp

/-- The boundary Gaussian feature is square-summable at every positive
proper time. -/
theorem summable_norm_sq_zetaUpperBoundaryGaussianFeature
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Summable (fun rho : NontrivialZetaZero ↦
      ‖zetaUpperBoundaryGaussianFeature x tau rho‖ ^ 2) := by
  simpa only [Complex.sq_norm,
    normSq_zetaUpperBoundaryGaussianFeature] using
      summable_zetaUpperHyperbolicBoundaryHeatSummand x htau

/-- The complete reflected-pair Gaussian feature as a literal Hilbert vector
in `ℓ²` of the nontrivial zeta zeros. -/
def riemannXiUpperBoundaryGaussianFeatureVector
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    ℓ²(NontrivialZetaZero, ℂ) :=
  ⟨zetaUpperBoundaryGaussianFeature x tau, by
    apply memℓp_gen
    simpa using
      summable_norm_sq_zetaUpperBoundaryGaussianFeature x htau⟩

/-- The complete boundary heat invariant is exactly the squared Hilbert norm
of the reflected-pair Gaussian feature vector. -/
theorem norm_sq_riemannXiUpperBoundaryGaussianFeatureVector
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    ‖riemannXiUpperBoundaryGaussianFeatureVector x htau‖ ^ 2 =
      riemannXiUpperHyperbolicBoundaryHeatTotal x tau := by
  calc
    ‖riemannXiUpperBoundaryGaussianFeatureVector x htau‖ ^ 2 =
        ∑' rho : NontrivialZetaZero,
          ‖riemannXiUpperBoundaryGaussianFeatureVector x htau rho‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
          (riemannXiUpperBoundaryGaussianFeatureVector x htau))
    _ = ∑' rho : NontrivialZetaZero,
          zetaUpperHyperbolicBoundaryHeatSummand x tau rho := by
      apply tsum_congr
      intro rho
      change ‖zetaUpperBoundaryGaussianFeature x tau rho‖ ^ 2 = _
      rw [Complex.sq_norm,
        normSq_zetaUpperBoundaryGaussianFeature]
    _ = riemannXiUpperHyperbolicBoundaryHeatTotal x tau := rfl

/-- The entire matched-pair correlation and the Hilbert construction are the
same invariant: the former is the complex embedding of the latter's squared
norm. -/
theorem riemannXiUpperReflectedPairGaussianTotal_eq_norm_sq_featureVector
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperReflectedPairGaussianTotal x tau =
      (‖riemannXiUpperBoundaryGaussianFeatureVector x htau‖ ^ 2 : ℝ) := by
  calc
    riemannXiUpperReflectedPairGaussianTotal x tau =
        riemannXiUpperHyperbolicBoundaryHeatResidueTotal x tau :=
      riemannXiUpperReflectedPairGaussianTotal_eq_boundaryHeatResidueTotal
        x tau
    _ = (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) :=
      riemannXiUpperHyperbolicBoundaryHeatResidueTotal_eq_ofReal x htau
    _ = (‖riemannXiUpperBoundaryGaussianFeatureVector x htau‖ ^ 2 : ℝ) := by
      rw [norm_sq_riemannXiUpperBoundaryGaussianFeatureVector x htau]

/-- Vanishing of the explicit reflected-pair Gaussian Hilbert vector is
equivalent to RH. -/
theorem riemannXiUpperBoundaryGaussianFeatureVector_eq_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperBoundaryGaussianFeatureVector x htau = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    have htotal :
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 := by
      rw [← norm_sq_riemannXiUpperBoundaryGaussianFeatureVector
        x htau, hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mp htotal
  · intro hRH
    have htotal :
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mpr hRH
    apply norm_eq_zero.mp
    have hsquare :
        ‖riemannXiUpperBoundaryGaussianFeatureVector x htau‖ ^ 2 = 0 := by
      rw [norm_sq_riemannXiUpperBoundaryGaussianFeatureVector x htau,
        htotal]
    nlinarith [norm_nonneg
      (riemannXiUpperBoundaryGaussianFeatureVector x htau)]

end

end RiemannGaussian
