import RiemannGaussian.FiniteToEntireHardyReductio
import RiemannGaussian.GaussianXiDivisorContour
import RiemannGaussian.GaussianXiGrowth
import RiemannGaussian.HyperbolicHeatBridge

/-!
# The fixed-proper-time spectral-xi heat sum

This file constructs the entire multiplicity-counted upper-half-plane heat
sum at each fixed positive proper time.  Its coefficients are not postulated:
Lean identifies every term with the genuine local residue of
`logDeriv riemannXiSpectral`, hence with the analytic zeta-zero multiplicity.
The Gaussian ordinate bound already proved for xi gives absolute convergence.

This deliberately precedes any integration in proper time.  Fixed positive
time suppresses remote zeros by a Gaussian and avoids the endpoint-uniformity
problem in the finite-to-entire passage.
-/

namespace RiemannGaussian

noncomputable section

open Filter Topology

/-- The complex upper-half-plane heat kernel is strictly positive at positive
proper time. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_pos
    {z alpha : ℂ} {tau : ℝ} (hz : 0 < z.im)
    (halpha : 0 < alpha.im) (htau : 0 < tau) :
    0 < upperHalfPlaneHyperbolicHeatIntegrand z alpha tau := by
  rw [upperHalfPlaneHyperbolicHeatIntegrand_eq_pair]
  exact pairHyperbolicHeatIntegrand_pos hz halpha htau

/-- At fixed positive proper time, one heat term is dominated by the same
Gaussian zero envelope already controlled in the xi explicit-formula chain. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_gaussianZeroEnvelope
    (z alpha : ℂ) {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau ≤
      tau⁻¹ * Real.exp
        (tau * alpha.im ^ 2 - tau * (alpha.re - z.re) ^ 2) := by
  have hsub :
      Real.exp (-(Complex.normSq (z - alpha) * tau)) -
          Real.exp
            (-(Complex.normSq (z - starRingEnd ℂ alpha) * tau)) ≤
        Real.exp (-(Complex.normSq (z - alpha) * tau)) := by
    nlinarith [Real.exp_pos
      (-(Complex.normSq (z - starRingEnd ℂ alpha) * tau))]
  have hexponent :
      -(Complex.normSq (z - alpha) * tau) ≤
        tau * alpha.im ^ 2 - tau * (alpha.re - z.re) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (z.im - alpha.im),
      sq_nonneg (z.re - alpha.re)]
  unfold upperHalfPlaneHyperbolicHeatIntegrand
  exact (mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr htau.le)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
      (inv_nonneg.mpr htau.le))

/-- The contribution of one distinct nontrivial zeta zero to the upper
spectral heat sum.  Critical-line and lower-half-plane zeros contribute zero;
upper zeros contribute with their genuine analytic multiplicity. -/
def zetaUpperHyperbolicHeatSummand
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      upperHalfPlaneHyperbolicHeatIntegrand z
        (zetaSpectralCoordinate rho.1) tau
  else 0

/-- The same coefficient, regarded as the heat-weighted local residue of the
spectral-xi logarithmic derivative. -/
def riemannXiUpperHyperbolicHeatResidue
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (upperHalfPlaneHyperbolicHeatIntegrand z
        (zetaSpectralCoordinate rho.1) tau : ℂ) *
      (analyticZetaZeroMultiplicity rho : ℂ)
  else 0

@[simp] theorem riemannXiUpperHyperbolicHeatResidue_eq_ofReal
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) :
    riemannXiUpperHyperbolicHeatResidue z tau rho =
      (zetaUpperHyperbolicHeatSummand z tau rho : ℂ) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [riemannXiUpperHyperbolicHeatResidue,
      zetaUpperHyperbolicHeatSummand, if_pos hupper, if_pos hupper]
    push_cast
    ring
  · rw [riemannXiUpperHyperbolicHeatResidue,
      zetaUpperHyperbolicHeatSummand, if_neg hupper, if_neg hupper]
    simp

/-- Each selected heat residue is derived directly from the local spectral-xi
logarithmic derivative, with no assumed zero weight. -/
theorem tendsto_upperHyperbolicHeat_mul_logDeriv_riemannXiSpectral
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    Tendsto
      (fun w ↦
        (upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau : ℂ) *
          ((w - zetaSpectralCoordinate rho.1) *
            logDeriv riemannXiSpectral w))
      (nhdsWithin (zetaSpectralCoordinate rho.1)
        ({zetaSpectralCoordinate rho.1}ᶜ))
      (nhds (riemannXiUpperHyperbolicHeatResidue z tau rho)) := by
  have hweight : Tendsto
      (fun _ : ℂ ↦
        (upperHalfPlaneHyperbolicHeatIntegrand z
          (zetaSpectralCoordinate rho.1) tau : ℂ))
      (nhdsWithin (zetaSpectralCoordinate rho.1)
        ({zetaSpectralCoordinate rho.1}ᶜ))
      (nhds
        (upperHalfPlaneHyperbolicHeatIntegrand z
          (zetaSpectralCoordinate rho.1) tau : ℂ)) :=
    tendsto_const_nhds
  have hlocal := hweight.mul
    (tendsto_zetaSpectralCoordinate_mul_logDeriv_riemannXiSpectral rho)
  rw [riemannXiUpperHyperbolicHeatResidue, if_pos hupper]
  exact hlocal

/-- Every fixed-positive-time upper heat series is absolutely summable. -/
theorem summable_zetaUpperHyperbolicHeatSummand
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Summable (zetaUpperHyperbolicHeatSummand z tau) := by
  have hzeroSum :=
    (representsCanonicalZetaGaussianZeroSum_unconditional tau z.re htau)
  have hdistinct := hasSum_zetaGaussianDistinctZeroSummand
    analyticZetaZeroMultiplicity tau z.re
      (canonicalZetaGaussianZeroSum tau z.re) hzeroSum
  have henvelope : Summable fun rho : NontrivialZetaZero ↦
      (analyticZetaZeroMultiplicity rho : ℝ) *
        Real.exp
          (tau * (zetaSpectralCoordinate rho.1).im ^ 2 -
            tau * ((zetaSpectralCoordinate rho.1).re - z.re) ^ 2) := by
    simpa only [zetaGaussianDistinctZeroSummand, Complex.norm_mul,
      Complex.norm_natCast, norm_complexTranslatedGaussian] using
        hdistinct.summable.norm
  apply (henvelope.mul_left tau⁻¹).of_norm_bounded
  intro rho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hheatPos := upperHalfPlaneHyperbolicHeatIntegrand_pos
      hz hupper htau
    rw [zetaUpperHyperbolicHeatSummand, if_pos hupper,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hheatPos.le)]
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau ≤
        (analyticZetaZeroMultiplicity rho : ℝ) *
          (tau⁻¹ * Real.exp
            (tau * (zetaSpectralCoordinate rho.1).im ^ 2 -
              tau * ((zetaSpectralCoordinate rho.1).re - z.re) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (upperHalfPlaneHyperbolicHeatIntegrand_le_gaussianZeroEnvelope
            z (zetaSpectralCoordinate rho.1) htau)
          (Nat.cast_nonneg _)
      _ = tau⁻¹ *
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            Real.exp
              (tau * (zetaSpectralCoordinate rho.1).im ^ 2 -
                tau * ((zetaSpectralCoordinate rho.1).re - z.re) ^ 2)) := by
        ring
  · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper, Real.norm_eq_abs,
      abs_zero]
    positivity

/-- The canonical entire fixed-proper-time heat sum of the upper spectral-xi
zero divisor. -/
noncomputable def riemannXiUpperHyperbolicHeatSum
    (z : ℂ) (tau : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperHyperbolicHeatSummand z tau rho

/-- The entire fixed-time heat sum is literally the convergent sum of the
heat-weighted logarithmic-derivative residues. -/
theorem hasSum_riemannXiUpperHyperbolicHeatResidue
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    HasSum (riemannXiUpperHyperbolicHeatResidue z tau)
      (riemannXiUpperHyperbolicHeatSum z tau : ℂ) := by
  have hreal := (summable_zetaUpperHyperbolicHeatSummand hz htau).hasSum
  have hcomplex := Complex.hasSum_ofReal.mpr hreal
  exact hcomplex.congr_fun fun rho ↦
    riemannXiUpperHyperbolicHeatResidue_eq_ofReal z tau rho

/-- Every fixed-positive-time spectral-xi upper heat sum is nonnegative. -/
theorem riemannXiUpperHyperbolicHeatSum_nonneg
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    0 ≤ riemannXiUpperHyperbolicHeatSum z tau := by
  unfold riemannXiUpperHyperbolicHeatSum
  apply tsum_nonneg
  intro rho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [zetaUpperHyperbolicHeatSummand, if_pos hupper]
    exact mul_nonneg (Nat.cast_nonneg _)
      (upperHalfPlaneHyperbolicHeatIntegrand_pos hz hupper htau).le
  · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper]

/-- A single upper spectral-xi zero makes every positive-time upper heat sum
strictly positive. -/
theorem riemannXiUpperHyperbolicHeatSum_pos_of_upper_zero
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < riemannXiUpperHyperbolicHeatSum z tau := by
  unfold riemannXiUpperHyperbolicHeatSum
  refine (summable_zetaUpperHyperbolicHeatSummand hz htau).tsum_pos ?_ rho ?_
  · intro sigma
    by_cases hsigma : 0 < (zetaSpectralCoordinate sigma.1).im
    · simp only [zetaUpperHyperbolicHeatSummand, if_pos hsigma]
      exact mul_nonneg (Nat.cast_nonneg _)
        (upperHalfPlaneHyperbolicHeatIntegrand_pos hz hsigma htau).le
    · rw [zetaUpperHyperbolicHeatSummand, if_neg hsigma]
  · simp only [zetaUpperHyperbolicHeatSummand, if_pos hupper]
    exact mul_pos (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
      (upperHalfPlaneHyperbolicHeatIntegrand_pos hz hupper htau)

/-- At any one upper observation point and positive proper time, the complete
upper spectral-xi heat sum vanishes exactly when RH holds. -/
theorem riemannXiUpperHyperbolicHeatSum_eq_zero_iff_riemannHypothesis
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicHeatSum z tau = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hpos := riemannXiUpperHyperbolicHeatSum_pos_of_upper_zero
      hz htau rho hwupper
    linarith
  · intro hRH
    unfold riemannXiUpperHyperbolicHeatSum
    have hzero : zetaUpperHyperbolicHeatSummand z tau = fun _ ↦ 0 := by
      funext rho
      have him : (zetaSpectralCoordinate rho.1).im = 0 :=
        (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
          rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
      have hnot : ¬0 < (zetaSpectralCoordinate rho.1).im := by
        linarith
      rw [zetaUpperHyperbolicHeatSummand, if_neg hnot]
    rw [hzero, tsum_zero]

/-- Vanishing of the complete upper heat divisor at every positive proper
time and upper observation point. -/
def RiemannXiUpperHyperbolicHeatVanishes : Prop :=
  ∀ (z : ℂ) (tau : ℝ), 0 < z.im → 0 < tau →
    riemannXiUpperHyperbolicHeatSum z tau = 0

/-- Fixed-proper-time heat-residue vanishing is exactly RH. -/
theorem riemannXiUpperHyperbolicHeatVanishes_iff_riemannHypothesis :
    RiemannXiUpperHyperbolicHeatVanishes ↔ RiemannHypothesis := by
  constructor
  · intro hvanish
    exact
      (riemannXiUpperHyperbolicHeatSum_eq_zero_iff_riemannHypothesis
        (z := Complex.I) (tau := 1) (by simp) zero_lt_one).mp
        (hvanish Complex.I 1 (by simp) zero_lt_one)
  · intro hRH z tau hz htau
    exact
      (riemannXiUpperHyperbolicHeatSum_eq_zero_iff_riemannHypothesis
        hz htau).mpr hRH

end

end RiemannGaussian
