import RiemannGaussian.RiemannXiBoundaryFixedTimeHeat

/-!
# Integrating the fixed-proper-time boundary heat

This file integrates the complete fixed-time boundary heat density over all
positive proper times.  Each Gaussian term integrates exactly to its boundary
Poisson density.  Nonnegativity and Tonelli's theorem then identify the
integral of the complete boundary heat sum with the already constructed
cancellation-free boundary invariant.

Thus the fixed-time spectral-xi residue construction and the integrated heat
action meet in Lean: the boundary heat integral, the normalized Poisson
boundary limit, and the embedded norm of the complete boundary Blaschke
logarithmic derivative are exactly equal.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- One boundary heat summand is continuous in proper time. -/
theorem continuous_zetaUpperHyperbolicBoundaryHeatSummand
    (x : ℝ) (rho : NontrivialZetaZero) :
    Continuous (fun tau : ℝ ↦
      zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper]
    fun_prop
  · simp only [zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]
    fun_prop

/-- A positive-rate exponential integrates to the inverse rate over positive
proper time. -/
theorem integral_exp_neg_mul_Ioi_zero
    {D : ℝ} (hD : 0 < D) :
    (∫ tau : ℝ in Ioi 0, Real.exp (-(D * tau))) = D⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -D) (by linarith) 0
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with tau
    congr 1
    ring
  · simp

/-- Integrating one lifted fixed-time boundary heat summand gives exactly its
lifted boundary Poisson density. -/
theorem lintegral_ofReal_zetaUpperHyperbolicBoundaryHeatSummand
    (x : ℝ) (rho : NontrivialZetaZero) :
    (∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
      (zetaUpperHyperbolicBoundaryHeatSummand x tau rho)) =
      ENNReal.ofReal (zetaUpperBlaschkeBoundaryDensitySummand x rho) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha := zetaSpectralCoordinate rho.1
    let D := Complex.normSq ((x : ℂ) - alpha)
    let C := (analyticZetaZeroMultiplicity rho : ℝ) * (2 * alpha.im)
    have hD : 0 < D := by
      dsimp [D, alpha]
      apply Complex.normSq_pos.mpr
      apply sub_ne_zero.mpr
      intro heq
      have him := congrArg Complex.im heq
      simp only [ofReal_im] at him
      linarith
    have hC : 0 ≤ C := by
      dsimp [C, alpha]
      positivity
    have hexpInt : IntegrableOn
        (fun tau : ℝ ↦ Real.exp (-(D * tau))) (Ioi 0) := by
      convert integrableOn_exp_mul_Ioi (a := -D) (by linarith) 0 using 1
      funext tau
      congr 1
      ring
    have hfInt : IntegrableOn
        (fun tau : ℝ ↦ C * Real.exp (-(D * tau))) (Ioi 0) :=
      hexpInt.const_mul C
    have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun tau : ℝ ↦ C * Real.exp (-(D * tau)) :=
      Eventually.of_forall fun _ ↦ mul_nonneg hC (Real.exp_pos _).le
    have hlin :=
      (ofReal_integral_eq_lintegral_ofReal hfInt hfNonneg).symm
    calc
      (∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
          (zetaUpperHyperbolicBoundaryHeatSummand x tau rho)) =
          ∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
            (C * Real.exp (-(D * tau))) := by
        apply lintegral_congr
        intro tau
        congr 1
        rw [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper]
        dsimp [C, D, alpha]
        ring
      _ = ENNReal.ofReal
          (∫ tau in Ioi (0 : ℝ), C * Real.exp (-(D * tau))) := hlin
      _ = ENNReal.ofReal
          (zetaUpperBlaschkeBoundaryDensitySummand x rho) := by
        congr 1
        rw [MeasureTheory.integral_const_mul,
          integral_exp_neg_mul_Ioi_zero hD,
          zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
        dsimp [C, D, alpha]
        ring
  · simp only [zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, ENNReal.ofReal_zero,
      lintegral_zero]

/-- Lifting the convergent fixed-time boundary heat series commutes with its
sum. -/
theorem ofReal_riemannXiUpperHyperbolicBoundaryHeatTotal_eq_tsum
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    ENNReal.ofReal (riemannXiUpperHyperbolicBoundaryHeatTotal x tau) =
      ∑' rho : NontrivialZetaZero, ENNReal.ofReal
        (zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
  unfold riemannXiUpperHyperbolicBoundaryHeatTotal
  exact ENNReal.ofReal_tsum_of_nonneg
    (zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau)
    (summable_zetaUpperHyperbolicBoundaryHeatSummand x htau)

/-- The proper-time integral of the complete fixed-time boundary heat
density. -/
def riemannXiUpperHyperbolicBoundaryHeatAction (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ tau in Ioi (0 : ℝ),
    ENNReal.ofReal (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)

/-- Tonelli identifies the complete boundary heat action with the finite
boundary Poisson density total. -/
theorem riemannXiUpperHyperbolicBoundaryHeatAction_eq_density
    (x : ℝ) :
    riemannXiUpperHyperbolicBoundaryHeatAction x =
      ENNReal.ofReal (riemannXiUpperBlaschkeBoundaryDensityTotal x) := by
  unfold riemannXiUpperHyperbolicBoundaryHeatAction
  calc
    (∫⁻ tau in Ioi (0 : ℝ),
        ENNReal.ofReal
          (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) =
        ∫⁻ tau in Ioi (0 : ℝ),
          ∑' rho : NontrivialZetaZero, ENNReal.ofReal
            (zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
      exact
        ofReal_riemannXiUpperHyperbolicBoundaryHeatTotal_eq_tsum
          x htau
    _ = ∑' rho : NontrivialZetaZero,
          ∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
            (zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
      exact lintegral_tsum fun rho ↦
        (continuous_zetaUpperHyperbolicBoundaryHeatSummand
          x rho).aemeasurable.ennreal_ofReal
    _ = ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            (zetaUpperBlaschkeBoundaryDensitySummand x rho) := by
      apply tsum_congr
      exact lintegral_ofReal_zetaUpperHyperbolicBoundaryHeatSummand x
    _ = ENNReal.ofReal
          (riemannXiUpperBlaschkeBoundaryDensityTotal x) := by
      unfold riemannXiUpperBlaschkeBoundaryDensityTotal
      exact (ENNReal.ofReal_tsum_of_nonneg
        (zetaUpperBlaschkeBoundaryDensitySummand_nonneg x)
        (summable_zetaUpperBlaschkeBoundaryDensitySummand x)).symm

/-- The integrated fixed-time boundary heat is the normalized Poisson
boundary limit. -/
theorem riemannXiUpperHyperbolicBoundaryHeatAction_eq_poissonBoundaryLimit
    (x : ℝ) :
    riemannXiUpperHyperbolicBoundaryHeatAction x =
      riemannXiUpperHyperbolicPoissonBoundaryLimit x := by
  exact riemannXiUpperHyperbolicBoundaryHeatAction_eq_density x

/-- The same boundary heat action is the embedded norm of the complete
boundary Blaschke logarithmic derivative. -/
theorem riemannXiUpperHyperbolicBoundaryHeatAction_eq_logDerivativeNorm
    (x : ℝ) :
    riemannXiUpperHyperbolicBoundaryHeatAction x =
      ENNReal.ofReal
        ‖riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)‖ := by
  rw [riemannXiUpperHyperbolicBoundaryHeatAction_eq_density,
    norm_riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density]

/-- The normalized interior heat action converges to the integral of the
fixed-time boundary heat density. -/
theorem tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient_boundaryHeatAction
    (x : ℝ) :
    Tendsto
      (riemannXiUpperHyperbolicHeatActionBoundaryQuotient x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicBoundaryHeatAction x)) := by
  rw [riemannXiUpperHyperbolicBoundaryHeatAction_eq_poissonBoundaryLimit]
  exact tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient x

/-- The complete boundary heat action is finite at every real point. -/
theorem riemannXiUpperHyperbolicBoundaryHeatAction_ne_top
    (x : ℝ) :
    riemannXiUpperHyperbolicBoundaryHeatAction x ≠ ∞ := by
  rw [riemannXiUpperHyperbolicBoundaryHeatAction_eq_density]
  exact ENNReal.ofReal_ne_top

/-- Vanishing of the integrated fixed-time boundary heat is exactly RH. -/
theorem riemannXiUpperHyperbolicBoundaryHeatAction_eq_zero_iff_rh
    (x : ℝ) :
    riemannXiUpperHyperbolicBoundaryHeatAction x = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiUpperHyperbolicBoundaryHeatAction_eq_poissonBoundaryLimit]
  exact riemannXiUpperHyperbolicPoissonBoundaryLimit_eq_zero_iff_rh x

end

end RiemannGaussian
