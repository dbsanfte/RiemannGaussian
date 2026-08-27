import RiemannGaussian.FiniteToEntirePoissonBlaschkeTransfer

/-!
# A finite Blaschke-cancellation frontier forced by the Hardy defect

The complete elementary Blaschke derivative variation is exhausted by finite
spectral windows.  A positive lower bound on the complete variation therefore
forces a fixed smaller lower bound in every sufficiently large window.  The
finite variation is in turn bounded by the norm of the finite Blaschke-product
logarithmic derivative plus its explicit triangle-cancellation gap.

Critical-line reflection rewrites that product logarithmic derivative exactly
in terms of the genuine spectral-xi logarithmic derivative, its analytic
finite-window remainder, the critical-line Cauchy part, and the upper divisor
Cauchy sum.  Thus failure of RH now forces either a persistent positive lower
bound on this concrete finite analytic residual plus cancellation, or the
canonical polynomial upper-height masses are unbounded.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The exact reflection residual represented by the logarithmic derivative
of the finite upper spectral Blaschke product. -/
def riemannXiUpperSpectralReflectionResidual (z : ℂ) (T : ℝ) : ℂ :=
  2 * riemannXiSpectralUpperCauchyWindow z T -
    (logDeriv riemannXiSpectral z -
      riemannXiSpectralWindowLogDerivativeRawRemainder T z -
      riemannXiSpectralCriticalCauchyWindow z T)

/-- The finite upper spectral Blaschke-product logarithmic derivative is
exactly the spectral reflection residual. -/
theorem logDeriv_riemannXiUpperBlaschkeProductWindow_eq_reflectionResidual
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    logDeriv (riemannXiUpperBlaschkeProductWindow T) z =
      riemannXiUpperSpectralReflectionResidual z T := by
  unfold riemannXiUpperSpectralReflectionResidual
  rw [two_mul_riemannXiSpectralUpperCauchyWindow_eq_xiLogDeriv_sub_remainders_add_blaschke
    hz hxi hT]
  ring

/-- A positive complete Blaschke-variation threshold has half its value in
every sufficiently large finite spectral window. -/
theorem eventually_half_le_riemannXiUpperBlaschkeDerivativeVariationWindow
    {z : ℂ} {q : ℝ} (hq : 0 < q)
    (hmass : ENNReal.ofReal q ≤
      riemannXiUpperBlaschkeDerivativeVariationMass z) :
    ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (q / 2) ≤
        riemannXiUpperBlaschkeDerivativeVariationWindow z T := by
  have hhalf : ENNReal.ofReal (q / 2) < ENNReal.ofReal q := by
    rw [ENNReal.ofReal_lt_ofReal_iff hq]
    linarith
  have hhalfMass :
      ENNReal.ofReal (q / 2) <
        riemannXiUpperBlaschkeDerivativeVariationMass z :=
    hhalf.trans_le hmass
  exact
    ((tendsto_order.mp
      (tendsto_riemannXiUpperBlaschkeDerivativeVariationWindow z)).1
        _ hhalfMass).mono fun _T hT => hT.le

/-- A positive complete Blaschke-variation threshold forces the same fixed
half-threshold into the finite reflection residual plus its explicit
cancellation gap at every sufficiently large window. -/
theorem eventually_half_threshold_le_reflectionResidual_add_cancellation
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {q : ℝ} (hq : 0 < q)
    (hmass : ENNReal.ofReal q ≤
      riemannXiUpperBlaschkeDerivativeVariationMass z) :
    ∀ᶠ T : ℝ in atTop,
      q / 2 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  have hwindows :=
    eventually_half_le_riemannXiUpperBlaschkeDerivativeVariationWindow
      hq hmass
  filter_upwards [hwindows, eventually_ge_atTop (0 : ℝ)] with T hwindow hT
  have hfinite :=
    riemannXiUpperBlaschkeDerivativeVariationWindow_le_ofReal_logDerivativeVariation
      hz hxi T
  rw [
    riemannXiUpperBlaschkeLogDerivativeVariationWindow_eq_product_norm_add_cancellation
      hz hxi T] at hfinite
  have hchain :
      ENNReal.ofReal (q / 2) ≤
        ENNReal.ofReal
          (‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖ +
            riemannXiUpperBlaschkeLogDerivativeCancellation z T) :=
    hwindow.trans hfinite
  have hnonneg :
      0 ≤ ‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T :=
    add_nonneg (norm_nonneg _)
      (riemannXiUpperBlaschkeLogDerivativeCancellation_nonneg z T)
  have hreal :
      q / 2 ≤ ‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T :=
    (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hchain
  rw [logDeriv_riemannXiUpperBlaschkeProductWindow_eq_reflectionResidual
    hz hxi hT] at hreal
  exact hreal

/-- A complete-variation-versus-height alternative transfers to the explicit
finite reflection-residual-versus-cancellation frontier. -/
theorem eventually_reflectionResidual_or_height_unbounded
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {q : ℝ} (hq : 0 < q) (height : ℕ → ℝ)
    (halternative :
      ENNReal.ofReal q ≤
          riemannXiUpperBlaschkeDerivativeVariationMass z ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n) :
    (∀ᶠ T : ℝ in atTop,
      q / 2 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T) ∨
      ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n := by
  rcases halternative with hmass | hunbounded
  · exact Or.inl
      (eventually_half_threshold_le_reflectionResidual_add_cancellation
        hz hxi hq hmass)
  · exact Or.inr hunbounded

/-- Under failure of RH, the canonical finite Hardy frontier forces a fixed
positive lower bound on the explicit spectral reflection residual plus the
finite Blaschke cancellation gap at all sufficiently large windows, unless
the canonical polynomial upper-height masses are unbounded. -/
theorem exists_canonicalFiniteHardyFrontier_reflectionResidual_or_height_unbounded_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ delta : ℝ, 0 < delta ∧
      (∀ rho : NontrivialZetaZero,
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖) ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ (a error : ℝ), 0 < a → 0 < error →
          ∃ T : ℝ, a ≤ T ∧
            ∀ᶠ n in atTop,
              (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
                  (∫ tau in a..T,
                    riemannXiUpperHyperbolicHeatSum z tau) - error) /
                    (4 * a * z.im) <
                realPolynomialUpperHeightMass (B n)) ∧
        0 < riemannXiUpperBlaschkeVariationThreshold
          (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta ∧
        ((∀ᶠ T : ℝ in atTop,
            riemannXiUpperBlaschkeVariationThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta /
                2 ≤
              ‖riemannXiUpperSpectralReflectionResidual z T‖ +
                riemannXiUpperBlaschkeLogDerivativeCancellation z T) ∨
          ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
            M < realPolynomialUpperHeightMass (B n)) := by
  obtain ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B,
      hlimit, hfrontier, hpositive, hobstruction, _hpoissonPositive,
      hvariationPositive, htransferred⟩ :=
    exists_canonicalFiniteHardyFrontier_poisson_blaschke_or_height_unbounded_of_not_rh
      hRH
  have hvariationAlternative :
      ENNReal.ofReal
          (riemannXiUpperBlaschkeVariationThreshold
            (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta) ≤
          riemannXiUpperBlaschkeDerivativeVariationMass z ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
          M < realPolynomialUpperHeightMass (B n) := by
    rcases htransferred with hbounds | hunbounded
    · exact Or.inl hbounds.2
    · exact Or.inr hunbounded
  have hanalytic :=
    eventually_reflectionResidual_or_height_unbounded
      hz hxi hvariationPositive
        (fun n ↦ realPolynomialUpperHeightMass (B n))
        hvariationAlternative
  exact ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B, hlimit,
    hfrontier, hpositive, hobstruction, hvariationPositive, hanalytic⟩

end

end RiemannGaussian
