import RiemannGaussian.FiniteToEntireBlaschkeCancellationFrontier

/-!
# Separating the finite xi residual from Blaschke cancellation

The previous frontier forces a positive lower bound on the sum of two
nonnegative quantities: the norm of the exact xi reflection residual and the
finite Blaschke triangle-cancellation gap.  This file separates the two
mechanisms quantitatively.

If their sum is eventually at least `q / 2`, then either the residual is at
least `q / 4` along arbitrarily late windows, or the cancellation gap is at
least `q / 4` in every sufficiently large window.  Applied to the canonical
Hardy sequence under failure of RH, this gives a precise three-way frontier:
persistent xi residual, persistent Blaschke cancellation, or unbounded finite
polynomial height mass.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- If a sum exceeds half a threshold, one summand exceeds a quarter of the
same threshold. -/
theorem fourth_le_left_or_fourth_le_right_of_half_le_add
    {q x y : ℝ} (h : q / 2 ≤ x + y) :
    q / 4 ≤ x ∨ q / 4 ≤ y := by
  by_contra hsmall
  push Not at hsmall
  linarith

/-- An eventual lower bound on residual plus cancellation separates into a
frequently-large residual or an eventually-large cancellation gap. -/
theorem frequently_reflectionResidual_or_eventually_cancellation
    {z : ℂ} {q : ℝ}
    (hfrontier : ∀ᶠ T : ℝ in atTop,
      q / 2 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T) :
    (∃ᶠ T : ℝ in atTop,
      q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      ∀ᶠ T : ℝ in atTop,
        q / 4 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  have hpointwise : ∀ᶠ T : ℝ in atTop,
      q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖ ∨
        q / 4 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T :=
    hfrontier.mono fun T hT =>
      fourth_le_left_or_fourth_le_right_of_half_le_add hT
  by_cases hresidual : ∃ᶠ T : ℝ in atTop,
      q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖
  · exact Or.inl hresidual
  · right
    have hnotResidual : ∀ᶠ T : ℝ in atTop,
        ¬q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖ :=
      not_frequently.mp hresidual
    filter_upwards [hpointwise, hnotResidual] with T hT hnotT
    exact hT.resolve_left hnotT

/-- A complete Blaschke-variation threshold therefore forces either an
arbitrarily late xi reflection residual or an eventual cancellation gap. -/
theorem frequently_reflectionResidual_or_eventually_cancellation_of_variationMass
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {q : ℝ} (hq : 0 < q)
    (hmass : ENNReal.ofReal q ≤
      riemannXiUpperBlaschkeDerivativeVariationMass z) :
    (∃ᶠ T : ℝ in atTop,
      q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      ∀ᶠ T : ℝ in atTop,
        q / 4 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  exact frequently_reflectionResidual_or_eventually_cancellation
    (eventually_half_threshold_le_reflectionResidual_add_cancellation
      hz hxi hq hmass)

/-- A complete-variation-versus-height alternative becomes a trichotomy
between residual, cancellation, and unbounded height. -/
theorem reflectionResidual_or_cancellation_or_height_unbounded
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {q : ℝ} (hq : 0 < q) (height : ℕ → ℝ)
    (halternative :
      ENNReal.ofReal q ≤
          riemannXiUpperBlaschkeDerivativeVariationMass z ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n) :
    (∃ᶠ T : ℝ in atTop,
      q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      (∀ᶠ T : ℝ in atTop,
        q / 4 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T) ∨
      ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n := by
  rcases halternative with hmass | hunbounded
  · rcases
      frequently_reflectionResidual_or_eventually_cancellation_of_variationMass
        hz hxi hq hmass with hresidual | hcancellation
    · exact Or.inl hresidual
    · exact Or.inr (Or.inl hcancellation)
  · exact Or.inr (Or.inr hunbounded)

/-- Under failure of RH, the canonical finite Hardy frontier forces either a
quantitatively large exact xi reflection residual along arbitrarily late
windows, a quantitatively large Blaschke cancellation gap in all sufficiently
large windows, or unbounded polynomial upper-height mass. -/
theorem exists_canonicalFiniteHardyFrontier_residual_or_cancellation_or_height_unbounded_of_not_rh
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
        ((∃ᶠ T : ℝ in atTop,
            riemannXiUpperBlaschkeVariationThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta /
                4 ≤
              ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
          (∀ᶠ T : ℝ in atTop,
            riemannXiUpperBlaschkeVariationThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta /
                4 ≤
              riemannXiUpperBlaschkeLogDerivativeCancellation z T) ∨
          ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
            M < realPolynomialUpperHeightMass (B n)) := by
  obtain ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B,
      hlimit, hfrontier, hpositive, hobstruction, hvariationPositive,
      hanalytic⟩ :=
    exists_canonicalFiniteHardyFrontier_reflectionResidual_or_height_unbounded_of_not_rh
      hRH
  have htrichotomy :
      (∃ᶠ T : ℝ in atTop,
        riemannXiUpperBlaschkeVariationThreshold
            (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta / 4 ≤
          ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
        (∀ᶠ T : ℝ in atTop,
          riemannXiUpperBlaschkeVariationThreshold
              (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta / 4 ≤
            riemannXiUpperBlaschkeLogDerivativeCancellation z T) ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
          M < realPolynomialUpperHeightMass (B n) := by
    rcases hanalytic with hsum | hunbounded
    · rcases frequently_reflectionResidual_or_eventually_cancellation hsum with
        hresidual | hcancellation
      · exact Or.inl hresidual
      · exact Or.inr (Or.inl hcancellation)
    · exact Or.inr (Or.inr hunbounded)
  exact ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B, hlimit,
    hfrontier, hpositive, hobstruction, hvariationPositive, htrichotomy⟩

end

end RiemannGaussian
