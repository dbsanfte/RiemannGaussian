import RiemannGaussian.RiemannXiHyperbolicHeatAction

/-!
# Transferring the finite Hardy defect into the entire spectral action

The complete spectral proper-time action is now an exact extended-real
object.  This file isolates the remaining endpoint issue.  Eventual uniform
control of the finite upper-root height makes the small-time actions uniformly
tight; the persistent finite Hardy lower bound must then survive in the
complete spectral action.

For the canonical sequence under `¬RH`, Lean obtains a precise alternative:
either the complete spectral logarithmic defect already dominates the fixed
Hardy threshold, or the finite upper-height masses exceed every prescribed
bound infinitely often.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complete spectral heat is interval-integrable on every compact
positive proper-time interval. -/
theorem intervalIntegrable_riemannXiUpperHyperbolicHeatSum
    {z : ℂ} (hz : 0 < z.im) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (riemannXiUpperHyperbolicHeatSum z)
      volume a b := by
  apply AntitoneOn.intervalIntegrable
  intro s hs t ht hst
  rw [uIcc_of_le hab] at hs ht
  exact riemannXiUpperHyperbolicHeatSum_le_of_time_le
    hz (ha.trans_le hs.1) hst

/-- Every compact positive-time spectral action is bounded by the complete
extended proper-time action. -/
theorem ofReal_intervalIntegral_riemannXiUpperHyperbolicHeatSum_le_action
    {z : ℂ} (hz : 0 < z.im) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ENNReal.ofReal
        (∫ tau in a..b, riemannXiUpperHyperbolicHeatSum z tau) ≤
      riemannXiUpperHyperbolicHeatAction z := by
  have hint :=
    intervalIntegrable_riemannXiUpperHyperbolicHeatSum hz ha hab
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)]
      riemannXiUpperHyperbolicHeatSum z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with tau htau
    exact riemannXiUpperHyperbolicHeatSum_nonneg hz
      (ha.trans htau.1)
  rw [intervalIntegral.integral_of_le hab]
  rw [ofReal_integral_eq_lintegral_ofReal hint.1 hnonneg]
  unfold riemannXiUpperHyperbolicHeatAction
  apply lintegral_mono_set
  intro tau htau
  exact ha.trans htau.1

/-- A quantitative small-time height obstruction transfers its lower bound
to the complete spectral action whenever the finite height statistics are
eventually uniformly bounded. -/
theorem ofReal_le_riemannXiUpperHyperbolicHeatAction_of_heightBound
    {z : ℂ} (hz : 0 < z.im) {D : ℝ} (height : ℕ → ℝ)
    (hobstruction : ∀ (a error : ℝ), 0 < a → 0 < error →
      ∃ T : ℝ, a ≤ T ∧
        ∀ᶠ n in atTop,
          (D -
              (∫ tau in a..T,
                riemannXiUpperHyperbolicHeatSum z tau) - error) /
                (4 * a * z.im) < height n)
    {M : ℝ} (hM : 0 ≤ M)
    (hheight : ∀ᶠ n in atTop, height n ≤ M) :
    ENNReal.ofReal D ≤ riemannXiUpperHyperbolicHeatAction z := by
  by_cases htop : riemannXiUpperHyperbolicHeatAction z = ⊤
  · rw [htop]
    exact le_top
  · rw [ENNReal.ofReal_le_iff_le_toReal htop]
    by_contra hnot
    have hDgt :
        (riemannXiUpperHyperbolicHeatAction z).toReal < D :=
      lt_of_not_ge hnot
    let C : ℝ := 4 * z.im * M
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    let error : ℝ :=
      (D - (riemannXiUpperHyperbolicHeatAction z).toReal) / 4
    have herror : 0 < error := by
      dsimp [error]
      linarith
    have hCOne : 0 < C + 1 := by linarith
    let a : ℝ := error / (C + 1)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have haC : a * C < error := by
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hCOne).2
      nlinarith
    obtain ⟨T, haT, hstage⟩ := hobstruction a error ha herror
    obtain ⟨n, hn, hnHeight⟩ := (hstage.and hheight).exists
    have hdenominator : 0 < 4 * a * z.im := by positivity
    have hraw :
        D -
              (∫ tau in a..T,
                riemannXiUpperHyperbolicHeatSum z tau) - error <
            a * C := by
      calc
        D -
              (∫ tau in a..T,
                riemannXiUpperHyperbolicHeatSum z tau) - error <
            M * (4 * a * z.im) :=
          (div_lt_iff₀ hdenominator).1 (hn.trans_le hnHeight)
        _ = a * C := by
          dsimp [C]
          ring
    have hcompactENN :=
      ofReal_intervalIntegral_riemannXiUpperHyperbolicHeatSum_le_action
        hz ha haT
    have hcompact :
        (∫ tau in a..T, riemannXiUpperHyperbolicHeatSum z tau) ≤
          (riemannXiUpperHyperbolicHeatAction z).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).1 hcompactENN
    have htooSmall :
        D < (riemannXiUpperHyperbolicHeatAction z).toReal +
          2 * error := by
      linarith
    dsimp [error] at htooSmall
    linarith

/-- Without assuming a height bound, the same argument gives the exact
alternative: either the lower bound survives in the complete spectral action,
or the finite heights exceed every nonnegative bound frequently. -/
theorem ofReal_le_riemannXiUpperHyperbolicHeatAction_or_height_unbounded
    {z : ℂ} (hz : 0 < z.im) {D : ℝ} (height : ℕ → ℝ)
    (hobstruction : ∀ (a error : ℝ), 0 < a → 0 < error →
      ∃ T : ℝ, a ≤ T ∧
        ∀ᶠ n in atTop,
          (D -
              (∫ tau in a..T,
                riemannXiUpperHyperbolicHeatSum z tau) - error) /
                (4 * a * z.im) < height n) :
    ENNReal.ofReal D ≤ riemannXiUpperHyperbolicHeatAction z ∨
      ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n := by
  by_cases haction :
      ENNReal.ofReal D ≤ riemannXiUpperHyperbolicHeatAction z
  · exact Or.inl haction
  · right
    intro M hM
    by_contra hnotFrequently
    have hheight : ∀ᶠ n in atTop, height n ≤ M := by
      filter_upwards [(not_frequently.mp hnotFrequently)] with n hn
      exact le_of_not_gt hn
    exact haction
      (ofReal_le_riemannXiUpperHyperbolicHeatAction_of_heightBound
        hz height hobstruction hM hheight)

/-- Under failure of RH, the canonical root-pinned Hardy sequence reaches a
fully explicit entire-versus-boundary alternative.  Either the complete
spectral logarithmic defect dominates the fixed Hardy threshold, or its
finite polynomial upper-height masses cross every nonnegative bound
infinitely often. -/
theorem exists_canonicalFiniteHardyFrontier_logDefect_or_height_unbounded_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ B : ℕ → ℝ[X],
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
        (ENNReal.ofReal
              (-2 * Real.log (pairHyperbolicThreshold eta z.im)) ≤
            riemannXiUpperHyperbolicLogDefectMass z ∨
          ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
            M < realPolynomialUpperHeightMass (B n)) := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier,
      hpositive, hobstruction⟩ :=
    exists_canonicalFiniteHardyFrontier_smallTimeHeightObstruction_of_not_rh
      hRH
  have halternative :=
    ofReal_le_riemannXiUpperHyperbolicHeatAction_or_height_unbounded
      hz (fun n ↦ realPolynomialUpperHeightMass (B n)) hobstruction
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi] at halternative
  exact ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier,
    hpositive, hobstruction, halternative⟩

end

end RiemannGaussian
