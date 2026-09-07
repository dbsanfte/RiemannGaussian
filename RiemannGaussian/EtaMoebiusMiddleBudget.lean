import RiemannGaussian.EtaMoebiusArithmeticGrowingHead
import RiemannGaussian.EtaMoebiusContinuumBudget

/-!
# The original zero bound after controlling both arithmetic ends

The growing logarithmic head, complete quadratic tail, and original grid
and coefficient costs all tend to zero. The unchanged canonical deficit
and actual zero displacement are bounded by the intervening arithmetic
square sum plus these explicit costs. Decay of the intervening sum, the
full uniform weighted current bound, and RH remain open.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The full explicit end and transport allowance at the original arithmetic stage. -/
def pairedEtaDyadicMoebiusMiddleAllowance (k : ℕ) : ℝ :=
  484 / Real.log (k + 1 : ℕ) + pairedEtaMoebiusQuadraticTailAllowance (k + 1) +
    pairedEtaDyadicMoebiusRefinedAllowance k

/-- Both actual arithmetic ends and the original grid and coefficient transport have a combined allowance tending to zero. -/
theorem pairedEtaDyadicMoebiusMiddleAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusMiddleAllowance atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ 484 / Real.log (k + 1 : ℕ) +
    pairedEtaMoebiusQuadraticTailAllowance (k + 1) + pairedEtaDyadicMoebiusRefinedAllowance k) atTop (𝓝 0)
  have hh : Tendsto (fun k : ℕ ↦ 484 / Real.log (k + 1 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1))
  have ht := pairedEtaMoebiusQuadraticTailAllowance_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, add_zero] using
    (hh.add ht).add pairedEtaDyadicMoebiusRefinedAllowance_tendsto_zero

/-- The full unchanged continuum residual is bounded by the actual intervening arithmetic band and explicit costs for both complete ends. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_le_middle_add_ends {M : ℕ} (hM : 1 < M) :
    pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) ≤
      pairedEtaMoebiusArithmeticMiddleEnergy M + 484 / Real.log M + pairedEtaMoebiusQuadraticTailAllowance M := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_head_middle_tail (by omega : 1 ≤ M)]
  have hh := pairedEtaMoebiusArithmeticSquarePrefix_logarithmic_le hM
  have ht := pairedEtaMoebiusArithmeticSquareTail_quadratic_le (by omega : 1 ≤ M)
  linarith

/-- The original canonical deficit is bounded by the unchanged intervening arithmetic square sum plus the proved vanishing end and transport allowance. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_middle {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaDyadicTranslateDeficit k ≤ pairedEtaMoebiusArithmeticMiddleEnergy (k + 1) +
      pairedEtaDyadicMoebiusMiddleAllowance k := by
  have hc := pairedEtaDyadicTranslateDeficit_le_moebius_continuum hk
  have hb := pairedEtaMoebiusContinuumResidualEnergy_le_middle_add_ends (by omega : 1 < k + 1)
  unfold pairedEtaDyadicMoebiusContinuumResidual at hc
  unfold pairedEtaDyadicMoebiusMiddleAllowance
  linarith

/-- Every original actual zero retains its unchanged displacement comparison after both full arithmetic end costs are discharged asymptotically; the middle energy remains uncontrolled. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_middle
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaMoebiusArithmeticMiddleEnergy (k + 1) + pairedEtaDyadicMoebiusMiddleAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_middle hk)

end

end RiemannGaussian
