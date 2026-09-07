import RiemannGaussian.EtaMoebiusContinuumEnergy
import RiemannGaussian.EtaMoebiusRefinedBudget

/-!
# The unchanged canonical deficit and the full continuum arithmetic residual

The fixed-cutoff continuum limit is combined with the already uniform
refinement bounds before the arithmetic cutoff is allowed to grow. This
proves that the complete refined residual and the explicit signed continuum
residual differ by a vanishing allowance for every refinement schedule.
The canonical deficit and original zero displacement inherit the same full
arithmetic target. Decay of that target is still unproved.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The full exact signed continuum residual at the original logarithmic Möbius arithmetic stages. -/
def pairedEtaDyadicMoebiusContinuumResidual (k : ℕ) : ℝ :=
  pairedEtaMoebiusContinuumResidualEnergy (k + 1) (pairedEtaMoebiusTrialLogWeight (k + 1))

/-- The complete original dyadic-grid-to-continuum critical square error, retaining the original arithmetic cutoff and coefficient law. -/
def pairedEtaDyadicMoebiusContinuumGridError (k : ℕ) : ℝ :=
  pairedEtaMoebiusContinuumGridError (pairedEtaDyadicTranslateDimension k) (k + 1)
    (pairedEtaMoebiusTrialLogWeight (k + 1))

/-- At each fixed arithmetic stage, the actual complete refined residual converges to the identified continuum residual as the physical grid is refined. -/
theorem pairedEtaDyadicMoebiusRefinedResidual_tendsto_continuum (k : ℕ) :
    Tendsto (pairedEtaDyadicMoebiusRefinedResidual k) atTop (𝓝 (pairedEtaDyadicMoebiusContinuumResidual k)) :=
  pairedEtaMoebiusTrialGridResidualEnergy_tendsto_continuum (k + 1)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)
    ((tendsto_add_atTop_nat 1).const_mul_atTop' (pairedEtaDyadicTranslateDimension_pos k))

/-- The entire original dyadic-grid-to-continuum error has the same proved allowance as all finite refinements. -/
theorem pairedEtaDyadicMoebiusContinuumGridError_le {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaDyadicMoebiusContinuumGridError k ≤ pairedEtaDyadicMoebiusTrialRefinementAllowance k := by
  apply le_of_tendsto (pairedEtaMoebiusTrialRefinementError_tendsto_continuum
    (pairedEtaDyadicTranslateDimension_pos k) (k + 1)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn))
  exact Eventually.of_forall fun q ↦ pairedEtaDyadicMoebiusTrialRefinementError_le hk q

/-- The actual full critical square distance from the original grid to the explicit arithmetic continuum carrier tends to zero as the arithmetic cutoff grows. -/
theorem pairedEtaDyadicMoebiusContinuumGridError_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusContinuumGridError atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ integral_nonneg (fun _ ↦ by positivity))
    _ pairedEtaDyadicMoebiusTrialRefinementAllowance_tendsto_zero
  filter_upwards [eventually_ge_atTop 7] with k hk
  exact pairedEtaDyadicMoebiusContinuumGridError_le hk

/-- The entire original dyadic target residual differs from its explicit continuum arithmetic residual by the existing uniform and vanishing grid allowance. -/
theorem abs_pairedEtaDyadicMoebiusResidual_sub_continuum_le {k : ℕ} (hk : 7 ≤ k) :
    |pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) -
        pairedEtaDyadicMoebiusContinuumResidual k| ≤ pairedEtaDyadicMoebiusGridResidualAllowance k := by
  apply le_of_tendsto (tendsto_const_nhds.sub
    (pairedEtaDyadicMoebiusRefinedResidual_tendsto_continuum k)).abs
  exact Eventually.of_forall fun q ↦ abs_pairedEtaDyadicMoebiusResidual_sub_refined_le hk q

/-- Every refined complete residual differs from the same signed continuum residual by a bound independent of its refinement factor. -/
theorem abs_pairedEtaDyadicMoebiusRefinedResidual_sub_continuum_le {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    |pairedEtaDyadicMoebiusRefinedResidual k q - pairedEtaDyadicMoebiusContinuumResidual k| ≤
      2 * pairedEtaDyadicMoebiusGridResidualAllowance k := by
  have h := abs_sub_le (pairedEtaDyadicMoebiusRefinedResidual k q)
    (pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)))
    (pairedEtaDyadicMoebiusContinuumResidual k)
  have hleft := abs_pairedEtaDyadicMoebiusResidual_sub_refined_le hk q
  rw [abs_sub_comm] at hleft
  have hright := abs_pairedEtaDyadicMoebiusResidual_sub_continuum_le hk
  linarith

/-- The complete refined target residual and the exact continuum arithmetic residual have the same asymptotic energy for every refinement schedule; no fixed-cutoff limit is exchanged with the growing-cutoff limit. -/
theorem pairedEtaDyadicMoebiusRefinedResidual_sub_continuum_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ |pairedEtaDyadicMoebiusRefinedResidual k (q k) -
      pairedEtaDyadicMoebiusContinuumResidual k|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _)
    _ (by simpa only [mul_zero] using pairedEtaDyadicMoebiusGridResidualAllowance_tendsto_zero.const_mul (2 : ℝ))
  filter_upwards [eventually_ge_atTop 7] with k hk
  exact abs_pairedEtaDyadicMoebiusRefinedResidual_sub_continuum_le hk (q k)

/-- The original canonical minimizing deficit is bounded by the full identified continuum arithmetic residual with exactly the existing proved vanishing grid and coefficient allowance. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_continuum {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaDyadicTranslateDeficit k ≤
      pairedEtaDyadicMoebiusContinuumResidual k + pairedEtaDyadicMoebiusRefinedAllowance k := by
  apply ge_of_tendsto ((pairedEtaDyadicMoebiusRefinedResidual_tendsto_continuum k).add_const
    (pairedEtaDyadicMoebiusRefinedAllowance k))
  exact Eventually.of_forall fun q ↦ pairedEtaDyadicTranslateDeficit_le_refined_moebius hk q

/-- Every original actual zero displacement inherits the complete continuum arithmetic residual bound, with no arithmetic-decay assumption. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_continuum
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicMoebiusContinuumResidual k + pairedEtaDyadicMoebiusRefinedAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_continuum hk)

end

end RiemannGaussian
