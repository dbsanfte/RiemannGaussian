import RiemannGaussian.EtaMoebiusTrialHead
import RiemannGaussian.EtaMoebiusRefinedBudget

/-!
# Actual arithmetic residual decay on the complete eta target interval

The logarithmic harmonic correction and the exact finite-grid rounding
estimate prove decay of the original residual square integral on
`(0, log 2]`, uniformly over every positive integer refinement. The full
energy splits into this vanishing term and the actual infinite exterior
integral. Decay of that exterior integral remains unproved.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The genuine target-interval residual energy of the original logarithmic Möbius candidate on a physical grid. -/
def pairedEtaMoebiusTrialHeadResidualEnergy (d M : ℕ) : ℝ :=
  pairedEtaTranslatedResidualEnergyCutoff (fun j : Fin d ↦ pairedEtaMoebiusTrialGridPoint d (j.1 + 1))
    (fun j ↦ (pairedEtaMoebiusTrialCoefficient d M (pairedEtaMoebiusTrialLogWeight M) j : ℂ)) (Real.log 2)

/-- The actual target-interval integral is nonnegative. -/
theorem pairedEtaMoebiusTrialHeadResidualEnergy_nonneg (d M : ℕ) :
    0 ≤ pairedEtaMoebiusTrialHeadResidualEnergy d M := integral_nonneg (fun _ ↦ by positivity)

/-- A complete quantitative bound on the actual arithmetic residual over the whole target support. -/
theorem pairedEtaMoebiusTrialHeadResidualEnergy_le {d M : ℕ} (hd : 0 < d) (hM : 1 < M) :
    pairedEtaMoebiusTrialHeadResidualEnergy d M ≤
      (2 * |pairedEtaMoebiusLogHarmonic M| + 4 * |1 - pairedEtaMoebiusLogHarmonic M| / d) ^ 2 := by
  let B := 2 * |pairedEtaMoebiusLogHarmonic M| + 4 * |1 - pairedEtaMoebiusLogHarmonic M| / d
  let a := fun j : Fin d ↦ pairedEtaMoebiusTrialGridPoint d (j.1 + 1)
  let c := fun j : Fin d ↦ (pairedEtaMoebiusTrialCoefficient d M (pairedEtaMoebiusTrialLogWeight M) j : ℂ)
  have hi := (integrableOn_pairedEtaTranslatedResidual_weighted_sq a c).mono_set
    (show Ioc 0 (Real.log 2) ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * B ^ 2) (Ioi 0) := by
    have hh : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
      simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    exact hh.mul_const _
  change (∫ t : ℝ in Ioc 0 (Real.log 2), Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2) ≤ B ^ 2
  calc
    _ ≤ ∫ t : ℝ in Ioc 0 (Real.log 2), Real.exp (-t) * B ^ 2 := by
      apply integral_mono_ae hi (he.mono_set Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hb : ‖pairedEtaTranslatedResidual a c t‖ ≤ B := norm_pairedEtaMoebiusTrialHeadResidual_le hd hM ht
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (Real.exp_pos _).le
    _ ≤ ∫ t : ℝ in Ioi 0, Real.exp (-t) * B ^ 2 :=
      setIntegral_mono_set he (Eventually.of_forall (fun _ ↦ by positivity))
        (Eventually.of_forall (fun _ h ↦ h.1))
    _ = B ^ 2 := by rw [integral_mul_const, integral_Ioi_exp_neg_eq]; simp

/-- A single arithmetic head allowance which works for every positive integer refinement of the original dyadic grid. -/
def pairedEtaDyadicMoebiusHeadAllowance (k : ℕ) : ℝ :=
  (2 * |pairedEtaMoebiusLogHarmonic (k + 1)| +
    4 * |1 - pairedEtaMoebiusLogHarmonic (k + 1)| / (2 : ℝ) ^ k) ^ 2

/-- Every refined actual target-interval energy is bounded by the same arithmetic allowance. -/
theorem pairedEtaMoebiusTrialHeadResidualEnergy_refined_le {k : ℕ} (hk : 1 ≤ k) (q : ℕ) :
    pairedEtaMoebiusTrialHeadResidualEnergy (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1) ≤
      pairedEtaDyadicMoebiusHeadAllowance k := by
  unfold pairedEtaDyadicMoebiusHeadAllowance
  have hd := pairedEtaDyadicTranslateDimension_pos k
  have hdp : (0 : ℝ) < pairedEtaDyadicTranslateDimension k := by exact_mod_cast hd
  have hle : (pairedEtaDyadicTranslateDimension k : ℝ) ≤
      ((pairedEtaDyadicTranslateDimension k * (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_mul_of_pos_right (pairedEtaDyadicTranslateDimension k) (Nat.succ_pos q))
  apply (pairedEtaMoebiusTrialHeadResidualEnergy_le (Nat.mul_pos hd (Nat.succ_pos q)) (by omega)).trans
  apply pow_le_pow_left₀ (by positivity) _ 2
  apply add_le_add le_rfl
  change 4 * |1 - pairedEtaMoebiusLogHarmonic (k + 1)| /
      ((pairedEtaDyadicTranslateDimension k * (q + 1) : ℕ) : ℝ) ≤ _
  simpa only [pairedEtaDyadicTranslateDimension, Nat.cast_pow, Nat.cast_ofNat] using
    div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 * |1 - pairedEtaMoebiusLogHarmonic (k + 1)|) hdp hle

/-- The complete head allowance tends to zero from actual Möbius harmonic cancellation and the original physical-grid growth. -/
theorem pairedEtaDyadicMoebiusHeadAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusHeadAllowance atTop (𝓝 0) := by
  have hP := pairedEtaMoebiusLogHarmonic_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have hfirst := hP.abs.const_mul (2 : ℝ)
  have hsecond := (((tendsto_const_nhds (x := (1 : ℝ))).sub hP).abs.const_mul (4 : ℝ)).div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have h := (hfirst.add hsecond).pow 2
  change Tendsto (fun k : ℕ ↦ (2 * |pairedEtaMoebiusLogHarmonic (k + 1)| +
    4 * |1 - pairedEtaMoebiusLogHarmonic (k + 1)| / (2 : ℝ) ^ k) ^ 2) atTop (𝓝 0)
  simpa using h

/-- The actual refined arithmetic residual square integral on the entire target interval tends to zero for every refinement schedule. -/
theorem pairedEtaDyadicMoebiusRefinedHeadResidual_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ pairedEtaMoebiusTrialHeadResidualEnergy
      (pairedEtaDyadicTranslateDimension k * (q k + 1)) (k + 1)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ pairedEtaMoebiusTrialHeadResidualEnergy_nonneg _ _)
    _ pairedEtaDyadicMoebiusHeadAllowance_tendsto_zero
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact pairedEtaMoebiusTrialHeadResidualEnergy_refined_le hk (q k)

/-- The actual complete exterior energy, outside the target support, retaining the entire refined arithmetic combination. -/
def pairedEtaDyadicMoebiusRefinedExteriorEnergy (k q : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) *
    ‖pairedEtaMoebiusTrialGridCombination (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1)
      (pairedEtaMoebiusTrialLogWeight (k + 1)) t‖ ^ 2

/-- The full refined residual splits exactly into its actual head error and the entire exterior arithmetic energy. -/
theorem pairedEtaDyadicMoebiusRefinedResidual_eq_head_add_exterior (k q : ℕ) :
    pairedEtaDyadicMoebiusRefinedResidual k q =
      pairedEtaMoebiusTrialHeadResidualEnergy (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1) +
        pairedEtaDyadicMoebiusRefinedExteriorEnergy k q := by
  unfold pairedEtaDyadicMoebiusRefinedResidual pairedEtaMoebiusTrialGridResidualEnergy
  rw [pairedEtaTranslatedResidualEnergy_eq_cutoff_add_tail _ _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [pairedEtaTranslatedResidual_eq_neg_of_log_two_lt _ _ ht, norm_neg]
  rfl

/-- The difference between the full residual and its unchanged infinite exterior integral tends to zero by the proved arithmetic head decay. -/
theorem pairedEtaDyadicMoebiusRefinedResidual_sub_exterior_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ pairedEtaDyadicMoebiusRefinedResidual k (q k) -
      pairedEtaDyadicMoebiusRefinedExteriorEnergy k (q k)) atTop (𝓝 0) := by
  simp_rw [pairedEtaDyadicMoebiusRefinedResidual_eq_head_add_exterior, add_sub_cancel_right]
  exact pairedEtaDyadicMoebiusRefinedHeadResidual_tendsto_zero q

/-- All proved head, grid, and coefficient costs in the comparison with the complete exterior arithmetic integral. -/
def pairedEtaDyadicMoebiusExteriorAllowance (k : ℕ) : ℝ :=
  pairedEtaDyadicMoebiusHeadAllowance k + pairedEtaDyadicMoebiusRefinedAllowance k

/-- The full allowance accompanying the unchanged exterior integral tends to zero unconditionally. -/
theorem pairedEtaDyadicMoebiusExteriorAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusExteriorAllowance atTop (𝓝 0) := by
  change Tendsto (fun k ↦ pairedEtaDyadicMoebiusHeadAllowance k + pairedEtaDyadicMoebiusRefinedAllowance k)
    atTop (𝓝 0)
  simpa only [add_zero] using
    pairedEtaDyadicMoebiusHeadAllowance_tendsto_zero.add pairedEtaDyadicMoebiusRefinedAllowance_tendsto_zero

/-- The actual canonical deficit is bounded by the complete refined exterior arithmetic integral with every removed cost proved vanishing. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_exterior {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaDyadicTranslateDeficit k ≤ pairedEtaDyadicMoebiusRefinedExteriorEnergy k q +
      pairedEtaDyadicMoebiusExteriorAllowance k := by
  have hb := pairedEtaDyadicTranslateDeficit_le_refined_moebius hk q
  rw [pairedEtaDyadicMoebiusRefinedResidual_eq_head_add_exterior] at hb
  have hh := pairedEtaMoebiusTrialHeadResidualEnergy_refined_le (by omega : 1 ≤ k) q
  unfold pairedEtaDyadicMoebiusExteriorAllowance
  linarith

/-- Every original actual zero displacement satisfies the exterior arithmetic bound with the same proved vanishing allowance. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_exterior
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicMoebiusRefinedExteriorEnergy k q + pairedEtaDyadicMoebiusExteriorAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_exterior hk q)

end

end RiemannGaussian
