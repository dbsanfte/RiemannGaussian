import RiemannGaussian.EtaTranslatedFiniteResidual
import RiemannGaussian.EtaCurrentFinitePhasePower

/-!
# Finite translated eta arithmetic bounds the original current's power

Every finite family of nonnegative real translates supplies a complete
arithmetic residual budget. The compact target is nonzero at each actual
zero and its reflected partner, so that budget bounds the horizontal
displacement on both halves of the strip. Taking the minimum preserves
all earlier phase and prime bounds. The unchanged current, literal Gaussian
return, and full inverse energy inherit this exponent at every cutoff.

No family with a vanishing complete residual budget is constructed here.
The positive target normalization depends on the actual zero coordinates;
this is not yet an ordinate-only numerical improvement of the zero strip.
-/

open Complex Set

namespace RiemannGaussian

noncomputable section

/-- The compact target's positive normalization retains both actual reflected zero coordinates. -/
def pairedEtaProjectionHeadZeroWeight (rho : NontrivialZetaZero) : ℝ :=
  min (‖pairedEtaProjectionHeadTransform rho.1‖ ^ 2)
    (‖pairedEtaProjectionHeadTransform (NontrivialZetaZero.conjugatePartner rho).1‖ ^ 2)

/-- Neither actual zero in the reflected pair is lost by the compact target. -/
theorem pairedEtaProjectionHeadZeroWeight_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaProjectionHeadZeroWeight rho := by
  apply lt_min
  · exact sq_pos_of_pos (norm_pos_iff.mpr (pairedEtaProjectionHeadTransform_ne_zero rho))
  · exact sq_pos_of_pos (norm_pos_iff.mpr
      (pairedEtaProjectionHeadTransform_ne_zero (NontrivialZetaZero.conjugatePartner rho)))

/-- The signed right-half displacement inequality extends to the entire actual zero strip. -/
theorem two_mul_re_sub_one_mul_head_norm_sq_le_finiteBudget_all {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    (2 * rho.1.re - 1) * ‖pairedEtaProjectionHeadTransform rho.1‖ ^ 2 ≤
      pairedEtaTranslatedFiniteResidualBudget N a c := by
  by_cases hrho : 1 / 2 < rho.1.re
  · exact two_mul_re_sub_one_mul_head_norm_sq_le_finiteBudget rho hrho hN ha c
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)).trans
      (pairedEtaTranslatedFiniteResidualBudget_nonneg hN ha c)

/-- Reflection turns the complete finite arithmetic budget into an absolute displacement bound, with no omitted coefficient or tail cost. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_finiteBudget {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaTranslatedFiniteResidualBudget N a c := by
  unfold pairedEtaCurrentHorizontalDisplacement
  by_cases hrho : 0 ≤ 2 * rho.1.re - 1
  · rw [abs_of_nonneg hrho]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hrho).trans
      (two_mul_re_sub_one_mul_head_norm_sq_le_finiteBudget_all rho hN ha c)
  · rw [abs_of_neg (lt_of_not_ge hrho)]
    have hp := two_mul_re_sub_one_mul_head_norm_sq_le_finiteBudget_all
      (NontrivialZetaZero.conjugatePartner rho) hN ha c
    have hre : 2 * (NontrivialZetaZero.conjugatePartner rho).1.re - 1 =
        -(2 * rho.1.re - 1) := by
      simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
        Complex.one_re, Complex.conj_re]
      ring
    rw [hre] at hp
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith : 0 ≤ -(2 * rho.1.re - 1))).trans hp

/-- Every finite translated eta family bounds the literal zero displacement after division by a proved positive target weight. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_translatedFiniteBudget {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    pairedEtaCurrentHorizontalDisplacement rho ≤
      pairedEtaTranslatedFiniteResidualBudget N a c / pairedEtaProjectionHeadZeroWeight rho :=
  (le_div_iff₀ (pairedEtaProjectionHeadZeroWeight_pos rho)).mpr
    (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_finiteBudget rho hN ha c)

/-- The full translated Gram budget combined with every preceding finite phase and prime exponent. -/
def etaTranslatedProjectionCurrentExponent {d : ℕ} (rho : NontrivialZetaZero) (N : ℕ)
    (a : Fin d → ℝ) (c : Fin d → ℂ) : ℝ :=
  min (etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im)
    (pairedEtaTranslatedFiniteResidualBudget N a c / pairedEtaProjectionHeadZeroWeight rho)

/-- Adding a translated eta family never increases the previously allowed current power. -/
theorem etaTranslatedProjectionCurrentExponent_le_finitePhase {d : ℕ}
    (rho : NontrivialZetaZero) (N : ℕ) (a : Fin d → ℝ) (c : Fin d → ℂ) :
    etaTranslatedProjectionCurrentExponent rho N a c ≤
      etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im :=
  min_le_left _ _

/-- The complete translated arithmetic exponent lies between zero and one for every valid finite family. -/
theorem etaTranslatedProjectionCurrentExponent_bounds {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    0 ≤ etaTranslatedProjectionCurrentExponent rho N a c ∧
      etaTranslatedProjectionCurrentExponent rho N a c < 1 := by
  have hold := etaFinitePhaseCurrentExponent_bounds rho N
  exact ⟨le_min hold.1 (div_nonneg (pairedEtaTranslatedFiniteResidualBudget_nonneg hN ha c)
    (pairedEtaProjectionHeadZeroWeight_pos rho).le),
    (etaTranslatedProjectionCurrentExponent_le_finitePhase rho N a c).trans_lt hold.2⟩

/-- The actual displacement is bounded by the combined exponent at every original eta arithmetic cutoff. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_translatedProjection {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    pairedEtaCurrentHorizontalDisplacement rho ≤ etaTranslatedProjectionCurrentExponent rho N a c :=
  le_min (pairedEtaCurrentHorizontalDisplacement_le_finitePhase rho N)
    (pairedEtaCurrentHorizontalDisplacement_le_translatedFiniteBudget rho hN ha c)

/-- The full finite translated Gram and its proved tail control both branches of the original weighted current at every cutoff. -/
theorem pairedEtaLeadingCurrent_firstMoment_le_translatedProjection {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho n|) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ etaTranslatedProjectionCurrentExponent rho N a c :=
  (pairedEtaLeadingCurrent_firstMoment_le_growthConstant rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (pairedEtaCurrentHorizontalDisplacement_le_translatedProjection rho hN ha c))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The unchanged linear-width Gaussian return inherits the complete translated eta exponent with its original constant. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_translatedProjection {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho n‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ etaTranslatedProjectionCurrentExponent rho N a c :=
  (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (pairedEtaCurrentHorizontalDisplacement_le_translatedProjection rho hN ha c))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The complete signed inverse energy retains its summable error allowance under the same finite translated arithmetic power. -/
theorem pairedEtaCurrentFullInverseEnergy_firstMoment_le_translatedProjection {d N : ℕ}
    (rho : NontrivialZetaZero) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho n|) ≤
      (pairedEtaCurrentReturnGrowthConstant rho + ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n) *
        (K + 1 : ℝ) ^ etaTranslatedProjectionCurrentExponent rho N a c := by
  have hstab := (abs_le.mp (pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability rho K)).1
  have hcurrent := pairedEtaLeadingCurrent_firstMoment_le_translatedProjection rho hN ha c K
  have hB : 0 ≤ ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n :=
    tsum_nonneg (pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho)
  have hpow : 1 ≤ (K + 1 : ℝ) ^ etaTranslatedProjectionCurrentExponent rho N a c :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (etaTranslatedProjectionCurrentExponent_bounds rho hN ha c).1
  nlinarith [mul_le_mul_of_nonneg_left hpow hB]

end

end RiemannGaussian
