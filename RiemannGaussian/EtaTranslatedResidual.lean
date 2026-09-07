import RiemannGaussian.EtaProjectionHeadTarget

/-!
# Complete complex residuals for eta translate approximation

The compact target and every complex coefficient survive in the residual.
Its exact Laplace value at an actual zero is the nonzero target transform.
The critical square energy is genuinely integrable, and the entire tail
past the target support has an explicit coefficient-dependent bound.
-/

open Complex Filter MeasureTheory Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The full complex error from the compact target to the original eta translate combination. -/
def pairedEtaTranslatedResidual {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) : ℂ :=
  pairedEtaProjectionHead t - pairedEtaTranslatedCombination a c t

/-- The actual critical weighted residual energy, before any cutoff or matrix compression. -/
def pairedEtaTranslatedResidualEnergy {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2

/-- The same residual energy restricted to a finite logarithmic interval. -/
def pairedEtaTranslatedResidualEnergyCutoff {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) (T : ℝ) : ℝ :=
  ∫ t : ℝ in Ioc 0 T, Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2

/-- All complex coefficients remain in the measurable combination. -/
theorem measurable_pairedEtaTranslatedCombination {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) :
    Measurable (pairedEtaTranslatedCombination a c) := by
  unfold pairedEtaTranslatedCombination
  exact Finset.measurable_sum _ (fun j _ ↦ measurable_const.mul (measurable_pairedEtaTranslatedColour (a j)).complex_ofReal)

/-- The literal residual is measurable. -/
theorem measurable_pairedEtaTranslatedResidual {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) :
    Measurable (pairedEtaTranslatedResidual a c) :=
  measurable_pairedEtaProjectionHead.sub (measurable_pairedEtaTranslatedCombination a c)

/-- The finite coefficient norm sum bounds the actual translated combination pointwise. -/
theorem norm_pairedEtaTranslatedCombination_le {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    ‖pairedEtaTranslatedCombination a c t‖ ≤ ∑ j, ‖c j‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rcases pairedEtaTranslatedColour_eq_zero_or_one (a j) t with h | h <;> simp [h]

/-- The compact target contributes at most two to the full pointwise residual. -/
theorem norm_pairedEtaTranslatedResidual_le {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    ‖pairedEtaTranslatedResidual a c t‖ ≤ 2 + ∑ j, ‖c j‖ :=
  (norm_sub_le _ _).trans (add_le_add (norm_pairedEtaProjectionHead_le t)
    (norm_pairedEtaTranslatedCombination_le a c t))

/-- Every compact-target residual has a genuinely integrable critical square. -/
theorem integrableOn_pairedEtaTranslatedResidual_weighted_sq {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  apply hi.mul_bdd ((measurable_pairedEtaTranslatedResidual a c).norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaTranslatedResidual_le a c t) 2

/-- The complete residual energy is nonnegative. -/
theorem pairedEtaTranslatedResidualEnergy_nonneg {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) :
    0 ≤ pairedEtaTranslatedResidualEnergy a c :=
  integral_nonneg (fun _ ↦ by positivity)

/-- The full residual Laplace kernel remains integrable throughout the positive half-plane. -/
theorem integrable_pairedEtaTranslatedResidual_mul_exp {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    (a : Fin d → ℝ) (c : Fin d → ℂ) :
    Integrable (fun t : ℝ ↦ pairedEtaTranslatedResidual a c t * Complex.exp (-s * t)) := by
  simp only [pairedEtaTranslatedResidual, sub_mul]
  exact (integrable_pairedEtaProjectionHead_mul_exp s).sub (integrable_pairedEtaTranslatedCombination hs a c)

/-- At an actual zero, the unchanged complete residual has the nonzero compact target transform. -/
theorem integral_pairedEtaTranslatedResidual_mul_exp_zero {d : ℕ} (rho : NontrivialZetaZero)
    (a : Fin d → ℝ) (c : Fin d → ℂ) :
    (∫ t : ℝ, pairedEtaTranslatedResidual a c t * Complex.exp (-rho.1 * t)) =
      pairedEtaProjectionHeadTransform rho.1 := by
  simp only [pairedEtaTranslatedResidual, sub_mul]
  rw [integral_sub (integrable_pairedEtaProjectionHead_mul_exp rho.1)
    (integrable_pairedEtaTranslatedCombination (NontrivialZetaZero.zero_lt_re rho) a c),
    integral_pairedEtaProjectionHead_mul_exp, integral_pairedEtaTranslatedCombination_eq_zero, sub_zero]

/-- Nonnegative translates keep the full residual supported at positive logarithmic time. -/
theorem pairedEtaTranslatedResidual_eq_zero_of_nonpos {d : ℕ} {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) {t : ℝ} (ht : t ≤ 0) :
    pairedEtaTranslatedResidual a c t = 0 := by
  have hhead : pairedEtaProjectionHead t = 0 := by
    apply Set.indicator_of_notMem
    exact fun h ↦ (not_lt_of_ge ht) h.1
  simp only [pairedEtaTranslatedResidual, hhead, pairedEtaTranslatedCombination,
    pairedEtaTranslatedColour_eq_zero_of_nonpos (ha _) ht, Complex.ofReal_zero, mul_zero,
    Finset.sum_const_zero, sub_zero]

/-- The actual zero identity also holds on the positive half-line where the critical energy is measured. -/
theorem integral_Ioi_pairedEtaTranslatedResidual_mul_exp_zero {d : ℕ} (rho : NontrivialZetaZero)
    {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    (∫ t : ℝ in Ioi 0, pairedEtaTranslatedResidual a c t * Complex.exp (-rho.1 * t)) =
      pairedEtaProjectionHeadTransform rho.1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_pairedEtaTranslatedResidual_mul_exp_zero rho a c
  · intro t ht
    rw [pairedEtaTranslatedResidual_eq_zero_of_nonpos ha c (le_of_not_gt ht), zero_mul]

/-- Beyond the compact target, the full residual is the unchanged negative translate combination. -/
theorem pairedEtaTranslatedResidual_eq_neg_of_log_two_lt {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ)
    {t : ℝ} (ht : Real.log 2 < t) :
    pairedEtaTranslatedResidual a c t = -pairedEtaTranslatedCombination a c t := by
  have hhead : pairedEtaProjectionHead t = 0 := Set.indicator_of_notMem (fun h ↦ (not_le_of_gt ht) h.2) _
  simp only [pairedEtaTranslatedResidual, hhead, zero_sub]

/-- The entire infinite residual tail has an explicit cutoff and coefficient norm cost. -/
theorem integral_Ioi_pairedEtaTranslatedResidual_weighted_sq_le {d : ℕ}
    (a : Fin d → ℝ) (c : Fin d → ℂ) {T : ℝ} (hT : Real.log 2 ≤ T) :
    (∫ t : ℝ in Ioi T, Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2) ≤
      Real.exp (-T) * (∑ j, ‖c j‖) ^ 2 := by
  have hT0 : 0 ≤ T := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hT
  have hi := (integrableOn_pairedEtaTranslatedResidual_weighted_sq a c).mono_set (Ioi_subset_Ioi hT0)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * (∑ j, ‖c j‖) ^ 2) (Ioi T) := by
    have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi T) := by
      simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
    exact hexp.mul_const _
  calc
    _ ≤ ∫ t : ℝ in Ioi T, Real.exp (-t) * (∑ j, ‖c j‖) ^ 2 := by
      apply integral_mono_ae hi he
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [pairedEtaTranslatedResidual_eq_neg_of_log_two_lt a c (hT.trans_lt ht), norm_neg]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaTranslatedCombination_le a c t) 2) (Real.exp_pos _).le
    _ = _ := by
      rw [integral_mul_const]
      have h : (∫ t : ℝ in Ioi T, Real.exp (-t)) = Real.exp (-T) := by
        simpa only [neg_one_mul, neg_div_neg_eq, div_one] using
          integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
      rw [h]

/-- The complete critical residual splits exactly into its finite interval and the unchanged tail. -/
theorem pairedEtaTranslatedResidualEnergy_eq_cutoff_add_tail {d : ℕ}
    (a : Fin d → ℝ) (c : Fin d → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTranslatedResidualEnergy a c = pairedEtaTranslatedResidualEnergyCutoff a c T +
      ∫ t : ℝ in Ioi T, Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2 := by
  have hi := integrableOn_pairedEtaTranslatedResidual_weighted_sq a c
  have h := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hT))
  rw [intervalIntegral.integral_of_le hT] at h
  exact h.symm

/-- The complete finite residual and the full coefficient-dependent tail give an unconditional energy bound. -/
theorem pairedEtaTranslatedResidualEnergy_le_cutoff {d : ℕ}
    (a : Fin d → ℝ) (c : Fin d → ℂ) {T : ℝ} (hT : Real.log 2 ≤ T) :
    pairedEtaTranslatedResidualEnergy a c ≤ pairedEtaTranslatedResidualEnergyCutoff a c T +
      Real.exp (-T) * (∑ j, ‖c j‖) ^ 2 := by
  rw [pairedEtaTranslatedResidualEnergy_eq_cutoff_add_tail a c
    ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hT)]
  exact add_le_add le_rfl (integral_Ioi_pairedEtaTranslatedResidual_weighted_sq_le a c hT)

end

end RiemannGaussian
