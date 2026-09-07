import RiemannGaussian.EtaMoebiusGridArithmetic

/-!
# Complete exterior energy in signed Möbius interval arithmetic

The full original exterior integral is exactly its finite signed primitive
square integral plus its genuine infinite tail. The tail has an explicit
arithmetic cutoff bound independent of the physical grid dimension. All
integrability conditions are proved for the actual carrier.
-/

open Complex Filter MeasureTheory Set

namespace RiemannGaussian

noncomputable section

/-- Every original finite-grid arithmetic combination has a genuinely integrable critical square on every upper half-line. -/
theorem integrableOn_pairedEtaMoebiusTrialGridCombination_weighted_sq
    (d M : ℕ) (w : ℕ → ℝ) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) (Ioi T) := by
  let a := fun j : Fin d ↦ pairedEtaMoebiusTrialGridPoint d (j.1 + 1)
  let c := fun j : Fin d ↦ (pairedEtaMoebiusTrialCoefficient d M w j : ℂ)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi T) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
  apply he.mul_bdd ((measurable_pairedEtaTranslatedCombination a c).norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaTranslatedCombination_le a c t) 2

/-- The entire infinite arithmetic tail has a dimension-independent bound in the original arithmetic cutoff. -/
theorem integral_Ioi_pairedEtaMoebiusTrialGridCombination_weighted_sq_le
    (d M : ℕ) {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (T : ℝ) :
    (∫ t : ℝ in Ioi T, Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) ≤
      4 * (M : ℝ) ^ 2 * Real.exp (-T) := by
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi T) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
  have hbound (t : ℝ) : ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ≤ 2 * M := by
    apply (norm_pairedEtaTranslatedCombination_le _ _ t).trans
    simpa only [Complex.norm_real, Real.norm_eq_abs] using pairedEtaMoebiusTrialCoefficient_sum_abs_le d M hw
  calc
    _ ≤ ∫ t : ℝ in Ioi T, Real.exp (-t) * (2 * (M : ℝ)) ^ 2 := by
      apply integral_mono_ae (integrableOn_pairedEtaMoebiusTrialGridCombination_weighted_sq d M w T) (he.mul_const _)
      exact Eventually.of_forall fun t ↦ mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2) (Real.exp_pos _).le
    _ = _ := by rw [integral_mul_const, integral_Ioi_exp_neg_eq]; ring

/-- The complete signed arithmetic formula has an integrable weighted square on its full exterior window, inherited from the unchanged original combination. -/
theorem integrableOn_pairedEtaMoebiusTrialArithmeticPrefix_weighted_sq (N d M : ℕ) (w : ℕ → ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * pairedEtaMoebiusTrialArithmeticPrefix N d M w t ^ 2)
      (Ioc (Real.log 2) (Real.log (2 * N + 1 : ℝ))) := by
  have hi := (integrableOn_pairedEtaMoebiusTrialGridCombination_weighted_sq d M w (Real.log 2)).mono_set
    (show Ioc (Real.log 2) (Real.log (2 * N + 1 : ℝ)) ⊆ Ioi (Real.log 2) from Ioc_subset_Ioi_self)
  apply hi.congr_fun _ measurableSet_Ioc
  intro t ht
  dsimp only
  rw [pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix N d M w ht.2,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The full original exterior energy is exactly its signed arithmetic primitive square integral plus the entire unchanged infinite tail. -/
theorem pairedEtaMoebiusTrialExteriorEnergy_eq_arithmetic_add_tail {N : ℕ} (hN : 1 ≤ N)
    (d M : ℕ) (w : ℕ → ℝ) :
    (∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) =
      (∫ t : ℝ in Ioc (Real.log 2) (Real.log (2 * N + 1 : ℝ)),
        Real.exp (-t) * pairedEtaMoebiusTrialArithmeticPrefix N d M w t ^ 2) +
      ∫ t : ℝ in Ioi (Real.log (2 * N + 1 : ℝ)),
        Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2 := by
  have hT : Real.log 2 ≤ Real.log (2 * N + 1 : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hi := integrableOn_pairedEtaMoebiusTrialGridCombination_weighted_sq d M w (Real.log 2)
  have hh := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hT))
  rw [intervalIntegral.integral_of_le hT] at hh
  rw [← hh]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix N d M w ht.2,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- An explicit finite signed arithmetic square integral bounds the complete original exterior energy with every omitted contribution included. -/
theorem pairedEtaMoebiusTrialExteriorEnergy_le_arithmetic {N : ℕ} (hN : 1 ≤ N)
    (d M : ℕ) {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∫ t : ℝ in Ioi (Real.log 2), Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ^ 2) ≤
      (∫ t : ℝ in Ioc (Real.log 2) (Real.log (2 * N + 1 : ℝ)),
        Real.exp (-t) * pairedEtaMoebiusTrialArithmeticPrefix N d M w t ^ 2) +
      4 * (M : ℝ) ^ 2 / (2 * N + 1 : ℝ) := by
  rw [pairedEtaMoebiusTrialExteriorEnergy_eq_arithmetic_add_tail hN]
  apply add_le_add le_rfl
  have h := integral_Ioi_pairedEtaMoebiusTrialGridCombination_weighted_sq_le d M hw (Real.log (2 * N + 1 : ℝ))
  simpa only [Real.exp_neg, Real.exp_log (by positivity : 0 < (2 * N + 1 : ℝ)), div_eq_mul_inv] using h

end

end RiemannGaussian
