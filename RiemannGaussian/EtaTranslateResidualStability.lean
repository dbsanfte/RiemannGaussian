import RiemannGaussian.EtaTranslateGridError

/-!
# Full residual-energy stability under actual eta grid perturbation

Weighted Young's inequality transfers a bound for the complete grid error
to the original compact-target residual. Both full infinite residual
integrals and every complex coefficient are retained. The free positive
parameter keeps a vanishing grid error usable for growing coefficient norms.
-/

open Complex Filter MeasureTheory Set

namespace RiemannGaussian

noncomputable section

private theorem norm_add_sq_le_weighted (x y : ℂ) {e : ℝ} (he : 0 < e) :
    ‖x + y‖ ^ 2 ≤ (1 + e) * ‖x‖ ^ 2 + (1 + 1 / e) * ‖y‖ ^ 2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  have hmul := mul_le_mul_of_nonneg_left hnorm he.le
  have hc : e * (1 + 1 / e) = e + 1 := by field_simp
  apply (mul_le_mul_iff_right₀ he).mp
  rw [mul_add, ← mul_assoc e (1 + 1 / e), hc]
  nlinarith [sq_nonneg (e * ‖x‖ - ‖y‖)]

/-- Every original residual square has a pointwise grid-error comparison with a tunable coefficient cost. -/
theorem pairedEtaTranslatedResidual_sq_le_grid_error {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) {e : ℝ} (he : 0 < e) (t : ℝ) :
    ‖pairedEtaTranslatedResidual a c t‖ ^ 2 ≤
      ‖pairedEtaTranslatedResidual b c t‖ ^ 2 + e * (2 + ∑ j, ‖c j‖) ^ 2 +
        (1 + 1 / e) * ‖pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t‖ ^ 2 := by
  have hid : pairedEtaTranslatedResidual a c t = pairedEtaTranslatedResidual b c t +
      (pairedEtaTranslatedCombination b c t - pairedEtaTranslatedCombination a c t) := by
    unfold pairedEtaTranslatedResidual
    ring
  have h := norm_add_sq_le_weighted (pairedEtaTranslatedResidual b c t)
    (pairedEtaTranslatedCombination b c t - pairedEtaTranslatedCombination a c t) he
  rw [← hid, norm_sub_rev (pairedEtaTranslatedCombination b c t)] at h
  have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaTranslatedResidual_le b c t) 2
  have hb' := mul_le_mul_of_nonneg_left hb he.le
  nlinarith

/-- The complete target residual energy changes by at most the tunable coefficient cost and the entire actual grid error. -/
theorem pairedEtaTranslatedResidualEnergy_le_grid_error {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) {e : ℝ} (he : 0 < e) :
    pairedEtaTranslatedResidualEnergy a c ≤ pairedEtaTranslatedResidualEnergy b c +
      e * (2 + ∑ j, ‖c j‖) ^ 2 + (1 + 1 / e) * pairedEtaTranslateGridError a b c := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have hc := hi.mul_const (e * (2 + ∑ j, ‖c j‖) ^ 2)
  have hg := (integrableOn_pairedEtaTranslateGridError a b c).const_mul (1 + 1 / e)
  calc
    _ ≤ ∫ t : ℝ in Ioi 0,
        (Real.exp (-t) * ‖pairedEtaTranslatedResidual b c t‖ ^ 2 +
          Real.exp (-t) * (e * (2 + ∑ j, ‖c j‖) ^ 2)) +
          (1 + 1 / e) * (Real.exp (-t) *
            ‖pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t‖ ^ 2) := by
      apply integral_mono_ae (integrableOn_pairedEtaTranslatedResidual_weighted_sq a c)
        (((integrableOn_pairedEtaTranslatedResidual_weighted_sq b c).add hc).add hg)
      exact Eventually.of_forall fun t ↦ by
        have h := mul_le_mul_of_nonneg_left (pairedEtaTranslatedResidual_sq_le_grid_error a b c he t)
          (Real.exp_pos (-t)).le
        convert h using 1
        simp only [Pi.add_apply]
        ring
    _ = _ := by
      have hsplit := integral_add ((integrableOn_pairedEtaTranslatedResidual_weighted_sq b c).add hc) hg
      have hfirst := integral_add (integrableOn_pairedEtaTranslatedResidual_weighted_sq b c) hc
      simp only [Pi.add_apply] at hsplit hfirst
      rw [hsplit, hfirst, integral_mul_const, integral_const_mul]
      have hmass : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
        simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
      rw [hmass, one_mul]
      rfl

/-- The absolute change of the complete residual energy has the same symmetric grid-error allowance. -/
theorem abs_pairedEtaTranslatedResidualEnergy_sub_le_grid_error {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) {e : ℝ} (he : 0 < e) :
    |pairedEtaTranslatedResidualEnergy a c - pairedEtaTranslatedResidualEnergy b c| ≤
      e * (2 + ∑ j, ‖c j‖) ^ 2 + (1 + 1 / e) * pairedEtaTranslateGridError a b c := by
  have h₁ := pairedEtaTranslatedResidualEnergy_le_grid_error a b c he
  have h₂ := pairedEtaTranslatedResidualEnergy_le_grid_error b a c he
  rw [pairedEtaTranslateGridError_symm b a c] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end RiemannGaussian
