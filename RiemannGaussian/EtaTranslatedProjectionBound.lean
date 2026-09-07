import RiemannGaussian.EtaTranslatedResidual

/-!
# Actual zero displacement from the complete eta translate residual

The nonzero compact target transform is recovered exactly at an actual
zero. Cauchy--Schwarz on the positive half-line then controls that zero's
horizontal displacement by the full critical residual energy. The finite
cutoff version includes the entire coefficient-dependent tail budget.
-/

open Complex Filter MeasureTheory Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The complete translate residual bounds the right-half zero coordinate with its exact nonzero compact-target normalization. -/
theorem two_mul_re_sub_one_mul_head_norm_sq_le_residual {d : ℕ} (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    (2 * rho.1.re - 1) * ‖pairedEtaProjectionHeadTransform rho.1‖ ^ 2 ≤
      pairedEtaTranslatedResidualEnergy a c := by
  let f : ℝ → ℝ := fun t ↦ Real.exp (-(1 / 2) * t) * ‖pairedEtaTranslatedResidual a c t‖
  let g : ℝ → ℝ := fun t ↦ Real.exp (-(rho.1.re - 1 / 2) * t)
  have hf0 (t : ℝ) : 0 ≤ f t := by dsimp [f]; positivity
  have hg0 (t : ℝ) : 0 ≤ g t := (Real.exp_pos _).le
  have hfsq (t : ℝ) : f t ^ 2 = Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hgsq (t : ℝ) : g t ^ 2 = Real.exp (-(2 * rho.1.re - 1) * t) := by
    dsimp [g]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hfi : IntegrableOn (fun t : ℝ ↦ f t ^ 2) (Ioi 0) := by
    simp_rw [hfsq]
    exact integrableOn_pairedEtaTranslatedResidual_weighted_sq a c
  have hgi : IntegrableOn (fun t : ℝ ↦ g t ^ 2) (Ioi 0) := by
    simp_rw [hgsq]
    exact integrableOn_exp_mul_Ioi (by linarith : -(2 * rho.1.re - 1) < 0) 0
  have hfm : Measurable f := by
    dsimp [f]
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_pairedEtaTranslatedResidual a c).norm
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hf : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioi 0)) := by
    simpa using (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfi
  have hg : MemLp g (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioi 0)) := by
    simpa using (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hgi
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_iff.mpr ⟨(by norm_num : (1 : ℝ) < 2), (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)⟩)
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hf hg
  have hcs : (∫ t : ℝ in Ioi 0, f t * g t) ≤
      Real.sqrt (pairedEtaTranslatedResidualEnergy a c) * Real.sqrt (1 / (2 * rho.1.re - 1)) := by
    have hF : (∫ t : ℝ in Ioi 0, f t ^ 2) = pairedEtaTranslatedResidualEnergy a c := by
      simp_rw [hfsq]
      rfl
    have hG : (∫ t : ℝ in Ioi 0, g t ^ 2) = 1 / (2 * rho.1.re - 1) := by
      simp_rw [hgsq]
      rw [integral_exp_mul_Ioi (by linarith : -(2 * rho.1.re - 1) < 0)]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hF, hG] using hholder
  have hpoint (t : ℝ) :
      ‖pairedEtaTranslatedResidual a c t * Complex.exp (-rho.1 * t)‖ = f t * g t := by
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, mul_zero, sub_zero]
    have he : Real.exp (-rho.1.re * t) = Real.exp (-(1 / 2) * t) *
        Real.exp (-(rho.1.re - 1 / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    dsimp [f, g]
    ring
  have hnorm : ‖pairedEtaProjectionHeadTransform rho.1‖ ≤
      Real.sqrt (pairedEtaTranslatedResidualEnergy a c) * Real.sqrt (1 / (2 * rho.1.re - 1)) := by
    rw [← integral_Ioi_pairedEtaTranslatedResidual_mul_exp_zero rho ha c]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [hpoint]
    exact hcs
  have hd : 0 < 2 * rho.1.re - 1 := by linarith
  have hsquare : ‖pairedEtaProjectionHeadTransform rho.1‖ ^ 2 ≤
      pairedEtaTranslatedResidualEnergy a c / (2 * rho.1.re - 1) := by
    calc
      _ ≤ (Real.sqrt (pairedEtaTranslatedResidualEnergy a c) * Real.sqrt (1 / (2 * rho.1.re - 1))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (pairedEtaTranslatedResidualEnergy_nonneg a c),
          Real.sq_sqrt (by positivity : 0 ≤ 1 / (2 * rho.1.re - 1))]
        ring
  simpa only [mul_comm] using (le_div_iff₀ hd).mp hsquare

/-- Every finite residual interval supplies an actual-zero inequality with its complete infinite-tail allowance. -/
theorem two_mul_re_sub_one_mul_head_norm_sq_le_residual_cutoff {d : ℕ} (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ)
    {T : ℝ} (hT : Real.log 2 ≤ T) :
    (2 * rho.1.re - 1) * ‖pairedEtaProjectionHeadTransform rho.1‖ ^ 2 ≤
      pairedEtaTranslatedResidualEnergyCutoff a c T + Real.exp (-T) * (∑ j, ‖c j‖) ^ 2 :=
  (two_mul_re_sub_one_mul_head_norm_sq_le_residual rho hrho ha c).trans
    (pairedEtaTranslatedResidualEnergy_le_cutoff a c hT)

end

end RiemannGaussian
