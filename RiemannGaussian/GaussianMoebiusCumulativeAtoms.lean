import RiemannGaussian.GaussianMoebiusPrimitive

/-!
# Absolute arithmetic exchange at a cumulative Gaussian cutoff

The actual individual Möbius Gaussians have an absolutely summable family
of norm integrals up to each real cutoff. The complete signed cumulative
source is therefore exactly their integrated series, with no omitted tail
and no unproved sum–integral interchange.
-/

open Complex MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Each actual Gaussian arithmetic coefficient has the full absolute Dirichlet-line majorant. -/
theorem abs_gaussianMoebiusSummand_le_dirichlet (a sigma : ℝ) {tau : ℝ}
    (htau : 0 < tau) (n : ℕ) :
    |gaussianMoebiusSummand a tau n| ≤ Real.exp (a * sigma + tau * sigma ^ 2) *
      ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) (sigma : ℂ) n‖ := by
  have h : ‖∫ t : ℝ, gaussianMoebiusMellinTerm a tau sigma n t‖ ≤
      ∫ t : ℝ, ‖gaussianMoebiusMellinTerm a tau sigma n t‖ := norm_integral_le_integral_norm _
  rw [integral_gaussianMoebiusMellinTerm a sigma htau, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  simp_rw [norm_gaussianMoebiusMellinTerm] at h
  rw [integral_mul_const, integral_const_mul, integral_gaussian] at h
  have hp := Real.sqrt_pos.mpr (div_pos Real.pi_pos htau)
  nlinarith

/-- Each actual signed arithmetic atom is integrable as a function of its full real center. -/
theorem integrable_gaussianMoebiusSummand_center {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    Integrable (fun a : ℝ ↦ gaussianMoebiusSummand a tau n) := by
  convert ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * tau))).comp_sub_right
    (Real.log n)).const_mul (((μ n : ℤ) : ℝ)) using 1
  funext a
  unfold gaussianMoebiusSummand
  congr 2
  ring

/-- The norm integrals of every original Möbius atom form an absolutely summable series at each cumulative cutoff. -/
theorem summable_integral_norm_gaussianMoebiusSummand_Iic {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    Summable (fun n : ℕ ↦ ∫ u : ℝ in Iic a, ‖gaussianMoebiusSummand u tau n‖) := by
  have hs := (summable_moebiusDirichletMass (by norm_num : (1 : ℝ) < 2)).mul_left
    (Real.exp (4 * tau) * (Real.exp (2 * a) / 2))
  apply hs.of_nonneg_of_le (fun n ↦ integral_nonneg fun u ↦ norm_nonneg _)
  intro n
  let D := ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) (2 : ℂ) n‖
  have hg : IntegrableOn (fun u : ℝ ↦ (Real.exp (4 * tau) * D) * Real.exp (2 * u)) (Iic a) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) a).const_mul _
  have hb := integral_mono (integrable_gaussianMoebiusSummand_center htau n).integrableOn.norm hg
    (fun u ↦ by
      rw [Real.norm_eq_abs]
      apply (abs_gaussianMoebiusSummand_le_dirichlet u 2 htau n).trans_eq
      rw [show u * 2 + tau * (2 : ℝ) ^ 2 = 4 * tau + 2 * u by ring, Real.exp_add]
      dsimp [D]
      ring)
  rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 2)] at hb
  exact hb.trans_eq (by dsimp [D]; ring)

/-- The cumulative actual signed source is exactly the complete series of integrated Möbius atoms. -/
theorem gaussianMoebiusCumulative_eq_tsum_integral {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    gaussianMoebiusCumulative a tau =
      ∑' n : ℕ, ∫ u : ℝ in Iic a, gaussianMoebiusSummand u tau n := by
  unfold gaussianMoebiusCumulative gaussianMoebiusSum
  exact (integral_tsum_of_summable_integral_norm
    (fun n ↦ (integrable_gaussianMoebiusSummand_center htau n).integrableOn)
    (summable_integral_norm_gaussianMoebiusSummand_Iic htau a)).symm

/-- The positive-index cumulative arithmetic series is absolutely convergent; its zero index contributes nothing. -/
theorem gaussianMoebiusCumulative_eq_tsum_integral_succ {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    gaussianMoebiusCumulative a tau =
      ∑' n : ℕ, ∫ u : ℝ in Iic a, gaussianMoebiusSummand u tau (n + 1) := by
  have hs := (hasSum_integral_of_summable_integral_norm
    (fun n ↦ (integrable_gaussianMoebiusSummand_center htau n).integrableOn)
    (summable_integral_norm_gaussianMoebiusSummand_Iic htau a)).summable
  have hzero : (∫ u : ℝ in Iic a, gaussianMoebiusSummand u tau 0) = 0 := by
    simp [gaussianMoebiusSummand]
  rw [gaussianMoebiusCumulative_eq_tsum_integral htau]
  simpa only [Finset.sum_range_one, hzero, zero_add] using (hs.sum_add_tsum_nat_add 1).symm

end

end RiemannGaussian
