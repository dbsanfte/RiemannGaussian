import RiemannGaussian.GaussianMoebiusCancellation

/-!
# A global dominator for the normalized actual Möbius Gaussian

The proved cancellation controls the positive arithmetic end. A direct
absolutely convergent reciprocal-line bound controls every remaining real
center. Together they supply the global domination needed to transport
the signed sum through a complex Gaussian heat kernel.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- Absolute Dirichlet convergence gives a bound for the actual Gaussian sum at every real center. -/
theorem abs_gaussianMoebiusSum_le_dirichlet (a : ℝ) {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 1 < sigma) :
    |gaussianMoebiusSum a tau| ≤ moebiusDirichletMass sigma * Real.exp (a * sigma + tau * sigma ^ 2) := by
  have hg := ((integrable_exp_neg_mul_sq htau).const_mul
    (Real.exp (a * sigma + tau * sigma ^ 2))).mul_const (moebiusDirichletMass sigma)
  have h := norm_integral_le_of_norm_le hg
    (Eventually.of_forall (norm_zetaReciprocalGaussianKernel_le_dirichlet a tau hsigma))
  rw [integral_zetaReciprocalGaussianKernel_eq_gaussianMoebiusSum a htau hsigma,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    integral_mul_const, integral_const_mul, integral_gaussian] at h
  have hp := Real.sqrt_pos.mpr (div_pos Real.pi_pos htau)
  nlinarith

/-- The actual signed Gaussian sum normalized by its arithmetic exponential scale. -/
def normalizedGaussianMoebius (a : ℝ) : ℝ := gaussianMoebiusSum a 1 / Real.exp a

/-- The actual normalized signed sum tends to zero at the positive arithmetic end. -/
theorem normalizedGaussianMoebius_tendsto_zero : Tendsto normalizedGaussianMoebius atTop (𝓝 0) :=
  gaussianMoebiusSum_one_exp_ratio_tendsto_zero

/-- Every translate of the normalized arithmetic source is measurable for the heat integral. -/
theorem aestronglyMeasurable_normalizedGaussianMoebius_add (a : ℝ) :
    AEStronglyMeasurable (fun v : ℝ ↦ (normalizedGaussianMoebius (a + v) : ℂ)) := by
  unfold normalizedGaussianMoebius gaussianMoebiusSum
  simp_rw [Complex.ofReal_div, Complex.ofReal_tsum]
  have hn : AEStronglyMeasurable (fun v : ℝ ↦ ∑' n : ℕ, (gaussianMoebiusSummand (a + v) 1 n : ℂ)) :=
    AEStronglyMeasurable.tsum fun n ↦ by unfold gaussianMoebiusSummand; fun_prop
  have hd : AEStronglyMeasurable (fun v : ℝ ↦ ((Real.exp (a + v) : ℂ))⁻¹) := by fun_prop
  convert hn.mul hd using 1
  funext v
  exact div_eq_mul_inv _ _

/-- One finite global bound controls the actual normalized source at every real center. -/
theorem exists_bound_normalizedGaussianMoebius :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, |normalizedGaussianMoebius a| ≤ C := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp gaussianMoebiusSum_one_le_reciprocal_log_gain_eventually
  let B := max A 1
  let C := max 1 (moebiusDirichletMass 2 * Real.exp (B + 4))
  have hD : 0 ≤ moebiusDirichletMass 2 := le_trans zero_le_one (one_le_moebiusDirichletMass (by norm_num))
  refine ⟨C, (show 0 ≤ (1 : ℝ) by norm_num).trans (le_max_left _ _), ?_⟩
  intro a
  unfold normalizedGaussianMoebius
  rw [abs_div, abs_of_pos (Real.exp_pos a)]
  by_cases ha : B ≤ a
  · have haA : A ≤ a := (le_max_left _ _).trans ha
    have haone : 1 ≤ a := (le_max_right _ _).trans ha
    have hL : 0 < localZetaLogHeight a := by linarith [two_lt_localZetaLogHeight a]
    apply (div_le_div_of_nonneg_right (hA a haA) (Real.exp_pos a).le).trans
    apply (show Real.exp (a - a / (1000000 * localZetaLogHeight a)) / Real.exp a ≤ 1 from ?_).trans (le_max_left _ _)
    rw [div_le_one (Real.exp_pos a), Real.exp_le_exp]
    have h : 0 ≤ a / (1000000 * localZetaLogHeight a) := by positivity
    linarith
  · have hb := abs_gaussianMoebiusSum_le_dirichlet a (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    norm_num at hb
    apply (div_le_div_of_nonneg_right hb (Real.exp_pos a).le).trans
    calc
      _ = moebiusDirichletMass 2 * Real.exp (a + 4) := by
        rw [mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
      _ ≤ moebiusDirichletMass 2 * Real.exp (B + 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hD
      _ ≤ C := le_max_right _ _

end

end RiemannGaussian
