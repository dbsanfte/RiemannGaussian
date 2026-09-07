import RiemannGaussian.GaussianMoebiusCumulativeAtoms
import RiemannGaussian.GaussianMoebiusCutoffKernel
import RiemannGaussian.MoebiusFiniteCutoff

/-!
# Exact Gaussian smoothing of the literal finite Möbius prefix

Each genuine integer endpoint gives a signed cutoff atom. Its reflection
identity and summable norm integrals justify the full arithmetic exchange.
The smoothed finite prefix is exactly the cumulative Gaussian sum. The
unsmoothed prefix retains an explicit error from multiplicative cutoff
displacement and integer rounding.
-/

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- One signed positive-integer endpoint contributes to the literal Gaussian-smoothed finite cutoff. -/
def moebiusGaussianCutoffAtom (a tau : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  moebiusCutoffGaussian tau v *
    if Real.log (n + 1 : ℝ) ≤ a + v then ((μ (n + 1) : ℤ) : ℝ) else 0

/-- Reflection at the actual logarithmic integer endpoint preserves the complete signed cutoff atom. -/
theorem moebiusGaussianCutoffAtom_eq_reflected (a tau : ℝ) (n : ℕ) (v : ℝ) :
    moebiusGaussianCutoffAtom a tau n v =
      (Iic a).indicator (fun u : ℝ ↦ gaussianMoebiusSummand u tau (n + 1))
        (Real.log (n + 1 : ℝ) - v) := by
  unfold moebiusGaussianCutoffAtom
  simp only [indicator_apply, mem_Iic]
  by_cases h : Real.log (n + 1 : ℝ) ≤ a + v
  · have h' : Real.log (n + 1 : ℝ) - v ≤ a := by linarith
    simp only [h, h', if_true, gaussianMoebiusSummand, moebiusCutoffGaussian, Nat.cast_add, Nat.cast_one]
    rw [mul_comm]
    congr 2
    ring
  · have h' : ¬ Real.log (n + 1 : ℝ) - v ≤ a := by linarith
    simp only [h, h', if_false, mul_zero]

/-- Every actual Gaussian cutoff atom is integrable, including its sharp integer endpoint. -/
theorem integrable_moebiusGaussianCutoffAtom {tau : ℝ} (htau : 0 < tau) (a : ℝ) (n : ℕ) :
    Integrable (moebiusGaussianCutoffAtom a tau n) := by
  change Integrable (fun v : ℝ ↦ moebiusGaussianCutoffAtom a tau n v)
  simp_rw [moebiusGaussianCutoffAtom_eq_reflected]
  have hi : Integrable ((Iic a).indicator (fun u : ℝ ↦ gaussianMoebiusSummand u tau (n + 1))) :=
    (integrable_gaussianMoebiusSummand_center htau (n + 1)).indicator measurableSet_Iic
  exact hi.comp_sub_left _

/-- The full signed integral of a sharp cutoff atom equals its cumulative arithmetic Gaussian. -/
theorem integral_moebiusGaussianCutoffAtom (a tau : ℝ) (n : ℕ) :
    (∫ v : ℝ, moebiusGaussianCutoffAtom a tau n v) =
      ∫ u : ℝ in Iic a, gaussianMoebiusSummand u tau (n + 1) := by
  simp_rw [moebiusGaussianCutoffAtom_eq_reflected]
  rw [integral_sub_left_eq_self, integral_indicator measurableSet_Iic]

/-- The same reflection retains the exact absolute integral needed for the infinite arithmetic exchange. -/
theorem integral_norm_moebiusGaussianCutoffAtom (a tau : ℝ) (n : ℕ) :
    (∫ v : ℝ, ‖moebiusGaussianCutoffAtom a tau n v‖) =
      ∫ u : ℝ in Iic a, ‖gaussianMoebiusSummand u tau (n + 1)‖ := by
  simp_rw [moebiusGaussianCutoffAtom_eq_reflected, norm_indicator_eq_indicator_norm]
  rw [integral_sub_left_eq_self, integral_indicator measurableSet_Iic]

/-- The complete family of sharp-cutoff atom norm integrals is summable at every positive heat time. -/
theorem summable_integral_norm_moebiusGaussianCutoffAtom {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    Summable (fun n : ℕ ↦ ∫ v : ℝ, ‖moebiusGaussianCutoffAtom a tau n v‖) := by
  simp_rw [integral_norm_moebiusGaussianCutoffAtom]
  exact (summable_integral_norm_gaussianMoebiusSummand_Iic htau a).comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + 1) by intro n m h; change n + 1 = m + 1 at h; omega)

/-- The full endpoint series is exactly the literal finite prefix at the shifted cutoff, with all Möbius signs retained. -/
theorem tsum_moebiusGaussianCutoffAtom (a tau v : ℝ) :
    (∑' n : ℕ, moebiusGaussianCutoffAtom a tau n v) =
      moebiusCutoffGaussian tau v * moebiusLogPrefix (a + v) := by
  unfold moebiusGaussianCutoffAtom
  rw [tsum_mul_left, ← moebiusLogPrefix_eq_tsum]

/-- The cumulative actual Gaussian sum equals the Gaussian convolution of the original finite arithmetic prefix. -/
theorem gaussianMoebiusCumulative_eq_smoothed_finitePrefix {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    gaussianMoebiusCumulative a tau =
      ∫ v : ℝ, moebiusCutoffGaussian tau v * moebiusLogPrefix (a + v) := by
  rw [gaussianMoebiusCumulative_eq_tsum_integral_succ htau]
  simp_rw [← integral_moebiusGaussianCutoffAtom a tau]
  rw [integral_tsum_of_summable_integral_norm (integrable_moebiusGaussianCutoffAtom htau a)
    (summable_integral_norm_moebiusGaussianCutoffAtom htau a)]
  simp_rw [tsum_moebiusGaussianCutoffAtom]

/-- The whole Gaussian-smoothed finite prefix is genuinely integrable over the complete logarithmic displacement range. -/
theorem integrable_moebiusGaussian_finitePrefix {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    Integrable (fun v : ℝ ↦ moebiusCutoffGaussian tau v * moebiusLogPrefix (a + v)) := by
  have hg : Integrable (fun v : ℝ ↦ Real.exp a * (moebiusCutoffGaussian tau v * Real.exp v)) := by
    simpa only [one_mul] using (integrable_moebiusCutoffGaussian_mul_exp htau 1).const_mul (Real.exp a)
  apply hg.mono' ?_ (Eventually.of_forall fun v ↦ ?_)
  · apply Measurable.aestronglyMeasurable
    have hm : Measurable (moebiusCutoffGaussian tau) := by unfold moebiusCutoffGaussian; fun_prop
    exact hm.mul
      (measurable_moebiusLogPrefix.comp (measurable_const.add measurable_id))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (moebiusCutoffGaussian_pos _ _)]
    apply (mul_le_mul_of_nonneg_left (abs_moebiusLogPrefix_le (a + v))
      (moebiusCutoffGaussian_pos _ _).le).trans_eq
    rw [Real.exp_add]
    ring

/-- The exact signed cutoff error is retained before taking its absolute arithmetic bound. -/
theorem moebiusFinitePrefix_gaussian_error_identity {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    moebiusCutoffGaussianMass tau * moebiusLogPrefix a - gaussianMoebiusCumulative a tau =
      ∫ v : ℝ, moebiusCutoffGaussian tau v * (moebiusLogPrefix a - moebiusLogPrefix (a + v)) := by
  rw [gaussianMoebiusCumulative_eq_smoothed_finitePrefix htau]
  have hc : Integrable (fun v : ℝ ↦ moebiusCutoffGaussian tau v * moebiusLogPrefix a) :=
    (integrable_moebiusCutoffGaussian htau).mul_const _
  calc
    _ = (∫ v : ℝ, moebiusCutoffGaussian tau v * moebiusLogPrefix a) -
        ∫ v : ℝ, moebiusCutoffGaussian tau v * moebiusLogPrefix (a + v) := by
      rw [integral_mul_const, integral_moebiusCutoffGaussian htau]
    _ = _ := by
      rw [← integral_sub hc (integrable_moebiusGaussian_finitePrefix htau a)]
      apply integral_congr_ae
      exact Eventually.of_forall fun v ↦ by dsimp only; ring

/-- The literal finite prefix differs from its smoothed counterpart by the full multiplicative cutoff error and one integer-rounding unit. -/
theorem abs_moebiusFinitePrefix_gaussian_error_le {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    |moebiusCutoffGaussianMass tau * moebiusLogPrefix a - gaussianMoebiusCumulative a tau| ≤
      Real.exp a * (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) +
        moebiusCutoffGaussianMass tau := by
  have hg : Integrable (fun v : ℝ ↦
      Real.exp a * (moebiusCutoffGaussian tau v * |Real.exp v - 1|) + moebiusCutoffGaussian tau v) :=
    ((integrable_moebiusCutoffGaussian_abs_exp_sub_one htau).const_mul (Real.exp a)).add
      (integrable_moebiusCutoffGaussian htau)
  have h := norm_integral_le_of_norm_le
    (f := fun v : ℝ ↦ moebiusCutoffGaussian tau v * (moebiusLogPrefix a - moebiusLogPrefix (a + v)))
    hg (Eventually.of_forall fun v ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (moebiusCutoffGaussian_pos _ _),
      abs_sub_comm (moebiusLogPrefix a)]
    apply (mul_le_mul_of_nonneg_left (abs_moebiusLogPrefix_sub_le a v)
      (moebiusCutoffGaussian_pos _ _).le).trans_eq
    ring)
  rw [integral_add ((integrable_moebiusCutoffGaussian_abs_exp_sub_one htau).const_mul (Real.exp a))
    (integrable_moebiusCutoffGaussian htau), integral_const_mul, integral_moebiusCutoffGaussian htau] at h
  rw [moebiusFinitePrefix_gaussian_error_identity htau]
  exact h

end

end RiemannGaussian
