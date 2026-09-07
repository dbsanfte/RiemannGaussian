import RiemannGaussian.GaussianMoebiusHeatScale
import RiemannGaussian.GaussianMoebiusNormalized
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The cumulative actual Gaussian Möbius sum

Cancellation at every fixed positive heat time survives integration up to
a literal real cutoff. A global bound for the normalized arithmetic source
discharges the one-sided dominated-convergence argument. The exact change
of variables is retained before taking the normalized limit.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual Gaussian Möbius sum is measurable as a function of its arithmetic center. -/
theorem measurable_gaussianMoebiusSum (tau : ℝ) :
    Measurable (fun a : ℝ ↦ gaussianMoebiusSum a tau) := by
  unfold gaussianMoebiusSum
  exact Measurable.tsum fun n ↦ by unfold gaussianMoebiusSummand; fun_prop

/-- At each positive heat time, one finite constant bounds the normalized actual arithmetic source at all real centers. -/
theorem exists_bound_gaussianMoebiusSum_exp_ratio {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, |gaussianMoebiusSum a tau / Real.exp a| ≤ C := by
  have hz := (gaussianMoebiusSum_exp_ratio_tendsto_zero htau).norm
  have he : ∀ᶠ a : ℝ in atTop, |gaussianMoebiusSum a tau / Real.exp a| < 1 := by
    simpa only [Real.norm_eq_abs] using hz.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℝ)‖ < 1))
  obtain ⟨A, hA⟩ := eventually_atTop.mp he
  let B := max A 0
  let C := max 1 (moebiusDirichletMass 2 * Real.exp (B + 4 * tau))
  have hD : 0 ≤ moebiusDirichletMass 2 := le_trans zero_le_one (one_le_moebiusDirichletMass (by norm_num))
  refine ⟨C, (show 0 ≤ (1 : ℝ) by norm_num).trans (le_max_left _ _), ?_⟩
  intro a
  by_cases ha : B ≤ a
  · exact (hA a ((le_max_left _ _).trans ha)).le.trans (le_max_left _ _)
  · rw [abs_div, abs_of_pos (Real.exp_pos a)]
    have hb := abs_gaussianMoebiusSum_le_dirichlet a htau (by norm_num : (1 : ℝ) < 2)
    apply (div_le_div_of_nonneg_right hb (Real.exp_pos a).le).trans
    calc
      _ = moebiusDirichletMass 2 * Real.exp (a + 4 * tau) := by
        rw [mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
      _ ≤ moebiusDirichletMass 2 * Real.exp (B + 4 * tau) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hD
      _ ≤ C := le_max_right _ _

/-- The complete signed Gaussian source is integrable up to every actual real cutoff. -/
theorem integrableOn_gaussianMoebiusSum_Iic {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    IntegrableOn (fun u : ℝ ↦ gaussianMoebiusSum u tau) (Iic a) := by
  obtain ⟨C, _, hC⟩ := exists_bound_gaussianMoebiusSum_exp_ratio htau
  apply ((integrableOn_exp_Iic a).const_mul C).mono'
    (measurable_gaussianMoebiusSum tau).aestronglyMeasurable
  exact Eventually.of_forall fun u ↦ by
    rw [Real.norm_eq_abs]
    have h := hC u
    rw [abs_div, abs_of_pos (Real.exp_pos u), div_le_iff₀ (Real.exp_pos u)] at h
    exact h

/-- The full signed Gaussian arithmetic source integrated up to the literal logarithmic cutoff. -/
def gaussianMoebiusCumulative (a tau : ℝ) : ℝ :=
  ∫ u : ℝ in Iic a, gaussianMoebiusSum u tau

/-- A reflected translation of the whole real line keeps the one-sided cutoff exactly. -/
theorem gaussianMoebiusCumulative_eq_integral_sub (a tau : ℝ) :
    gaussianMoebiusCumulative a tau =
      ∫ v : ℝ in Ici 0, gaussianMoebiusSum (a - v) tau := by
  unfold gaussianMoebiusCumulative
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici]
  rw [← integral_sub_left_eq_self ((Iic a).indicator (fun u : ℝ ↦ gaussianMoebiusSum u tau)) volume a]
  apply integral_congr_ae
  exact Eventually.of_forall fun v ↦ by
    simp only [indicator_apply, mem_Iic, mem_Ici]
    simp only [show a - v ≤ a ↔ (0 : ℝ) ≤ v by constructor <;> intro h <;> linarith]

/-- The exact normalized cumulative identity is a one-sided exponential convolution of the original signed source. -/
theorem gaussianMoebiusCumulative_exp_ratio_eq_integral (a tau : ℝ) :
    gaussianMoebiusCumulative a tau / Real.exp a =
      ∫ v : ℝ in Ici 0, (gaussianMoebiusSum (a - v) tau / Real.exp (a - v)) * Real.exp (-v) := by
  rw [gaussianMoebiusCumulative_eq_integral_sub, ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun v ↦ by
    dsimp only
    rw [Real.exp_sub, Real.exp_neg]
    field_simp

/-- Every fixed positive heat time gives a vanishing normalized cumulative signed Möbius source. -/
theorem gaussianMoebiusCumulative_exp_ratio_tendsto_zero {tau : ℝ} (htau : 0 < tau) :
    Tendsto (fun a : ℝ ↦ gaussianMoebiusCumulative a tau / Real.exp a) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_bound_gaussianMoebiusSum_exp_ratio htau
  have hg : IntegrableOn (fun v : ℝ ↦ C * Real.exp (-v)) (Ici 0) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_neg_Ioi 0)).const_mul C
  have hmeas (a : ℝ) : AEStronglyMeasurable (fun v : ℝ ↦
      (gaussianMoebiusSum (a - v) tau / Real.exp (a - v)) * Real.exp (-v)) (volume.restrict (Ici 0)) := by
    apply Measurable.aestronglyMeasurable
    exact (((measurable_gaussianMoebiusSum tau).comp (measurable_const.sub measurable_id)).div
      (by fun_prop)).mul (by fun_prop)
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := fun a v : ℝ ↦ (gaussianMoebiusSum (a - v) tau / Real.exp (a - v)) * Real.exp (-v))
    (f := fun _ : ℝ ↦ (0 : ℝ)) (fun v : ℝ ↦ C * Real.exp (-v))
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun a ↦ Eventually.of_forall fun v ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hC (a - v)) (Real.exp_pos _).le)
    hg
    (Eventually.of_forall fun v ↦ by
      have hs : Tendsto (fun a : ℝ ↦ a - v) atTop atTop := by
        simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-v) tendsto_id
      simpa using (gaussianMoebiusSum_exp_ratio_tendsto_zero htau).comp hs |>.mul_const (Real.exp (-v)))
  simp only [integral_zero] at h
  simpa only [gaussianMoebiusCumulative_exp_ratio_eq_integral] using h

end

end RiemannGaussian
