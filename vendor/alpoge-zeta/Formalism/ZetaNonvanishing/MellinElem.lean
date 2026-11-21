import Formalism.ZetaRealNonvanish

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

theorem mellinElem_part1 (a σ : ℝ) (h : a < σ) :
    IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (a + (-σ - 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  simp only
  rw [Real.rpow_add hx0]

theorem mellinElem_part2 (σ : ℝ) (h : 1 < σ) :
    IntegrableOn (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) (Ioi 1) := by
  set ε : ℝ := (σ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (ε - σ) / ε) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by rw [hε]; linarith) one_pos).div_const ε
  refine hi.mono' ?_ ?_
  · have : Measurable (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) := by fun_prop
    exact this.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hl := Real.log_le_rpow_div hx0.le hε0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have e1 : x * Real.log x * x ^ (-σ - 1) = Real.log x * x ^ (-σ) := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    rw [e1, Real.rpow_sub hx0, Real.rpow_neg hx0.le]
    calc Real.log x * (x ^ σ)⁻¹ ≤ x ^ ε / ε * (x ^ σ)⁻¹ :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = x ^ ε / x ^ σ / ε := by ring

theorem mellinElem_part3 (a : ℝ) (s : ℂ) (h : a < s.re) :
    ∫ x in Ioi (1:ℝ), ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - a) := by
  have e : EqOn (fun x : ℝ => ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - s - 1)) (Ioi 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    simp only
    rw [ofReal_cpow hx0.le, ← cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne')]
    ring_nf
  have hre : ((a : ℂ) - s - 1).re < -1 := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_cpow_of_lt hre one_pos,
    ofReal_one, one_cpow, show (a : ℂ) - s - 1 + 1 = -(s - a) by ring, neg_div_neg_eq]

theorem mellinElem_part4 (s : ℂ) (h : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - 1) ^ 2 := by
  set w : ℂ := 1 - s with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hw] at this
    linarith
  have hwre : w.re < 0 := by simp [hw]; linarith
  have e : EqOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans one_pos hx).ne'
    simp only
    rw [cpow_sub _ _ hx0, cpow_one]
    push_cast
    field_simp
  have hderiv : ∀ x ∈ Ici (1:ℝ), HasDerivAt
      (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
      ((Real.log x : ℂ) * (x : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    have hx0c : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
    have h1 := hasDerivAt_ofReal_cpow_const hx0.ne' hw0
    have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
      (Real.hasDerivAt_log hx0.ne').ofReal_comp
    have h3 := h1.mul ((h2.div_const w).sub_const (1 / w ^ 2))
    have h4 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
        (w * (x : ℂ) ^ (w - 1) * ((Real.log x : ℂ) / w - 1 / w ^ 2) + (x : ℂ) ^ w * (((x⁻¹ : ℝ) : ℂ) / w)) x := h3
    refine h4.congr_deriv ?_
    have ea : (x : ℂ) ^ (w - 1) = (x : ℂ) ^ (-s) := by congr 1; rw [hw]; ring
    have eb : (x : ℂ) ^ w = x * (x : ℂ) ^ (-s) := by
      rw [show w = 1 + -s by rw [hw]; ring, cpow_add _ _ hx0c, cpow_one]
    rw [ea, eb]
    push_cast
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
    refine (mellinElem_part2 s.re h).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      exact ((continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0.ne')).mul
        (continuousAt_ofReal_cpow_const x (-s) (Or.inr hx0.ne'))).continuousWithinAt
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
        norm_cpow_eq_rpow_re_of_pos hx0, abs_of_nonneg (by positivity),
        Real.rpow_sub_one hx0.ne']
      simp only [neg_re]
      apply le_of_eq
      field_simp
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w.re = -r := ⟨-w.re, by ring⟩
    have hr0 : 0 < r := by linarith
    have hA : Tendsto (fun x : ℝ => x ^ (-r)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hr0
    have hB : Tendsto (fun x : ℝ => Real.log x * x ^ (-r)) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hr0).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.rpow_neg hx.le, div_eq_mul_inv]
    have hg := (hB.div_const ‖w‖).add (hA.div_const (‖w‖ ^ 2))
    simp only [zero_div, add_zero] at hg
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, hr]
    calc x ^ (-r) * ‖(Real.log x : ℂ) / w - 1 / w ^ 2‖
        ≤ x ^ (-r) * (Real.log x / ‖w‖ + 1 / ‖w‖ ^ 2) := by
          gcongr
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
            norm_one, norm_pow]
      _ = Real.log x * x ^ (-r) / ‖w‖ + x ^ (-r) / ‖w‖ ^ 2 := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_div, zero_sub, one_mul]
  rw [hw]
  field_simp
  ring

theorem mellinElem : MellinElem :=
  ⟨mellinElem_part1, mellinElem_part2, mellinElem_part3, mellinElem_part4⟩

end Formalism
