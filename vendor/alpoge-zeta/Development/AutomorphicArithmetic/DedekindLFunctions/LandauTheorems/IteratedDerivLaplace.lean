import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem iteratedDeriv_laplace_int (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hb
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

theorem iteratedDeriv_laplace_meas (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

theorem iteratedDeriv_laplace_bound (g : ℝ → ℝ) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (b : ℝ) (z : ℂ) (hz : 2 + b ≤ z.re)
    (u : ℝ) (hu : 0 < u) :
    ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-b * u)) := by
  have h1 : ‖(g u : ℂ)‖ ≤ C * Real.exp (2 * u) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu.le
  have h2 : ‖((-u : ℝ) : ℂ) ^ k‖ = u ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
  have h3 : ‖cexp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC : 0 ≤ C * Real.exp (2 * u) := le_trans (norm_nonneg _) h1
  rw [norm_mul, norm_mul, h2]
  calc ‖(g u : ℂ)‖ * u ^ k * ‖cexp (-z * u)‖
      ≤ C * Real.exp (2 * u) * u ^ k * Real.exp (-(2 + b) * u) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
          (mul_nonneg hC (by positivity))
    _ = C * (u ^ k * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
    _ = C * (u ^ k * Real.exp (-b * u)) := by
        rw [← Real.exp_add]
        ring_nf

theorem iteratedDeriv_laplace_hasDerivAt (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-s * u)) s := by
  set δ := (s.re - 2) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hre : ∀ z ∈ Metric.ball s δ, 2 + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re] at h1
    have h2 := (abs_le.mp (h1.trans hz.le)).1
    linarith
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' (Integrable.const_mul (iteratedDeriv_laplace_int k δ hδpos) C)
      (iteratedDeriv_laplace_meas g hg k s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact iteratedDeriv_laplace_bound g C hgC k δ s (hre s (Metric.mem_ball_self hδpos)) u hu
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
    (F' := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-z * u))
    (Metric.ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => iteratedDeriv_laplace_meas g hg k z) hint
    (iteratedDeriv_laplace_meas g hg (k + 1) s) ?_
    (Integrable.const_mul (iteratedDeriv_laplace_int (k + 1) δ hδpos) C) ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hz => ?_)
    exact iteratedDeriv_laplace_bound g C hgC (k + 1) δ z (hre z hz) u hu
  · refine Eventually.of_forall fun u z _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (u : ℂ)) (-(u : ℂ)) z := by
      simpa using (hasDerivAt_id' z).neg.mul_const (u : ℂ)
    have h2 := h1.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ k)
    refine h2.congr_deriv ?_
    push_cast
    ring

theorem iteratedDeriv_laplace (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) s =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u) := by
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ j : ℕ, ∀ z : ℂ, 2 < z.re →
      iteratedDeriv j (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) z =
        ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u) := by
    intro j
    induction j with
    | zero =>
      intro z _
      simp
    | succ j ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u))
          =ᶠ[𝓝 z] fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-w * u) :=
        Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => ih w hw
      rw [hev.deriv_eq]
      exact (iteratedDeriv_laplace_hasDerivAt g hg C hgC j z hz).deriv
  exact key k s hs

end Deduction

end
