/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexGaussianCurvature
import RiemannGaussian.SuzukiEtaSignedCurrent

/-!
# A signed Gaussian estimate for the infinite eta quartic numerator

All eta factors and their phases remain in the numerator. The whole
real-line current is integrable together with its derivative, so its
integral disappears legitimately. The resulting exact square identity
gives an unconditional one-sided bound by an eta fourth-power allowance.
No completion or variable carrier denominator is included in that bound.
-/

open Complex Filter MeasureTheory Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- Cauchy's estimate gives a linear growth bound for every derivative
of the actual infinite eta function on the positive half-plane. -/
theorem norm_iteratedDeriv_pairedEtaCore_le (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖iteratedDeriv k pairedEtaCore s‖ ≤
      (k.factorial : ℝ) * ((‖s‖ + s.re / 2) / (s.re / 2)) / (s.re / 2) ^ k := by
  have hr : 0 < s.re / 2 := by positivity
  have hre (w : ℂ) (hw : ‖w - s‖ ≤ s.re / 2) : s.re / 2 ≤ w.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hw)).1
    simp only [Complex.sub_re] at h
    linarith
  have hf : DiffContOnCl ℂ pairedEtaCore (ball s (s.re / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    rw [closure_ball _ hr.ne', mem_closedBall, dist_eq_norm] at hw
    exact (analyticOnNhd_pairedEtaCore w (hr.trans_le (hre w hw))).differentiableAt.differentiableWithinAt
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hf
  intro w hw
  have hd : ‖w - s‖ = s.re / 2 := mem_sphere_iff_norm.mp hw
  have hwre := hre w hd.le
  have hwn : ‖w‖ ≤ ‖s‖ + s.re / 2 := by
    have h := norm_add_le (w - s) s
    rw [sub_add_cancel, hd] at h
    linarith
  exact (norm_pairedEtaCore_le_div_re (hr.trans_le hwre)).trans (by gcongr)

private lemma eta_vertical_linear_bound {sigma : ℝ} (hsigma : 0 < sigma) (c : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      ‖iteratedDeriv k pairedEtaCore (pairedEtaVerticalArgument sigma t)‖ ≤
        C * (1 + |t - c|) := by
  let R := sigma / 2
  let L := 3 * sigma / 2 + |c| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg c]
  refine ⟨(k.factorial : ℝ) * (L / R) / R ^ k, by positivity, ?_⟩
  intro t
  have hs : 0 < (pairedEtaVerticalArgument sigma t).re := by simpa [pairedEtaVerticalArgument] using hsigma
  have hnorm : ‖pairedEtaVerticalArgument sigma t‖ ≤ sigma + |t| := by
    simpa [pairedEtaVerticalArgument, abs_of_pos hsigma] using
      norm_add_le (sigma : ℂ) ((t : ℂ) * I)
  have ht : |t| ≤ |t - c| + |c| := by simpa using abs_add_le (t - c) c
  have hb : ‖pairedEtaVerticalArgument sigma t‖ + R ≤ L * (1 + |t - c|) := by
    have hmul := mul_le_mul_of_nonneg_right hL (abs_nonneg (t - c))
    dsimp [R, L] at *
    nlinarith
  have h := norm_iteratedDeriv_pairedEtaCore_le k hs
  simp only [pairedEtaVerticalArgument, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_self, add_zero] at h
  calc
    _ ≤ (k.factorial : ℝ) * ((‖pairedEtaVerticalArgument sigma t‖ + R) / R) / R ^ k := h
    _ ≤ (k.factorial : ℝ) * ((L * (1 + |t - c|)) / R) / R ^ k := by gcongr
    _ = _ := by ring

private lemma eta_vertical_data {sigma : ℝ} (hsigma : 0 < sigma) (c : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t,
      ‖pairedEtaCore (pairedEtaVerticalArgument sigma t)‖ ≤ C * (1 + |t - c|) ∧
      ‖deriv pairedEtaCore (pairedEtaVerticalArgument sigma t)‖ ≤ C * (1 + |t - c|) ∧
      ‖deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t)‖ ≤ C * (1 + |t - c|) := by
  obtain ⟨C0, hC0, h0⟩ := eta_vertical_linear_bound hsigma c 0
  obtain ⟨C1, hC1, h1⟩ := eta_vertical_linear_bound hsigma c 1
  obtain ⟨C2, hC2, h2⟩ := eta_vertical_linear_bound hsigma c 2
  refine ⟨1 + C0 + C1 + C2, by linarith, ?_⟩
  intro t
  have ht : 0 ≤ 1 + |t - c| := by positivity
  constructor
  · exact (h0 t).trans (mul_le_mul_of_nonneg_right (by linarith) ht)
  constructor
  · simpa only [iteratedDeriv_one] using
      (h1 t).trans (mul_le_mul_of_nonneg_right (show C1 ≤ 1 + C0 + C1 + C2 by linarith) ht)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (h2 t).trans (mul_le_mul_of_nonneg_right (show C2 ≤ 1 + C0 + C1 + C2 by linarith) ht)

/-- The complete complex quartic eta numerator on an arithmetic vertical
line, including both conjugated derivatives and the original eta square. -/
def pairedEtaVerticalQuarticCurvature (sigma t : ℝ) : ℂ :=
  pairedEtaCore (pairedEtaVerticalArgument sigma t) ^ 2 *
    starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t) ^ 2 -
      pairedEtaCore (pairedEtaVerticalArgument sigma t) *
        deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t))

private lemma eta_vertical_continuous {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun t => pairedEtaCore (pairedEtaVerticalArgument sigma t)) ∧
    Continuous (fun t => deriv pairedEtaCore (pairedEtaVerticalArgument sigma t)) ∧
    Continuous (fun t => deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t)) := by
  have hs (t : ℝ) : 0 < (pairedEtaVerticalArgument sigma t).re := by
    simpa [pairedEtaVerticalArgument] using hsigma
  have hl : Continuous (pairedEtaVerticalArgument sigma) := by unfold pairedEtaVerticalArgument; fun_prop
  exact ⟨continuous_iff_continuousAt.mpr fun t =>
    (analyticOnNhd_pairedEtaCore _ (hs t)).continuousAt.comp (hl.continuousAt),
    continuous_iff_continuousAt.mpr fun t =>
    (analyticOnNhd_pairedEtaCore _ (hs t)).deriv.continuousAt.comp (hl.continuousAt),
    continuous_iff_continuousAt.mpr fun t =>
    (analyticOnNhd_pairedEtaCore _ (hs t)).deriv.deriv.continuousAt.comp (hl.continuousAt)⟩

/-- The exact nonnegative square left after coupling the eta phase
current with the derivative of the same Gaussian weight. -/
def pairedEtaGaussianPhaseSquare (tau c sigma t : ℝ) : ℝ :=
  translatedGaussian tau c t *
    ((pairedEtaCore (pairedEtaVerticalArgument sigma t) *
      starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).im -
      tau * (t - c) * normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) / 4) ^ 2

private lemma eta_gaussian_integrability {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (c : ℝ) :
    Integrable (fun t => (translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t) ∧
    Integrable (fun t => (translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurrent sigma t) ∧
    Integrable (pairedEtaGaussianPhaseSquare tau c sigma) ∧
    Integrable (fun t => (t - c) ^ 2 * translatedGaussian tau c t *
      normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2) := by
  let f (t : ℝ) := pairedEtaCore (pairedEtaVerticalArgument sigma t)
  let g (t : ℝ) := deriv pairedEtaCore (pairedEtaVerticalArgument sigma t)
  let h (t : ℝ) := deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t)
  obtain ⟨hf, hg, hh⟩ := eta_vertical_continuous hsigma
  change Continuous f at hf
  change Continuous g at hg
  change Continuous h at hh
  obtain ⟨C, hC1, hb⟩ := eta_vertical_data hsigma c
  have hC : 0 ≤ C := by linarith
  have hfg (t : ℝ) : |(f t * starRingEnd ℂ (g t)).im| ≤ C ^ 2 * (1 + |t - c|) ^ 2 := by
    calc
      _ ≤ ‖f t * starRingEnd ℂ (g t)‖ := Complex.abs_im_le_norm _
      _ = ‖f t‖ * ‖g t‖ := by simp
      _ ≤ (C * (1 + |t - c|)) * (C * (1 + |t - c|)) := by
        exact mul_le_mul (hb t).1 (hb t).2.1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hmass (t : ℝ) : normSq (f t) ≤ C ^ 2 * (1 + |t - c|) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hb t).1 2).trans_eq (by ring)
  constructor
  · have hm : AEStronglyMeasurable (fun t => f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h t)) :=
      (by fun_prop : Continuous (fun t => f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h t))).aestronglyMeasurable
    have hi := integrable_translatedGaussian_mul_of_polynomial_bound htau c hm
      (C := 2 * C ^ 4) (by positivity) 4 (fun t => ?_)
    · simpa only [Complex.real_smul, pairedEtaVerticalQuarticCurvature, f, g, h] using hi
    calc
      _ ≤ ‖f t‖ ^ 2 * (‖g t‖ ^ 2 + ‖f t‖ * ‖h t‖) := by
        simp only [norm_mul, norm_conj, Complex.norm_pow]
        exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans_eq
          (by rw [Complex.norm_pow, norm_mul])) (sq_nonneg _)
      _ ≤ (C * (1 + |t - c|)) ^ 2 *
          ((C * (1 + |t - c|)) ^ 2 + (C * (1 + |t - c|)) * (C * (1 + |t - c|))) := by
        gcongr
        · exact (hb t).1
        · exact (hb t).2.1
        · exact (hb t).1
        · exact (hb t).2.2
      _ = _ := by ring
  constructor
  · have hm : AEStronglyMeasurable (complexQuarticCurrent f g) :=
      (by unfold complexQuarticCurrent; fun_prop : Continuous (complexQuarticCurrent f g)).aestronglyMeasurable
    have hi := integrable_translatedGaussian_mul_of_polynomial_bound htau c hm
      (C := C ^ 4) (by positivity) 4 (fun t => ?_)
    · simpa only [Complex.real_smul, pairedEtaVerticalQuarticCurrent, f, g] using hi
    dsimp [complexQuarticCurrent]
    simp only [norm_mul, Complex.norm_pow, norm_conj]
    calc
      _ ≤ (C * (1 + |t - c|)) ^ 2 *
          (C * (1 + |t - c|)) * (C * (1 + |t - c|)) := by
        gcongr
        · exact (hb t).1
        · exact (hb t).1
        · exact (hb t).2.1
      _ = _ := by ring
  constructor
  · have hm : AEStronglyMeasurable (fun t =>
        ((f t * starRingEnd ℂ (g t)).im - tau * (t - c) * normSq (f t) / 4) ^ 2) := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    have hi := integrable_translatedGaussian_mul_of_polynomial_bound htau c hm
      (C := ((1 + |tau|) * C ^ 2) ^ 2) (by positivity) 6 (fun t => ?_)
    · simpa only [smul_eq_mul, pairedEtaGaussianPhaseSquare, f, g] using! hi
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hu : 1 ≤ 1 + |t - c| := by linarith [abs_nonneg (t - c)]
    have hu0 : 0 ≤ 1 + |t - c| := by positivity
    have hmass0 : 0 ≤ normSq (f t) := normSq_nonneg _
    have hq : |(f t * starRingEnd ℂ (g t)).im - tau * (t - c) * normSq (f t) / 4| ≤
        (1 + |tau|) * C ^ 2 * (1 + |t - c|) ^ 3 := by
      calc
        _ ≤ |(f t * starRingEnd ℂ (g t)).im| + |tau * (t - c) * normSq (f t) / 4| := abs_sub _ _
        _ ≤ C ^ 2 * (1 + |t - c|) ^ 2 + |tau| * (1 + |t - c|) *
            (C ^ 2 * (1 + |t - c|) ^ 2) := by
          rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (normSq_nonneg _)]
          norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
          apply add_le_add (hfg t)
          calc
            _ ≤ |tau| * (1 + |t - c|) * (C ^ 2 * (1 + |t - c|) ^ 2) / 4 := by
              gcongr
              · linarith [abs_nonneg (t - c)]
              · exact hmass t
            _ ≤ _ := by
              have hp : 0 ≤ |tau| * (1 + |t - c|) * (C ^ 2 * (1 + |t - c|) ^ 2) := by positivity
              linarith
        _ ≤ (1 + |tau|) * C ^ 2 * (1 + |t - c|) ^ 3 := by
          have hc := mul_le_mul_of_nonneg_left hu (mul_nonneg (sq_nonneg C) (sq_nonneg (1 + |t - c|)))
          nlinarith [hc]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hq 2
    simpa only [sq_abs] using hs.trans_eq (by ring)
  · have hm : AEStronglyMeasurable (fun t => (t - c) ^ 2 * normSq (f t) ^ 2) :=
      (by fun_prop : Continuous (fun t => (t - c) ^ 2 * normSq (f t) ^ 2)).aestronglyMeasurable
    have hi := integrable_translatedGaussian_mul_of_polynomial_bound htau c hm
      (C := C ^ 4) (by positivity) 6 (fun t => ?_)
    · convert hi using 1
      funext t
      simp only [smul_eq_mul, f]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hu : (t - c) ^ 2 ≤ (1 + |t - c|) ^ 2 := by
      nlinarith [sq_abs (t - c), abs_nonneg (t - c)]
    calc
      _ ≤ (1 + |t - c|) ^ 2 * (C ^ 2 * (1 + |t - c|) ^ 2) ^ 2 := by
        gcongr
        · exact normSq_nonneg _
        · exact hmass t
      _ = _ := by ring

/-- The complex infinite eta quartic numerator is integrable under every
positive Gaussian on every positive vertical line. -/
theorem integrable_pairedEtaVerticalQuarticCurvature_gaussian {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (c : ℝ) :
    Integrable (fun t => (translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t) :=
  (eta_gaussian_integrability hsigma htau c).1

/-- The actual fourth-power allowance is integrable even on vertical
lines inside the zero strip. -/
theorem integrable_pairedEta_quartic_gaussian_allowance {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (c : ℝ) :
    Integrable (fun t => (t - c) ^ 2 * translatedGaussian tau c t *
      normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2) :=
  (eta_gaussian_integrability hsigma htau c).2.2.2

/-- The complete infinite eta quartic integral equals an exact negative
phase square plus a positive Gaussian fourth-power allowance. Both
improper boundary terms are discharged using the actual eta bounds. -/
theorem pairedEta_quartic_gaussian_square {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (c : ℝ) :
    (∫ t : ℝ, (translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t).re =
      -4 * (∫ t : ℝ, pairedEtaGaussianPhaseSquare tau c sigma t) +
        tau ^ 2 / 4 * (∫ t : ℝ, (t - c) ^ 2 * translatedGaussian tau c t *
          normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2) := by
  let f (t : ℝ) := pairedEtaCore (pairedEtaVerticalArgument sigma t)
  let g (t : ℝ) := deriv pairedEtaCore (pairedEtaVerticalArgument sigma t)
  let h (t : ℝ) := deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t)
  let F (t : ℝ) := (translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurrent sigma t
  have hs (t : ℝ) : 0 < (pairedEtaVerticalArgument sigma t).re := by simpa [pairedEtaVerticalArgument] using hsigma
  have hf (t : ℝ) : HasDerivAt f (I * g t) t :=
    hasDerivAt_pairedEtaVertical_comp (analyticOnNhd_pairedEtaCore _ (hs t)).differentiableAt.hasDerivAt
  have hg (t : ℝ) : HasDerivAt g (I * h t) t :=
    hasDerivAt_pairedEtaVertical_comp (analyticOnNhd_pairedEtaCore _ (hs t)).deriv.differentiableAt.hasDerivAt
  have hF (t : ℝ) : DifferentiableAt ℝ F t := by
    have hw : DifferentiableAt ℝ (fun u => (translatedGaussian tau c u : ℂ)) t := by
      unfold translatedGaussian
      fun_prop
    exact hw.fun_mul (hasDerivAt_complexQuarticCurrent (hf t) (hg t)).differentiableAt
  have he (t : ℝ) :
      ((translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t).re =
        (deriv F t).im - 4 * pairedEtaGaussianPhaseSquare tau c sigma t +
          tau ^ 2 / 4 * ((t - c) ^ 2 * translatedGaussian tau c t * normSq (f t) ^ 2) := by
    have he := complexSignedCurvature_gaussian_square (tau := tau) (c := c) (hf t) (hg t)
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      pairedEtaVerticalQuarticCurvature, pairedEtaGaussianPhaseSquare,
      pairedEtaVerticalQuarticCurrent, f, g, h, F, mul_assoc] using he
  obtain ⟨hQ, hcur, hSq, hA⟩ := eta_gaussian_integrability hsigma htau c
  have hB := hA.const_mul (tau ^ 2 / 4)
  have hD : Integrable (fun t => (deriv F t).im) := by
    apply ((hQ.re.add (hSq.const_mul 4)).sub hB).congr
    filter_upwards with t
    change ((translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t).re +
      4 * pairedEtaGaussianPhaseSquare tau c sigma t -
        tau ^ 2 / 4 * ((t - c) ^ 2 * translatedGaussian tau c t * normSq (f t) ^ 2) =
          (deriv F t).im
    rw [he t]
    ring
  have hzero : (∫ t : ℝ, (deriv F t).im) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun t => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hF t).hasDerivAt) hD hcur.im
  calc
    _ = ∫ t : ℝ, ((translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t).re :=
      (integral_re hQ).symm
    _ = _ := by
      simp_rw [he]
      have hsub : Integrable (fun t => (deriv F t).im - 4 * pairedEtaGaussianPhaseSquare tau c sigma t) :=
        hD.sub (hSq.const_mul 4)
      have hb : Integrable (fun t => tau ^ 2 / 4 *
          ((t - c) ^ 2 * translatedGaussian tau c t * normSq (f t) ^ 2)) := hB
      rw [integral_add hsub hb,
        integral_sub hD (hSq.const_mul 4), integral_const_mul, integral_const_mul, hzero]
      ring

/-- Discarding only the already retained nonnegative square gives an
independent upper bound for the signed quartic numerator. -/
theorem pairedEta_quartic_gaussian_upper {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (c : ℝ) :
    (∫ t : ℝ, (translatedGaussian tau c t : ℂ) * pairedEtaVerticalQuarticCurvature sigma t).re ≤
      tau ^ 2 / 4 * (∫ t : ℝ, (t - c) ^ 2 * translatedGaussian tau c t *
        normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2) := by
  rw [pairedEta_quartic_gaussian_square hsigma htau c]
  have hnonneg : 0 ≤ ∫ t : ℝ, pairedEtaGaussianPhaseSquare tau c sigma t :=
    integral_nonneg fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  linarith

end
end RiemannGaussian
