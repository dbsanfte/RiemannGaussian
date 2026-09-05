import RiemannGaussian.EtaSupportGapGaussianProfile
import Mathlib.MeasureTheory.Group.Integral

/-!
# Gaussian transfer between the literal eta support and its gaps

The continuous two-time kernel retains the actual eta support indicator.
Symmetry and a positive-quadrant change of variables connect it to the
phase-resolved arithmetic displacement, with genuine integrability throughout.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Translation of a positive-half-line integral to a half-line starting at
an arbitrary real point. -/
theorem integral_Ioi_eq_integral_add_left (f : ℝ → ℝ) (t : ℝ) :
    (∫ u in Ioi t, f u) = ∫ r in Ioi 0, f (t + r) := by
  have h := integral_add_left_eq_self ((Ioi t).indicator f) t (μ := volume)
  have hfun : (fun r : ℝ ↦ (Ioi t).indicator f (t + r)) =
      (Ioi 0).indicator (fun r ↦ f (t + r)) := by
    funext r
    by_cases hr : 0 < r
    · have ht : t + r ∈ Ioi t := by simp only [mem_Ioi]; linarith
      simp [hr, ht]
    · have ht : t + r ∉ Ioi t := by simp only [mem_Ioi]; linarith
      simp [hr, ht]
  rw [hfun, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h.symm

/-- A symmetric integrable kernel on the positive quadrant is twice its
upper-triangle integral. The diagonal is removed using atomlessness. -/
theorem integral_positiveQuadrant_eq_twice_upper {F : ℝ × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    (hsymm : ∀ t u : ℝ, F (t, u) = F (u, t)) :
    (∫ p, F p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      2 * ∫ t in Ioi 0, ∫ u in Ioi t, F (t, u) := by
  let S : Set (ℝ × ℝ) := {p | p.1 < p.2}
  let U : ℝ × ℝ → ℝ := S.indicator F
  have hS : MeasurableSet S := measurableSet_lt measurable_fst measurable_snd
  have hU : Integrable U ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    hF.indicator hS
  have hUswap : Integrable (fun p : ℝ × ℝ ↦ U p.swap)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    simpa only [Function.comp_def] using hU.swap
  have hneq : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      p.1 ≠ p.2 := by
    have hm : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
    apply (Measure.ae_prod_iff_ae_ae hm).2
    exact Eventually.of_forall fun t ↦ by
      rw [ae_iff]
      simp
  have hsplit : ∀ᵐ p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      F p = U p + U p.swap := by
    filter_upwards [hneq] with p hp
    rcases p with ⟨t, u⟩
    rcases lt_or_gt_of_ne hp with htu | hut
    · simp [U, S, htu, not_lt.mpr htu.le]
    · simpa [U, S, hut, not_lt.mpr hut.le] using hsymm t u
  calc
    (∫ p, F p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
        (∫ p, U p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) +
          ∫ p, U p.swap ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
      rw [← integral_add hU hUswap]
      exact integral_congr_ae hsplit
    _ = 2 * ∫ p, U p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
      rw [integral_prod_swap]
      ring
    _ = 2 * ∫ t in Ioi 0, ∫ u in Ioi t, F (t, u) := by
      congr 1
      rw [integral_prod _ hU]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hu : (fun u : ℝ ↦ U (t, u)) = (Ioi t).indicator (fun u ↦ F (t, u)) := rfl
      rw [hu, setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi ht.le)]

/-- Positive-quadrant symmetry followed by the exact displacement
substitution, before any Fubini exchange in the new coordinates. -/
theorem integral_positiveQuadrant_eq_twice_displacement {F : ℝ × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    (hsymm : ∀ t u : ℝ, F (t, u) = F (u, t)) :
    (∫ p, F p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      2 * ∫ t in Ioi 0, ∫ r in Ioi 0, F (t, t + r) := by
  rw [integral_positiveQuadrant_eq_twice_upper hF hsymm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t ↦ integral_Ioi_eq_integral_add_left (fun u ↦ F (t, u)) t

/-- The normalized Gaussian heat kernel at heat time `h^2`. -/
def etaNormalizedHeatKernel (h r : ℝ) : ℝ :=
  Real.exp (-(1 / 4) * (r / h) ^ 2) / (2 * Real.sqrt Real.pi * h)

/-- The normalized heat kernel is positive at every positive width. -/
theorem etaNormalizedHeatKernel_pos {h : ℝ} (hh : 0 < h) (r : ℝ) :
    0 < etaNormalizedHeatKernel h r := by
  unfold etaNormalizedHeatKernel
  positivity

/-- Reflection preserves the normalized heat kernel. -/
theorem etaNormalizedHeatKernel_neg (h r : ℝ) :
    etaNormalizedHeatKernel h (-r) = etaNormalizedHeatKernel h r := by
  simp [etaNormalizedHeatKernel, neg_div]

/-- The Gaussian is bounded by its value at zero. -/
theorem etaNormalizedHeatKernel_le {h : ℝ} (hh : 0 < h) (r : ℝ) :
    etaNormalizedHeatKernel h r ≤ 1 / (2 * Real.sqrt Real.pi * h) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (r / h)])

/-- The positive envelope measuring transfer between the actual eta support
and its omitted intervals. -/
def pairedEtaSupportGapHeatWeight (sigma h : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-sigma * (p.1 + p.2)) * etaNormalizedHeatKernel h (p.2 - p.1) *
    pairedEtaLogShiftMismatch (p.2 - p.1) p.1

/-- The phase-resolved real two-time kernel. -/
def pairedEtaSupportGapHeatKernel (sigma h : ℝ) (phi : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  pairedEtaSupportGapHeatWeight sigma h p * Real.cos (phi p.2 - phi p.1)

/-- Continuous Gaussian transfer between the literal eta support and gaps. -/
def pairedEtaSupportGapGaussianLeakage (sigma h : ℝ) (phi : ℝ → ℝ) : ℝ :=
  ∫ p, pairedEtaSupportGapHeatKernel sigma h phi p
    ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- The mismatch in two-time coordinates is the squared difference of the
actual eta support indicators. -/
theorem pairedEtaLogShiftMismatch_sub (t u : ℝ) :
    pairedEtaLogShiftMismatch (u - t) t =
      (pairedEtaLogIndicator u - pairedEtaLogIndicator t) ^ 2 := by
  simp [pairedEtaLogShiftMismatch]

/-- The support/gap envelope is symmetric in its two time variables. -/
theorem pairedEtaSupportGapHeatWeight_swap (sigma h t u : ℝ) :
    pairedEtaSupportGapHeatWeight sigma h (t, u) =
      pairedEtaSupportGapHeatWeight sigma h (u, t) := by
  unfold pairedEtaSupportGapHeatWeight
  simp only [pairedEtaLogShiftMismatch_sub]
  rw [show t - u = -(u - t) by ring, etaNormalizedHeatKernel_neg]
  rw [show (pairedEtaLogIndicator u - pairedEtaLogIndicator t) ^ 2 =
      (pairedEtaLogIndicator t - pairedEtaLogIndicator u) ^ 2 by ring, add_comm t u]

/-- The real phase kernel remains symmetric for every real phase function. -/
theorem pairedEtaSupportGapHeatKernel_swap (sigma h : ℝ) (phi : ℝ → ℝ) (t u : ℝ) :
    pairedEtaSupportGapHeatKernel sigma h phi (t, u) =
      pairedEtaSupportGapHeatKernel sigma h phi (u, t) := by
  unfold pairedEtaSupportGapHeatKernel
  rw [pairedEtaSupportGapHeatWeight_swap]
  congr 1
  rw [show phi t - phi u = -(phi u - phi t) by ring, Real.cos_neg]

/-- The positive support/gap envelope is measurable in both time variables. -/
theorem measurable_pairedEtaSupportGapHeatWeight (sigma h : ℝ) :
    Measurable (pairedEtaSupportGapHeatWeight sigma h) := by
  have he : Continuous (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + p.2))) := by fun_prop
  have hg : Continuous (fun p : ℝ × ℝ ↦ etaNormalizedHeatKernel h (p.2 - p.1)) := by
    unfold etaNormalizedHeatKernel
    fun_prop
  exact (he.measurable.mul hg.measurable).mul
    (measurable_pairedEtaLogShiftMismatch.comp
      ((measurable_snd.sub measurable_fst).prodMk measurable_fst))

/-- Every measurable real phase gives a measurable two-time kernel. -/
theorem measurable_pairedEtaSupportGapHeatKernel {phi : ℝ → ℝ}
    (hphi : Measurable phi) (sigma h : ℝ) :
    Measurable (pairedEtaSupportGapHeatKernel sigma h phi) := by
  exact (measurable_pairedEtaSupportGapHeatWeight sigma h).mul
    (Real.continuous_cos.measurable.comp
      ((hphi.comp measurable_snd).sub (hphi.comp measurable_fst)))

/-- Positivity of the envelope retains the genuine arithmetic support factor. -/
theorem pairedEtaSupportGapHeatWeight_nonneg {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (p : ℝ × ℝ) : 0 ≤ pairedEtaSupportGapHeatWeight sigma h p := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (etaNormalizedHeatKernel_pos hh _).le)
    (pairedEtaLogShiftMismatch_nonneg _ _)

/-- A separable exponential majorant for the full phase kernel. -/
theorem norm_pairedEtaSupportGapHeatKernel_le {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (phi : ℝ → ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaSupportGapHeatKernel sigma h phi p‖ ≤
      (1 / (2 * Real.sqrt Real.pi * h)) *
        (Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2)) := by
  rw [pairedEtaSupportGapHeatKernel, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pairedEtaSupportGapHeatWeight_nonneg hh sigma p)]
  calc
    _ ≤ pairedEtaSupportGapHeatWeight sigma h p :=
      mul_le_of_le_one_right (pairedEtaSupportGapHeatWeight_nonneg hh sigma p)
        (Real.abs_cos_le_one _)
    _ ≤ Real.exp (-sigma * (p.1 + p.2)) * etaNormalizedHeatKernel h (p.2 - p.1) :=
      mul_le_of_le_one_right
        (mul_nonneg (Real.exp_pos _).le (etaNormalizedHeatKernel_pos hh _).le)
        (pairedEtaLogShiftMismatch_le_one _ _)
    _ ≤ Real.exp (-sigma * (p.1 + p.2)) * (1 / (2 * Real.sqrt Real.pi * h)) :=
      mul_le_mul_of_nonneg_left (etaNormalizedHeatKernel_le hh _) (Real.exp_pos _).le
    _ = _ := by
      have he : Real.exp (-sigma * (p.1 + p.2)) =
          Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring

/-- Genuine integrability of the continuous two-time kernel at positive tilt
and positive heat width. -/
theorem integrable_pairedEtaSupportGapHeatKernel {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi : ℝ → ℝ} (hphi : Measurable phi) :
    Integrable (pairedEtaSupportGapHeatKernel sigma h phi)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have he := integrableOn_exp_mul_Ioi (a := -sigma) (by linarith) 0
  apply ((he.mul_prod he).const_mul (1 / (2 * Real.sqrt Real.pi * h))).mono'
    (measurable_pairedEtaSupportGapHeatKernel hphi sigma h).aestronglyMeasurable
  exact Eventually.of_forall fun p ↦ norm_pairedEtaSupportGapHeatKernel_le hh sigma phi p

/-- Exact factorization of the literal kernel in displacement coordinates. -/
theorem pairedEtaSupportGapHeatKernel_displacement (sigma h : ℝ) (phi : ℝ → ℝ) (t r : ℝ) :
    pairedEtaSupportGapHeatKernel sigma h phi (t, t + r) =
      (etaNormalizedHeatKernel h r * Real.exp (-sigma * r)) *
        (pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t) *
          Real.cos (phi (t + r) - phi t)) := by
  unfold pairedEtaSupportGapHeatKernel pairedEtaSupportGapHeatWeight
  simp only [add_sub_cancel_left]
  rw [show -sigma * (t + (t + r)) = -sigma * r + -(2 * sigma) * t by ring,
    Real.exp_add]
  ring

/-- A separable majorant also controls the kernel after the displacement
substitution, justifying Fubini in the new coordinates. -/
theorem integrable_pairedEtaSupportGapHeatKernel_displacement {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi : ℝ → ℝ} (hphi : Measurable phi) :
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaSupportGapHeatKernel sigma h phi (p.1, p.1 + p.2))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have he₁ := integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) 0
  have he₂ := integrableOn_exp_mul_Ioi (a := -sigma) (by linarith) 0
  apply ((he₁.mul_prod he₂).const_mul (1 / (2 * Real.sqrt Real.pi * h))).mono'
    ((measurable_pairedEtaSupportGapHeatKernel hphi sigma h).comp
      (measurable_fst.prodMk (measurable_fst.add measurable_snd))).aestronglyMeasurable
  exact Eventually.of_forall fun p ↦ by
    have hbound := norm_pairedEtaSupportGapHeatKernel_le hh sigma phi (p.1, p.1 + p.2)
    have he : Real.exp (-sigma * p.1) * Real.exp (-sigma * (p.1 + p.2)) =
        Real.exp (-(2 * sigma) * p.1) * Real.exp (-sigma * p.2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simpa only [he, Function.comp_apply, Pi.add_apply] using hbound

/-- The real part of the retained complex arithmetic displacement is exactly
its cosine-weighted integral. -/
theorem pairedEtaPhaseMismatch_re_eq_cosine_integral {sigma : ℝ} (hsigma : 0 < sigma)
    {phi : ℝ → ℝ} (hphi : Measurable phi) (r : ℝ) :
    (pairedEtaPhaseMismatch sigma phi r).re =
      ∫ t in Ioi 0, pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t) *
        Real.cos (phi (t + r) - phi t) := by
  have hi := integrableOn_pairedEtaLogShiftMismatch_mul
    (integrableOn_pairedEtaShiftPhaseKernel hsigma hphi r 0) r
  calc
    _ = ∫ t in Ioi 0,
        ((pairedEtaLogShiftMismatch r t : ℂ) * pairedEtaShiftPhaseKernel sigma phi r t).re :=
      (integral_re hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [pairedEtaShiftPhaseKernel, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]
      ring

/-- Exact identification of the continuous support/gap Gaussian transfer
with the phase-resolved arithmetic displacement integral. -/
theorem pairedEtaSupportGapGaussianLeakage_eq_displacement {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi : ℝ → ℝ} (hphi : Measurable phi) :
    pairedEtaSupportGapGaussianLeakage sigma h phi =
      2 * ∫ r in Ioi 0, etaNormalizedHeatKernel h r * Real.exp (-sigma * r) *
        (pairedEtaPhaseMismatch sigma phi r).re := by
  rw [pairedEtaSupportGapGaussianLeakage,
    integral_positiveQuadrant_eq_twice_displacement
      (integrable_pairedEtaSupportGapHeatKernel hsigma hh hphi)
      (pairedEtaSupportGapHeatKernel_swap sigma h phi)]
  congr 1
  rw [integral_integral_swap (integrable_pairedEtaSupportGapHeatKernel_displacement hsigma hh hphi)]
  apply integral_congr_ae
  filter_upwards with r
  simp_rw [pairedEtaSupportGapHeatKernel_displacement]
  rw [integral_const_mul, pairedEtaPhaseMismatch_re_eq_cosine_integral hsigma hphi]

/-- A linear phase factors out of the actual arithmetic displacement integral
without an approximation or a colour average. -/
theorem pairedEtaPhaseMismatch_linear (sigma gamma r : ℝ) :
    pairedEtaPhaseMismatch sigma (fun t ↦ gamma * t) r =
      (pairedEtaMismatch sigma r : ℂ) * Complex.exp (((gamma * r : ℝ) : ℂ) * Complex.I) := by
  have hfun : (fun t : ℝ ↦ (pairedEtaLogShiftMismatch r t : ℂ) *
      pairedEtaShiftPhaseKernel sigma (fun t ↦ gamma * t) r t) =
      (fun t ↦ ((pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t) : ℝ) : ℂ) *
        Complex.exp (((gamma * r : ℝ) : ℂ) * Complex.I)) := by
    funext t
    unfold pairedEtaShiftPhaseKernel
    rw [show gamma * (t + r) - gamma * t = gamma * r by ring]
    simp only [Complex.ofReal_mul]
    ring
  unfold pairedEtaPhaseMismatch
  rw [hfun, integral_mul_const, integral_complex_ofReal]
  rfl

/-- The real linear-phase displacement is the uncoloured arithmetic
displacement multiplied by the exact cosine phase. -/
theorem pairedEtaPhaseMismatch_linear_re (sigma gamma r : ℝ) :
    (pairedEtaPhaseMismatch sigma (fun t ↦ gamma * t) r).re =
      pairedEtaMismatch sigma r * Real.cos (gamma * r) := by
  rw [pairedEtaPhaseMismatch_linear]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, mul_one, Real.exp_zero, one_mul]

/-- Exact identification of the continuous eta support/gap heat transfer
with the rescaled literal displacement carrier. -/
theorem pairedEtaSupportGapGaussianLeakage_linear_eq_scaled {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (gamma : ℝ) :
    pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ gamma * t) =
      pairedEtaScaledGaussianMismatch sigma h (h * gamma) := by
  have hphi : Measurable (fun t : ℝ ↦ gamma * t) := measurable_const.mul measurable_id
  rw [pairedEtaSupportGapGaussianLeakage_eq_displacement hsigma hh hphi]
  simp_rw [pairedEtaPhaseMismatch_linear_re]
  let f : ℝ → ℝ := fun r ↦ etaNormalizedHeatKernel h r * Real.exp (-sigma * r) *
    (pairedEtaMismatch sigma r * Real.cos (gamma * r))
  have hscale := integral_comp_mul_left_Ioi' f 0 hh
  simp only [mul_zero, smul_eq_mul] at hscale
  change 2 * (∫ r in Ioi 0, f r) = pairedEtaScaledGaussianMismatch sigma h (h * gamma)
  rw [← hscale]
  unfold pairedEtaScaledGaussianMismatch
  rw [show 2 * (h * ∫ v in Ioi 0, f (h * v)) =
      (2 * h) * ∫ v in Ioi 0, f (h * v) by ring,
    ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  dsimp [f, etaNormalizedHeatKernel]
  rw [show h * v / h = v by field_simp,
    show gamma * (h * v) = h * gamma * v by ring]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

/-- Uniform critical heat law on the actual continuous eta support/gap
kernel, valid at every real Gaussian centre. -/
theorem pairedEtaSupportGapGaussianLeakage_uniform_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) (gamma : ℝ) :
    |pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ gamma * t) -
      h * Real.log (1 / h) * pairedEtaHeatPhaseProfile (h * gamma)| ≤ 32 * h := by
  rw [pairedEtaSupportGapGaussianLeakage_linear_eq_scaled (by norm_num) hh]
  exact pairedEtaScaledGaussianMismatch_uniform_error_le hh hhone (h * gamma)

/-- The actual uncoloured support/gap heat transfer has the sharp critical
leading term and a fully explicit remainder. -/
theorem pairedEtaSupportGapGaussianLeakage_critical_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) :
    |pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun _ ↦ 0) -
      (2 / Real.sqrt Real.pi) * h * Real.log (1 / h)| ≤ 32 * h := by
  have hbound := pairedEtaSupportGapGaussianLeakage_uniform_error_le hh hhone 0
  simpa only [zero_mul, mul_zero, pairedEtaHeatPhaseProfile_zero, mul_comm, mul_left_comm, mul_assoc]
    using hbound

end

end RiemannGaussian
