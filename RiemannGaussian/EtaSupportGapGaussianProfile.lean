import RiemannGaussian.EtaLogSupportCritical
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Uniform Gaussian phase profile of the actual eta displacement

The critical arithmetic boundary estimate is integrated against a Gaussian
without discarding the ordinate phase. The rescaled displacement integral is
the intermediate carrier for the continuous support/gap heat identity.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A logarithmic factor times its positive argument is bounded by a
quadratic polynomial on the entire positive half-line. -/
theorem mul_abs_log_le_one_add_sq {v : ℝ} (hv : 0 < v) :
    v * |Real.log v| ≤ 1 + v ^ 2 := by
  by_cases hvone : v ≤ 1
  · have hlognonpos := Real.log_nonpos hv.le hvone
    rw [abs_of_nonpos hlognonpos]
    have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / v by positivity)
    have hmul := mul_le_mul_of_nonneg_left hlog hv.le
    have hid : v * (1 / v - 1) = 1 - v := by field_simp
    rw [hid] at hmul
    simp only [one_div, Real.log_inv] at hmul
    nlinarith [sq_nonneg v]
  · have hlognonneg := Real.log_nonneg (show 1 ≤ v by linarith)
    rw [abs_of_nonneg hlognonneg]
    have hmul := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hv) hv.le
    nlinarith [sq_nonneg v]

/-- A global, Gaussian-integrable pointwise error bound after rescaling the
actual critical eta displacement. -/
theorem pairedEtaMismatch_damped_scaled_error_le {h v : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) (hv : 0 < v) :
    |Real.exp (-(1 / 2) * (h * v)) * pairedEtaMismatch (1 / 2) (h * v) -
      h * v * Real.log (1 / h)| ≤ h * (10 + 11 * v ^ 2) := by
  let r := h * v
  let D := pairedEtaMismatch (1 / 2) r
  let e := Real.exp (-(1 / 2) * r)
  have hr : 0 < r := mul_pos hh hv
  have hDnonneg : 0 ≤ D := pairedEtaMismatch_nonneg (1 / 2) r
  have hDle : D ≤ 1 := by
    simpa [D] using pairedEtaMismatch_le_inv (sigma := 1 / 2) (by norm_num) r
  have henonneg : 0 ≤ e := (Real.exp_pos _).le
  have hele : e ≤ 1 := Real.exp_le_one_iff.mpr (by dsimp [r]; nlinarith)
  have heerror : 1 - e ≤ r := by
    have he := Real.add_one_le_exp (-(1 / 2) * r)
    change -(1 / 2) * r + 1 ≤ e at he
    linarith
  have hweight : |(e - 1) * D| ≤ r := by
    rw [abs_mul, abs_of_nonpos (by linarith : e - 1 ≤ 0), abs_of_nonneg hDnonneg]
    have hmul := mul_le_mul_of_nonneg_left hDle (show 0 ≤ 1 - e by linarith)
    nlinarith
  have hbase : |e * D - r * Real.log (1 / r)| ≤ 17 * r + r ^ 2 := by
    calc
      |e * D - r * Real.log (1 / r)| =
          |(D - r * Real.log (1 / r)) + (e - 1) * D| := by congr 1; ring
      _ ≤ |D - r * Real.log (1 / r)| + |(e - 1) * D| := abs_add_le _ _
      _ ≤ (16 * r + r ^ 2) + r :=
        add_le_add (pairedEtaMismatch_critical_error_global hr) hweight
      _ = 17 * r + r ^ 2 := by ring
  have hlog : Real.log (1 / r) = Real.log (1 / h) - Real.log v := by
    dsimp [r]
    rw [Real.log_div (by norm_num) (by positivity),
      Real.log_div (by norm_num) (ne_of_gt hh),
      Real.log_mul (ne_of_gt hh) (ne_of_gt hv), Real.log_one]
    ring
  have hscaled : |e * D - r * Real.log (1 / h)| ≤
      17 * r + r ^ 2 + r * |Real.log v| := by
    calc
      |e * D - r * Real.log (1 / h)| =
          |(e * D - r * Real.log (1 / r)) - r * Real.log v| := by
        rw [hlog]
        congr 1
        ring
      _ ≤ |e * D - r * Real.log (1 / r)| + |r * Real.log v| := abs_sub _ _
      _ ≤ 17 * r + r ^ 2 + r * |Real.log v| := by
        rw [abs_mul, abs_of_pos hr]
        linarith
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hr2 : r ^ 2 ≤ h * v ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hh2 (sq_nonneg v)
    dsimp [r]
    nlinarith
  have hlogbound := mul_le_mul_of_nonneg_left (mul_abs_log_le_one_add_sq hv) hh.le
  have hpoly : 17 * v + 2 * v ^ 2 + 1 ≤ 10 + 11 * v ^ 2 := by
    nlinarith [sq_nonneg (v - 1)]
  have hpolyh := mul_le_mul_of_nonneg_left hpoly hh.le
  change |e * D - r * Real.log (1 / h)| ≤ h * (10 + 11 * v ^ 2)
  apply hscaled.trans
  dsimp [r] at hr2 ⊢
  nlinarith

/-- The ordinate profile of the leading critical Gaussian boundary law. -/
def pairedEtaHeatPhaseProfile (kappa : ℝ) : ℝ :=
  (1 / Real.sqrt Real.pi) *
    ∫ v in Ioi 0, v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos (kappa * v)

/-- The rescaled Gaussian integral of the actual eta displacement, retaining
the full phase parameter. -/
def pairedEtaScaledGaussianMismatch (sigma h kappa : ℝ) : ℝ :=
  (1 / Real.sqrt Real.pi) *
    ∫ v in Ioi 0, Real.exp (-(1 / 4) * v ^ 2) * Real.exp (-sigma * (h * v)) *
      pairedEtaMismatch sigma (h * v) * Real.cos (kappa * v)

/-- Integrability of the leading phase-profile kernel. -/
theorem integrableOn_pairedEtaHeatPhaseProfile_kernel (kappa : ℝ) :
    IntegrableOn (fun v ↦ v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos (kappa * v)) (Ioi 0) := by
  apply (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn.mul_bdd
    (by fun_prop : Continuous (fun v : ℝ ↦ Real.cos (kappa * v))).aestronglyMeasurable
  exact Eventually.of_forall fun v ↦ by
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (kappa * v)

/-- Integrability of the rescaled literal eta Gaussian kernel at every
positive tilt and positive heat width. -/
theorem integrableOn_pairedEtaScaledGaussianMismatch_kernel {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (kappa : ℝ) :
    IntegrableOn (fun v ↦ Real.exp (-(1 / 4) * v ^ 2) * Real.exp (-sigma * (h * v)) *
      pairedEtaMismatch sigma (h * v) * Real.cos (kappa * v)) (Ioi 0) := by
  have hg : IntegrableOn (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn
  apply (hg.mul_const (1 / (2 * sigma))).mono'
  · have hD : Measurable (fun v : ℝ ↦ pairedEtaMismatch sigma (h * v)) :=
      (measurable_pairedEtaMismatch sigma).comp (measurable_const.mul measurable_id)
    exact (((Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).measurable.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul continuous_id))).measurable).mul
      hD |>.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have he : Real.exp (-sigma * (h * v)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have : 0 < v := hv; nlinarith [mul_pos hh this])
    have hD := pairedEtaMismatch_le_inv hsigma (h * v)
    have hDnonneg := pairedEtaMismatch_nonneg sigma (h * v)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), abs_of_nonneg hDnonneg]
    have hcos := Real.abs_cos_le_one (kappa * v)
    calc
      _ ≤ Real.exp (-(1 / 4) * v ^ 2) * Real.exp (-sigma * (h * v)) *
          pairedEtaMismatch sigma (h * v) :=
        mul_le_of_le_one_right (by positivity) hcos
      _ ≤ Real.exp (-(1 / 4) * v ^ 2) * pairedEtaMismatch sigma (h * v) := by
        calc
          _ = (Real.exp (-(1 / 4) * v ^ 2) * pairedEtaMismatch sigma (h * v)) *
              Real.exp (-sigma * (h * v)) := by ring
          _ ≤ _ := mul_le_of_le_one_right (by positivity) he
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le

/-- The zeroth moment of the Gaussian at the normalization of the eta heat profile. -/
theorem integral_etaHeatGaussian : (∫ v : ℝ in Ioi 0, Real.exp (-(1 / 4) * v ^ 2)) = Real.sqrt Real.pi := by
  rw [integral_gaussian_Ioi]
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [div_eq_mul_inv, Real.sqrt_mul Real.pi_pos.le, hs]
  ring

/-- The second half-line moment of the Gaussian in the eta heat profile. -/
theorem integral_sq_mul_etaHeatGaussian : (∫ v : ℝ in Ioi 0, v ^ 2 * Real.exp (-(1 / 4) * v ^ 2)) = 2 * Real.sqrt Real.pi := by
  have hchange : 2 * (∫ v : ℝ in Ioi 0, v ^ 2 * Real.exp (-(1 / 4) * v ^ 2)) =
      ∫ y : ℝ in Ioi 0, y ^ (1 / 2 : ℝ) * Real.exp (-(1 / 4) * y) := by
    rw [← integral_const_mul]
    convert integral_comp_rpow_Ioi_of_pos (p := 2)
      (g := fun y : ℝ ↦ y ^ (1 / 2 : ℝ) * Real.exp (-(1 / 4) * y)) (by norm_num) using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hpow : (x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_mul hx.le]
      norm_num
    dsimp only
    rw [smul_eq_mul, hpow]
    norm_num [Real.rpow_two]
    ring
  have hp : (1 / 4 : ℝ) ^ (3 / 2 : ℝ) = 1 / 8 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hs : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [hs]
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3 / 2) (r := 1 / 4)
    (by norm_num) (by norm_num)
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, hp, hg] at hval
  simp only [neg_mul] at hchange hval
  rw [hval] at hchange
  simp only [neg_mul]
  linarith

/-- The first half-line moment fixes the critical leading coefficient. -/
theorem integral_mul_etaHeatGaussian : (∫ v : ℝ in Ioi 0, v * Real.exp (-(1 / 4) * v ^ 2)) = 2 := by
  have hchange : 2 * (∫ v : ℝ in Ioi 0, v * Real.exp (-(1 / 4) * v ^ 2)) =
      ∫ y : ℝ in Ioi 0, Real.exp (-(1 / 4) * y) := by
    rw [← integral_const_mul]
    convert integral_comp_rpow_Ioi_of_pos (p := 2)
      (g := fun y : ℝ ↦ Real.exp (-(1 / 4) * y)) (by norm_num) using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [smul_eq_mul]
    norm_num [Real.rpow_two]
    ring
  rw [integral_exp_mul_Ioi (by norm_num)] at hchange
  norm_num at hchange
  simp only [neg_mul]
  linarith

/-- Integrability of the second Gaussian moment used in the uniform error. -/
theorem integrableOn_sq_mul_etaHeatGaussian :
    IntegrableOn (fun v : ℝ ↦ v ^ 2 * Real.exp (-(1 / 4) * v ^ 2)) (Ioi 0) := by
  simpa only [Real.rpow_two] using
    integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (s := 2) (by norm_num) (by norm_num)

/-- The leading ordinate profile has the expected value at the central phase. -/
theorem pairedEtaHeatPhaseProfile_zero :
    pairedEtaHeatPhaseProfile 0 = 2 / Real.sqrt Real.pi := by
  simp only [pairedEtaHeatPhaseProfile, zero_mul, Real.cos_zero, mul_one,
    integral_mul_etaHeatGaussian]
  ring

/-- Uniform, explicit critical Gaussian error bound for every scaled ordinate
of the actual eta displacement integral. -/
theorem pairedEtaScaledGaussianMismatch_uniform_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) (kappa : ℝ) :
    |pairedEtaScaledGaussianMismatch (1 / 2) h kappa -
      h * Real.log (1 / h) * pairedEtaHeatPhaseProfile kappa| ≤ 32 * h := by
  let w : ℝ → ℝ := fun v ↦ Real.exp (-(1 / 4) * v ^ 2)
  let F : ℝ → ℝ := fun v ↦ w v * Real.exp (-(1 / 2) * (h * v)) *
    pairedEtaMismatch (1 / 2) (h * v) * Real.cos (kappa * v)
  let G : ℝ → ℝ := fun v ↦ v * w v * Real.cos (kappa * v)
  let a := h * Real.log (1 / h)
  let R : ℝ → ℝ := fun v ↦ F v - a * G v
  have hiF : IntegrableOn F (Ioi 0) :=
    integrableOn_pairedEtaScaledGaussianMismatch_kernel (by norm_num) hh kappa
  have hiG : IntegrableOn G (Ioi 0) := integrableOn_pairedEtaHeatPhaseProfile_kernel kappa
  have hiw : IntegrableOn w (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn
  have hiw2 := integrableOn_sq_mul_etaHeatGaussian
  have hpoly : (fun v : ℝ ↦ h * ((10 + 11 * v ^ 2) * w v)) =
      (fun v ↦ h * (10 * w v + 11 * (v ^ 2 * w v))) := by funext v; ring
  have himajor : IntegrableOn (fun v ↦ h * ((10 + 11 * v ^ 2) * w v)) (Ioi 0) := by
    rw [hpoly]
    exact ((hiw.const_mul 10).add (hiw2.const_mul 11)).const_mul h
  have hmajor : (∫ v in Ioi 0, h * ((10 + 11 * v ^ 2) * w v)) =
      h * (32 * Real.sqrt Real.pi) := by
    rw [hpoly, integral_const_mul,
      integral_add (hiw.const_mul 10) (hiw2.const_mul 11), integral_const_mul, integral_const_mul]
    change h * (10 * (∫ v in Ioi 0, Real.exp (-(1 / 4) * v ^ 2)) +
      11 * (∫ v in Ioi 0, v ^ 2 * Real.exp (-(1 / 4) * v ^ 2))) = _
    rw [integral_etaHeatGaussian, integral_sq_mul_etaHeatGaussian]
    ring
  have hpoint : ∀ᵐ v ∂volume.restrict (Ioi 0), ‖R v‖ ≤ h * ((10 + 11 * v ^ 2) * w v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hvpos : 0 < v := hv
    have herror := pairedEtaMismatch_damped_scaled_error_le hh hhone hvpos
    have hwpos : 0 < w v := Real.exp_pos _
    have hcos := Real.abs_cos_le_one (kappa * v)
    have hid : R v = w v * Real.cos (kappa * v) *
        (Real.exp (-(1 / 2) * (h * v)) * pairedEtaMismatch (1 / 2) (h * v) -
          h * v * Real.log (1 / h)) := by dsimp [R, F, G, a]; ring
    rw [hid, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hwpos]
    calc
      _ ≤ w v * |Real.exp (-(1 / 2) * (h * v)) * pairedEtaMismatch (1 / 2) (h * v) -
          h * v * Real.log (1 / h)| :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hwpos.le hcos) (abs_nonneg _)
      _ ≤ w v * (h * (10 + 11 * v ^ 2)) := mul_le_mul_of_nonneg_left herror hwpos.le
      _ = h * ((10 + 11 * v ^ 2) * w v) := by ring
  have hbound := norm_integral_le_of_norm_le himajor hpoint
  rw [Real.norm_eq_abs, hmajor] at hbound
  have hRI : (∫ v in Ioi 0, R v) = (∫ v in Ioi 0, F v) - a * ∫ v in Ioi 0, G v := by
    exact (integral_sub hiF (hiG.const_mul a)).trans (by rw [integral_const_mul])
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  change |(1 / Real.sqrt Real.pi) * (∫ v in Ioi 0, F v) -
    a * ((1 / Real.sqrt Real.pi) * ∫ v in Ioi 0, G v)| ≤ 32 * h
  rw [show (1 / Real.sqrt Real.pi) * (∫ v in Ioi 0, F v) -
      a * ((1 / Real.sqrt Real.pi) * ∫ v in Ioi 0, G v) =
      (1 / Real.sqrt Real.pi) * ((∫ v in Ioi 0, F v) - a * ∫ v in Ioi 0, G v) by ring,
    ← hRI, abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.sqrt Real.pi)]
  calc
    _ ≤ (1 / Real.sqrt Real.pi) * (h * (32 * Real.sqrt Real.pi)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 32 * h := by field_simp

/-- The sharp uncoloured Gaussian leading term, with the same explicit error. -/
theorem pairedEtaScaledGaussianMismatch_critical_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) :
    |pairedEtaScaledGaussianMismatch (1 / 2) h 0 -
      (2 / Real.sqrt Real.pi) * h * Real.log (1 / h)| ≤ 32 * h := by
  have hbound := pairedEtaScaledGaussianMismatch_uniform_error_le hh hhone 0
  rw [pairedEtaHeatPhaseProfile_zero] at hbound
  convert hbound using 1
  congr 1
  ring

end

end RiemannGaussian
