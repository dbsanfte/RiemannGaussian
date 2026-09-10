/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiEulerCurvature
import RiemannGaussian.SuzukiSafeHalfPlaneSourceDecay
import RiemannGaussian.ComplexGaussianCurvature

/-!
# Arithmetic source decay up to the Euler boundary

The full carrier source is an exact positive radial multiple of the
conjugate logarithmic curvature. The new polynomial curvature estimate
therefore gives quadratic smoothing decay on the entire closed Euler
half-plane. The original reflection weight and Gaussian are retained.
This removes the fixed buffer required by the earlier safe-half-plane
estimate; the arithmetic contribution inside the zero strip remains open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

private lemma euler_xi_ne_zero {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    riemannXi (suzukiArithmeticZetaArgument z) ≠ 0 := by
  intro hzero
  let rho : NontrivialZetaZero :=
    ⟨suzukiArithmeticZetaArgument z,
      (riemannXi_eq_zero_iff_isNontrivialZetaZero _).mp hzero⟩
  have h := NontrivialZetaZero.re_lt_one rho
  change (suzukiArithmeticZetaArgument z).re < 1 at h
  rw [suzukiArithmeticZetaArgument_re] at h
  linarith

private lemma spectral_logDeriv_eq_euler (z : ℂ) :
    logDeriv riemannXiSpectral z = -I * logDeriv riemannXi (suzukiArithmeticZetaArgument z) := by
  rw [logDeriv_riemannXiSpectral_eq_I_mul_completed,
    show suzukiArithmeticZetaArgument z = 1 - completedSpectralCoordinate z by
      unfold suzukiArithmeticZetaArgument completedSpectralCoordinate
      ring]
  simp only [logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub]
  ring

/-- The affine spectral-to-Euler change of coordinates preserves the
entire logarithmic curvature, with its exact negative Jacobian square. -/
theorem deriv_logDeriv_riemannXiSpectral_eq_neg_euler {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    deriv (logDeriv riemannXiSpectral) z =
      -deriv (logDeriv riemannXi) (suzukiArithmeticZetaArgument z) := by
  have hA := analyticOnNhd_riemannXi (suzukiArithmeticZetaArgument z) (mem_univ _)
  have hL : DifferentiableAt ℂ (logDeriv riemannXi) (suzukiArithmeticZetaArgument z) := by
    simpa only [logDeriv] using (hA.deriv.div hA (euler_xi_ne_zero hz)).differentiableAt
  have hs : HasDerivAt suzukiArithmeticZetaArgument (-I) z := by
    unfold suzukiArithmeticZetaArgument
    simpa only [mul_one, zero_mul, zero_add, zero_sub, id_eq] using
      (hasDerivAt_const z (1 / 2 : ℂ)).fun_sub
        ((hasDerivAt_const z I).fun_mul (hasDerivAt_id z))
  have hd := ((hL.hasDerivAt.comp z hs).const_mul (-I)).deriv
  simp only [Function.comp_def] at hd
  rw [show logDeriv riemannXiSpectral =
      (fun w => -I * logDeriv riemannXi (suzukiArithmeticZetaArgument w)) from
        funext spectral_logDeriv_eq_euler, hd]
  linear_combination deriv (logDeriv riemannXi) (suzukiArithmeticZetaArgument z) * I_sq

/-- The genuine spectral logarithmic curvature has polynomial growth on
the closed safe half-plane, with no fixed distance from its boundary. -/
theorem exists_norm_deriv_logDeriv_riemannXiSpectral_safe_polynomial_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 ≤ z.im →
      ‖deriv (logDeriv riemannXiSpectral) z‖ ≤ C * (1 + ‖z‖) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_deriv_logDeriv_riemannXi_euler_polynomial_bound
  refine ⟨16 * C, by positivity, ?_⟩
  intro z hz
  have hs : 1 ≤ (suzukiArithmeticZetaArgument z).re := by
    rw [suzukiArithmeticZetaArgument_re]
    linarith
  have hn : ‖suzukiArithmeticZetaArgument z‖ ≤ 1 + ‖z‖ := by
    unfold suzukiArithmeticZetaArgument
    have h := norm_sub_le (1 / 2 : ℂ) (I * z)
    norm_num only [norm_div, norm_one, norm_ofNat, norm_mul, norm_I, one_mul] at h
    linarith
  rw [deriv_logDeriv_riemannXiSpectral_eq_neg_euler hz, norm_neg]
  calc
    _ ≤ C * (1 + ‖suzukiArithmeticZetaArgument z‖) ^ 4 := hbound _ hs
    _ ≤ C * (2 * (1 + ‖z‖)) ^ 4 := by gcongr; linarith [norm_nonneg z]
    _ = _ := by ring

/-- The derivative of the actual safe carrier keeps its full complex
phase: it is minus the carrier square times logarithmic curvature. -/
theorem deriv_suzukiXiZeroCarrier_eq_neg_sq_mul_curvature_safe {z : ℂ}
    (hz : 1 / 2 ≤ z.im) :
    deriv suzukiXiZeroCarrier z =
      -suzukiXiZeroCarrier z ^ 2 * deriv (logDeriv riemannXiSpectral) z := by
  have hxi := riemannXiSpectral_ne_zero_of_half_le_abs_im (hz.trans (le_abs_self _))
  have hE := suzukiXiEValue_ne_zero_of_half_le_im hz
  have he : suzukiXiZeroCarrier =ᶠ[𝓝 z]
      fun w => I / (1 + I * logDeriv riemannXiSpectral w) := by
    filter_upwards [(analyticAt_riemannXiSpectral z).continuousAt.eventually_ne hxi,
      (analyticAt_suzukiXiEValue z).continuousAt.eventually_ne hE] with w hw hwE
    exact suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv hw hwE
  have hden : 1 + I * logDeriv riemannXiSpectral z ≠ 0 := by
    have hh := analyticEValue_riemannXiSpectral_eq_mul_logDeriv hxi 1
    change suzukiXiEValue z = _ at hh
    simp only [ofReal_one, mul_one] at hh
    intro hn
    rw [hn, mul_zero] at hh
    exact hE hh
  have hL := (analyticAt_logDeriv_riemannXiSpectral_of_ne hxi).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_const z I).fun_div ((hL.const_mul I).const_add 1) hden
  rw [he.deriv_eq, hd.deriv, suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv hxi hE]
  field_simp
  ring

/-- Exact source-curvature identity on the closed safe half-plane.
Only the radial coefficient is real and nonnegative; the full conjugate
curvature and its orientation remain visible. -/
theorem suzukiXiSmoothCarrierSource_eq_curvature_safe {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    suzukiXiSmoothCarrierSource r z =
      2 * I * (r : ℂ) ^ 2 * (normSq (suzukiXiZeroCarrier z) : ℂ) ^ 2 *
        starRingEnd ℂ (deriv (logDeriv riemannXiSpectral) z) /
          ((1 + r ^ 2 * normSq (suzukiXiZeroCarrier z) : ℝ) : ℂ) ^ 2 := by
  rw [suzukiXiSmoothCarrierSource_eq_radial_deriv_safe hr hz,
    deriv_suzukiXiZeroCarrier_eq_neg_sq_mul_curvature_safe hz]
  simp only [map_mul, map_neg, map_pow, ← Complex.mul_conj]
  ring

private lemma radial_quartic_bound {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    r ^ 2 * a ^ 2 / (1 + r ^ 2 * a) ^ 2 ≤ 1 / r ^ 2 := by
  apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hr)).mpr
  nlinarith [mul_nonneg (sq_nonneg r) ha]

/-- Quadratic smoothing decay of the full source, measured against its
actual logarithmic curvature. The estimate includes the Euler boundary. -/
theorem norm_suzukiXiSmoothCarrierSource_le_curvature_safe {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    ‖suzukiXiSmoothCarrierSource r z‖ ≤
      2 * ‖deriv (logDeriv riemannXiSpectral) z‖ / r ^ 2 := by
  rw [suzukiXiSmoothCarrierSource_eq_curvature_safe hr hz]
  simp only [norm_div, norm_mul, norm_pow, norm_conj, norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one]
  calc
    _ = 2 * ‖deriv (logDeriv riemannXiSpectral) z‖ *
        (r ^ 2 * normSq (suzukiXiZeroCarrier z) ^ 2 /
          (1 + r ^ 2 * normSq (suzukiXiZeroCarrier z)) ^ 2) := by ring
    _ ≤ 2 * ‖deriv (logDeriv riemannXiSpectral) z‖ * (1 / r ^ 2) := by
      exact mul_le_mul_of_nonneg_left (radial_quartic_bound hr (normSq_nonneg _))
        (by positivity)
    _ = _ := by ring

/-- A single polynomial majorant gives quadratic smoothing decay of
the actual normalized arithmetic source on all of `Re s >= 1`. -/
theorem exists_suzukiGammaShiftArithmeticSource_euler_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ z : ℂ, 1 / 2 ≤ z.im →
      ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ ≤
        C * (1 + ‖z‖) ^ 4 / r ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_deriv_logDeriv_riemannXiSpectral_safe_polynomial_bound
  refine ⟨2 * C + 1 / 4, by positivity, ?_⟩
  intro r hr z hz
  have hs : 0 < (suzukiArithmeticZetaArgument z).re := by
    rw [suzukiArithmeticZetaArgument_re]
    linarith
  have he := norm_suzukiXiSmoothCarrierSource_gammaShift_error_le hr hs (1 : ℂ)
  simp only [one_mul, norm_one] at he
  have hv := norm_suzukiXiSmoothCarrierSource_le_curvature_safe hr hz
  have ht := norm_sub_le (suzukiXiSmoothCarrierSource r z)
    (suzukiXiSmoothCarrierSource r z -
      suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z))
  rw [sub_sub_cancel] at ht
  have hp : 1 ≤ (1 + ‖z‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg z])
  calc
    _ ≤ 2 * ‖deriv (logDeriv riemannXiSpectral) z‖ / r ^ 2 + 1 / (4 * r ^ 2) :=
      ht.trans (add_le_add hv he)
    _ ≤ 2 * (C * (1 + ‖z‖) ^ 4) / r ^ 2 + (1 + ‖z‖) ^ 4 / (4 * r ^ 2) := by
      gcongr
      exact hbound z hz
    _ = _ := by ring

private lemma integrable_gaussian_abs_polynomial {tau : ℝ} (htau : 0 < tau)
    (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-tau * (c - x) ^ 2) * (1 + |x|) ^ n) := by
  have hh := integrable_translatedGaussian_mul_of_polynomial_bound
    (f := fun x : ℝ => (1 + |x|) ^ n) htau c (by fun_prop)
    (show 0 ≤ (1 + |c|) ^ n by positivity) n (fun x => ?_)
  · convert! hh using 1
    funext x
    simp only [translatedGaussian, smul_eq_mul, sub_sq_comm c x]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have ht : |x| ≤ |x - c| + |c| := by
    simpa only [sub_add_cancel] using abs_add_le (x - c) c
  nlinarith [mul_nonneg (abs_nonneg c) (abs_nonneg (x - c))]

/-- Every polynomial in the planar norm is integrable against the
original boundary heat. This supplies one majorant for all moving cutoffs. -/
theorem integrable_norm_suzukiSmoothSpectralBoundaryHeat_mul_polynomial
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) (n : ℕ) :
    Integrable (fun z : ℂ => (1 + ‖z‖) ^ n * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖) := by
  let f := fun x : ℝ => Real.exp (-tau * (c - x) ^ 2) * (1 + |x|) ^ n
  let g := fun y : ℝ => 2 * Real.exp (-tau * y ^ 2) * (1 + |y|) ^ (n + 1)
  have hx : Integrable f := integrable_gaussian_abs_polynomial htau c n
  have hy : Integrable g := by
    convert! (integrable_gaussian_abs_polynomial htau 0 (n + 1)).const_mul 2 using 1
    funext y
    simp only [g, zero_sub, neg_sq]
    ring
  have hp := hx.mul_prod hy
  have hm : Integrable (fun z : ℂ => f z.re * g z.im) := by
    convert! (Complex.volume_preserving_equiv_real_prod.integrable_comp
      hp.aestronglyMeasurable).mpr hp using 1
  have hB := (differentiable_suzukiSmoothSpectralBoundaryHeat c tau).continuous
  refine hm.mono' (by fun_prop) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hn : ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ =
      2 * |z.im| * Real.exp (-tau * ((c - z.re) ^ 2 + z.im ^ 2)) := by
    rw [suzukiSmoothSpectralBoundaryHeat_eq, Complex.norm_real, Real.norm_eq_abs]
    simp only [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hU : (1 + ‖z‖) ^ n ≤ (1 + |z.re|) ^ n * (1 + |z.im|) ^ n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Complex.norm_le_abs_re_add_abs_im z,
      mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]
  have hyP : |z.im| * (1 + |z.im|) ^ n ≤ (1 + |z.im|) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show 0 ≤ 1 + |z.im| by positivity) n]
  rw [hn, mul_add, Real.exp_add]
  calc
    _ ≤ ((1 + |z.re|) ^ n * (1 + |z.im|) ^ n) *
        (2 * |z.im| * (Real.exp (-tau * (c - z.re) ^ 2) * Real.exp (-tau * z.im ^ 2))) := by
      exact mul_le_mul_of_nonneg_right hU (by positivity)
    _ = (2 * Real.exp (-tau * (c - z.re) ^ 2) * Real.exp (-tau * z.im ^ 2) *
        (1 + |z.re|) ^ n) * (|z.im| * (1 + |z.im|) ^ n) := by ring
    _ ≤ (2 * Real.exp (-tau * (c - z.re) ^ 2) * Real.exp (-tau * z.im ^ 2) *
        (1 + |z.re|) ^ n) * (1 + |z.im|) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hyP (by positivity)
    _ = f z.re * g z.im := by dsimp [f, g]; ring

/-- The genuine selected zero has a positive distance from the Euler
boundary. Its original reflected weight is bounded there without an
additional sampling buffer. -/
theorem norm_suzukiXiReflectionWeight_le_euler (rho : NontrivialZetaZero)
    {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    ‖suzukiXiReflectionWeight rho z‖ ≤
      4 * (zetaSpectralCoordinate rho.1).im ^ 2 /
        (1 / 2 - |(zetaSpectralCoordinate rho.1).im|) ^ 4 := by
  let a := zetaSpectralCoordinate rho.1
  let d := 1 / 2 - |a.im|
  have hd0 : 0 < d := sub_pos.mpr (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho)
  have hd : d ≤ ‖z - a‖ := by
    have hh := Complex.im_le_norm (z - a)
    simp only [sub_im] at hh
    dsimp [d]
    linarith [le_abs_self a.im]
  have he : d ≤ ‖z - starRingEnd ℂ a‖ := by
    have hh := Complex.im_le_norm (z - starRingEnd ℂ a)
    simp only [sub_im, conj_im] at hh
    dsimp [d]
    linarith [neg_le_abs a.im]
  have hza : z ≠ a := sub_ne_zero.mp (norm_pos_iff.mp (hd0.trans_le hd))
  have hzb : z ≠ starRingEnd ℂ a := sub_ne_zero.mp (norm_pos_iff.mp (hd0.trans_le he))
  rw [suzukiXiReflectionWeight_eq_quartic rho hza hzb, norm_div, norm_mul, norm_pow,
    norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num only [norm_ofNat]
  calc
    _ ≤ 4 * (zetaSpectralCoordinate rho.1).im ^ 2 / (d * d) ^ 2 := by gcongr
    _ = _ := by dsimp [d, a]; ring

/-- The original reflected arithmetic density has one polynomial-Gaussian
majorant on the closed Euler half-plane, uniformly in smoothing and cutoff. -/
theorem exists_suzukiGammaShiftWeightedArithmeticSource_euler_bound
    (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ c tau : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.im →
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖ ≤
        (C / r ^ 2) * ((1 + ‖z‖) ^ 4 * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖) := by
  obtain ⟨C, hC, hA⟩ := exists_suzukiGammaShiftArithmeticSource_euler_bound
  let W := 4 * (zetaSpectralCoordinate rho.1).im ^ 2 /
    (1 / 2 - |(zetaSpectralCoordinate rho.1).im|) ^ 4
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨W * C, mul_nonneg hW hC, ?_⟩
  intro r hr c tau z hz
  unfold suzukiGammaShiftWeightedArithmeticSource
  simp only [norm_mul]
  calc
    _ ≤ W * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ *
        (C * (1 + ‖z‖) ^ 4 / r ^ 2) := by
      gcongr
      · exact norm_suzukiXiReflectionWeight_le_euler rho hz
      · exact hA r hr z hz
    _ = _ := by ring

private lemma integrable_weighted_source_euler (rho : NontrivialZetaZero)
    {r tau : ℝ} (hr : 0 < r) (htau : 0 < tau) (c : ℝ) :
    IntegrableOn (fun z => suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z *
      suzukiXiSmoothCarrierSource r z) {z : ℂ | 1 / 2 ≤ z.im} := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_deriv_logDeriv_riemannXiSpectral_safe_polynomial_bound
  let W := 4 * (zetaSpectralCoordinate rho.1).im ^ 2 /
    (1 / 2 - |(zetaSpectralCoordinate rho.1).im|) ^ 4
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hmW : Measurable (suzukiXiReflectionWeight rho) := by
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    fun_prop
  have hmB := (differentiable_suzukiSmoothSpectralBoundaryHeat c tau).continuous.measurable
  have hmV := (continuous_suzukiXiSmoothCarrierSource hr).measurable
  have hm := ((hmW.mul hmB).mul hmV).aestronglyMeasurable (μ := volume)
  have hmajor := ((integrable_norm_suzukiSmoothSpectralBoundaryHeat_mul_polynomial htau c 4).const_mul
    (2 * W * C / r ^ 2)).integrableOn (s := {z : ℂ | 1 / 2 ≤ z.im})
  refine hmajor.mono' (hm.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem (isClosed_le continuous_const Complex.continuous_im).measurableSet]
    with z hz
  simp only [norm_mul]
  have hv := (norm_suzukiXiSmoothCarrierSource_le_curvature_safe hr hz).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound z hz) (by norm_num))
      (sq_nonneg r))
  calc
    _ ≤ W * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ *
        (2 * (C * (1 + ‖z‖) ^ 4) / r ^ 2) := by
      gcongr
      exact norm_suzukiXiReflectionWeight_le_euler rho hz
    _ = _ := by ring

/-- The literal normalized arithmetic density is integrable on the whole
closed Euler half-plane, including its boundary and all spatial tails. -/
theorem integrableOn_suzukiGammaShiftWeightedArithmeticSource_euler
    (rho : NontrivialZetaZero) {r tau : ℝ} (hr : 1 ≤ r) (htau : 0 < tau) (c : ℝ) :
    IntegrableOn (suzukiGammaShiftWeightedArithmeticSource rho r c tau)
      {z : ℂ | 1 / 2 ≤ z.im} := by
  have hV := integrable_weighted_source_euler rho (lt_of_lt_of_le zero_lt_one hr) htau c
  have hE := (integrableOn_suzukiGammaShiftReflectionError rho hr htau c).mono_set
    (show {z : ℂ | 1 / 2 ≤ z.im} ⊆ {z : ℂ | 0 ≤ z.im} from
      fun _ hz => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hz)
  convert! hV.sub hE using 1
  funext z
  simp only [Pi.sub_apply, suzukiGammaShiftWeightedArithmeticSource, suzukiGammaShiftReflectionError]
  ring

/-- The complete reflected arithmetic L1 mass on the closed Euler
half-plane is bounded by a fixed constant times `r^-2`. -/
theorem exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_euler_bound
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      (∫ z in {z : ℂ | 1 / 2 ≤ z.im},
        ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖) ≤ C / r ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_suzukiGammaShiftWeightedArithmeticSource_euler_bound rho
  let J := ∫ z : ℂ, (1 + ‖z‖) ^ 4 * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  refine ⟨C * J, mul_nonneg hC hJ, ?_⟩
  intro r hr
  have hB := integrable_norm_suzukiSmoothSpectralBoundaryHeat_mul_polynomial htau c 4
  calc
    _ ≤ ∫ z in {z : ℂ | 1 / 2 ≤ z.im},
        (C / r ^ 2) * ((1 + ‖z‖) ^ 4 * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖) := by
      apply integral_mono_ae
        (integrableOn_suzukiGammaShiftWeightedArithmeticSource_euler rho hr htau c).norm
        (hB.const_mul (C / r ^ 2)).integrableOn
      filter_upwards [ae_restrict_mem (isClosed_le continuous_const Complex.continuous_im).measurableSet]
        with z hz
      exact hbound r (lt_of_lt_of_le zero_lt_one hr) c tau z hz
    _ = (C / r ^ 2) * ∫ z in {z : ℂ | 1 / 2 ≤ z.im},
        (1 + ‖z‖) ^ 4 * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ := integral_const_mul _ _
    _ ≤ (C / r ^ 2) * J := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hB (ae_of_all _ fun _ => by positivity)) (by positivity)
    _ = _ := by ring

/-- The complete closed Euler half-plane is independently negligible
in the normalized arithmetic source, with no fixed buffer left over. -/
theorem tendsto_integral_norm_suzukiGammaShiftWeightedArithmeticSource_euler
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | 1 / 2 ≤ z.im},
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_euler_bound rho htau c
  have hb : Tendsto (fun r : ℝ => C / r ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact hbound r hr

/-- Arbitrary moving cutoffs in the closed Euler half-plane inherit
the full arithmetic decay from one global L1 estimate. -/
theorem tendsto_setIntegral_suzukiGammaShiftWeightedArithmeticSource_euler
    (rho : NontrivialZetaZero) {tau : ℝ} (htau : 0 < tau) (c : ℝ) (K : ℝ → Set ℂ)
    (hK : ∀ r, K r ⊆ {z : ℂ | 1 / 2 ≤ z.im}) :
    Tendsto (fun r : ℝ => ∫ z in K r, suzukiGammaShiftWeightedArithmeticSource rho r c tau z)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_integral_norm_suzukiGammaShiftWeightedArithmeticSource_euler rho htau c)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_mono_set
    (integrableOn_suzukiGammaShiftWeightedArithmeticSource_euler rho hr htau c).norm
    (ae_of_all _ fun _ => norm_nonneg _) (ae_of_all _ fun _ hz => hK r hz)

open scoped Interval in
/-- After removing the entire closed Euler half-plane, the original
selected source remains in the zero strip itself, even under simultaneous
spatial and smoothing growth. Its independent arithmetic ceiling is open. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_zero_strip
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {tau : ℝ}
    (htau : 0 < tau) (c : ℝ) (R : ℝ → ℝ)
    (hR : ∀ r, 1 ≤ R r) (hc : ∀ r, 2 * |c| ≤ R r)
    (hRe : ∀ r, 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R r) :
    Tendsto (fun r : ℝ => ∫ z in ([[ -R r,R r]] ×ℂ [[0,R r]]) \ {z : ℂ | 1 / 2 ≤ z.im},
      suzukiGammaShiftWeightedArithmeticSource rho r c tau z) atTop
      (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let K : ℝ → Set ℂ := fun r => [[-R r,R r]] ×ℂ [[0,R r]]
  let T : Set ℂ := {z : ℂ | 1 / 2 ≤ z.im}
  have hT : MeasurableSet T := (isClosed_le continuous_const Complex.continuous_im).measurableSet
  have hfull := tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_rectangle rho hzero htau c R hR hc hRe
  have htail := tendsto_setIntegral_suzukiGammaShiftWeightedArithmeticSource_euler rho htau c
    (fun r => K r ∩ T) (fun _ => inter_subset_right)
  have h := hfull.sub htail
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hupper : K r ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hy := hz.2
    rw [uIcc_of_le (show 0 ≤ R r by linarith [hR r])] at hy
    exact hy.1
  have hA := integrableOn_suzukiGammaShiftWeightedArithmeticSource rho hr htau c
    (show IsCompact (K r) from isCompact_uIcc.reProdIm isCompact_uIcc) hupper
  have he := integral_inter_add_sdiff hT hA
  change (∫ z in K r, suzukiGammaShiftWeightedArithmeticSource rho r c tau z) -
      (∫ z in K r ∩ T, suzukiGammaShiftWeightedArithmeticSource rho r c tau z) =
      (∫ z in K r \ T, suzukiGammaShiftWeightedArithmeticSource rho r c tau z)
  rw [← he]
  ring

end
end RiemannGaussian
