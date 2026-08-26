import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.Deriv.Star
import RiemannGaussian.GaussianHeat

/-!
# A Gaussian-integrable bound for the quarter-line digamma function

The explicit formula samples `digamma` on `1 / 4 + I * r / 2`.  Mathlib
currently provides the definition and functional equation, but no vertical
growth estimate.  This file derives a deliberately coarse exponential bound
from Euler's integral for `Gamma`, its differentiated Mellin integral, and
Euler reflection.  Exponential growth is more than sufficient under every
positive-width Gaussian.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory Set

/-- The common norm integral majorizing `Gamma'` on the vertical line
`re z = 1 / 4`. -/
def gammaQuarterDerivativeMass : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ‖(x : ℂ) ^ ((1 / 4 : ℂ) - 1) *
      (Real.log x * Real.exp (-x))‖

/-- The common norm integral majorizing `Gamma` on the vertical line
`re z = 3 / 4`. -/
def gammaThreeQuarterMass : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ ((3 / 4 : ℂ) - 1)‖

lemma gammaQuarterDerivativeMass_nonneg :
    0 ≤ gammaQuarterDerivativeMass := by
  exact integral_nonneg fun _ => norm_nonneg _

lemma gammaThreeQuarterMass_nonneg :
    0 ≤ gammaThreeQuarterMass := by
  exact integral_nonneg fun _ => norm_nonneg _

/-- On the positive half-plane, differentiating Euler's Gamma integral gives
the derivative of the meromorphic Gamma function itself. -/
theorem deriv_Gamma_eq_integral_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    deriv Complex.Gamma s =
      ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have heq : Complex.Gamma =ᶠ[nhds s] Complex.GammaIntegral := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact Complex.Gamma_eq_integral hz
  calc
    deriv Complex.Gamma s = deriv Complex.GammaIntegral s :=
      heq.deriv_eq
    _ = ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x)) :=
      (Complex.hasDerivAt_GammaIntegral hs).deriv

theorem norm_deriv_Gamma_quarter_line_le (r : ℝ) :
    ‖deriv Complex.Gamma
      (1 / 4 + Complex.I * (r / 2))‖ ≤
        gammaQuarterDerivativeMass := by
  let z : ℂ := 1 / 4 + Complex.I * (r / 2)
  have hz : 0 < z.re := by
    simp [z]
  rw [deriv_Gamma_eq_integral_of_re_pos hz]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (z - 1) *
          (Real.log x * Real.exp (-x))‖ ≤
        ∫ x : ℝ in Ioi 0,
          ‖(x : ℂ) ^ (z - 1) *
            (Real.log x * Real.exp (-x))‖ :=
      norm_integral_le_integral_norm _
    _ = gammaQuarterDerivativeMass := by
      unfold gammaQuarterDerivativeMass
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      simp only [norm_mul]
      congr 1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [z]

theorem norm_Gamma_threeQuarter_line_le (r : ℝ) :
    ‖Complex.Gamma (3 / 4 - Complex.I * (r / 2))‖ ≤
      gammaThreeQuarterMass := by
  let z : ℂ := 3 / 4 - Complex.I * (r / 2)
  have hz : 0 < z.re := by
    simp [z]
  rw [Complex.Gamma_eq_integral hz]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ ≤
        ∫ x : ℝ in Ioi 0,
          ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = gammaThreeQuarterMass := by
      unfold gammaThreeQuarterMass
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      simp only [norm_mul]
      congr 1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [z]

/-- A coarse global bound for the complex sine. -/
lemma norm_complex_sin_le_exp_norm (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  change ‖(Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) *
    Complex.I / 2‖ ≤ Real.exp ‖z‖
  calc
    ‖(Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) *
        Complex.I / 2‖ ≤
        (‖Complex.exp (-z * Complex.I)‖ +
          ‖Complex.exp (z * Complex.I)‖) / 2 := by
      rw [norm_div, norm_mul]
      norm_num
      exact div_le_div_of_nonneg_right
        (norm_sub_le (Complex.exp (-(z * Complex.I)))
          (Complex.exp (z * Complex.I))) (by norm_num)
    _ ≤ (Real.exp ‖z‖ + Real.exp ‖z‖) / 2 := by
      gcongr
      · simpa using Complex.norm_exp_le_exp_norm (-z * Complex.I)
      · simpa using Complex.norm_exp_le_exp_norm (z * Complex.I)
    _ = Real.exp ‖z‖ := by ring

/-- Reflection converts the reciprocal Gamma factor on `re z = 1 / 4`
into a Gamma factor on `re z = 3 / 4` and one complex sine. -/
theorem norm_inv_Gamma_quarter_line_le (r : ℝ) :
    ‖(Complex.Gamma
      (1 / 4 + Complex.I * (r / 2)))⁻¹‖ ≤
      gammaThreeQuarterMass / Real.pi *
        Real.exp (Real.pi * (|r| + 1)) := by
  let z : ℂ := 1 / 4 + Complex.I * (r / 2)
  have hz : 0 < z.re := by simp [z]
  have h1z : 0 < (1 - z).re := by
    simp [z]
    norm_num
  have hGamma : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hz
  have hGamma1 : Complex.Gamma (1 - z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1z
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at href
    exact (mul_ne_zero hGamma hGamma1) href
  have href' :
      Complex.Gamma z * Complex.Gamma (1 - z) *
          Complex.sin ((Real.pi : ℂ) * z) = (Real.pi : ℂ) := by
    calc
      Complex.Gamma z * Complex.Gamma (1 - z) *
          Complex.sin ((Real.pi : ℂ) * z) =
          ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z)) *
            Complex.sin ((Real.pi : ℂ) * z) := by rw [href]
      _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hsin
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv :
      (Complex.Gamma z)⁻¹ =
        Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) /
          (Real.pi : ℂ) := by
    apply mul_left_cancel₀ hGamma
    rw [mul_inv_cancel₀ hGamma]
    calc
      1 = (Real.pi : ℂ) / (Real.pi : ℂ) := (div_self hpi).symm
      _ = (Complex.Gamma z * Complex.Gamma (1 - z) *
          Complex.sin ((Real.pi : ℂ) * z)) / (Real.pi : ℂ) := by rw [href']
      _ = Complex.Gamma z *
          (Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) /
            (Real.pi : ℂ)) := by ring
  have honeSub :
      1 - z = 3 / 4 - Complex.I * (r / 2) := by
    dsimp [z]
    ring
  have hGammaNorm :
      ‖Complex.Gamma (1 - z)‖ ≤ gammaThreeQuarterMass := by
    rw [honeSub]
    exact norm_Gamma_threeQuarter_line_le r
  have hzNorm : ‖z‖ ≤ |r| + 1 := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| :=
        Complex.norm_le_abs_re_add_abs_im z
      _ = 1 / 4 + |r| / 2 := by
        simp [z, abs_div]
      _ ≤ |r| + 1 := by
        nlinarith [abs_nonneg r]
  have hpizNorm :
      ‖(Real.pi : ℂ) * z‖ ≤ Real.pi * (|r| + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hzNorm Real.pi_pos.le
  have hsinNorm :
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤
        Real.exp (Real.pi * (|r| + 1)) := by
    exact (norm_complex_sin_le_exp_norm _).trans
      (Real.exp_le_exp.mpr hpizNorm)
  change ‖(Complex.Gamma z)⁻¹‖ ≤ _
  rw [hinv, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    ‖Complex.Gamma (1 - z)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * z)‖ / Real.pi ≤
        gammaThreeQuarterMass *
          Real.exp (Real.pi * (|r| + 1)) / Real.pi := by
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      exact mul_le_mul hGammaNorm hsinNorm (norm_nonneg _)
        gammaThreeQuarterMass_nonneg
    _ = gammaThreeQuarterMass / Real.pi *
        Real.exp (Real.pi * (|r| + 1)) := by ring

/-- A fixed nonnegative coefficient for the exponential digamma bound. -/
def quarterDigammaExponentialConstant : ℝ :=
  gammaQuarterDerivativeMass * gammaThreeQuarterMass / Real.pi

lemma quarterDigammaExponentialConstant_nonneg :
    0 ≤ quarterDigammaExponentialConstant := by
  exact div_nonneg
    (mul_nonneg gammaQuarterDerivativeMass_nonneg
      gammaThreeQuarterMass_nonneg)
    Real.pi_pos.le

/-- The quarter-line digamma has at most exponential vertical growth.  This
coarse estimate is tailored to convergence under a Gaussian, not numerical
certification. -/
theorem norm_digamma_quarter_line_le (r : ℝ) :
    ‖Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ ≤
      quarterDigammaExponentialConstant *
        Real.exp (Real.pi * (|r| + 1)) := by
  rw [Complex.digamma_def, logDeriv_apply, div_eq_mul_inv, norm_mul]
  calc
    ‖deriv Complex.Gamma (1 / 4 + Complex.I * (r / 2))‖ *
        ‖(Complex.Gamma (1 / 4 + Complex.I * (r / 2)))⁻¹‖ ≤
      gammaQuarterDerivativeMass *
        (gammaThreeQuarterMass / Real.pi *
          Real.exp (Real.pi * (|r| + 1))) := by
      exact mul_le_mul
        (norm_deriv_Gamma_quarter_line_le r)
        (norm_inv_Gamma_quarter_line_le r)
        (norm_nonneg _)
        gammaQuarterDerivativeMass_nonneg
    _ = quarterDigammaExponentialConstant *
        Real.exp (Real.pi * (|r| + 1)) := by
      unfold quarterDigammaExponentialConstant
      ring

/-- Digamma is analytic throughout the positive real half-plane.  This
global form is useful for contour arguments inside the critical strip. -/
theorem analyticOnNhd_digamma_re_pos :
    AnalyticOnNhd ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hGammaDiff : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z _).differentiableWithinAt
    intro m hzm
    have hre := congrArg Complex.re hzm
    simp [U] at hz hre
    linarith
  have hGammaAnalytic : AnalyticOnNhd ℂ Complex.Gamma U :=
    hGammaDiff.analyticOnNhd hUopen
  have hDigammaAnalytic : AnalyticOnNhd ℂ Complex.digamma U := by
    rw [Complex.digamma_def]
    change AnalyticOnNhd ℂ
      (fun z => deriv Complex.Gamma z / Complex.Gamma z) U
    exact hGammaAnalytic.deriv.div hGammaAnalytic
      (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)
  exact hDigammaAnalytic

/-- The quarter-line restriction avoids every Gamma pole, so the digamma
restriction is continuous. -/
theorem continuous_digamma_quarter_line :
    Continuous (fun r : ℝ =>
      Complex.digamma (1 / 4 + Complex.I * (r / 2))) := by
  exact analyticOnNhd_digamma_re_pos.continuousOn.comp_continuous
    (by fun_prop)
    (fun r => by norm_num)

@[simp]
theorem digamma_conj (z : ℂ) :
    Complex.digamma (starRingEnd ℂ z) =
      starRingEnd ℂ (Complex.digamma z) := by
  have hfun :
      (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) =
        Complex.Gamma := by
    funext w
    simp [Function.comp_apply, Complex.Gamma_conj]
  have hderiv :
      deriv Complex.Gamma (starRingEnd ℂ z) =
        starRingEnd ℂ (deriv Complex.Gamma z) := by
    have h := congrFun (deriv_conj_conj (f := Complex.Gamma))
      (starRingEnd ℂ z)
    rw [hfun] at h
    simpa [Function.comp_apply] using h
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply,
    hderiv, Complex.Gamma_conj, map_div₀]

/-- A translated Gaussian absorbs the deliberately coarse exponential
majorant used for the quarter-line digamma. -/
theorem integrable_translatedGaussian_mul_exp_pi_abs
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      Real.exp (-ε * (r - t) ^ 2) *
        Real.exp (Real.pi * (|r| + 1))) := by
  let P : ℝ → ℂ := fun r => Complex.exp
    (-((ε : ℂ)) * r ^ 2 +
      ((2 * ε * t + Real.pi : ℝ) : ℂ) * r +
        ((-ε * t ^ 2 + Real.pi : ℝ) : ℂ))
  let M : ℝ → ℂ := fun r => Complex.exp
    (-((ε : ℂ)) * r ^ 2 +
      ((2 * ε * t - Real.pi : ℝ) : ℂ) * r +
        ((-ε * t ^ 2 + Real.pi : ℝ) : ℂ))
  have hP : Integrable P := by
    exact integrable_cexp_quadratic (b := (ε : ℂ))
      (by simpa using hε)
      ((2 * ε * t + Real.pi : ℝ) : ℂ)
      ((-ε * t ^ 2 + Real.pi : ℝ) : ℂ)
  have hM : Integrable M := by
    exact integrable_cexp_quadratic (b := (ε : ℂ))
      (by simpa using hε)
      ((2 * ε * t - Real.pi : ℝ) : ℂ)
      ((-ε * t ^ 2 + Real.pi : ℝ) : ℂ)
  apply Integrable.mono' (hP.norm.add hM.norm)
  · exact (by fun_prop : Continuous (fun r : ℝ =>
      Real.exp (-ε * (r - t) ^ 2) *
        Real.exp (Real.pi * (|r| + 1)))).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    rcases le_total 0 r with hr | hr
    · calc
        Real.exp (-ε * (r - t) ^ 2) *
            Real.exp (Real.pi * (|r| + 1)) =
            Real.exp (-ε * (r - t) ^ 2 +
              Real.pi * (r + 1)) := by
          rw [abs_of_nonneg hr, ← Real.exp_add]
        _ = ‖P r‖ := by
          unfold P
          rw [Complex.norm_exp]
          congr 1
          push_cast
          simp [pow_two]
          ring
        _ ≤ ‖P r‖ + ‖M r‖ := le_add_of_nonneg_right (norm_nonneg _)
    · calc
        Real.exp (-ε * (r - t) ^ 2) *
            Real.exp (Real.pi * (|r| + 1)) =
            Real.exp (-ε * (r - t) ^ 2 +
              Real.pi * (-r + 1)) := by
          rw [abs_of_nonpos hr, ← Real.exp_add]
        _ = ‖M r‖ := by
          unfold M
          rw [Complex.norm_exp]
          congr 1
          push_cast
          simp [pow_two]
          ring
        _ ≤ ‖P r‖ + ‖M r‖ := le_add_of_nonneg_left (norm_nonneg _)

/-- Consequently the real part of quarter-line digamma is integrable against
every translated positive-width Gaussian. -/
theorem integrable_translatedGaussian_mul_re_digamma_quarter
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      Real.exp (-ε * (r - t) ^ 2) *
        (Complex.digamma (1 / 4 + Complex.I * (r / 2))).re) := by
  have hmajor :=
    (integrable_translatedGaussian_mul_exp_pi_abs hε t).const_mul
      quarterDigammaExponentialConstant
  apply Integrable.mono' hmajor
  · have hRe : Continuous (fun r : ℝ =>
        (Complex.digamma (1 / 4 + Complex.I * (r / 2))).re) :=
      Complex.continuous_re.comp continuous_digamma_quarter_line
    exact ((by fun_prop : Continuous (fun r : ℝ =>
      Real.exp (-ε * (r - t) ^ 2))).mul hRe).aestronglyMeasurable
  · filter_upwards with r
    calc
      ‖Real.exp (-ε * (r - t) ^ 2) *
          (Complex.digamma
            (1 / 4 + Complex.I * (r / 2))).re‖ =
          Real.exp (-ε * (r - t) ^ 2) *
            |(Complex.digamma
              (1 / 4 + Complex.I * (r / 2))).re| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-ε * (r - t) ^ 2) *
          ‖Complex.digamma
            (1 / 4 + Complex.I * (r / 2))‖ :=
        mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm _) (Real.exp_nonneg _)
      _ ≤ Real.exp (-ε * (r - t) ^ 2) *
          (quarterDigammaExponentialConstant *
            Real.exp (Real.pi * (|r| + 1))) :=
        mul_le_mul_of_nonneg_left
          (norm_digamma_quarter_line_le r) (Real.exp_nonneg _)
      _ = quarterDigammaExponentialConstant *
          (Real.exp (-ε * (r - t) ^ 2) *
            Real.exp (Real.pi * (|r| + 1))) := by ring

/-- The full complex quarter-line digamma, not only its real part, is
integrable against every translated positive-width Gaussian. -/
theorem integrable_translatedGaussian_mul_digamma_quarter
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      (Real.exp (-ε * (r - t) ^ 2) : ℂ) *
        Complex.digamma (1 / 4 + Complex.I * (r / 2))) := by
  have hmajorReal :=
    (integrable_translatedGaussian_mul_exp_pi_abs hε t).const_mul
      quarterDigammaExponentialConstant
  refine hmajorReal.mono' ?_ ?_
  · exact ((by fun_prop : Continuous (fun r : ℝ =>
      (Real.exp (-ε * (r - t) ^ 2) : ℂ))).mul
        continuous_digamma_quarter_line).aestronglyMeasurable
  · filter_upwards with r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-ε * (r - t) ^ 2) *
          ‖Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ ≤
        Real.exp (-ε * (r - t) ^ 2) *
          (quarterDigammaExponentialConstant *
            Real.exp (Real.pi * (|r| + 1))) :=
        mul_le_mul_of_nonneg_left
          (norm_digamma_quarter_line_le r) (Real.exp_nonneg _)
      _ = quarterDigammaExponentialConstant *
          (Real.exp (-ε * (r - t) ^ 2) *
            Real.exp (Real.pi * (|r| + 1))) := by ring

/-- The even Gaussian used by the explicit formula also absorbs the full
complex quarter-line digamma. -/
theorem integrable_symmetricGaussian_mul_digamma_quarter
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) *
        Complex.digamma (1 / 4 + Complex.I * (r / 2))) := by
  have hfirst := integrable_translatedGaussian_mul_digamma_quarter hε t
  have hsecondCenter :=
    integrable_translatedGaussian_mul_digamma_quarter hε (-t)
  have hsecond : Integrable (fun r : ℝ =>
      (translatedGaussian ε t (-r) : ℂ) *
        Complex.digamma (1 / 4 + Complex.I * (r / 2))) := by
    apply hsecondCenter.congr
    filter_upwards with r
    congr 2
    unfold translatedGaussian
    congr 1
    ring
  rw [show (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) *
        Complex.digamma (1 / 4 + Complex.I * (r / 2))) =
      fun r : ℝ =>
        (translatedGaussian ε t r : ℂ) *
            Complex.digamma (1 / 4 + Complex.I * (r / 2)) +
          (translatedGaussian ε t (-r) : ℂ) *
            Complex.digamma (1 / 4 + Complex.I * (r / 2)) by
    funext r
    unfold symmetricGaussian
    push_cast
    ring]
  exact hfirst.add hsecond

end

end RiemannGaussian
