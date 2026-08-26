import RiemannGaussian.GaussianDigammaGrowth

/-!
# Uniform digamma growth in the contour-shift strip

The Archimedean contour shift samples `digamma w` uniformly for
`1 / 4 ≤ re w ≤ 3 / 4`.  This file extends the critical-line estimate to
that closed strip.  Endpoint Mellin integrals dominate the whole strip;
Euler reflection then supplies a deliberately coarse exponential vertical
bound, which is sufficient against a positive-width Gaussian.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory Set Filter Asymptotics

/-- Absolute convergence of the differentiated Euler-Gamma integral on the
whole positive half-plane. -/
theorem integrableOn_Gamma_derivative_integrand
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) *
        (Real.log x * Real.exp (-x))) (Ioi 0) := by
  have hconv : MellinConvergent
      (fun x : ℝ => Real.log x • (Real.exp (-x) : ℂ)) s := by
    refine (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
      ?_ ?_ (lt_add_one _) ?_ hs).1
    · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
      exact Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)
    · rw [← isBigO_norm_left]
      simp_rw [Complex.norm_real, isBigO_norm_left]
      simpa only [neg_one_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
    · simp_rw [neg_zero, Real.rpow_zero]
      refine isBigO_const_of_tendsto (?_ : Tendsto _ _
        (nhds (1 : ℂ))) one_ne_zero
      rw [(by simp : (1 : ℂ) = Real.exp (-0))]
      exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)).continuousWithinAt
  simpa only [MellinConvergent, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_log, Complex.ofReal_exp,
    Complex.ofReal_neg, mul_assoc] using hconv

/-- Sum of the two endpoint norm integrals dominating `Gamma'` in the
closed strip. -/
def gammaStripDerivativeMass : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ‖(x : ℂ) ^ ((1 / 4 : ℂ) - 1) *
        (Real.log x * Real.exp (-x))‖ +
      ‖(x : ℂ) ^ ((3 / 4 : ℂ) - 1) *
        (Real.log x * Real.exp (-x))‖

/-- Sum of the two endpoint norm integrals dominating `Gamma` in the
closed strip. -/
def gammaStripMass : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ‖(Real.exp (-x) : ℂ) *
        (x : ℂ) ^ ((1 / 4 : ℂ) - 1)‖ +
      ‖(Real.exp (-x) : ℂ) *
        (x : ℂ) ^ ((3 / 4 : ℂ) - 1)‖

lemma gammaStripDerivativeMass_nonneg :
    0 ≤ gammaStripDerivativeMass := by
  exact integral_nonneg fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma gammaStripMass_nonneg :
    0 ≤ gammaStripMass := by
  exact integral_nonneg fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma norm_cpow_strip_le_endpoint_sum
    {s : ℂ} {x : ℝ} (hx : 0 < x)
    (hlo : 1 / 4 ≤ s.re) (hhi : s.re ≤ 3 / 4) :
    ‖(x : ℂ) ^ (s - 1)‖ ≤
      ‖(x : ℂ) ^ ((1 / 4 : ℂ) - 1)‖ +
        ‖(x : ℂ) ^ ((3 / 4 : ℂ) - 1)‖ := by
  simp_rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rw [show (s - 1).re = s.re - 1 by simp,
    show (((1 / 4 : ℂ) - 1).re) = (1 / 4 : ℝ) - 1 by
      norm_num [Complex.div_re],
    show (((3 / 4 : ℂ) - 1).re) = (3 / 4 : ℝ) - 1 by
      norm_num [Complex.div_re]]
  by_cases hxone : x ≤ 1
  · calc
      x ^ (s.re - 1) ≤ x ^ ((1 / 4 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx hxone (by linarith)
      _ ≤ x ^ ((1 / 4 : ℝ) - 1) + x ^ ((3 / 4 : ℝ) - 1) :=
        le_add_of_nonneg_right (Real.rpow_nonneg hx.le _)
  · have hone : 1 ≤ x := le_of_not_ge hxone
    calc
      x ^ (s.re - 1) ≤ x ^ ((3 / 4 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ ≤ x ^ ((1 / 4 : ℝ) - 1) + x ^ ((3 / 4 : ℝ) - 1) :=
        le_add_of_nonneg_left (Real.rpow_nonneg hx.le _)

/-- The differentiated Euler integral is uniformly bounded throughout the
closed strip by the sum of its two endpoint norm integrals. -/
theorem norm_deriv_Gamma_strip_le
    {s : ℂ} (hlo : 1 / 4 ≤ s.re) (hhi : s.re ≤ 3 / 4) :
    ‖deriv Complex.Gamma s‖ ≤ gammaStripDerivativeMass := by
  have hs : 0 < s.re := lt_of_lt_of_le (by norm_num) hlo
  have hquarter : 0 < ((1 / 4 : ℂ)).re := by norm_num [Complex.div_re]
  have hthreequarter : 0 < ((3 / 4 : ℂ)).re := by
    norm_num [Complex.div_re]
  have hsInt := integrableOn_Gamma_derivative_integrand hs
  have hquarterInt :=
    integrableOn_Gamma_derivative_integrand hquarter
  have hthreequarterInt :=
    integrableOn_Gamma_derivative_integrand hthreequarter
  rw [deriv_Gamma_eq_integral_of_re_pos hs]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))‖ ≤
        ∫ x : ℝ in Ioi 0,
          ‖(x : ℂ) ^ (s - 1) *
            (Real.log x * Real.exp (-x))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ ((1 / 4 : ℂ) - 1) *
            (Real.log x * Real.exp (-x))‖ +
          ‖(x : ℂ) ^ ((3 / 4 : ℂ) - 1) *
            (Real.log x * Real.exp (-x))‖ := by
      refine setIntegral_mono_on hsInt.norm
        (hquarterInt.norm.add hthreequarterInt.norm)
        measurableSet_Ioi ?_
      intro x hx
      simp only [norm_mul]
      have h := mul_le_mul_of_nonneg_right
        (norm_cpow_strip_le_endpoint_sum hx hlo hhi)
        (norm_nonneg ((Real.log x * Real.exp (-x) : ℂ)))
      simpa only [norm_mul, add_mul] using h
    _ = gammaStripDerivativeMass := rfl

/-- Euler's Gamma integral is uniformly bounded throughout the same closed
strip by the sum of its two endpoint norm integrals. -/
theorem norm_Gamma_strip_le
    {s : ℂ} (hlo : 1 / 4 ≤ s.re) (hhi : s.re ≤ 3 / 4) :
    ‖Complex.Gamma s‖ ≤ gammaStripMass := by
  have hs : 0 < s.re := lt_of_lt_of_le (by norm_num) hlo
  have hquarter : 0 < ((1 / 4 : ℂ)).re := by norm_num [Complex.div_re]
  have hthreequarter : 0 < ((3 / 4 : ℂ)).re := by
    norm_num [Complex.div_re]
  have hsInt := Complex.GammaIntegral_convergent hs
  have hquarterInt := Complex.GammaIntegral_convergent hquarter
  have hthreequarterInt := Complex.GammaIntegral_convergent hthreequarter
  rw [Complex.Gamma_eq_integral hs]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x : ℝ in Ioi 0,
          ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 0,
        ‖(Real.exp (-x) : ℂ) *
            (x : ℂ) ^ ((1 / 4 : ℂ) - 1)‖ +
          ‖(Real.exp (-x) : ℂ) *
            (x : ℂ) ^ ((3 / 4 : ℂ) - 1)‖ := by
      refine setIntegral_mono_on hsInt.norm
        (hquarterInt.norm.add hthreequarterInt.norm)
        measurableSet_Ioi ?_
      intro x hx
      simp only [norm_mul]
      have h := mul_le_mul_of_nonneg_left
        (norm_cpow_strip_le_endpoint_sum hx hlo hhi)
        (norm_nonneg (Real.exp (-x) : ℂ))
      simpa only [norm_mul, mul_add] using h
    _ = gammaStripMass := rfl

/-- Euler reflection gives a uniform reciprocal-Gamma bound on the closed
strip.  The exponential dependence on the height is intentionally coarse;
it will be absorbed by the Gaussian contour kernel. -/
theorem norm_inv_Gamma_strip_le
    {s : ℂ} (hlo : 1 / 4 ≤ s.re) (hhi : s.re ≤ 3 / 4) :
    ‖(Complex.Gamma s)⁻¹‖ ≤ gammaStripMass / Real.pi *
      Real.exp (Real.pi * (|s.im| + 1)) := by
  have hs : 0 < s.re := lt_of_lt_of_le (by norm_num) hlo
  have h1s : 0 < (1 - s).re := by
    change 0 < 1 - s.re
    linarith
  have hGamma : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs
  have hGamma1 : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos h1s
  have href := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at href
    exact (mul_ne_zero hGamma hGamma1) href
  have href' :
      Complex.Gamma s * Complex.Gamma (1 - s) *
          Complex.sin ((Real.pi : ℂ) * s) = (Real.pi : ℂ) := by
    calc
      Complex.Gamma s * Complex.Gamma (1 - s) *
          Complex.sin ((Real.pi : ℂ) * s) =
          ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
            Complex.sin ((Real.pi : ℂ) * s) := by rw [href]
      _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hsin
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv :
      (Complex.Gamma s)⁻¹ =
        Complex.Gamma (1 - s) * Complex.sin ((Real.pi : ℂ) * s) /
          (Real.pi : ℂ) := by
    apply mul_left_cancel₀ hGamma
    rw [mul_inv_cancel₀ hGamma]
    calc
      1 = (Real.pi : ℂ) / (Real.pi : ℂ) := (div_self hpi).symm
      _ = (Complex.Gamma s * Complex.Gamma (1 - s) *
          Complex.sin ((Real.pi : ℂ) * s)) / (Real.pi : ℂ) := by
        rw [href']
      _ = Complex.Gamma s *
          (Complex.Gamma (1 - s) * Complex.sin ((Real.pi : ℂ) * s) /
            (Real.pi : ℂ)) := by ring
  have hOneSubLo : 1 / 4 ≤ (1 - s).re := by
    change 1 / 4 ≤ 1 - s.re
    linarith
  have hOneSubHi : (1 - s).re ≤ 3 / 4 := by
    change 1 - s.re ≤ 3 / 4
    linarith
  have hGammaNorm :
      ‖Complex.Gamma (1 - s)‖ ≤ gammaStripMass :=
    norm_Gamma_strip_le hOneSubLo hOneSubHi
  have hsReNonneg : 0 ≤ s.re := le_trans (by norm_num) hlo
  have hsNorm : ‖s‖ ≤ |s.im| + 1 := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| :=
        Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_nonneg hsReNonneg]
      _ ≤ |s.im| + 1 := by linarith
  have hpisNorm :
      ‖(Real.pi : ℂ) * s‖ ≤ Real.pi * (|s.im| + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hsNorm Real.pi_pos.le
  have hsinNorm :
      ‖Complex.sin ((Real.pi : ℂ) * s)‖ ≤
        Real.exp (Real.pi * (|s.im| + 1)) := by
    exact (norm_complex_sin_le_exp_norm _).trans
      (Real.exp_le_exp.mpr hpisNorm)
  rw [hinv, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    ‖Complex.Gamma (1 - s)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * s)‖ / Real.pi ≤
        gammaStripMass *
          Real.exp (Real.pi * (|s.im| + 1)) / Real.pi := by
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      exact mul_le_mul hGammaNorm hsinNorm (norm_nonneg _)
        gammaStripMass_nonneg
    _ = gammaStripMass / Real.pi *
        Real.exp (Real.pi * (|s.im| + 1)) := by ring

/-- A fixed nonnegative coefficient for the strip-wide exponential digamma
bound. -/
def stripDigammaExponentialConstant : ℝ :=
  gammaStripDerivativeMass * gammaStripMass / Real.pi

lemma stripDigammaExponentialConstant_nonneg :
    0 ≤ stripDigammaExponentialConstant := by
  exact div_nonneg
    (mul_nonneg gammaStripDerivativeMass_nonneg gammaStripMass_nonneg)
    Real.pi_pos.le

/-- Uniform exponential vertical growth for digamma throughout
`1 / 4 ≤ re s ≤ 3 / 4`. -/
theorem norm_digamma_strip_le
    {s : ℂ} (hlo : 1 / 4 ≤ s.re) (hhi : s.re ≤ 3 / 4) :
    ‖Complex.digamma s‖ ≤ stripDigammaExponentialConstant *
      Real.exp (Real.pi * (|s.im| + 1)) := by
  rw [Complex.digamma_def, logDeriv_apply, div_eq_mul_inv, norm_mul]
  calc
    ‖deriv Complex.Gamma s‖ * ‖(Complex.Gamma s)⁻¹‖ ≤
        gammaStripDerivativeMass *
          (gammaStripMass / Real.pi *
            Real.exp (Real.pi * (|s.im| + 1))) := by
      exact mul_le_mul
        (norm_deriv_Gamma_strip_le hlo hhi)
        (norm_inv_Gamma_strip_le hlo hhi)
        (norm_nonneg _) gammaStripDerivativeMass_nonneg
    _ = stripDigammaExponentialConstant *
        Real.exp (Real.pi * (|s.im| + 1)) := by
      unfold stripDigammaExponentialConstant
      ring

end

end RiemannGaussian
