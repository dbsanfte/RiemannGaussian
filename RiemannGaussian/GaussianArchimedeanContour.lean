import RiemannGaussian.GaussianExplicitContour
import RiemannGaussian.GaussianDigammaStripGrowth
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Critical-line Archimedean contour terms

This file evaluates the elementary completed-zeta terms on the critical
spectral line.  It is independent of the still-missing zero-divisor contour
shift: the rational pair cancels by oddness, the constant term gives the
certificate's `log pi` normalization, and conjugation symmetry of digamma
turns its full-line integral into the exact positive-half-line integral used
by `gaussianArchimedeanContribution`.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory Set

/-- A negative quadratic dominates every fixed linear exponential at
positive infinity. -/
lemma tendsto_exp_neg_quadratic_add_linear_atTop
    {ε : ℝ} (hε : 0 < ε) (a b c : ℝ) :
    Filter.Tendsto
      (fun T : ℝ => Real.exp (-ε * (T - a) ^ 2 + b * T + c))
      Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto
      (fun T : ℝ => T - (a + b / (2 * ε)))
      Filter.atTop Filter.atTop := by
    refine (Filter.tendsto_atTop_add_const_right Filter.atTop
      (-(a + b / (2 * ε))) Filter.tendsto_id).congr' ?_
    filter_upwards with T
    simp only [id_eq, sub_eq_add_neg]
  have hsquare : Filter.Tendsto
      (fun T : ℝ => (T - (a + b / (2 * ε))) ^ 2)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hshift
  have hquad : Filter.Tendsto
      (fun T : ℝ => -ε * (T - (a + b / (2 * ε))) ^ 2)
      Filter.atTop Filter.atBot :=
    hsquare.const_mul_atTop_of_neg (neg_lt_zero.mpr hε)
  have hadd : Filter.Tendsto
      (fun T : ℝ =>
        -ε * (T - (a + b / (2 * ε))) ^ 2 +
          (c + a * b + b ^ 2 / (4 * ε)))
      Filter.atTop Filter.atBot :=
    Filter.tendsto_atBot_add_const_right Filter.atTop
      (c + a * b + b ^ 2 / (4 * ε)) hquad
  refine (Real.tendsto_exp_atBot.comp hadd).congr' ?_
  filter_upwards with T
  apply congrArg Real.exp
  field_simp [hε.ne']
  ring

lemma integral_even_eq_two_mul_integral_Ioi
    {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x : ℝ, f x) = 2 * ∫ x : ℝ in Ioi 0, f x := by
  have hleft : (∫ x : ℝ in Iic 0, f x) =
      ∫ x : ℝ in Ioi 0, f x := by
    calc
      (∫ x : ℝ in Iic 0, f x) =
          ∫ x : ℝ in Iic 0, f (-x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        exact (heven x).symm
      _ = ∫ x : ℝ in Ioi 0, f x := by
        simpa using integral_comp_neg_Iic 0 f
  rw [← intervalIntegral.integral_Iic_add_Ioi
    hf.integrableOn hf.integrableOn, hleft]
  ring

lemma integral_odd_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsAddTorsionFree E]
    (f : ℝ → E) (hodd : ∀ x : ℝ, f (-x) = -f x) :
    (∫ x : ℝ, f x) = 0 := by
  have hreflect := integral_neg_eq_self f volume
  have hfun : (fun x : ℝ => f (-x)) = fun x : ℝ => -f x := by
    funext x
    exact hodd x
  rw [hfun, integral_neg] at hreflect
  exact self_eq_neg.mp hreflect.symm

lemma digamma_quarter_line_neg (r : ℝ) :
    Complex.digamma (1 / 4 + Complex.I * ((-r : ℝ) / 2)) =
      starRingEnd ℂ
        (Complex.digamma (1 / 4 + Complex.I * (r / 2))) := by
  calc
    Complex.digamma (1 / 4 + Complex.I * ((-r : ℝ) / 2)) =
        Complex.digamma
          (starRingEnd ℂ (1 / 4 + Complex.I * (r / 2))) := by
      congr 1
      push_cast
      simp only [map_add, map_mul, map_div₀, map_ofNat, map_one,
        Complex.conj_I, Complex.conj_ofReal]
      ring
    _ = starRingEnd ℂ
        (Complex.digamma (1 / 4 + Complex.I * (r / 2))) :=
      digamma_conj _

theorem integrable_translatedGaussian (hε : 0 < ε) (t : ℝ) :
    Integrable (translatedGaussian ε t) := by
  change Integrable (fun r : ℝ => Real.exp (-ε * (r - t) ^ 2))
  exact (integrable_exp_neg_mul_sq hε).comp_sub_right t

theorem integral_translatedGaussian
    (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ, translatedGaussian ε t r) =
      Real.sqrt (Real.pi / ε) := by
  calc
    (∫ r : ℝ, translatedGaussian ε t r) =
        ∫ r : ℝ, Real.exp (-ε * r ^ 2) := by
      simpa only [translatedGaussian] using
        integral_sub_right_eq_self
          (fun r : ℝ => Real.exp (-ε * r ^ 2)) t
    _ = Real.sqrt (Real.pi / ε) := integral_gaussian ε

theorem integrable_symmetricGaussian
    (hε : 0 < ε) (t : ℝ) :
    Integrable (symmetricGaussian ε t) := by
  unfold symmetricGaussian
  exact (integrable_translatedGaussian hε t).add
    ((integrable_translatedGaussian hε (-t)).congr
      (Filter.Eventually.of_forall fun r => by
        unfold translatedGaussian
        congr 1
        ring))

theorem integral_symmetricGaussian
    (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ, symmetricGaussian ε t r) =
      2 * Real.sqrt (Real.pi / ε) := by
  have hfirst := integrable_translatedGaussian hε t
  have hsecond : Integrable (fun r : ℝ => translatedGaussian ε t (-r)) := by
    simpa only [Function.comp_apply] using
      (integrable_translatedGaussian hε t).comp_neg
  unfold symmetricGaussian
  rw [integral_add hfirst hsecond, integral_translatedGaussian hε t]
  calc
    Real.sqrt (Real.pi / ε) +
        ∫ r : ℝ, translatedGaussian ε t (-r) =
      Real.sqrt (Real.pi / ε) +
        ∫ r : ℝ, translatedGaussian ε t r := by
      rw [integral_neg_eq_self]
    _ = 2 * Real.sqrt (Real.pi / ε) := by
      rw [integral_translatedGaussian hε t]
      ring

/-- The full critical-line digamma integral is real and is twice its
positive-half-line real part. -/
theorem integral_symmetricGaussian_mul_digamma_quarter
    { ε : ℝ } (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ,
      (symmetricGaussian ε t r : ℂ) *
        Complex.digamma (1 / 4 + Complex.I * (r / 2))) =
      ((2 * ∫ r : ℝ in Ioi 0,
        symmetricGaussian ε t r *
          (Complex.digamma
            (1 / 4 + Complex.I * (r / 2))).re : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun r =>
    (symmetricGaussian ε t r : ℂ) *
      Complex.digamma (1 / 4 + Complex.I * (r / 2))
  have hF : Integrable F := by
    simpa only [F] using
      integrable_symmetricGaussian_mul_digamma_quarter hε t
  have hrealEven : ∀ r : ℝ, (F (-r)).re = (F r).re := by
    intro r
    unfold F
    rw [symmetricGaussian_even, digamma_quarter_line_neg]
    simp
  have himagOdd : ∀ r : ℝ, (F (-r)).im = -(F r).im := by
    intro r
    unfold F
    rw [symmetricGaussian_even, digamma_quarter_line_neg]
    simp
  have hre : (∫ r : ℝ, (F r).re) =
      2 * ∫ r : ℝ in Ioi 0,
        symmetricGaussian ε t r *
          (Complex.digamma
            (1 / 4 + Complex.I * (r / 2))).re := by
    calc
      (∫ r : ℝ, (F r).re) =
          2 * ∫ r : ℝ in Ioi 0, (F r).re :=
        integral_even_eq_two_mul_integral_Ioi hF.re hrealEven
      _ = 2 * ∫ r : ℝ in Ioi 0,
          symmetricGaussian ε t r *
            (Complex.digamma
              (1 / 4 + Complex.I * (r / 2))).re := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        unfold F
        simp
  have him : (∫ r : ℝ, (F r).im) = 0 :=
    integral_odd_eq_zero (fun r => (F r).im) himagOdd
  change (∫ r : ℝ, F r) = _
  apply Complex.ext
  · calc
      (∫ r : ℝ, F r).re = ∫ r : ℝ, (F r).re :=
        (integral_re hF).symm
      _ = 2 * ∫ r : ℝ in Ioi 0,
          symmetricGaussian ε t r *
            (Complex.digamma
              (1 / 4 + Complex.I * (r / 2))).re := hre
      _ = (((2 * ∫ r : ℝ in Ioi 0,
          symmetricGaussian ε t r *
            (Complex.digamma
              (1 / 4 + Complex.I * (r / 2))).re : ℝ) : ℂ)).re := by simp
  · calc
      (∫ r : ℝ, F r).im = ∫ r : ℝ, (F r).im :=
        (integral_im hF).symm
      _ = 0 := him
      _ = (((2 * ∫ r : ℝ in Ioi 0,
          symmetricGaussian ε t r *
            (Complex.digamma
              (1 / 4 + Complex.I * (r / 2))).re : ℝ) : ℂ)).im := by simp

theorem integral_complexSymmetricGaussian_realLine
    (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ, complexSymmetricGaussian ε t (r : ℂ)) =
      (2 * Real.sqrt (Real.pi / ε) : ℝ) := by
  simp_rw [complexSymmetricGaussian_ofReal]
  rw [integral_complex_ofReal, integral_symmetricGaussian hε t]

/-- The constant logarithmic Gamma-factor term has exactly the normalization
appearing in the arithmetic explicit formula. -/
theorem integral_criticalLine_logPi_term
    (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ,
      complexSymmetricGaussian ε t (r : ℂ) *
        (-Complex.log Real.pi / 2)) =
      (-Real.log Real.pi * Real.sqrt (Real.pi / ε) : ℝ) := by
  rw [integral_mul_const, integral_complexSymmetricGaussian_realLine hε t,
    ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  ring

/-- The critical-line Gamma logarithmic derivative is exactly `pi` times
the certificate's half-line digamma contribution. -/
theorem integral_criticalLine_digamma_term
    { ε : ℝ } (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ,
      complexSymmetricGaussian ε t (r : ℂ) *
        (Complex.digamma
          (1 / 4 + Complex.I * (r / 2)) / 2)) =
      (Real.pi * gaussianDigammaIntegral ε t : ℝ) := by
  rw [show (fun r : ℝ =>
      complexSymmetricGaussian ε t (r : ℂ) *
        (Complex.digamma
          (1 / 4 + Complex.I * (r / 2)) / 2)) =
      fun r : ℝ =>
        ((symmetricGaussian ε t r : ℂ) *
          Complex.digamma
            (1 / 4 + Complex.I * (r / 2))) * (1 / 2 : ℂ) by
    funext r
    rw [complexSymmetricGaussian_ofReal]
    ring]
  rw [integral_mul_const,
    integral_symmetricGaussian_mul_digamma_quarter hε t]
  unfold gaussianDigammaIntegral
  rw [show (∫ r : ℝ in Ioi 0,
      symmetricGaussian ε t r * riemannArchimedeanDensity r) =
      ∫ r : ℝ in Ioi 0,
        symmetricGaussian ε t r *
          (Complex.digamma
            (1 / 4 + Complex.I * (r / 2))).re by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    unfold riemannArchimedeanDensity
    congr 2
    ]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp [hpi]

/-- The elementary rational pair on the critical line. -/
def criticalLineRationalPair (r : ℝ) : ℂ :=
  1 / (1 / 2 + Complex.I * (r : ℂ)) +
    1 / (1 / 2 + Complex.I * (r : ℂ) - 1)

lemma criticalLineRationalPair_neg (r : ℝ) :
    criticalLineRationalPair (-r) = -criticalLineRationalPair r := by
  unfold criticalLineRationalPair
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, one_div, Complex.inv_re]
    simp [Complex.normSq_apply]
    ring
  · simp only [Complex.add_im, Complex.neg_im, one_div, Complex.inv_im]
    simp [Complex.normSq_apply]
    ring

lemma criticalLineDenominator_ne_zero (r : ℝ) :
    (1 / 2 + Complex.I * (r : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

lemma criticalLineDenominator_sub_one_ne_zero (r : ℝ) :
    (1 / 2 + Complex.I * (r : ℂ) - 1) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem continuous_criticalLineRationalPair :
    Continuous criticalLineRationalPair := by
  unfold criticalLineRationalPair
  have h : Continuous
      ((fun r : ℝ => 1 / 2 + Complex.I * (r : ℂ))⁻¹ +
        (fun r : ℝ => 1 / 2 + Complex.I * (r : ℂ) - 1)⁻¹) :=
    ((by fun_prop : Continuous (fun r : ℝ =>
      1 / 2 + Complex.I * (r : ℂ))).inv₀ criticalLineDenominator_ne_zero).add
      ((by fun_prop : Continuous (fun r : ℝ =>
        1 / 2 + Complex.I * (r : ℂ) - 1)).inv₀
          criticalLineDenominator_sub_one_ne_zero)
  convert h using 1
  ext r
  simp only [one_div, Pi.add_apply, Pi.inv_apply]

lemma norm_inv_criticalLineDenominator_le_two (r : ℝ) :
    ‖(1 / 2 + Complex.I * (r : ℂ))⁻¹‖ ≤ 2 := by
  rw [norm_inv]
  have hnormPos : 0 < ‖1 / 2 + Complex.I * (r : ℂ)‖ :=
    norm_pos_iff.mpr (criticalLineDenominator_ne_zero r)
  have hre := Complex.abs_re_le_norm
    (1 / 2 + Complex.I * (r : ℂ))
  rw [inv_le_comm₀ hnormPos (by norm_num : (0 : ℝ) < 2)]
  norm_num at hre ⊢
  exact hre

lemma norm_inv_criticalLineDenominator_sub_one_le_two (r : ℝ) :
    ‖(1 / 2 + Complex.I * (r : ℂ) - 1)⁻¹‖ ≤ 2 := by
  rw [norm_inv]
  have hnormPos : 0 < ‖1 / 2 + Complex.I * (r : ℂ) - 1‖ :=
    norm_pos_iff.mpr (criticalLineDenominator_sub_one_ne_zero r)
  have hre := Complex.abs_re_le_norm
    (1 / 2 + Complex.I * (r : ℂ) - 1)
  rw [inv_le_comm₀ hnormPos (by norm_num : (0 : ℝ) < 2)]
  norm_num at hre ⊢
  exact hre

lemma norm_criticalLineRationalPair_le_four (r : ℝ) :
    ‖criticalLineRationalPair r‖ ≤ 4 := by
  unfold criticalLineRationalPair
  calc
    ‖1 / (1 / 2 + Complex.I * (r : ℂ)) +
        1 / (1 / 2 + Complex.I * (r : ℂ) - 1)‖ ≤
      ‖1 / (1 / 2 + Complex.I * (r : ℂ))‖ +
        ‖1 / (1 / 2 + Complex.I * (r : ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ 2 + 2 := add_le_add
      (by simpa only [one_div] using
        norm_inv_criticalLineDenominator_le_two r)
      (by simpa only [one_div] using
        norm_inv_criticalLineDenominator_sub_one_le_two r)
    _ = 4 := by norm_num

theorem integrable_symmetricGaussian_mul_criticalLineRationalPair
    { ε : ℝ } (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) * criticalLineRationalPair r) := by
  have hmajor := (integrable_symmetricGaussian hε t).const_mul 4
  refine hmajor.mono' ?_ ?_
  · have hsymReal : Continuous (fun r : ℝ => symmetricGaussian ε t r) := by
      unfold symmetricGaussian translatedGaussian
      fun_prop
    have hsymComplex : Continuous (fun r : ℝ =>
        (symmetricGaussian ε t r : ℂ)) :=
      Complex.continuous_ofReal.comp hsymReal
    exact (hsymComplex.mul
      continuous_criticalLineRationalPair).aestronglyMeasurable
  · filter_upwards with r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (symmetricGaussian_pos ε t r)]
    calc
      symmetricGaussian ε t r * ‖criticalLineRationalPair r‖ ≤
          symmetricGaussian ε t r * 4 :=
        mul_le_mul_of_nonneg_left
          (norm_criticalLineRationalPair_le_four r)
          (symmetricGaussian_pos ε t r).le
      _ = 4 * symmetricGaussian ε t r := by ring

/-- The rational pair has zero critical-line Gaussian integral. -/
theorem integral_criticalLine_rationalPair_zero (ε t : ℝ) :
    (∫ r : ℝ,
      (symmetricGaussian ε t r : ℂ) *
        criticalLineRationalPair r) = 0 := by
  apply integral_odd_eq_zero
  intro r
  rw [symmetricGaussian_even, criticalLineRationalPair_neg]
  ring

/-- The full elementary part of the completed logarithmic derivative on the
critical line.  This is the exact sum of the rational, logarithmic, and
Gamma-factor contributions; no contour-shift assumption enters here. -/
theorem integral_criticalLine_completedElementary_terms
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ,
      complexSymmetricGaussian ε t (r : ℂ) *
        (criticalLineRationalPair r - Complex.log Real.pi / 2 +
          Complex.digamma
            (1 / 4 + Complex.I * (r / 2)) / 2)) =
      ((-Real.log Real.pi * Real.sqrt (Real.pi / ε) +
        Real.pi * gaussianDigammaIntegral ε t : ℝ) : ℂ) := by
  have hr : Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) * criticalLineRationalPair r) :=
    integrable_symmetricGaussian_mul_criticalLineRationalPair hε t
  have hsymComplex : Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (integrable_symmetricGaussian hε t)
  have hlog : Integrable (fun r : ℝ =>
      complexSymmetricGaussian ε t (r : ℂ) *
        (-Complex.log Real.pi / 2)) := by
    simpa only [complexSymmetricGaussian_ofReal] using
      hsymComplex.mul_const (-Complex.log Real.pi / 2)
  have hdigamma : Integrable (fun r : ℝ =>
      complexSymmetricGaussian ε t (r : ℂ) *
        (Complex.digamma
          (1 / 4 + Complex.I * (r / 2)) / 2)) := by
    simpa only [complexSymmetricGaussian_ofReal, div_eq_mul_inv, mul_assoc]
      using (integrable_symmetricGaussian_mul_digamma_quarter hε t).mul_const
        (2 : ℂ)⁻¹
  have hrlog : Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) * criticalLineRationalPair r +
        complexSymmetricGaussian ε t (r : ℂ) *
          (-Complex.log Real.pi / 2)) := by
    refine (hr.add hlog).congr ?_
    filter_upwards with r
    rfl
  rw [show (fun r : ℝ =>
      complexSymmetricGaussian ε t (r : ℂ) *
        (criticalLineRationalPair r - Complex.log Real.pi / 2 +
          Complex.digamma
            (1 / 4 + Complex.I * (r / 2)) / 2)) =
      fun r : ℝ =>
        ((symmetricGaussian ε t r : ℂ) * criticalLineRationalPair r +
          complexSymmetricGaussian ε t (r : ℂ) *
            (-Complex.log Real.pi / 2)) +
          complexSymmetricGaussian ε t (r : ℂ) *
            (Complex.digamma
              (1 / 4 + Complex.I * (r / 2)) / 2) by
    funext r
    rw [complexSymmetricGaussian_ofReal]
    ring]
  rw [integral_add hrlog hdigamma, integral_add hr hlog,
    integral_criticalLine_rationalPair_zero,
    integral_criticalLine_logPi_term hε,
    integral_criticalLine_digamma_term hε]
  push_cast
  ring

lemma gaussianArchimedean_criticalLine_normalization
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    -Real.log Real.pi * Real.sqrt (Real.pi / ε) +
        Real.pi * gaussianDigammaIntegral ε t =
      Real.pi *
        (gaussianArchimedeanContribution ε t -
          4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)) := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hsqrtε : Real.sqrt ε ≠ 0 :=
    (Real.sqrt_pos.2 hε).ne'
  have hsqrtPiSq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt hpi
  have hsqrt : Real.sqrt (Real.pi / ε) =
      Real.pi / Real.sqrt (Real.pi * ε) := by
    rw [Real.sqrt_div hpi, Real.sqrt_mul hpi]
    field_simp [hsqrtPi, hsqrtε]
    rw [hsqrtPiSq]
  rw [hsqrt]
  unfold gaussianArchimedeanContribution
  ring

/-- Repackaging the checked critical-line calculation in the exact
Archimedean normalization used by the arithmetic explicit formula.  The
subtracted exponential/cosine term is the boundary residue still to be
supplied by the safe-line-to-critical-line contour shift. -/
theorem integral_criticalLine_completedElementary_terms_eq_archimedean
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r : ℝ,
      complexSymmetricGaussian ε t (r : ℂ) *
        (criticalLineRationalPair r - Complex.log Real.pi / 2 +
          Complex.digamma
            (1 / 4 + Complex.I * (r / 2)) / 2)) =
      ((Real.pi *
        (gaussianArchimedeanContribution ε t -
          4 * Real.exp (ε / 4 - ε * t ^ 2) *
            Real.cos (ε * t)) : ℝ) : ℂ) := by
  rw [integral_criticalLine_completedElementary_terms hε t]
  exact_mod_cast gaussianArchimedean_criticalLine_normalization hε t

/-! ## Spectral-coordinate pole isolation -/

/-- The completed-zeta variable as a function of the spectral coordinate.
The real spectral axis is the critical line. -/
def completedSpectralCoordinate (z : ℂ) : ℂ :=
  1 / 2 + Complex.I * z

/-- The only elementary pole crossed from `im z = -1` to `im z = 0`. -/
def archimedeanPolePoint : ℂ := -Complex.I / 2

lemma completedSpectralCoordinate_sub_one (z : ℂ) :
    completedSpectralCoordinate z - 1 =
      Complex.I * (z - archimedeanPolePoint) := by
  unfold completedSpectralCoordinate archimedeanPolePoint
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ac_rfl

@[simp]
lemma completedSpectralCoordinate_archimedeanPolePoint :
    completedSpectralCoordinate archimedeanPolePoint = 1 := by
  unfold completedSpectralCoordinate archimedeanPolePoint
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The pole weight is exactly the boundary term occurring in the
certificate normalization. -/
theorem complexSymmetricGaussian_archimedeanPolePoint (ε t : ℝ) :
    complexSymmetricGaussian ε t archimedeanPolePoint =
      (2 * Real.exp (ε / 4 - ε * t ^ 2) *
        Real.cos (ε * t) : ℝ) := by
  unfold archimedeanPolePoint complexSymmetricGaussian
  rw [complexTranslatedGaussian_neg_center]
  calc
    complexTranslatedGaussian ε t (-Complex.I / 2) +
        complexTranslatedGaussian ε t (-(-Complex.I / 2)) =
      complexTranslatedGaussian ε t
          (((0 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) +
        complexTranslatedGaussian ε t
          (((0 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [add_comm]
      congr 1 <;> push_cast <;> ring
    _ = (2 * Real.exp (ε * (1 / 2 : ℝ) ^ 2 - ε * (0 - t) ^ 2) *
        Real.cos (2 * ε * (1 / 2 : ℝ) * (0 - t)) : ℝ) :=
      complexTranslatedGaussian_conjugate_pair ε t 0 (1 / 2)
    _ = (2 * Real.exp (ε / 4 - ε * t ^ 2) *
        Real.cos (ε * t) : ℝ) := by
      norm_cast
      rw [show 2 * ε * (1 / 2 : ℝ) * (0 - t) = -(ε * t) by ring,
        Real.cos_neg]
      congr 2 <;> ring

/-- The part of the elementary completed-zeta logarithmic derivative that
is regular at `s = 1`. -/
def archimedeanSpectralRegularTerms (z : ℂ) : ℂ :=
  1 / completedSpectralCoordinate z - Complex.log Real.pi / 2 +
    Complex.digamma (completedSpectralCoordinate z / 2) / 2

/-- All elementary completed-zeta terms, including the simple pole at
`s = 1`. -/
def archimedeanSpectralTerms (z : ℂ) : ℂ :=
  1 / completedSpectralCoordinate z +
    1 / (completedSpectralCoordinate z - 1) -
      Complex.log Real.pi / 2 +
        Complex.digamma (completedSpectralCoordinate z / 2) / 2

lemma archimedeanSpectralTerms_eq_regular_add_pole (z : ℂ) :
    archimedeanSpectralTerms z =
      archimedeanSpectralRegularTerms z +
        1 / (completedSpectralCoordinate z - 1) := by
  unfold archimedeanSpectralTerms archimedeanSpectralRegularTerms
  ring

/-- Spectral points for which the associated completed-zeta variable has
positive real part. -/
def spectralPositiveHalfPlane : Set ℂ :=
  {z : ℂ | z.im < 1 / 2}

lemma completedSpectralCoordinate_re (z : ℂ) :
    (completedSpectralCoordinate z).re = 1 / 2 - z.im := by
  unfold completedSpectralCoordinate
  simp
  ring

theorem isOpen_spectralPositiveHalfPlane :
    IsOpen spectralPositiveHalfPlane := by
  exact (isOpen_lt Complex.continuous_im continuous_const)

theorem differentiableOn_archimedeanSpectralRegularTerms :
    DifferentiableOn ℂ archimedeanSpectralRegularTerms
      spectralPositiveHalfPlane := by
  intro z hz
  have hspos : 0 < (completedSpectralCoordinate z).re := by
    rw [completedSpectralCoordinate_re]
    exact sub_pos.mpr hz
  have hsne : completedSpectralCoordinate z ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp only [Complex.zero_re] at this
    linarith
  have hsDiff : DifferentiableAt ℂ completedSpectralCoordinate z := by
    unfold completedSpectralCoordinate
    fun_prop
  have hdigamma : DifferentiableAt ℂ Complex.digamma
      (completedSpectralCoordinate z / 2) :=
    (analyticOnNhd_digamma_re_pos
      (completedSpectralCoordinate z / 2) (by
        have hhalfRe : (completedSpectralCoordinate z / 2).re =
            (completedSpectralCoordinate z).re / 2 := by
          rw [Complex.div_re]
          norm_num
          ring
        change 0 < (completedSpectralCoordinate z / 2).re
        rw [hhalfRe]
        exact div_pos hspos (by norm_num))).differentiableAt
  have hinv : DifferentiableAt ℂ
      (fun w => 1 / completedSpectralCoordinate w) z := by
    simpa only [one_div] using hsDiff.fun_inv hsne
  have hlog : DifferentiableAt ℂ
      (fun _ : ℂ => Complex.log Real.pi / 2) z := by
    fun_prop
  have hdigammaComp : DifferentiableAt ℂ
      (fun w => Complex.digamma (completedSpectralCoordinate w / 2) / 2) z :=
    (hdigamma.comp z (hsDiff.div_const 2)).div_const 2
  unfold archimedeanSpectralRegularTerms
  exact ((hinv.sub hlog).add hdigammaComp).differentiableWithinAt

/-- Removing the `s = 1` principal part with the analytic divided slope
produces a holomorphic integrand throughout the contour-shift strip. -/
def archimedeanRegularizedIntegrand (ε t : ℝ) (z : ℂ) : ℂ :=
  complexSymmetricGaussian ε t z * archimedeanSpectralRegularTerms z -
    Complex.I *
      dslope (complexSymmetricGaussian ε t) archimedeanPolePoint z

/-- Explicit principal part of the crossed `s = 1` pole in spectral
coordinates. -/
def archimedeanPrincipalPart (ε t : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * complexSymmetricGaussian ε t archimedeanPolePoint /
    (z - archimedeanPolePoint)

theorem differentiableOn_archimedeanRegularizedIntegrand (ε t : ℝ) :
    DifferentiableOn ℂ (archimedeanRegularizedIntegrand ε t)
      spectralPositiveHalfPlane := by
  have hGaussian : DifferentiableOn ℂ
      (complexSymmetricGaussian ε t) Set.univ := by
    intro z hz
    unfold complexSymmetricGaussian complexTranslatedGaussian
    fun_prop
  have hSlope : DifferentiableOn ℂ
      (dslope (complexSymmetricGaussian ε t) archimedeanPolePoint)
      Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).2 hGaussian
  unfold archimedeanRegularizedIntegrand
  exact (hGaussian.mono (Set.subset_univ _)).mul
      differentiableOn_archimedeanSpectralRegularTerms |>.sub
    ((differentiableOn_const (c := Complex.I)).mul
      (hSlope.mono (Set.subset_univ _)))

/-- Away from the crossed pole, the original elementary integrand is the
holomorphic regularization plus its explicit principal part. -/
theorem archimedeanSpectralIntegrand_eq_regularized_sub_principal
    (ε t : ℝ) {z : ℂ} (hz : z ≠ archimedeanPolePoint) :
    complexSymmetricGaussian ε t z * archimedeanSpectralTerms z =
      archimedeanRegularizedIntegrand ε t z +
        archimedeanPrincipalPart ε t z := by
  rw [archimedeanSpectralTerms_eq_regular_add_pole,
    completedSpectralCoordinate_sub_one]
  unfold archimedeanRegularizedIntegrand archimedeanPrincipalPart
  rw [dslope_of_ne _ hz, slope_def_field]
  have hsub : z - archimedeanPolePoint ≠ 0 := sub_ne_zero.mpr hz
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp [hsub, hI]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Uniform bounds on the finite vertical sides -/

/-- A real Gaussian envelope which dominates the symmetric entire kernel
on both vertical sides of the contour strip. -/
def archimedeanVerticalGaussianBound (ε t T : ℝ) : ℝ :=
  Real.exp (ε - ε * (T - t) ^ 2) +
    Real.exp (ε - ε * (T + t) ^ 2)

lemma norm_complexSymmetricGaussian_horizontal_strip_le
    {ε : ℝ} (hε : 0 < ε) (t x y : ℝ)
    (hylo : -1 ≤ y) (hyhi : y ≤ 0) :
    ‖complexSymmetricGaussian ε t
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp (ε - ε * (x - t) ^ 2) +
        Real.exp (ε - ε * (x + t) ^ 2) := by
  have hysq : y ^ 2 ≤ 1 := by nlinarith
  unfold complexSymmetricGaussian
  calc
    ‖complexTranslatedGaussian ε t
          ((x : ℂ) + (y : ℂ) * Complex.I) +
        complexTranslatedGaussian ε (-t)
          ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        ‖complexTranslatedGaussian ε t
          ((x : ℂ) + (y : ℂ) * Complex.I)‖ +
        ‖complexTranslatedGaussian ε (-t)
          ((x : ℂ) + (y : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = Real.exp (ε * y ^ 2 - ε * (x - t) ^ 2) +
        Real.exp (ε * y ^ 2 - ε * (x + t) ^ 2) := by
      rw [norm_complexTranslatedGaussian,
        norm_complexTranslatedGaussian]
      congr 1 <;> simp <;> ring
    _ ≤ Real.exp (ε - ε * (x - t) ^ 2) +
        Real.exp (ε - ε * (x + t) ^ 2) := by
      gcongr <;>
        simpa using mul_le_mul_of_nonneg_left hysq hε.le

lemma norm_complexSymmetricGaussian_right_vertical_le
    {ε : ℝ} (hε : 0 < ε) (t T y : ℝ)
    (hylo : -1 ≤ y) (hyhi : y ≤ 0) :
    ‖complexSymmetricGaussian ε t
        ((T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      archimedeanVerticalGaussianBound ε t T := by
  exact norm_complexSymmetricGaussian_horizontal_strip_le
    hε t T y hylo hyhi

lemma norm_complexSymmetricGaussian_left_vertical_le
    {ε : ℝ} (hε : 0 < ε) (t T y : ℝ)
    (hylo : -1 ≤ y) (hyhi : y ≤ 0) :
    ‖complexSymmetricGaussian ε t
        ((-T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      archimedeanVerticalGaussianBound ε t T := by
  have h := norm_complexSymmetricGaussian_horizontal_strip_le
    hε t (-T) y hylo hyhi
  calc
    ‖complexSymmetricGaussian ε t
        ((-T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp (ε - ε * (-T - t) ^ 2) +
        Real.exp (ε - ε * (-T + t) ^ 2) := by
      simpa only [Complex.ofReal_neg] using h
    _ = archimedeanVerticalGaussianBound ε t T := by
      unfold archimedeanVerticalGaussianBound
      rw [show (-T - t) ^ 2 = (T + t) ^ 2 by ring,
        show (-T + t) ^ 2 = (T - t) ^ 2 by ring,
        add_comm]

/-- Height-independent elementary terms plus the deliberately coarse
strip-wide digamma majorant. -/
def archimedeanVerticalTermsBound (T : ℝ) : ℝ :=
  3 + ‖Complex.log Real.pi‖ +
    stripDigammaExponentialConstant *
      Real.exp (Real.pi * (T + 1))

lemma completedSpectralCoordinate_horizontal_re (x y : ℝ) :
    (completedSpectralCoordinate
      ((x : ℂ) + (y : ℂ) * Complex.I)).re = 1 / 2 - y := by
  simp [completedSpectralCoordinate]
  ring

lemma completedSpectralCoordinate_horizontal_im (x y : ℝ) :
    (completedSpectralCoordinate
      ((x : ℂ) + (y : ℂ) * Complex.I)).im = x := by
  simp [completedSpectralCoordinate]

/-- Uniform bound for all completed elementary terms on either vertical
side.  The hypothesis `|x| = T` packages the right and left sides together. -/
lemma norm_archimedeanSpectralTerms_vertical_le
    (x y T : ℝ) (hx : |x| = T) (hT : 1 ≤ T)
    (hylo : -1 ≤ y) (hyhi : y ≤ 0) :
    ‖archimedeanSpectralTerms
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      archimedeanVerticalTermsBound T := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let s : ℂ := completedSpectralCoordinate z
  let w : ℂ := s / 2
  have hsre : s.re = 1 / 2 - y := by
    exact completedSpectralCoordinate_horizontal_re x y
  have hsim : s.im = x := by
    exact completedSpectralCoordinate_horizontal_im x y
  have hwre : w.re = 1 / 4 - y / 2 := by
    unfold w
    rw [Complex.div_re]
    norm_num
    rw [hsre]
    ring
  have hwim : w.im = x / 2 := by
    unfold w
    rw [Complex.div_im]
    norm_num
    rw [hsim]
    ring
  have hsReHalf : 1 / 2 ≤ s.re := by rw [hsre]; linarith
  have hsne : s ≠ 0 := by
    intro hszero
    have hre := congrArg Complex.re hszero
    simp only [Complex.zero_re] at hre
    linarith
  have hInvS : ‖1 / s‖ ≤ 2 := by
    rw [one_div, norm_inv]
    have hsNormPos : 0 < ‖s‖ := norm_pos_iff.mpr hsne
    rw [inv_le_comm₀ hsNormPos (by norm_num : (0 : ℝ) < 2)]
    have hre := Complex.abs_re_le_norm s
    rw [abs_of_nonneg (le_trans (by norm_num) hsReHalf)] at hre
    nlinarith
  have hInvSub : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [one_div, norm_inv]
    apply inv_le_one_of_one_le₀
    calc
      1 ≤ T := hT
      _ = |x| := hx.symm
      _ = |(s - 1).im| := by
        congr 1
        change x = s.im - 0
        rw [hsim, sub_zero]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have hwlo : 1 / 4 ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 / 4 := by rw [hwre]; linarith
  have hwimAbs : |w.im| ≤ T := by
    rw [hwim, abs_div, hx]
    norm_num
    nlinarith
  have hDigamma : ‖Complex.digamma w‖ ≤
      stripDigammaExponentialConstant *
        Real.exp (Real.pi * (T + 1)) := by
    calc
      ‖Complex.digamma w‖ ≤ stripDigammaExponentialConstant *
          Real.exp (Real.pi * (|w.im| + 1)) :=
        norm_digamma_strip_le hwlo hwhi
      _ ≤ stripDigammaExponentialConstant *
          Real.exp (Real.pi * (T + 1)) := by
        apply mul_le_mul_of_nonneg_left _
          stripDigammaExponentialConstant_nonneg
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hLogHalf : ‖Complex.log Real.pi / 2‖ ≤
      ‖Complex.log Real.pi‖ := by
    rw [norm_div]
    norm_num
  have hDigammaHalf : ‖Complex.digamma w / 2‖ ≤
      stripDigammaExponentialConstant *
        Real.exp (Real.pi * (T + 1)) := by
    calc
      ‖Complex.digamma w / 2‖ ≤ ‖Complex.digamma w‖ := by
        rw [norm_div]
        norm_num
      _ ≤ _ := hDigamma
  change ‖1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
      Complex.digamma w / 2‖ ≤ _
  calc
    ‖1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma w / 2‖ ≤
      ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma w / 2‖ := by
      calc
        ‖1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
            Complex.digamma w / 2‖ ≤
          ‖1 / s + 1 / (s - 1) - Complex.log Real.pi / 2‖ +
            ‖Complex.digamma w / 2‖ := norm_add_le _ _
        _ ≤ (‖1 / s + 1 / (s - 1)‖ +
              ‖Complex.log Real.pi / 2‖) +
            ‖Complex.digamma w / 2‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ (‖1 / s‖ + ‖1 / (s - 1)‖ +
              ‖Complex.log Real.pi / 2‖) +
            ‖Complex.digamma w / 2‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by ring
    _ ≤ 2 + 1 + ‖Complex.log Real.pi‖ +
        stripDigammaExponentialConstant *
          Real.exp (Real.pi * (T + 1)) := by
      gcongr
    _ = archimedeanVerticalTermsBound T := by
      unfold archimedeanVerticalTermsBound
      ring

/-- A scalar majorant for either vertical side of the pole-removed
integrand. -/
def archimedeanVerticalMajorant (ε t T : ℝ) : ℝ :=
  archimedeanVerticalGaussianBound ε t T *
      archimedeanVerticalTermsBound T +
    ‖complexSymmetricGaussian ε t archimedeanPolePoint‖ / T

lemma archimedeanVerticalGaussianBound_nonneg (ε t T : ℝ) :
    0 ≤ archimedeanVerticalGaussianBound ε t T := by
  unfold archimedeanVerticalGaussianBound
  positivity

lemma archimedeanVerticalTermsBound_nonneg (T : ℝ) :
    0 ≤ archimedeanVerticalTermsBound T := by
  unfold archimedeanVerticalTermsBound
  exact add_nonneg
    (add_nonneg (by norm_num) (norm_nonneg _))
    (mul_nonneg stripDigammaExponentialConstant_nonneg
      (Real.exp_pos _).le)

lemma norm_archimedeanPrincipalPart_vertical_le
    (ε t x y T : ℝ) (hx : |x| = T) (hT : 0 < T) :
    ‖archimedeanPrincipalPart ε t
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ‖complexSymmetricGaussian ε t archimedeanPolePoint‖ / T := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hdenom : T ≤ ‖z - archimedeanPolePoint‖ := by
    calc
      T = |x| := hx.symm
      _ = |(z - archimedeanPolePoint).re| := by
        congr 1
        unfold z archimedeanPolePoint
        simp
      _ ≤ ‖z - archimedeanPolePoint‖ :=
        Complex.abs_re_le_norm (z - archimedeanPolePoint)
  unfold archimedeanPrincipalPart
  rw [norm_div, norm_mul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hT hdenom

/-- Both finite vertical sides are bounded pointwise by one scalar
majorant, uniformly for `-1 ≤ y ≤ 0`. -/
lemma norm_archimedeanRegularizedIntegrand_vertical_le
    {ε : ℝ} (hε : 0 < ε) (t x y T : ℝ)
    (hx : |x| = T) (hT : 1 ≤ T)
    (hylo : -1 ≤ y) (hyhi : y ≤ 0) :
    ‖archimedeanRegularizedIntegrand ε t
        ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      archimedeanVerticalMajorant ε t T := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hxne : x ≠ 0 := by
    intro hxzero
    rw [hxzero, abs_zero] at hx
    linarith
  have hzPole : z ≠ archimedeanPolePoint := by
    intro hz
    have hre := congrArg Complex.re hz
    unfold z archimedeanPolePoint at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, Complex.neg_re, Complex.div_re] at hre
    norm_num at hre
    exact hxne hre
  have hdecomp :=
    archimedeanSpectralIntegrand_eq_regularized_sub_principal
      ε t hzPole
  have hreg : archimedeanRegularizedIntegrand ε t z =
      complexSymmetricGaussian ε t z * archimedeanSpectralTerms z -
        archimedeanPrincipalPart ε t z := by
    calc
      archimedeanRegularizedIntegrand ε t z =
          (archimedeanRegularizedIntegrand ε t z +
            archimedeanPrincipalPart ε t z) -
              archimedeanPrincipalPart ε t z := by ring
      _ = complexSymmetricGaussian ε t z * archimedeanSpectralTerms z -
          archimedeanPrincipalPart ε t z := by rw [← hdecomp]
  rw [hreg]
  calc
    ‖complexSymmetricGaussian ε t z * archimedeanSpectralTerms z -
        archimedeanPrincipalPart ε t z‖ ≤
      ‖complexSymmetricGaussian ε t z * archimedeanSpectralTerms z‖ +
        ‖archimedeanPrincipalPart ε t z‖ := norm_sub_le _ _
    _ ≤ archimedeanVerticalGaussianBound ε t T *
          archimedeanVerticalTermsBound T +
        ‖complexSymmetricGaussian ε t archimedeanPolePoint‖ / T := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul
          (by
            unfold z
            by_cases hxnonneg : 0 ≤ x
            · have hxeq : x = T := by
                rw [abs_of_nonneg hxnonneg] at hx
                exact hx
              subst x
              exact norm_complexSymmetricGaussian_right_vertical_le
                hε t T y hylo hyhi
            · have hxneg : x < 0 := lt_of_not_ge hxnonneg
              have hxeq : x = -T := by
                rw [abs_of_neg hxneg] at hx
                linarith
              subst x
              simpa only [Complex.ofReal_neg] using
                (norm_complexSymmetricGaussian_left_vertical_le
                  hε t T y hylo hyhi))
          (norm_archimedeanSpectralTerms_vertical_le
            x y T hx hT hylo hyhi)
          (norm_nonneg _) (archimedeanVerticalGaussianBound_nonneg _ _ _)
      · exact norm_archimedeanPrincipalPart_vertical_le
          ε t x y T hx (lt_of_lt_of_le zero_lt_one hT)
    _ = archimedeanVerticalMajorant ε t T := rfl

/-- The common vertical-side majorant vanishes at infinite height. -/
theorem tendsto_archimedeanVerticalMajorant
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Filter.Tendsto (archimedeanVerticalMajorant ε t)
      Filter.atTop (nhds 0) := by
  let E₁ : ℝ → ℝ := fun T => Real.exp (ε - ε * (T - t) ^ 2)
  let E₂ : ℝ → ℝ := fun T => Real.exp (ε - ε * (T + t) ^ 2)
  let L : ℝ → ℝ := fun T => Real.exp (Real.pi * (T + 1))
  let C : ℝ := 3 + ‖Complex.log Real.pi‖
  let D : ℝ := stripDigammaExponentialConstant
  let A : ℝ := ‖complexSymmetricGaussian ε t archimedeanPolePoint‖
  have hE₁ : Filter.Tendsto E₁ Filter.atTop (nhds 0) := by
    refine (tendsto_exp_neg_quadratic_add_linear_atTop
      hε t 0 ε).congr' ?_
    filter_upwards with T
    unfold E₁
    apply congrArg Real.exp
    ring
  have hE₂ : Filter.Tendsto E₂ Filter.atTop (nhds 0) := by
    refine (tendsto_exp_neg_quadratic_add_linear_atTop
      hε (-t) 0 ε).congr' ?_
    filter_upwards with T
    unfold E₂
    apply congrArg Real.exp
    ring
  have hE₁L : Filter.Tendsto (fun T => E₁ T * L T)
      Filter.atTop (nhds 0) := by
    refine (tendsto_exp_neg_quadratic_add_linear_atTop
      hε t Real.pi (ε + Real.pi)).congr' ?_
    filter_upwards with T
    unfold E₁ L
    rw [← Real.exp_add]
    apply congrArg Real.exp
    ring
  have hE₂L : Filter.Tendsto (fun T => E₂ T * L T)
      Filter.atTop (nhds 0) := by
    refine (tendsto_exp_neg_quadratic_add_linear_atTop
      hε (-t) Real.pi (ε + Real.pi)).congr' ?_
    filter_upwards with T
    unfold E₂ L
    rw [← Real.exp_add]
    apply congrArg Real.exp
    ring
  have hproduct : Filter.Tendsto
      (fun T => archimedeanVerticalGaussianBound ε t T *
        archimedeanVerticalTermsBound T)
      Filter.atTop (nhds 0) := by
    have hsum :=
      (((hE₁.mul_const C).add (hE₂.mul_const C)).add
        ((hE₁L.mul_const D).add (hE₂L.mul_const D)))
    have hsum' : Filter.Tendsto
        (fun T => E₁ T * C + E₂ T * C +
          (E₁ T * L T * D + E₂ T * L T * D))
        Filter.atTop (nhds 0) := by
      simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards with T
    unfold E₁ E₂ L C D
    unfold archimedeanVerticalGaussianBound archimedeanVerticalTermsBound
    ring
  have hprincipal : Filter.Tendsto (fun T => A / T)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have htotal : Filter.Tendsto
      (fun T =>
        archimedeanVerticalGaussianBound ε t T *
            archimedeanVerticalTermsBound T + A / T)
      Filter.atTop (nhds 0) := by
    simpa using hproduct.add hprincipal
  refine htotal.congr' ?_
  filter_upwards with T
  unfold archimedeanVerticalMajorant A
  rfl

/-- Finite-rectangle Cauchy identity for the pole-removed Archimedean
integrand.  The only remaining analytic estimate needed to pass to the
infinite contours is decay of the two vertical sides. -/
theorem archimedeanRegularized_rectangle_identity
    (ε t T : ℝ) :
    (∫ x : ℝ in -T..T,
        archimedeanRegularizedIntegrand ε t
          ((x : ℂ) - Complex.I)) -
      (∫ x : ℝ in -T..T,
        archimedeanRegularizedIntegrand ε t (x : ℂ)) +
      Complex.I * (∫ y : ℝ in (-1 : ℝ)..0,
        archimedeanRegularizedIntegrand ε t
          ((T : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-1 : ℝ)..0,
        archimedeanRegularizedIntegrand ε t
          ((-T : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
  have hdiff : DifferentiableOn ℂ
      (archimedeanRegularizedIntegrand ε t)
      (Complex.Rectangle ((-T : ℂ) - Complex.I) (T : ℂ)) := by
    apply (differentiableOn_archimedeanRegularizedIntegrand ε t).mono
    intro z hz
    change z.im < 1 / 2
    have him := hz.2
    change z.im ∈ Set.uIcc (((-T : ℂ) - Complex.I).im) ((T : ℂ).im) at him
    norm_num at him
    linarith [him.2]
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (archimedeanRegularizedIntegrand ε t)
    ((-T : ℂ) - Complex.I) (T : ℂ) hdiff
  simpa [sub_eq_add_neg] using hrect

/-- The right vertical side of the regularized rectangle vanishes as its
height tends to infinity. -/
theorem tendsto_archimedeanRegularized_rightVerticalIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Filter.Tendsto
      (fun T : ℝ => ∫ y : ℝ in (-1 : ℝ)..0,
        archimedeanRegularizedIntegrand ε t
          ((T : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_
    (tendsto_archimedeanVerticalMajorant hε t)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 0)
    (C := archimedeanVerticalMajorant ε t T) (f := fun y : ℝ =>
      archimedeanRegularizedIntegrand ε t
        ((T : ℂ) + (y : ℂ) * Complex.I)) (by
      intro y hy
      have hy' := uIoc_subset_uIcc hy
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hy'
      exact norm_archimedeanRegularizedIntegrand_vertical_le
        hε t T y T (abs_of_nonneg (le_trans zero_le_one hT))
          hT hy'.1 hy'.2)
  simpa using hbound

/-- The left vertical side obeys the same vanishing estimate. -/
theorem tendsto_archimedeanRegularized_leftVerticalIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Filter.Tendsto
      (fun T : ℝ => ∫ y : ℝ in (-1 : ℝ)..0,
        archimedeanRegularizedIntegrand ε t
          ((-T : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_
    (tendsto_archimedeanVerticalMajorant hε t)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
  have hTabs : |(-T : ℝ)| = T := by
    rw [abs_neg, abs_of_nonneg (le_trans zero_le_one hT)]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 0)
    (C := archimedeanVerticalMajorant ε t T) (f := fun y : ℝ =>
      archimedeanRegularizedIntegrand ε t
        ((-T : ℂ) + (y : ℂ) * Complex.I)) (by
      intro y hy
      have hy' := uIoc_subset_uIcc hy
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hy'
      simpa only [Complex.ofReal_neg] using
        (norm_archimedeanRegularizedIntegrand_vertical_le
          hε t (-T) y T hTabs hT hy'.1 hy'.2))
  simpa using hbound

/-- Consequently, the symmetric horizontal difference of the regularized
integrand tends to zero. -/
theorem tendsto_archimedeanRegularized_horizontalDifference
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ x : ℝ in -T..T,
          archimedeanRegularizedIntegrand ε t
            ((x : ℂ) - Complex.I)) -
        (∫ x : ℝ in -T..T,
          archimedeanRegularizedIntegrand ε t (x : ℂ)))
      Filter.atTop (nhds 0) := by
  have hright :=
    tendsto_archimedeanRegularized_rightVerticalIntegral hε t
  have hleft :=
    tendsto_archimedeanRegularized_leftVerticalIntegral hε t
  have hsides : Filter.Tendsto
      (fun T : ℝ =>
        -Complex.I * (∫ y : ℝ in (-1 : ℝ)..0,
          archimedeanRegularizedIntegrand ε t
            ((T : ℂ) + (y : ℂ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-1 : ℝ)..0,
          archimedeanRegularizedIntegrand ε t
            ((-T : ℂ) + (y : ℂ) * Complex.I)))
      Filter.atTop (nhds 0) := by
    simpa using (hright.const_mul (-Complex.I)).add
      (hleft.const_mul Complex.I)
  refine hsides.congr' ?_
  filter_upwards with T
  have hrect := archimedeanRegularized_rectangle_identity ε t T
  linear_combination -hrect

/-! ## Integrability of the two horizontal elementary contours -/

theorem continuous_digamma_threeQuarter_line :
    Continuous (fun r : ℝ =>
      Complex.digamma (3 / 4 + Complex.I * (r / 2))) := by
  exact analyticOnNhd_digamma_re_pos.continuousOn.comp_continuous
    (by fun_prop) (fun r => by norm_num)

theorem integrable_complexTranslatedGaussian_safeLine_mul_digamma
    {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (fun r : ℝ =>
      complexTranslatedGaussian ε c ((r : ℂ) - Complex.I) *
        Complex.digamma (3 / 4 + Complex.I * (r / 2))) := by
  have hmajor :=
    (integrable_translatedGaussian_mul_exp_pi_abs hε c).const_mul
      (Real.exp ε * stripDigammaExponentialConstant)
  refine hmajor.mono' ?_ ?_
  · have hGaussian : Continuous (fun r : ℝ =>
        complexTranslatedGaussian ε c ((r : ℂ) - Complex.I)) := by
      unfold complexTranslatedGaussian
      fun_prop
    exact (hGaussian.mul
        continuous_digamma_threeQuarter_line).aestronglyMeasurable
  · filter_upwards with r
    have hnormGaussian :
        ‖complexTranslatedGaussian ε c ((r : ℂ) - Complex.I)‖ =
          Real.exp (ε - ε * (r - c) ^ 2) := by
      rw [norm_complexTranslatedGaussian]
      congr 1
      simp
    have hDigamma :
        ‖Complex.digamma (3 / 4 + Complex.I * (r / 2))‖ ≤
          stripDigammaExponentialConstant *
            Real.exp (Real.pi * (|r / 2| + 1)) := by
      simpa using (norm_digamma_strip_le
        (s := 3 / 4 + Complex.I * (r / 2))
        (by norm_num) (by norm_num))
    have habs : |r / 2| ≤ |r| := by
      rw [abs_div]
      norm_num
    rw [norm_mul, hnormGaussian]
    calc
      Real.exp (ε - ε * (r - c) ^ 2) *
          ‖Complex.digamma (3 / 4 + Complex.I * (r / 2))‖ ≤
        Real.exp (ε - ε * (r - c) ^ 2) *
          (stripDigammaExponentialConstant *
            Real.exp (Real.pi * (|r / 2| + 1))) :=
        mul_le_mul_of_nonneg_left hDigamma (Real.exp_pos _).le
      _ ≤ Real.exp (ε - ε * (r - c) ^ 2) *
          (stripDigammaExponentialConstant *
            Real.exp (Real.pi * (|r| + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _
          stripDigammaExponentialConstant_nonneg
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      _ = (Real.exp ε * stripDigammaExponentialConstant) *
          (Real.exp (-ε * (r - c) ^ 2) *
            Real.exp (Real.pi * (|r| + 1))) := by
        rw [show ε - ε * (r - c) ^ 2 =
          ε + (-ε * (r - c) ^ 2) by ring, Real.exp_add]
        ring

theorem integrable_complexSymmetricGaussian_safeLine_mul_digamma
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
        Complex.digamma (3 / 4 + Complex.I * (r / 2))) := by
  rw [show (fun r : ℝ =>
      complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
        Complex.digamma (3 / 4 + Complex.I * (r / 2))) =
      fun r : ℝ =>
        complexTranslatedGaussian ε t ((r : ℂ) - Complex.I) *
            Complex.digamma (3 / 4 + Complex.I * (r / 2)) +
          complexTranslatedGaussian ε (-t) ((r : ℂ) - Complex.I) *
            Complex.digamma (3 / 4 + Complex.I * (r / 2)) by
    funext r
    unfold complexSymmetricGaussian
    ring]
  exact (integrable_complexTranslatedGaussian_safeLine_mul_digamma hε t).add
    (integrable_complexTranslatedGaussian_safeLine_mul_digamma hε (-t))

lemma norm_inv_le_two_of_half_le_abs_re
    {z : ℂ} (hz : 1 / 2 ≤ |z.re|) : ‖z⁻¹‖ ≤ 2 := by
  have hzre : z.re ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hz
    norm_num at hz
  have hzne : z ≠ 0 := fun hzero => hzre (congrArg Complex.re hzero)
  rw [norm_inv]
  have hnormPos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  rw [inv_le_comm₀ hnormPos (by norm_num : (0 : ℝ) < 2)]
  have hre := Complex.abs_re_le_norm z
  nlinarith

theorem integrable_safeLine_rational_log_terms
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
        (1 / (3 / 2 + Complex.I * (r : ℂ)) +
          1 / (3 / 2 + Complex.I * (r : ℂ) - 1) -
            Complex.log Real.pi / 2)) := by
  let R : ℝ → ℂ := fun r =>
    1 / (3 / 2 + Complex.I * (r : ℂ)) +
      1 / (3 / 2 + Complex.I * (r : ℂ) - 1) -
        Complex.log Real.pi / 2
  have hRContinuous : Continuous R := by
    unfold R
    apply Continuous.sub
    · apply Continuous.add
      · exact continuous_const.div
          (by fun_prop : Continuous (fun r : ℝ =>
            3 / 2 + Complex.I * (r : ℂ))) (fun r => by
          intro hzero
          have hre := congrArg Complex.re hzero
          norm_num at hre)
      · exact continuous_const.div
          (by fun_prop : Continuous (fun r : ℝ =>
            3 / 2 + Complex.I * (r : ℂ) - 1)) (fun r => by
          intro hzero
          have hre := congrArg Complex.re hzero
          norm_num at hre)
    · exact continuous_const
  have hRBound : ∀ r : ℝ, ‖R r‖ ≤
      4 + ‖Complex.log Real.pi‖ := by
    intro r
    have hfirst : ‖(3 / 2 + Complex.I * (r : ℂ))⁻¹‖ ≤ 2 :=
      norm_inv_le_two_of_half_le_abs_re (by norm_num)
    have hsecond : ‖(3 / 2 + Complex.I * (r : ℂ) - 1)⁻¹‖ ≤ 2 :=
      norm_inv_le_two_of_half_le_abs_re (by norm_num)
    have hlog : ‖Complex.log Real.pi / 2‖ ≤
        ‖Complex.log Real.pi‖ := by
      rw [norm_div]
      norm_num
    unfold R
    simp only [one_div]
    calc
      ‖(3 / 2 + Complex.I * (r : ℂ))⁻¹ +
          (3 / 2 + Complex.I * (r : ℂ) - 1)⁻¹ -
            Complex.log Real.pi / 2‖ ≤
        ‖(3 / 2 + Complex.I * (r : ℂ))⁻¹‖ +
          ‖(3 / 2 + Complex.I * (r : ℂ) - 1)⁻¹‖ +
            ‖Complex.log Real.pi / 2‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 + 2 + ‖Complex.log Real.pi‖ := by gcongr
      _ = 4 + ‖Complex.log Real.pi‖ := by ring
  have hH := integrable_complexSymmetricGaussian_safeLine hε t
  have hmul := hH.mul_bdd hRContinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hRBound)
  simpa only [R] using hmul

lemma completedSpectralCoordinate_safeLine (r : ℝ) :
    completedSpectralCoordinate ((r : ℂ) - Complex.I) =
      3 / 2 + Complex.I * (r : ℂ) := by
  unfold completedSpectralCoordinate
  ring_nf
  rw [Complex.I_sq]
  ring

lemma completedSpectralCoordinate_criticalLine (r : ℝ) :
    completedSpectralCoordinate (r : ℂ) =
      1 / 2 + Complex.I * (r : ℂ) := rfl

/-- On the safe spectral line, the completed-zeta decomposition is the
negative logarithmic derivative of xi plus the packaged elementary terms. -/
lemma negLogDeriv_riemannZeta_safeLine_eq_xi_add_archimedean
    (r : ℝ) :
    -deriv riemannZeta (3 / 2 + Complex.I * (r : ℂ)) /
        riemannZeta (3 / 2 + Complex.I * (r : ℂ)) =
      -deriv riemannXi (3 / 2 + Complex.I * (r : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (r : ℂ)) +
        archimedeanSpectralTerms ((r : ℂ) - Complex.I) := by
  rw [negLogDeriv_riemannZeta_safeLine_decomposition]
  unfold archimedeanSpectralTerms
  rw [completedSpectralCoordinate_safeLine]
  ring

theorem integrable_archimedeanSpectralIntegrand_safeLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
        archimedeanSpectralTerms ((r : ℂ) - Complex.I)) := by
  have hregular := integrable_safeLine_rational_log_terms hε t
  have hdigamma :=
    (integrable_complexSymmetricGaussian_safeLine_mul_digamma hε t).mul_const
      (2 : ℂ)⁻¹
  rw [show (fun r : ℝ =>
      complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
        archimedeanSpectralTerms ((r : ℂ) - Complex.I)) =
      fun r : ℝ =>
        complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
          (1 / (3 / 2 + Complex.I * (r : ℂ)) +
            1 / (3 / 2 + Complex.I * (r : ℂ) - 1) -
              Complex.log Real.pi / 2) +
        (complexSymmetricGaussian ε t ((r : ℂ) - Complex.I) *
          Complex.digamma (3 / 4 + Complex.I * (r / 2))) *
            (2 : ℂ)⁻¹ by
    funext r
    unfold archimedeanSpectralTerms
    rw [completedSpectralCoordinate_safeLine]
    have hhalf :
        (3 / 2 + Complex.I * (r : ℂ)) / 2 =
          3 / 4 + Complex.I * (r / 2) := by
      push_cast
      ring
    rw [hhalf]
    ring]
  exact hregular.add hdigamma

theorem integrable_archimedeanSpectralIntegrand_criticalLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun r : ℝ =>
      complexSymmetricGaussian ε t (r : ℂ) *
        archimedeanSpectralTerms (r : ℂ)) := by
  have hr : Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) * criticalLineRationalPair r) :=
    integrable_symmetricGaussian_mul_criticalLineRationalPair hε t
  have hsymComplex : Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (integrable_symmetricGaussian hε t)
  have hlog : Integrable (fun r : ℝ =>
      (symmetricGaussian ε t r : ℂ) *
        (-Complex.log Real.pi / 2)) :=
    hsymComplex.mul_const (-Complex.log Real.pi / 2)
  have hdigamma : Integrable (fun r : ℝ =>
      ((symmetricGaussian ε t r : ℂ) *
        Complex.digamma (1 / 4 + Complex.I * (r / 2))) *
          (2 : ℂ)⁻¹) :=
    (integrable_symmetricGaussian_mul_digamma_quarter hε t).mul_const
      (2 : ℂ)⁻¹
  rw [show (fun r : ℝ =>
      complexSymmetricGaussian ε t (r : ℂ) *
        archimedeanSpectralTerms (r : ℂ)) =
      fun r : ℝ =>
        ((symmetricGaussian ε t r : ℂ) * criticalLineRationalPair r +
          (symmetricGaussian ε t r : ℂ) *
            (-Complex.log Real.pi / 2)) +
        ((symmetricGaussian ε t r : ℂ) *
          Complex.digamma (1 / 4 + Complex.I * (r / 2))) *
            (2 : ℂ)⁻¹ by
    funext r
    rw [complexSymmetricGaussian_ofReal]
    unfold archimedeanSpectralTerms criticalLineRationalPair
    rw [completedSpectralCoordinate_criticalLine]
    have hhalf :
        (1 / 2 + Complex.I * (r : ℂ)) / 2 =
          1 / 4 + Complex.I * (r / 2) := by
      push_cast
      ring
    rw [hhalf]
    ring]
  exact (hr.add hlog).add hdigamma

lemma principalKernel_safeLine_sub_criticalLine (A : ℂ) (x : ℝ) :
    -Complex.I * A / ((x : ℂ) - Complex.I / 2) -
        (-Complex.I * A / ((x : ℂ) + Complex.I / 2)) =
      A * ((1 / (x ^ 2 + 1 / 4) : ℝ) : ℂ) := by
  have hminus : (x : ℂ) - Complex.I / 2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hplus : (x : ℂ) + Complex.I / 2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hquadReal : x ^ 2 + 1 / 4 ≠ 0 := by
    positivity
  have hquad : (((x ^ 2 + 1 / 4 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hquadReal
  push_cast
  field_simp [hminus, hplus, hquad]
  ring_nf
  have hminusTwo : -Complex.I + (x : ℂ) * 2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hplusTwo : Complex.I + (x : ℂ) * 2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hquadFour : 1 + (x : ℂ) ^ 2 * 4 ≠ 0 := by
    rw [show 1 + (x : ℂ) ^ 2 * 4 =
        4 * ((x ^ 2 + 1 / 4 : ℝ) : ℂ) by
      push_cast
      ring]
    exact mul_ne_zero (by norm_num) hquad
  field_simp [hminusTwo, hplusTwo, hquadFour]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The jump of the explicit principal part between the safe and critical
horizontal lines is the elementary Cauchy density. -/
theorem archimedeanPrincipalPart_safeLine_sub_criticalLine
    (ε t x : ℝ) :
    archimedeanPrincipalPart ε t ((x : ℂ) - Complex.I) -
        archimedeanPrincipalPart ε t (x : ℂ) =
      complexSymmetricGaussian ε t archimedeanPolePoint *
        ((1 / (x ^ 2 + 1 / 4) : ℝ) : ℂ) := by
  unfold archimedeanPrincipalPart
  rw [show (x : ℂ) - Complex.I - archimedeanPolePoint =
      (x : ℂ) - Complex.I / 2 by
        unfold archimedeanPolePoint
        ring,
    show (x : ℂ) - archimedeanPolePoint =
      (x : ℂ) + Complex.I / 2 by
        unfold archimedeanPolePoint
        ring]
  exact principalKernel_safeLine_sub_criticalLine
    (complexSymmetricGaussian ε t archimedeanPolePoint) x

lemma integral_cauchyDensity_neg_T_T (T : ℝ) :
    (∫ x : ℝ in -T..T, 1 / (x ^ 2 + 1 / 4)) =
      4 * Real.arctan (2 * T) := by
  rw [show (fun x : ℝ => 1 / (x ^ 2 + 1 / 4)) =
      fun x : ℝ => ((1 / 2 : ℝ) ^ 2 + x ^ 2)⁻¹ by
    funext x
    congr 1
    ring]
  rw [integral_inv_sq_add_sq (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [show T / (1 / 2 : ℝ) = 2 * T by ring,
    show -T / (1 / 2 : ℝ) = -(2 * T) by ring,
    Real.arctan_neg]
  ring

/-- Exact finite-height principal-part contribution.  Its limit is
`2 * pi` times the Gaussian pole weight. -/
theorem integral_archimedeanPrincipalPart_safeLine_sub_criticalLine
    (ε t T : ℝ) :
    (∫ x : ℝ in -T..T,
        archimedeanPrincipalPart ε t ((x : ℂ) - Complex.I)) -
      (∫ x : ℝ in -T..T,
        archimedeanPrincipalPart ε t (x : ℂ)) =
      complexSymmetricGaussian ε t archimedeanPolePoint *
        (4 * Real.arctan (2 * T) : ℝ) := by
  have hsafeContinuous : Continuous (fun x : ℝ =>
      archimedeanPrincipalPart ε t ((x : ℂ) - Complex.I)) := by
    unfold archimedeanPrincipalPart
    exact continuous_const.div (by fun_prop) (fun x => by
      intro h
      have him := congrArg Complex.im h
      unfold archimedeanPolePoint at him
      norm_num at him)
  have hcriticalContinuous : Continuous (fun x : ℝ =>
      archimedeanPrincipalPart ε t (x : ℂ)) := by
    unfold archimedeanPrincipalPart
    exact continuous_const.div (by fun_prop) (fun x => by
      intro h
      have him := congrArg Complex.im h
      unfold archimedeanPolePoint at him
      norm_num at him)
  rw [← intervalIntegral.integral_sub
    (hsafeContinuous.intervalIntegrable (-T) T)
    (hcriticalContinuous.intervalIntegrable (-T) T)]
  simp_rw [archimedeanPrincipalPart_safeLine_sub_criticalLine]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,
    integral_cauchyDensity_neg_T_T]

lemma tendsto_principalKernel_arctan (A : ℂ) :
    Filter.Tendsto
      (fun T : ℝ => A * ((4 * Real.arctan (2 * T) : ℝ) : ℂ))
      Filter.atTop
      (nhds (A * ((2 * Real.pi : ℝ) : ℂ))) := by
  have htwo : Filter.Tendsto (fun T : ℝ => 2 * T)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (by norm_num : (0 : ℝ) < 2)).2 Filter.tendsto_id
  have hatan : Filter.Tendsto (fun T : ℝ => Real.arctan (2 * T))
      Filter.atTop (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp htwo
  have hfour : Filter.Tendsto
      (fun T : ℝ => 4 * Real.arctan (2 * T))
      Filter.atTop (nhds (2 * Real.pi)) := by
    convert hatan.const_mul 4 using 1 <;> ring
  have hcast : Filter.Tendsto
      (fun T : ℝ => ((4 * Real.arctan (2 * T) : ℝ) : ℂ))
      Filter.atTop (nhds (((2 * Real.pi : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hfour
  exact hcast.const_mul A

/-- The finite principal-part jump tends to the exact residue contribution
`2 * pi * H(-i/2)`. -/
theorem tendsto_integral_archimedeanPrincipalPart_jump
    (ε t : ℝ) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ x : ℝ in -T..T,
            archimedeanPrincipalPart ε t ((x : ℂ) - Complex.I)) -
          (∫ x : ℝ in -T..T,
            archimedeanPrincipalPart ε t (x : ℂ)))
      Filter.atTop
      (nhds (complexSymmetricGaussian ε t archimedeanPolePoint *
        ((2 * Real.pi : ℝ) : ℂ))) := by
  rw [show (fun T : ℝ =>
      (∫ x : ℝ in -T..T,
          archimedeanPrincipalPart ε t ((x : ℂ) - Complex.I)) -
        (∫ x : ℝ in -T..T,
          archimedeanPrincipalPart ε t (x : ℂ))) =
      fun T : ℝ =>
        complexSymmetricGaussian ε t archimedeanPolePoint *
          ((4 * Real.arctan (2 * T) : ℝ) : ℂ) by
    funext T
    exact integral_archimedeanPrincipalPart_safeLine_sub_criticalLine ε t T]
  exact tendsto_principalKernel_arctan
    (complexSymmetricGaussian ε t archimedeanPolePoint)

lemma intervalIntegral_archimedean_safeLine_decomposition
    {ε : ℝ} (hε : 0 < ε) (t T : ℝ) :
    (∫ x : ℝ in -T..T,
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        archimedeanSpectralTerms ((x : ℂ) - Complex.I)) =
      (∫ x : ℝ in -T..T,
        archimedeanRegularizedIntegrand ε t
          ((x : ℂ) - Complex.I)) +
      (∫ x : ℝ in -T..T,
        archimedeanPrincipalPart ε t
          ((x : ℂ) - Complex.I)) := by
  let F : ℝ → ℂ := fun x =>
    complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
      archimedeanSpectralTerms ((x : ℂ) - Complex.I)
  let R : ℝ → ℂ := fun x =>
    archimedeanRegularizedIntegrand ε t ((x : ℂ) - Complex.I)
  let P : ℝ → ℂ := fun x =>
    archimedeanPrincipalPart ε t ((x : ℂ) - Complex.I)
  have hPContinuous : Continuous P := by
    unfold P archimedeanPrincipalPart
    exact continuous_const.div (by fun_prop) (fun x => by
      intro hzero
      have him := congrArg Complex.im hzero
      unfold archimedeanPolePoint at him
      norm_num at him)
  have hF : IntervalIntegrable F volume (-T) T :=
    (integrable_archimedeanSpectralIntegrand_safeLine hε t).intervalIntegrable
  have hP : IntervalIntegrable P volume (-T) T :=
    hPContinuous.intervalIntegrable _ _
  have hdecomp : ∀ x : ℝ, F x = R x + P x := by
    intro x
    unfold F R P
    apply archimedeanSpectralIntegrand_eq_regularized_sub_principal
    intro hpole
    have him := congrArg Complex.im hpole
    unfold archimedeanPolePoint at him
    norm_num at him
  have hR : IntervalIntegrable R volume (-T) T := by
    refine (hF.sub hP).congr ?_
    intro x hx
    change F x - P x = R x
    rw [hdecomp]
    ring
  rw [show (∫ x : ℝ in -T..T,
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        archimedeanSpectralTerms ((x : ℂ) - Complex.I)) =
      ∫ x : ℝ in -T..T, F x by rfl]
  rw [← intervalIntegral.integral_add hR hP]
  apply intervalIntegral.integral_congr
  intro x hx
  exact hdecomp x

lemma intervalIntegral_archimedean_criticalLine_decomposition
    {ε : ℝ} (hε : 0 < ε) (t T : ℝ) :
    (∫ x : ℝ in -T..T,
      complexSymmetricGaussian ε t (x : ℂ) *
        archimedeanSpectralTerms (x : ℂ)) =
      (∫ x : ℝ in -T..T,
        archimedeanRegularizedIntegrand ε t (x : ℂ)) +
      (∫ x : ℝ in -T..T,
        archimedeanPrincipalPart ε t (x : ℂ)) := by
  let F : ℝ → ℂ := fun x =>
    complexSymmetricGaussian ε t (x : ℂ) *
      archimedeanSpectralTerms (x : ℂ)
  let R : ℝ → ℂ := fun x =>
    archimedeanRegularizedIntegrand ε t (x : ℂ)
  let P : ℝ → ℂ := fun x =>
    archimedeanPrincipalPart ε t (x : ℂ)
  have hPContinuous : Continuous P := by
    unfold P archimedeanPrincipalPart
    exact continuous_const.div (by fun_prop) (fun x => by
      intro hzero
      have him := congrArg Complex.im hzero
      unfold archimedeanPolePoint at him
      norm_num at him)
  have hF : IntervalIntegrable F volume (-T) T :=
    (integrable_archimedeanSpectralIntegrand_criticalLine hε t).intervalIntegrable
  have hP : IntervalIntegrable P volume (-T) T :=
    hPContinuous.intervalIntegrable _ _
  have hdecomp : ∀ x : ℝ, F x = R x + P x := by
    intro x
    unfold F R P
    apply archimedeanSpectralIntegrand_eq_regularized_sub_principal
    intro hpole
    have him := congrArg Complex.im hpole
    unfold archimedeanPolePoint at him
    norm_num at him
  have hR : IntervalIntegrable R volume (-T) T := by
    refine (hF.sub hP).congr ?_
    intro x hx
    change F x - P x = R x
    rw [hdecomp]
    ring
  rw [show (∫ x : ℝ in -T..T,
      complexSymmetricGaussian ε t (x : ℂ) *
        archimedeanSpectralTerms (x : ℂ)) =
      ∫ x : ℝ in -T..T, F x by rfl]
  rw [← intervalIntegral.integral_add hR hP]
  apply intervalIntegral.integral_congr
  intro x hx
  exact hdecomp x

/-- The finite horizontal difference of the original elementary integrand
converges to the crossed `s = 1` residue. -/
theorem tendsto_archimedeanSpectralTerms_horizontalDifference
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ x : ℝ in -T..T,
          complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
            archimedeanSpectralTerms ((x : ℂ) - Complex.I)) -
        (∫ x : ℝ in -T..T,
          complexSymmetricGaussian ε t (x : ℂ) *
            archimedeanSpectralTerms (x : ℂ)))
      Filter.atTop
      (nhds (complexSymmetricGaussian ε t archimedeanPolePoint *
        ((2 * Real.pi : ℝ) : ℂ))) := by
  have hregular :=
    tendsto_archimedeanRegularized_horizontalDifference hε t
  have hprincipal :=
    tendsto_integral_archimedeanPrincipalPart_jump ε t
  have hsum : Filter.Tendsto
      (fun T : ℝ =>
        ((∫ x : ℝ in -T..T,
            archimedeanRegularizedIntegrand ε t
              ((x : ℂ) - Complex.I)) -
          (∫ x : ℝ in -T..T,
            archimedeanRegularizedIntegrand ε t (x : ℂ))) +
        ((∫ x : ℝ in -T..T,
            archimedeanPrincipalPart ε t
              ((x : ℂ) - Complex.I)) -
          (∫ x : ℝ in -T..T,
            archimedeanPrincipalPart ε t (x : ℂ))))
      Filter.atTop
      (nhds (complexSymmetricGaussian ε t archimedeanPolePoint *
        ((2 * Real.pi : ℝ) : ℂ))) := by
    simpa using hregular.add hprincipal
  refine hsum.congr' ?_
  filter_upwards with T
  rw [intervalIntegral_archimedean_safeLine_decomposition hε,
    intervalIntegral_archimedean_criticalLine_decomposition hε]
  ring

/-- Full safe-minus-critical contour shift for the elementary completed-zeta
terms. -/
theorem integral_archimedeanSpectralTerms_safe_sub_critical
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ x : ℝ,
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        archimedeanSpectralTerms ((x : ℂ) - Complex.I)) -
      (∫ x : ℝ,
        complexSymmetricGaussian ε t (x : ℂ) *
          archimedeanSpectralTerms (x : ℂ)) =
      complexSymmetricGaussian ε t archimedeanPolePoint *
        ((2 * Real.pi : ℝ) : ℂ) := by
  have hsafe := intervalIntegral_tendsto_integral
    (integrable_archimedeanSpectralIntegrand_safeLine hε t)
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hcritical := intervalIntegral_tendsto_integral
    (integrable_archimedeanSpectralIntegrand_criticalLine hε t)
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hwhole := hsafe.sub hcritical
  have hresidue :=
    tendsto_archimedeanSpectralTerms_horizontalDifference hε t
  exact tendsto_nhds_unique hwhole hresidue

theorem integral_archimedeanSpectralTerms_criticalLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ x : ℝ,
      complexSymmetricGaussian ε t (x : ℂ) *
        archimedeanSpectralTerms (x : ℂ)) =
      ((Real.pi *
        (gaussianArchimedeanContribution ε t -
          4 * Real.exp (ε / 4 - ε * t ^ 2) *
            Real.cos (ε * t)) : ℝ) : ℂ) := by
  rw [show (fun x : ℝ =>
      complexSymmetricGaussian ε t (x : ℂ) *
        archimedeanSpectralTerms (x : ℂ)) =
      fun x : ℝ =>
        complexSymmetricGaussian ε t (x : ℂ) *
          (criticalLineRationalPair x - Complex.log Real.pi / 2 +
            Complex.digamma
              (1 / 4 + Complex.I * (x / 2)) / 2) by
    funext x
    unfold archimedeanSpectralTerms criticalLineRationalPair
    rw [completedSpectralCoordinate_criticalLine]
    have hhalf :
        (1 / 2 + Complex.I * (x : ℂ)) / 2 =
          1 / 4 + Complex.I * (x / 2) := by
      push_cast
      ring
    rw [hhalf]]
  exact integral_criticalLine_completedElementary_terms_eq_archimedean
    hε t

/-- The safe-line elementary contour is exactly `pi` times the complete
Archimedean contribution used by the arithmetic certificate. -/
theorem integral_archimedeanSpectralTerms_safeLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ x : ℝ,
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        archimedeanSpectralTerms ((x : ℂ) - Complex.I)) =
      ((Real.pi * gaussianArchimedeanContribution ε t : ℝ) : ℂ) := by
  have hshift := integral_archimedeanSpectralTerms_safe_sub_critical hε t
  have hcritical := integral_archimedeanSpectralTerms_criticalLine hε t
  rw [hcritical, complexSymmetricGaussian_archimedeanPolePoint] at hshift
  push_cast at hshift ⊢
  linear_combination hshift

/-- The safe-line xi logarithmic derivative is absolutely integrable
against every positive-width translated Gaussian. -/
theorem integrable_complexSymmetricGaussian_mul_negLogDeriv_riemannXi_safeLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ =>
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (x : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (x : ℂ)))) := by
  have hzeta :=
    integrable_complexSymmetricGaussian_mul_negLogDeriv_riemannZeta hε t
  have harch := integrable_archimedeanSpectralIntegrand_safeLine hε t
  refine (hzeta.sub harch).congr
    (Filter.Eventually.of_forall fun x => ?_)
  change
    complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
          (-deriv riemannZeta (3 / 2 + Complex.I * (x : ℂ)) /
            riemannZeta (3 / 2 + Complex.I * (x : ℂ))) -
        complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
          archimedeanSpectralTerms ((x : ℂ) - Complex.I) =
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (x : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (x : ℂ)))
  rw [negLogDeriv_riemannZeta_safeLine_eq_xi_add_archimedean]
  ring

/-- Exact arithmetic evaluation of the remaining safe-line xi contour.
The sign is the one needed by the Gaussian explicit formula: the integral
is `-pi` times `archimedean - prime`. -/
theorem integral_negLogDeriv_riemannXi_safeLine_eq_arithmetic
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ x : ℝ,
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (x : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (x : ℂ)))) =
      ((-Real.pi * gaussianArithmeticExplicitFormula ε t : ℝ) : ℂ) := by
  have hzeta :=
    integrable_complexSymmetricGaussian_mul_negLogDeriv_riemannZeta hε t
  have harch := integrable_archimedeanSpectralIntegrand_safeLine hε t
  calc
    (∫ x : ℝ,
      complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (x : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (x : ℂ)))) =
        ∫ x : ℝ,
          complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
            (-deriv riemannZeta (3 / 2 + Complex.I * (x : ℂ)) /
              riemannZeta (3 / 2 + Complex.I * (x : ℂ))) -
          complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
            archimedeanSpectralTerms ((x : ℂ) - Complex.I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change
          complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
              (-deriv riemannXi (3 / 2 + Complex.I * (x : ℂ)) /
                riemannXi (3 / 2 + Complex.I * (x : ℂ))) =
            complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
                (-deriv riemannZeta (3 / 2 + Complex.I * (x : ℂ)) /
                  riemannZeta (3 / 2 + Complex.I * (x : ℂ))) -
              complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
                archimedeanSpectralTerms ((x : ℂ) - Complex.I)
        rw [negLogDeriv_riemannZeta_safeLine_eq_xi_add_archimedean]
        ring
    _ =
        (∫ x : ℝ,
          complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
            (-deriv riemannZeta (3 / 2 + Complex.I * (x : ℂ)) /
              riemannZeta (3 / 2 + Complex.I * (x : ℂ)))) -
        ∫ x : ℝ,
          complexSymmetricGaussian ε t ((x : ℂ) - Complex.I) *
            archimedeanSpectralTerms ((x : ℂ) - Complex.I) :=
      integral_sub hzeta harch
    _ = ((Real.pi * gaussianPrimeContribution ε t : ℝ) : ℂ) -
        ((Real.pi * gaussianArchimedeanContribution ε t : ℝ) : ℂ) := by
      rw [integral_complexSymmetricGaussian_mul_negLogDeriv_eq_primeContribution
        hε t, integral_archimedeanSpectralTerms_safeLine hε t]
    _ = ((-Real.pi * gaussianArithmeticExplicitFormula ε t : ℝ) : ℂ) := by
      unfold gaussianArithmeticExplicitFormula
      push_cast
      ring

end

end RiemannGaussian
