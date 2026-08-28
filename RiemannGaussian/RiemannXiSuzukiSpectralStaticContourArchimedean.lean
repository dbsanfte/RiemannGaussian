import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourEndpoint
import RiemannGaussian.RiemannXiSuzukiRealAxisDigamma

/-!
# Archimedean cancellation in the static-contour endpoint term

This module proves a fourth-root bound for digamma uniformly across the
closed strip from `1/4` to `3/4`.  It then integrates the logarithmic
derivative of `Gammaℝ` horizontally to show that the gamma-factor difference
between `1/2 + I*T` and `3/2 + I*T` is sublinear on the quantitative contour
sequence.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology
  RealInnerProductSpace

namespace RiemannGaussian

noncomputable section

/-! ## A uniform horizontal digamma bound -/

/-- The shifted square series controlling horizontal digamma variation in
the strip `1/4 ≤ re s ≤ 3/4`. -/
def staticContourDigammaHorizontalSquareSeries (n : ℕ) : ℝ :=
  1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ)

/-- The horizontal comparison series is summable. -/
theorem summable_staticContourDigammaHorizontalSquareSeries :
    Summable staticContourDigammaHorizontalSquareSeries := by
  unfold staticContourDigammaHorizontalSquareSeries
  exact (Real.summable_one_div_nat_add_rpow (1 / 4) 2).2 (by norm_num)

/-- A single Euler-series term changes by at most a fixed square-series
term under a horizontal displacement inside the closed quarter strip. -/
theorem norm_suzukiWeilDigammaDifferenceSummand_horizontal_le
    {x r : ℝ} (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 3 / 4) (n : ℕ) :
    ‖suzukiWeilDigammaDifferenceSummand
        (x + Complex.I * (r / 2))
        (1 / 4 + Complex.I * (r / 2)) n‖ ≤
      (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareSeries n := by
  let d : ℝ := (n : ℝ) + 1 / 4
  let a : ℂ := (n : ℂ) + (x + Complex.I * (r / 2))
  let b : ℂ := (n : ℂ) + (1 / 4 + Complex.I * (r / 2))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have haRe : d ≤ a.re := by
    dsimp [a, d]
    simpa using hxlo
  have hbRe : b.re = d := by
    dsimp [b, d]
    simp
  have haNorm : d ≤ ‖a‖ := haRe.trans (Complex.re_le_norm a)
  have hbNorm : d ≤ ‖b‖ := by
    rw [← hbRe]
    exact Complex.re_le_norm b
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hd.trans_le haNorm))
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hd.trans_le hbNorm))
  have hterm :
      suzukiWeilDigammaDifferenceSummand
          (x + Complex.I * (r / 2))
          (1 / 4 + Complex.I * (r / 2)) n =
        (((x - 1 / 4 : ℝ) : ℂ)) / (b * a) := by
    unfold suzukiWeilDigammaDifferenceSummand
    change b⁻¹ - a⁻¹ = _
    field_simp [ha0, hb0]
    push_cast
    ring
  have hnum : ‖(((x - 1 / 4 : ℝ) : ℂ))‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hprod : d ^ 2 ≤ ‖b‖ * ‖a‖ := by
    simpa only [pow_two] using
      mul_le_mul hbNorm haNorm hd.le (norm_nonneg b)
  rw [hterm, norm_div, norm_mul]
  calc
    ‖(((x - 1 / 4 : ℝ) : ℂ))‖ / (‖b‖ * ‖a‖) ≤
        (1 / 2 : ℝ) / d ^ 2 :=
      div_le_div₀ (by positivity) hnum (sq_pos_of_pos hd) hprod
    _ = (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareSeries n := by
      unfold staticContourDigammaHorizontalSquareSeries
      have hdabs : |(n : ℝ) + 1 / 4| = d := by
        simpa [d] using (abs_of_pos hd)
      rw [hdabs]
      rw [Real.rpow_two]
      field_simp [hd.ne']

/-- The finite mass of the horizontal comparison square series. -/
def staticContourDigammaHorizontalSquareMass : ℝ :=
  ∑' n : ℕ, staticContourDigammaHorizontalSquareSeries n

theorem staticContourDigammaHorizontalSquareMass_nonneg :
    0 ≤ staticContourDigammaHorizontalSquareMass := by
  unfold staticContourDigammaHorizontalSquareMass
  exact tsum_nonneg fun n ↦ by
    unfold staticContourDigammaHorizontalSquareSeries
    positivity

/-- Digamma varies by a height-independent constant along every horizontal
segment in the closed quarter strip. -/
theorem norm_digamma_horizontal_sub_quarter_vertical_le
    {x r : ℝ} (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 3 / 4) :
    ‖Complex.digamma (x + Complex.I * (r / 2)) -
        Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ ≤
      (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareMass := by
  let D : ℕ → ℂ := fun n ↦
    suzukiWeilDigammaDifferenceSummand
      (x + Complex.I * (r / 2))
      (1 / 4 + Complex.I * (r / 2)) n
  have ha : 0 < (x + Complex.I * (r / 2) : ℂ).re := by
    simpa using (show (0 : ℝ) < x by linarith)
  have hb : 0 < (1 / 4 + Complex.I * (r / 2) : ℂ).re := by norm_num
  have hDnorm : Summable (fun n ↦ ‖D n‖) := by
    simpa only [D] using
      summable_norm_suzukiWeilDigammaDifferenceSummand ha hb
  have hmajor : Summable (fun n ↦
      (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareSeries n) :=
    summable_staticContourDigammaHorizontalSquareSeries.mul_left _
  have hsum := hasSum_suzukiWeilDigammaDifferenceSummand ha hb
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, D n‖ ≤ ∑' n : ℕ, ‖D n‖ :=
      norm_tsum_le_tsum_norm hDnorm
    _ ≤ ∑' n : ℕ,
        (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareSeries n :=
      hDnorm.tsum_le_tsum
        (fun n ↦ norm_suzukiWeilDigammaDifferenceSummand_horizontal_le
          hxlo hxhi n)
        hmajor
    _ = (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareMass := by
      unfold staticContourDigammaHorizontalSquareMass
      exact summable_staticContourDigammaHorizontalSquareSeries.tsum_mul_left _

/-- A fixed nonnegative coefficient for the strip-wide fourth-root digamma
bound. -/
def staticContourDigammaStripGrowthConstant : ℝ :=
  suzukiRealAxisQuarterDigammaGrowthConstant +
    (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareMass

theorem staticContourDigammaStripGrowthConstant_nonneg :
    0 ≤ staticContourDigammaStripGrowthConstant := by
  unfold staticContourDigammaStripGrowthConstant
  positivity [suzukiRealAxisQuarterDigammaGrowthConstant_nonneg,
    staticContourDigammaHorizontalSquareMass_nonneg]

/-- Digamma has fourth-root growth uniformly throughout the gamma strip
needed by the two completed-xi endpoints. -/
theorem norm_digamma_staticContour_strip_le_quarterPower
    {x r : ℝ} (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 3 / 4) :
    ‖Complex.digamma (x + Complex.I * (r / 2))‖ ≤
      staticContourDigammaStripGrowthConstant *
        (|r| + 1) ^ (1 / 4 : ℝ) := by
  let P : ℝ := (|r| + 1) ^ (1 / 4 : ℝ)
  have hP : 1 ≤ P := by
    dsimp [P]
    exact Real.one_le_rpow (by linarith [abs_nonneg r]) (by norm_num)
  calc
    ‖Complex.digamma (x + Complex.I * (r / 2))‖ =
        ‖(Complex.digamma (x + Complex.I * (r / 2)) -
            Complex.digamma (1 / 4 + Complex.I * (r / 2))) +
          Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.digamma (x + Complex.I * (r / 2)) -
          Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ +
        ‖Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ :=
      norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * staticContourDigammaHorizontalSquareMass +
        suzukiRealAxisQuarterDigammaGrowthConstant * P := by
      exact add_le_add
        (norm_digamma_horizontal_sub_quarter_vertical_le hxlo hxhi)
        (by simpa [P] using norm_digamma_quarter_vertical_le_quarterPower r)
    _ ≤ ((1 / 2 : ℝ) * staticContourDigammaHorizontalSquareMass) * P +
        suzukiRealAxisQuarterDigammaGrowthConstant * P := by
      apply add_le_add
      · simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hP
            (mul_nonneg (by norm_num)
              staticContourDigammaHorizontalSquareMass_nonneg)
      · exact le_rfl
    _ = staticContourDigammaStripGrowthConstant * P := by
      unfold staticContourDigammaStripGrowthConstant
      ring

/-! ## Horizontal logarithmic derivative of `Gammaℝ` -/

/-- Logarithmic modulus of `Gammaℝ` on a horizontal line. -/
def staticContourGammaRHorizontalLogNorm (T x : ℝ) : ℝ :=
  Real.log ‖Complex.Gammaℝ
    ((x : ℂ) + (T : ℂ) * Complex.I)‖

/-- The real horizontal derivative of `Gammaℝ` is its complex derivative. -/
theorem hasDerivAt_GammaR_horizontal (T x : ℝ) (hx : 0 < x) :
    HasDerivAt
      (fun u : ℝ ↦ Complex.Gammaℝ
        ((u : ℂ) + (T : ℂ) * Complex.I))
      (deriv Complex.Gammaℝ
        ((x : ℂ) + (T : ℂ) * Complex.I)) x := by
  let s : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
  let a : ℂ → ℂ := fun u ↦ u + (T : ℂ) * Complex.I
  have ha : HasDerivAt a 1 (x : ℂ) := by
    simpa [a] using
      (hasDerivAt_id (𝕜 := ℂ) (x : ℂ)).add_const
        ((T : ℂ) * Complex.I)
  have hf : HasDerivAt Complex.Gammaℝ
      (deriv Complex.Gammaℝ s) s := by
    apply DifferentiableAt.hasDerivAt
    apply differentiableAt_Gammaℝ_of_re_pos
    simpa [s] using hx
  have hcomp : HasDerivAt (Complex.Gammaℝ ∘ a)
      (deriv Complex.Gammaℝ s) (x : ℂ) := by
    simpa [s] using hf.comp (x : ℂ) ha
  simpa only [Function.comp_apply, a, s] using hcomp.comp_ofReal

private theorem hasDerivAt_log_norm_of_hasDerivAt_mul
    {g : ℝ → ℂ} {D : ℂ} {x : ℝ}
    (hne : g x ≠ 0) (hg : HasDerivAt g (D * g x) x) :
    HasDerivAt (fun u ↦ Real.log ‖g u‖) D.re x := by
  let q : ℝ → ℝ := fun u ↦ ‖g u‖ ^ 2
  have hinner : inner ℝ (g x) (D * g x) = q x * D.re := by
    rw [Complex.inner]
    dsimp [q]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [mul_re, mul_im, conj_re, conj_im]
    ring
  have hq : HasDerivAt q (2 * q x * D.re) x := by
    have hraw := hg.norm_sq
    simpa [q, hinner, mul_assoc] using hraw
  have hqpos : 0 < q x := by
    dsimp [q]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hlog := hq.log hqpos.ne'
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hhalf' : HasDerivAt
      (fun u ↦ (1 / 2 : ℝ) * Real.log (q u)) D.re x := by
    apply hhalf.congr_deriv
    field_simp [hqpos.ne']
  convert hhalf' using 1
  funext u
  simp [q, Real.log_pow]

/-- On the positive horizontal half-plane, the derivative of the logarithmic
modulus of `Gammaℝ` is the real part of its logarithmic derivative. -/
theorem hasDerivAt_staticContourGammaRHorizontalLogNorm
    {T x : ℝ} (hx : 0 < x) :
    HasDerivAt (staticContourGammaRHorizontalLogNorm T)
      (logDeriv Complex.Gammaℝ
        ((x : ℂ) + (T : ℂ) * Complex.I)).re x := by
  let s : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
  let g : ℝ → ℂ := fun u ↦ Complex.Gammaℝ
    ((u : ℂ) + (T : ℂ) * Complex.I)
  let D : ℂ := logDeriv Complex.Gammaℝ s
  have hs : 0 < s.re := by simpa [s] using hx
  have hne : g x ≠ 0 := by
    simpa [g, s] using Gammaℝ_ne_zero_of_re_pos hs
  have hcurve := hasDerivAt_GammaR_horizontal T x hx
  have hderiv : deriv Complex.Gammaℝ s = D * g x := by
    calc
      deriv Complex.Gammaℝ s =
          (deriv Complex.Gammaℝ s / Complex.Gammaℝ s) *
            Complex.Gammaℝ s :=
        (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)).symm
      _ = D * g x := by simp [D, g, s, logDeriv_apply]
  apply hasDerivAt_log_norm_of_hasDerivAt_mul hne
  simpa [s, g, hderiv] using hcurve

/-- The horizontal integral of the real `Gammaℝ` logarithmic derivative is
exactly the endpoint log-modulus difference. -/
theorem intervalIntegral_logDeriv_GammaR_re_eq_logNorm_sub (T : ℝ) :
    (∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      (logDeriv Complex.Gammaℝ
        ((x : ℂ) + (T : ℂ) * Complex.I)).re) =
      staticContourGammaRHorizontalLogNorm T (3 / 2) -
        staticContourGammaRHorizontalLogNorm T (1 / 2) := by
  let f : ℝ → ℝ := fun x ↦
    (-Complex.log Real.pi / 2 +
      Complex.digamma
        (((x : ℂ) + (T : ℂ) * Complex.I) / 2) / 2).re
  have hderiv (x : ℝ) (hx : x ∈ uIcc (1 / 2 : ℝ) (3 / 2 : ℝ)) :
      HasDerivAt (staticContourGammaRHorizontalLogNorm T) (f x) x := by
    have hx' : 0 < x := by
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
      linarith [hx.1]
    have h := hasDerivAt_staticContourGammaRHorizontalLogNorm
      (T := T) hx'
    rw [logDeriv_Gammaℝ (by simpa using hx')] at h
    simpa [f] using h
  have hcontinuous : ContinuousOn f (uIcc (1 / 2 : ℝ) (3 / 2 : ℝ)) := by
    have hmap : MapsTo
        (fun x : ℝ ↦ (((x : ℂ) + (T : ℂ) * Complex.I) / 2))
        (uIcc (1 / 2 : ℝ) (3 / 2 : ℝ)) {z : ℂ | 0 < z.re} := by
      intro x hx
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
      change 0 < ((((x : ℂ) + (T : ℂ) * Complex.I) / 2)).re
      simp
      linarith [hx.1]
    have hdigamma : ContinuousOn
        (fun x : ℝ ↦ Complex.digamma
          (((x : ℂ) + (T : ℂ) * Complex.I) / 2))
        (uIcc (1 / 2 : ℝ) (3 / 2 : ℝ)) := by
      exact analyticOnNhd_digamma_re_pos.continuousOn.comp
        (by fun_prop) hmap
    dsimp [f]
    fun_prop
  have hint : IntervalIntegrable f volume (1 / 2) (3 / 2) :=
    hcontinuous.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2 : ℝ),
        (logDeriv Complex.Gammaℝ
          ((x : ℂ) + (T : ℂ) * Complex.I)).re) =
        ∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2 : ℝ), f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
      have hxpos : 0 < (((x : ℂ) + (T : ℂ) * Complex.I)).re := by
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hx.1]
      dsimp
      rw [logDeriv_Gammaℝ hxpos]
    _ = staticContourGammaRHorizontalLogNorm T (3 / 2) -
        staticContourGammaRHorizontalLogNorm T (1 / 2) := hFTC

/-- A fixed nonnegative coefficient for the horizontal `Gammaℝ`
log-modulus difference. -/
def staticContourGammaRLogNormGrowthConstant : ℝ :=
  ‖Complex.log (Real.pi : ℂ)‖ / 2 +
    staticContourDigammaStripGrowthConstant / 2

theorem staticContourGammaRLogNormGrowthConstant_nonneg :
    0 ≤ staticContourGammaRLogNormGrowthConstant := by
  unfold staticContourGammaRLogNormGrowthConstant
  positivity [staticContourDigammaStripGrowthConstant_nonneg]

/-- The real part of the `Gammaℝ` logarithmic derivative has uniform
fourth-root growth along the endpoint strip. -/
theorem abs_re_logDeriv_GammaR_staticContour_le_quarterPower
    {T x : ℝ} (hxlo : 1 / 2 ≤ x) (hxhi : x ≤ 3 / 2) :
    |(logDeriv Complex.Gammaℝ
        ((x : ℂ) + (T : ℂ) * Complex.I)).re| ≤
      staticContourGammaRLogNormGrowthConstant *
        (|T| + 1) ^ (1 / 4 : ℝ) := by
  let s : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
  let P : ℝ := (|T| + 1) ^ (1 / 4 : ℝ)
  change |(logDeriv Complex.Gammaℝ s).re| ≤
    staticContourGammaRLogNormGrowthConstant * P
  have hs : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have harg : s / 2 =
      (((x / 2 : ℝ) : ℂ) + Complex.I * ((T : ℂ) / 2)) := by
    dsimp [s]
    push_cast
    ring
  have hdigamma : ‖Complex.digamma (s / 2)‖ ≤
      staticContourDigammaStripGrowthConstant * P := by
    have hxlo' : (1 / 4 : ℝ) ≤ x / 2 := by linarith
    have hxhi' : x / 2 ≤ (3 / 4 : ℝ) := by linarith
    have hraw := norm_digamma_staticContour_strip_le_quarterPower
      (x := x / 2) (r := T) hxlo' hxhi'
    rw [harg]
    simpa only [P] using hraw
  have hP : 1 ≤ P := by
    dsimp [P]
    exact Real.one_le_rpow (by linarith [abs_nonneg T]) (by norm_num)
  have hlogNonneg : 0 ≤ ‖Complex.log (Real.pi : ℂ)‖ / 2 := by positivity
  calc
    |(logDeriv Complex.Gammaℝ s).re| ≤
        ‖logDeriv Complex.Gammaℝ s‖ := Complex.abs_re_le_norm _
    _ = ‖-Complex.log (Real.pi : ℂ) / 2 +
        Complex.digamma (s / 2) / 2‖ := by rw [logDeriv_Gammaℝ hs]
    _ ≤ ‖-Complex.log (Real.pi : ℂ) / 2‖ +
        ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
    _ = ‖Complex.log (Real.pi : ℂ)‖ / 2 +
        ‖Complex.digamma (s / 2)‖ / 2 := by
      rw [norm_div, norm_div, norm_neg]
      norm_num
    _ ≤ ‖Complex.log (Real.pi : ℂ)‖ / 2 +
        (staticContourDigammaStripGrowthConstant * P) / 2 := by
      gcongr
    _ ≤ (‖Complex.log (Real.pi : ℂ)‖ / 2) * P +
        (staticContourDigammaStripGrowthConstant / 2) * P := by
      apply add_le_add
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hP hlogNonneg
      · exact le_of_eq (by ring)
    _ = staticContourGammaRLogNormGrowthConstant * P := by
      unfold staticContourGammaRLogNormGrowthConstant
      ring

/-- The `Gammaℝ` endpoint log-modulus difference grows at most like the
fourth root of the height. -/
theorem abs_staticContourGammaRHorizontalLogNorm_sub_le_quarterPower
    (T : ℝ) :
    |staticContourGammaRHorizontalLogNorm T (3 / 2) -
        staticContourGammaRHorizontalLogNorm T (1 / 2)| ≤
      staticContourGammaRLogNormGrowthConstant *
        (|T| + 1) ^ (1 / 4 : ℝ) := by
  rw [← intervalIntegral_logDeriv_GammaR_re_eq_logNorm_sub]
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2 : ℝ),
        (logDeriv Complex.Gammaℝ
          ((x : ℂ) + (T : ℂ) * Complex.I)).re‖ ≤
        (staticContourGammaRLogNormGrowthConstant *
          (|T| + 1) ^ (1 / 4 : ℝ)) *
            |(3 / 2 : ℝ) - 1 / 2| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs]
      apply abs_re_logDeriv_GammaR_staticContour_le_quarterPower
      · rw [uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
        exact hx.1.le
      · rw [uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx
        exact hx.2
    _ = staticContourGammaRLogNormGrowthConstant *
        (|T| + 1) ^ (1 / 4 : ℝ) := by norm_num

/-- A fourth-root term divided by a positive height is bounded by a strict
negative power once the height is at least one. -/
lemma quarterPower_one_add_div_le_neg_threeQuarter
    {T : ℝ} (hT : 1 ≤ T) :
    (T + 1) ^ (1 / 4 : ℝ) / T ≤
      2 * T ^ (-(3 / 4 : ℝ)) := by
  have hTpos : 0 < T := one_pos.trans_le hT
  have hbase : T + 1 ≤ 2 * T := by linarith
  have hpow : (T + 1) ^ (1 / 4 : ℝ) ≤
      (2 * T) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have htwo : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 / 4 : ℝ) ≤ 1))
  have hmul : (2 * T) ^ (1 / 4 : ℝ) ≤
      2 * T ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTpos.le]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hTpos.le _)
  have hrpowDiv : T ^ (1 / 4 : ℝ) / T =
      T ^ (-(3 / 4 : ℝ)) := by
    calc
      T ^ (1 / 4 : ℝ) / T =
          T ^ (1 / 4 : ℝ) / T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((1 / 4 : ℝ) - 1) :=
        (Real.rpow_sub hTpos (1 / 4 : ℝ) 1).symm
      _ = T ^ (-(3 / 4 : ℝ)) := by norm_num
  calc
    (T + 1) ^ (1 / 4 : ℝ) / T ≤
        (2 * T ^ (1 / 4 : ℝ)) / T :=
      div_le_div_of_nonneg_right (hpow.trans hmul) hTpos.le
    _ = 2 * T ^ (-(3 / 4 : ℝ)) := by
      rw [mul_div_assoc, hrpowDiv]

/-- Along the quantitative zero-free heights, the entire `Gammaℝ` endpoint
contribution is `o(T)`.  Thus the exponential gamma decay common to the two
completed-xi endpoints cancels rigorously before the arithmetic zeta problem
is addressed. -/
theorem tendsto_staticContourGammaRHorizontalLogNorm_sub_div_quantitative_zero :
    Tendsto
      (fun n : ℕ ↦
        (staticContourGammaRHorizontalLogNorm
            (quantitativeSpectralBoundaryTruncation n) (3 / 2) -
          staticContourGammaRHorizontalLogNorm
            (quantitativeSpectralBoundaryTruncation n) (1 / 2)) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let K : ℝ := staticContourGammaRLogNormGrowthConstant
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let M : ℕ → ℝ := fun n ↦ 2 * K * (T n) ^ (-(3 / 4 : ℝ))
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hT : 1 ≤ T n := by
      have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact hncast.trans (quantitativeSpectralBoundaryTruncation_spec n).1.le
    have hTpos : 0 < T n := one_pos.trans_le hT
    have hendpoint :=
      abs_staticContourGammaRHorizontalLogNorm_sub_le_quarterPower (T n)
    have hquotient :
        ‖(staticContourGammaRHorizontalLogNorm (T n) (3 / 2) -
              staticContourGammaRHorizontalLogNorm (T n) (1 / 2)) /
            T n‖ ≤
          K * (((T n) + 1) ^ (1 / 4 : ℝ) / T n) := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hTpos]
      calc
        |staticContourGammaRHorizontalLogNorm (T n) (3 / 2) -
              staticContourGammaRHorizontalLogNorm (T n) (1 / 2)| /
            T n ≤
            (K * ((T n + 1) ^ (1 / 4 : ℝ))) / T n :=
          div_le_div_of_nonneg_right
            (by simpa [K, abs_of_pos hTpos] using hendpoint) hTpos.le
        _ = K * (((T n) + 1) ^ (1 / 4 : ℝ) / T n) := by ring
    calc
      ‖(staticContourGammaRHorizontalLogNorm (T n) (3 / 2) -
            staticContourGammaRHorizontalLogNorm (T n) (1 / 2)) /
          T n‖ ≤
          K * (((T n) + 1) ^ (1 / 4 : ℝ) / T n) := hquotient
      _ ≤ K * (2 * (T n) ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (quarterPower_one_add_div_le_neg_threeQuarter hT)
          staticContourGammaRLogNormGrowthConstant_nonneg
      _ = M n := by simp [M, K]; ring
  · have hpower : Tendsto
        (fun n : ℕ ↦ (T n) ^ (-(3 / 4 : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
        tendsto_quantitativeSpectralBoundaryTruncation_atTop
    have hconstant : Tendsto M atTop (nhds (2 * K * 0)) := by
      simpa only [M] using tendsto_const_nhds.mul hpower
    simpa using hconstant

end

end RiemannGaussian
