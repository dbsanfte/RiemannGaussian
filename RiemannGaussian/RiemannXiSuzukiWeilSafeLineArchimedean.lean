import RiemannGaussian.RiemannXiSuzukiWeilSafeLinePrime
import RiemannGaussian.RiemannXiSuzukiWeilArchimedean

/-!
# Archimedean analysis on the Suzuki--Weil safe line

This file supplies the growth and integrability estimates needed to pair the
reflected safe-line spectral weight with the elementary and digamma terms in
the completed-zeta logarithmic derivative.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal FourierTransform Interval LSeries.notation Topology lp

namespace RiemannGaussian

noncomputable section

/-! ## Sublinear growth of the three-quarter-line digamma -/

/-- The shifted `3/2`-series used to majorize the Euler series for the
three-quarter-line digamma difference. -/
def suzukiWeilThreeQuarterPSeries (n : ℕ) : ℝ :=
  1 / |(n : ℝ) + 3 / 4| ^ (3 / 2 : ℝ)

/-- The shifted `3/2`-series is summable. -/
theorem summable_suzukiWeilThreeQuarterPSeries :
    Summable suzukiWeilThreeQuarterPSeries := by
  unfold suzukiWeilThreeQuarterPSeries
  exact (Real.summable_one_div_nat_add_rpow (3 / 4) (3 / 2)).2 (by norm_num)

/-- One Euler-series summand for a vertical digamma difference has a
summable `3/2`-power majorant and only square-root dependence on height. -/
theorem norm_suzukiWeilDigammaDifferenceSummand_threeQuarter_le
    (r : ℝ) (n : ℕ) :
    ‖suzukiWeilDigammaDifferenceSummand
        (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ ≤
      Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeries n := by
  let d : ℝ := (n : ℝ) + 3 / 4
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hb : (n : ℂ) + (3 / 4 : ℂ) = (d : ℂ) := by
    dsimp [d]
    push_cast
    ring
  have ha : (n : ℂ) + (3 / 4 + Complex.I * (r / 2)) =
      (d : ℂ) + Complex.I * (r / 2) := by
    dsimp [d]
    push_cast
    ring
  have hb0 : ((d : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have ha0 : (d : ℂ) + Complex.I * (r / 2) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    exact hd.ne' hre
  have hAre : d ≤ ‖(d : ℂ) + Complex.I * (r / 2)‖ := by
    calc
      d = ((d : ℂ) + Complex.I * (r / 2)).re := by simp
      _ ≤ ‖(d : ℂ) + Complex.I * (r / 2)‖ := Complex.re_le_norm _
  have hAnormPos : 0 < ‖(d : ℂ) + Complex.I * (r / 2)‖ :=
    norm_pos_iff.mpr ha0
  have hhead :
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ ≤ 2 / d := by
    unfold suzukiWeilDigammaDifferenceSummand
    rw [hb, ha]
    calc
      ‖(d : ℂ)⁻¹ - ((d : ℂ) + Complex.I * (r / 2))⁻¹‖ ≤
          ‖((d : ℂ))⁻¹‖ +
            ‖((d : ℂ) + Complex.I * (r / 2))⁻¹‖ := norm_sub_le _ _
      _ ≤ 1 / d + 1 / d := by
        rw [norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hd]
        simpa only [one_div] using add_le_add le_rfl
          ((inv_le_inv₀ hAnormPos hd).2 hAre)
      _ = 2 / d := by ring
  have hquotient :
      suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n =
        (Complex.I * (r / 2)) /
          ((d : ℂ) * ((d : ℂ) + Complex.I * (r / 2))) := by
    unfold suzukiWeilDigammaDifferenceSummand
    rw [hb, ha]
    rw [inv_sub_inv hb0 ha0]
    congr 1
    ring
  have htail :
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ ≤ |r| / 2 / d ^ 2 := by
    rw [hquotient, norm_div, norm_mul, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hrhalf : ‖(r : ℂ) / 2‖ = |r| / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hrhalf]
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd)
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hAre hd.le
  have hnormNonneg : 0 ≤
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ := norm_nonneg _
  have hsq :
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ ^ 2 ≤
        |r| / d ^ 3 := by
    calc
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ ^ 2 =
          ‖suzukiWeilDigammaDifferenceSummand
            (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ *
          ‖suzukiWeilDigammaDifferenceSummand
            (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ := by ring
      _ ≤ (2 / d) * (|r| / 2 / d ^ 2) :=
        mul_le_mul hhead htail hnormNonneg (by positivity)
      _ = |r| / d ^ 3 := by field_simp [hd.ne']
  have hsqrtPos : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hmajorNonneg :
      0 ≤ Real.sqrt (|r| + 1) / (d * Real.sqrt d) := by positivity
  have hmajorSq :
      (Real.sqrt (|r| + 1) / (d * Real.sqrt d)) ^ 2 =
        (|r| + 1) / d ^ 3 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hd.le]
    field_simp [hd.ne']
  have hbound :
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ ≤
        Real.sqrt (|r| + 1) / (d * Real.sqrt d) := by
    apply (sq_le_sq₀ hnormNonneg hmajorNonneg).mp
    rw [hmajorSq]
    exact hsq.trans (div_le_div_of_nonneg_right (by linarith [abs_nonneg r])
      (by positivity))
  have hpSeries :
      suzukiWeilThreeQuarterPSeries n = 1 / (d * Real.sqrt d) := by
    unfold suzukiWeilThreeQuarterPSeries
    rw [show |(n : ℝ) + 3 / 4| = d by
      rw [abs_of_pos hd]
    ]
    have hrpow : d ^ (3 / 2 : ℝ) = d * Real.sqrt d := by
      rw [Real.sqrt_eq_rpow,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hd, Real.rpow_one]
    rw [hrpow]
  rw [hpSeries]
  simpa [div_eq_mul_inv, mul_assoc] using hbound

/-- The finite mass of the shifted `3/2`-series. -/
def suzukiWeilThreeQuarterPSeriesMass : ℝ :=
  ∑' n : ℕ, suzukiWeilThreeQuarterPSeries n

theorem suzukiWeilThreeQuarterPSeriesMass_nonneg :
    0 ≤ suzukiWeilThreeQuarterPSeriesMass := by
  unfold suzukiWeilThreeQuarterPSeriesMass
  exact tsum_nonneg fun n ↦ by
    unfold suzukiWeilThreeQuarterPSeries
    positivity

/-- The vertical digamma difference grows at most like the square root of
height.  This deliberately sublinear bound is what makes the rational
safe-line spectral weight absolutely integrable against digamma. -/
theorem norm_digamma_threeQuarter_vertical_sub_le (r : ℝ) :
    ‖Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
        Complex.digamma (3 / 4)‖ ≤
      Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeriesMass := by
  let D : ℕ → ℂ := fun n ↦
    suzukiWeilDigammaDifferenceSummand
      (3 / 4 + Complex.I * (r / 2)) (3 / 4) n
  have ha : 0 < (3 / 4 + Complex.I * (r / 2) : ℂ).re := by norm_num
  have hb : 0 < (3 / 4 : ℂ).re := by norm_num
  have hDnorm : Summable (fun n ↦ ‖D n‖) := by
    simpa only [D] using
      summable_norm_suzukiWeilDigammaDifferenceSummand ha hb
  have hmajor : Summable (fun n ↦
      Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeries n) :=
    summable_suzukiWeilThreeQuarterPSeries.mul_left _
  have hsum := hasSum_suzukiWeilDigammaDifferenceSummand ha hb
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, D n‖ ≤ ∑' n : ℕ, ‖D n‖ :=
      norm_tsum_le_tsum_norm hDnorm
    _ ≤ ∑' n : ℕ,
        Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeries n :=
      hDnorm.tsum_le_tsum
        (fun n ↦ norm_suzukiWeilDigammaDifferenceSummand_threeQuarter_le r n)
        hmajor
    _ = Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeriesMass := by
      unfold suzukiWeilThreeQuarterPSeriesMass
      exact summable_suzukiWeilThreeQuarterPSeries.tsum_mul_left _

/-- A fixed nonnegative constant for the sublinear three-quarter-line
digamma bound. -/
def suzukiWeilThreeQuarterDigammaGrowthConstant : ℝ :=
  suzukiWeilThreeQuarterPSeriesMass + ‖Complex.digamma (3 / 4)‖

theorem suzukiWeilThreeQuarterDigammaGrowthConstant_nonneg :
    0 ≤ suzukiWeilThreeQuarterDigammaGrowthConstant := by
  unfold suzukiWeilThreeQuarterDigammaGrowthConstant
  positivity [suzukiWeilThreeQuarterPSeriesMass_nonneg]

/-- The complete three-quarter-line digamma has a rigorous square-root
vertical-growth bound. -/
theorem norm_digamma_threeQuarter_vertical_le (r : ℝ) :
    ‖Complex.digamma (3 / 4 + Complex.I * (r / 2))‖ ≤
      suzukiWeilThreeQuarterDigammaGrowthConstant *
        Real.sqrt (|r| + 1) := by
  have hsqrt : 1 ≤ Real.sqrt (|r| + 1) := by
    rw [Real.one_le_sqrt]
    linarith [abs_nonneg r]
  calc
    ‖Complex.digamma (3 / 4 + Complex.I * (r / 2))‖ =
        ‖(Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
            Complex.digamma (3 / 4)) + Complex.digamma (3 / 4)‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
          Complex.digamma (3 / 4)‖ + ‖Complex.digamma (3 / 4)‖ :=
      norm_add_le _ _
    _ ≤ Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeriesMass +
          ‖Complex.digamma (3 / 4)‖ := by
      gcongr
      exact norm_digamma_threeQuarter_vertical_sub_le r
    _ ≤ Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeriesMass +
          Real.sqrt (|r| + 1) * ‖Complex.digamma (3 / 4)‖ := by
      exact add_le_add le_rfl (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hsqrt
            (norm_nonneg (Complex.digamma (3 / 4))))
    _ = suzukiWeilThreeQuarterDigammaGrowthConstant *
          Real.sqrt (|r| + 1) := by
      unfold suzukiWeilThreeQuarterDigammaGrowthConstant
      ring

/-! ## Quadratic decay of the reflected safe-line weight -/

/-- A positive comparison constant between a shifted Cauchy kernel and the
standard Japanese-bracket kernel. -/
def suzukiWeilShiftedCauchyComparisonConstant (a b : ℝ) : ℝ :=
  2 + (1 + 2 * a ^ 2) / b ^ 2

theorem suzukiWeilShiftedCauchyComparisonConstant_pos
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    0 < suzukiWeilShiftedCauchyComparisonConstant a b := by
  unfold suzukiWeilShiftedCauchyComparisonConstant
  have hbSq : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  positivity

/-- Every nondegenerate shifted Cauchy kernel is bounded by a fixed multiple
of `(1+r²)⁻¹`. -/
theorem inv_shifted_sq_add_sq_le_standard
    (r a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ((r - a) ^ 2 + b ^ 2)⁻¹ ≤
      suzukiWeilShiftedCauchyComparisonConstant a b * (1 + r ^ 2)⁻¹ := by
  let K := suzukiWeilShiftedCauchyComparisonConstant a b
  have hbSq : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hK : 0 < K :=
    suzukiWeilShiftedCauchyComparisonConstant_pos a hb
  have hKtwo : 2 ≤ K := by
    dsimp [K]
    unfold suzukiWeilShiftedCauchyComparisonConstant
    have : 0 ≤ (1 + 2 * a ^ 2) / b ^ 2 := by positivity
    linarith
  have hshift : r ^ 2 ≤ 2 * (r - a) ^ 2 + 2 * a ^ 2 := by
    nlinarith [sq_nonneg (r - 2 * a)]
  have hquadratic :
      1 + r ^ 2 ≤ K * ((r - a) ^ 2 + b ^ 2) := by
    have hfirst : 2 * (r - a) ^ 2 ≤ K * (r - a) ^ 2 :=
      mul_le_mul_of_nonneg_right hKtwo (sq_nonneg _)
    have hsecond : 1 + 2 * a ^ 2 ≤ K * b ^ 2 := by
      dsimp [K]
      unfold suzukiWeilShiftedCauchyComparisonConstant
      field_simp [hb]
      nlinarith [sq_nonneg b]
    nlinarith
  have hleft : 0 < (r - a) ^ 2 + b ^ 2 := by positivity
  have hright : 0 < 1 + r ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hright,
    inv_mul_le_iff₀ hleft]
  simpa [K, mul_comm] using hquadratic

/-- The exact two-Cauchy-kernel bound behind horizontal integrability of
Suzuki's spectral transform. -/
theorem norm_suzukiWeilSpectralTransform_horizontal_le_cauchy
    (t : ℝ) (z : ℂ) (r : ℝ) {c : ℝ} (hc : c ≠ 0)
    (hzc : z.im ≠ c) :
    ‖suzukiWeilSpectralTransform t z
        ((r : ℂ) + (c : ℂ) * Complex.I)‖ ≤
      (Real.exp (c * t) + 1) *
        ((r ^ 2 + c ^ 2)⁻¹ +
          ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹) := by
  let alpha : ℂ := (r : ℂ) + (c : ℂ) * Complex.I
  have halpha : alpha ≠ 0 := by
    intro ha
    have him := congrArg Complex.im ha
    simp [alpha] at him
    exact hc him
  have hza : z - alpha ≠ 0 := by
    intro hza
    have him := congrArg Complex.im hza
    simp [alpha] at him
    exact hzc (sub_eq_zero.mp him)
  have haPos : 0 < ‖alpha‖ := norm_pos_iff.mpr halpha
  have hzaPos : 0 < ‖z - alpha‖ := norm_pos_iff.mpr hza
  have hrecip :
      1 / (‖alpha‖ * ‖z - alpha‖) ≤
        (1 / 2 : ℝ) *
          (1 / ‖alpha‖ ^ 2 + 1 / ‖z - alpha‖ ^ 2) := by
    field_simp [haPos.ne', hzaPos.ne']
    nlinarith [sq_nonneg (‖alpha‖ - ‖z - alpha‖)]
  have hcoeff := norm_suzukiSpectralScrewCoefficient_le_div t halpha
  have hCnonneg : 0 ≤ Real.exp (c * t) + 1 := by positivity
  unfold suzukiWeilSpectralTransform
  rw [norm_div]
  calc
    ‖suzukiSpectralScrewCoefficient t alpha‖ / ‖z - alpha‖ ≤
        ((Real.exp (alpha.im * t) + 1) / ‖alpha‖) /
          ‖z - alpha‖ := by gcongr
    _ = (Real.exp (c * t) + 1) *
        (1 / (‖alpha‖ * ‖z - alpha‖)) := by
      have halphaIm : alpha.im = c := by simp [alpha]
      rw [halphaIm]
      field_simp [haPos.ne', hzaPos.ne']
    _ ≤ (Real.exp (c * t) + 1) * ((1 / 2 : ℝ) *
          (1 / ‖alpha‖ ^ 2 + 1 / ‖z - alpha‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hrecip hCnonneg
    _ ≤ (Real.exp (c * t) + 1) *
        ((r ^ 2 + c ^ 2)⁻¹ +
          ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹) := by
      have halphaSq : ‖alpha‖ ^ 2 = r ^ 2 + c ^ 2 := by
        rw [Complex.sq_norm]
        simp [alpha, Complex.normSq_apply]
        ring
      have hgapSq : ‖z - alpha‖ ^ 2 =
          (r - z.re) ^ 2 + (c - z.im) ^ 2 := by
        rw [Complex.sq_norm]
        simp [alpha, Complex.normSq_apply]
        ring
      rw [halphaSq, hgapSq]
      have hnonnegA : 0 ≤ (r ^ 2 + c ^ 2)⁻¹ := by positivity
      have hnonnegB :
          0 ≤ ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹ := by positivity
      apply mul_le_mul_of_nonneg_left _ hCnonneg
      have hsum : 0 ≤
          (r ^ 2 + c ^ 2)⁻¹ +
            ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹ :=
        add_nonneg hnonnegA hnonnegB
      have hhalf := mul_le_mul_of_nonneg_right
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hsum
      simpa only [one_mul, one_div] using hhalf

/-- A fixed decay constant for one horizontal frequency line. -/
def suzukiWeilHorizontalDecayConstant
    (t : ℝ) (z : ℂ) (c : ℝ) : ℝ :=
  (Real.exp (c * t) + 1) *
    (suzukiWeilShiftedCauchyComparisonConstant 0 c +
      suzukiWeilShiftedCauchyComparisonConstant z.re (c - z.im))

theorem suzukiWeilHorizontalDecayConstant_nonneg
    (t : ℝ) (z : ℂ) {c : ℝ} (hc : c ≠ 0)
    (hzc : z.im ≠ c) :
    0 ≤ suzukiWeilHorizontalDecayConstant t z c := by
  unfold suzukiWeilHorizontalDecayConstant
  have hgap : c - z.im ≠ 0 := sub_ne_zero.mpr hzc.symm
  positivity [suzukiWeilShiftedCauchyComparisonConstant_pos 0 hc,
    suzukiWeilShiftedCauchyComparisonConstant_pos z.re hgap]

/-- Suzuki's transform has uniform quadratic decay on every nonzero
horizontal line disjoint from the evaluation height. -/
theorem norm_suzukiWeilSpectralTransform_horizontal_le_standard
    (t : ℝ) (z : ℂ) (r : ℝ) {c : ℝ} (hc : c ≠ 0)
    (hzc : z.im ≠ c) :
    ‖suzukiWeilSpectralTransform t z
        ((r : ℂ) + (c : ℂ) * Complex.I)‖ ≤
      suzukiWeilHorizontalDecayConstant t z c * (1 + r ^ 2)⁻¹ := by
  have hgap : c - z.im ≠ 0 := sub_ne_zero.mpr hzc.symm
  have hzero := inv_shifted_sq_add_sq_le_standard r 0 hc
  have hshift := inv_shifted_sq_add_sq_le_standard r z.re hgap
  have hC : 0 ≤ Real.exp (c * t) + 1 := by positivity
  calc
    ‖suzukiWeilSpectralTransform t z
        ((r : ℂ) + (c : ℂ) * Complex.I)‖ ≤
      (Real.exp (c * t) + 1) *
        ((r ^ 2 + c ^ 2)⁻¹ +
          ((r - z.re) ^ 2 + (c - z.im) ^ 2)⁻¹) :=
      norm_suzukiWeilSpectralTransform_horizontal_le_cauchy t z r hc hzc
    _ ≤ (Real.exp (c * t) + 1) *
        ((suzukiWeilShiftedCauchyComparisonConstant 0 c *
            (1 + r ^ 2)⁻¹) +
          suzukiWeilShiftedCauchyComparisonConstant z.re (c - z.im) *
            (1 + r ^ 2)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [sub_zero] using add_le_add hzero hshift
    _ = suzukiWeilHorizontalDecayConstant t z c * (1 + r ^ 2)⁻¹ := by
      unfold suzukiWeilHorizontalDecayConstant
      ring

/-- The total quadratic-decay constant for the reflected lower/upper
safe-line weight. -/
def suzukiWeilSafeLineDecayConstant (t : ℝ) (z : ℂ) : ℝ :=
  suzukiWeilHorizontalDecayConstant t z (-1) +
    suzukiWeilHorizontalDecayConstant t z 1

theorem suzukiWeilSafeLineDecayConstant_nonneg
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    0 ≤ suzukiWeilSafeLineDecayConstant t z := by
  have hzLower : z.im ≠ -1 := by linarith
  have hzUpper : z.im ≠ 1 := by linarith
  unfold suzukiWeilSafeLineDecayConstant
  exact add_nonneg
    (suzukiWeilHorizontalDecayConstant_nonneg t z (by norm_num) hzLower)
    (suzukiWeilHorizontalDecayConstant_nonneg t z (by norm_num) hzUpper)

/-- The reflected Suzuki safe-line weight decays quadratically. -/
theorem norm_suzukiWeilSafeLineSpectralWeight_le_standard
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) (r : ℝ) :
    ‖suzukiWeilSafeLineSpectralWeight t z r‖ ≤
      suzukiWeilSafeLineDecayConstant t z * (1 + r ^ 2)⁻¹ := by
  have hzLower : z.im ≠ -1 := by linarith
  have hzUpper : z.im ≠ 1 := by linarith
  have hlower := norm_suzukiWeilSpectralTransform_horizontal_le_standard
    t z r (c := -1) (by norm_num) hzLower
  have hupper := norm_suzukiWeilSpectralTransform_horizontal_le_standard
    t z (-r) (c := 1) (by norm_num) hzUpper
  unfold suzukiWeilSafeLineSpectralWeight
  calc
    ‖suzukiWeilSpectralTransform t z ((r : ℂ) - Complex.I) +
        suzukiWeilSpectralTransform t z (((-r : ℝ) : ℂ) + Complex.I)‖ ≤
      ‖suzukiWeilSpectralTransform t z ((r : ℂ) - Complex.I)‖ +
        ‖suzukiWeilSpectralTransform t z
          (((-r : ℝ) : ℂ) + Complex.I)‖ := norm_add_le _ _
    _ ≤ suzukiWeilHorizontalDecayConstant t z (-1) * (1 + r ^ 2)⁻¹ +
        suzukiWeilHorizontalDecayConstant t z 1 * (1 + (-r) ^ 2)⁻¹ := by
      apply add_le_add
      · simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul,
          one_mul, sub_eq_add_neg] using hlower
      · simpa only [Complex.ofReal_neg, Complex.ofReal_one, one_mul] using hupper
    _ = suzukiWeilSafeLineDecayConstant t z * (1 + r ^ 2)⁻¹ := by
      unfold suzukiWeilSafeLineDecayConstant
      ring

/-! ## Weighted absolute integrability -/

/-- Square-root growth remains integrable against quadratic decay. -/
theorem integrable_sqrt_abs_add_one_mul_inv_one_add_sq :
    Integrable (fun r : ℝ ↦
      Real.sqrt (|r| + 1) * (1 + r ^ 2)⁻¹) := by
  have hbase : Integrable (fun r : ℝ ↦
      (1 + ‖r‖) ^ (-(3 / 2 : ℝ))) := by
    exact integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by norm_num)
  have hmajor : Integrable (fun r : ℝ ↦
      2 * (1 + ‖r‖) ^ (-(3 / 2 : ℝ))) := hbase.const_mul 2
  refine hmajor.mono' (by fun_prop) (Filter.Eventually.of_forall fun r ↦ ?_)
  let x : ℝ := |r| + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hxsq : x ^ 2 ≤ 2 * (1 + r ^ 2) := by
    dsimp [x]
    rw [add_sq, sq_abs]
    nlinarith [sq_abs r, sq_nonneg (|r| - 1)]
  have hinv : (1 + r ^ 2)⁻¹ ≤ 2 * (x ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos hx),
      inv_mul_le_iff₀ hden]
    simpa [mul_comm] using hxsq
  have hrpow : x ^ (-(3 / 2 : ℝ)) = (x * Real.sqrt x)⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = -(1 + 1 / 2) by norm_num,
      Real.rpow_neg hx.le, Real.rpow_add hx, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hidentity :
      Real.sqrt x * (2 * (x ^ 2)⁻¹) =
        2 * x ^ (-(3 / 2 : ℝ)) := by
    rw [hrpow]
    field_simp [hx.ne', (Real.sqrt_pos.2 hx).ne']
    exact Real.sq_sqrt hx.le
  rw [Real.norm_of_nonneg (by positivity :
    0 ≤ Real.sqrt (|r| + 1) * (1 + r ^ 2)⁻¹)]
  calc
    Real.sqrt (|r| + 1) * (1 + r ^ 2)⁻¹ ≤
        Real.sqrt (|r| + 1) * (2 * (x ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)
    _ = 2 * x ^ (-(3 / 2 : ℝ)) := by simpa [x] using hidentity
    _ = 2 * (1 + ‖r‖) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.norm_eq_abs]
      simp only [x]
      congr 2
      ring

/-- The safe-line weight is absolutely integrable against square-root
vertical growth. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight_mul_sqrtGrowth
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (Real.sqrt (|r| + 1) : ℂ)) := by
  have hC := suzukiWeilSafeLineDecayConstant_nonneg t hz
  have hmajor := integrable_sqrt_abs_add_one_mul_inv_one_add_sq.const_mul
    (suzukiWeilSafeLineDecayConstant t z)
  refine hmajor.mono' ?_ (Filter.Eventually.of_forall fun r ↦ ?_)
  · exact ((integrable_suzukiWeilSafeLineSpectralWeight t hz).aestronglyMeasurable.mul
      (by fun_prop : Continuous (fun r : ℝ ↦
        (Real.sqrt (|r| + 1) : ℂ))).aestronglyMeasurable)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      ‖suzukiWeilSafeLineSpectralWeight t z r‖ * Real.sqrt (|r| + 1) ≤
          (suzukiWeilSafeLineDecayConstant t z * (1 + r ^ 2)⁻¹) *
            Real.sqrt (|r| + 1) := by
        gcongr
        exact norm_suzukiWeilSafeLineSpectralWeight_le_standard t hz r
      _ = suzukiWeilSafeLineDecayConstant t z *
          (Real.sqrt (|r| + 1) * (1 + r ^ 2)⁻¹) := by ring

/-- The reflected safe-line weight times the three-quarter-line digamma is
absolutely integrable. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight_mul_digamma
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        Complex.digamma (3 / 4 + Complex.I * (r / 2))) := by
  let C : ℝ := suzukiWeilSafeLineDecayConstant t z *
    suzukiWeilThreeQuarterDigammaGrowthConstant
  have hC : 0 ≤ C := mul_nonneg
    (suzukiWeilSafeLineDecayConstant_nonneg t hz)
    suzukiWeilThreeQuarterDigammaGrowthConstant_nonneg
  have hmajor := integrable_sqrt_abs_add_one_mul_inv_one_add_sq.const_mul C
  refine hmajor.mono' ?_ (Filter.Eventually.of_forall fun r ↦ ?_)
  · exact (integrable_suzukiWeilSafeLineSpectralWeight t hz).aestronglyMeasurable.mul
      continuous_digamma_threeQuarter_line.aestronglyMeasurable
  · rw [norm_mul]
    calc
      ‖suzukiWeilSafeLineSpectralWeight t z r‖ *
          ‖Complex.digamma (3 / 4 + Complex.I * (r / 2))‖ ≤
        (suzukiWeilSafeLineDecayConstant t z * (1 + r ^ 2)⁻¹) *
          (suzukiWeilThreeQuarterDigammaGrowthConstant *
            Real.sqrt (|r| + 1)) := by
          exact mul_le_mul
            (norm_suzukiWeilSafeLineSpectralWeight_le_standard t hz r)
            (norm_digamma_threeQuarter_vertical_le r)
            (norm_nonneg _)
            (mul_nonneg (suzukiWeilSafeLineDecayConstant_nonneg t hz)
              (by positivity))
      _ = C * (Real.sqrt (|r| + 1) * (1 + r ^ 2)⁻¹) := by
        dsimp [C]
        ring

/-! ## Consequences for the completed-zeta factor -/

/-- The reflected safe-line weight has zero mean.  This is the exact
endpoint cancellation that removes every constant in Gauss's digamma
integral. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_eq_zero
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ, suzukiWeilSafeLineSpectralWeight t z r) = 0 := by
  have hinversion :=
    integral_suzukiWeilSafeLineSpectralWeight_mul_cexp ht hz 0
  simpa [suzukiWeilSymmetricSafeLineTest,
    suzukiWeilTest_zero ht] using hinversion

/-- Both elementary poles, the logarithmic constant, and the digamma factor
in the completed-zeta logarithmic derivative are absolutely integrable
against the reflected safe-line weight. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight_mul_archimedeanTerms
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        archimedeanSpectralTerms ((r : ℂ) - Complex.I)) := by
  let W : ℝ → ℂ := suzukiWeilSafeLineSpectralWeight t z
  have hW : Integrable W :=
    integrable_suzukiWeilSafeLineSpectralWeight t hz
  have hfirst : Integrable (fun r : ℝ ↦
      W r * (1 / (3 / 2 + Complex.I * (r : ℂ)))) := by
    apply hW.mul_bdd
      (show AEStronglyMeasurable (fun r : ℝ ↦
        (1 / (3 / 2 + Complex.I * (r : ℂ)) : ℂ)) volume from
          (show Continuous (fun r : ℝ ↦
            (1 / (3 / 2 + Complex.I * (r : ℂ)) : ℂ)) from
              continuous_const.div (by fun_prop) (fun r hzero ↦ by
                have hre := congrArg Complex.re hzero
                norm_num at hre)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun r ↦ by
      simpa only [one_div] using
        (norm_inv_le_two_of_half_le_abs_re
          (z := 3 / 2 + Complex.I * (r : ℂ)) (by norm_num))
  have hsecond : Integrable (fun r : ℝ ↦
      W r * (1 / (1 / 2 + Complex.I * (r : ℂ)))) := by
    apply hW.mul_bdd
      (show AEStronglyMeasurable (fun r : ℝ ↦
        (1 / (1 / 2 + Complex.I * (r : ℂ)) : ℂ)) volume from
          (show Continuous (fun r : ℝ ↦
            (1 / (1 / 2 + Complex.I * (r : ℂ)) : ℂ)) from
              continuous_const.div (by fun_prop) (fun r hzero ↦ by
                have hre := congrArg Complex.re hzero
                norm_num at hre)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun r ↦ by
      simpa only [one_div] using
        (norm_inv_le_two_of_half_le_abs_re
          (z := 1 / 2 + Complex.I * (r : ℂ)) (by norm_num))
  have hlog : Integrable (fun r : ℝ ↦
      W r * (-Complex.log Real.pi / 2)) :=
    hW.mul_const (-Complex.log Real.pi / 2)
  have hdigamma : Integrable (fun r : ℝ ↦
      W r * (Complex.digamma
        (3 / 4 + Complex.I * (r / 2)) / 2)) := by
    have h :=
      (integrable_suzukiWeilSafeLineSpectralWeight_mul_digamma t hz).mul_const
        (2 : ℂ)⁻¹
    exact h.congr (Filter.Eventually.of_forall fun r ↦ by
      dsimp [W]
      ring)
  have hsum := ((hfirst.add hsecond).add hlog).add hdigamma
  refine hsum.congr (Filter.Eventually.of_forall fun r ↦ ?_)
  dsimp [W]
  unfold archimedeanSpectralTerms
  rw [completedSpectralCoordinate_safeLine]
  have hsecondCoordinate :
      3 / 2 + Complex.I * (r : ℂ) - 1 =
        1 / 2 + Complex.I * (r : ℂ) := by ring
  have hhalfCoordinate :
      (3 / 2 + Complex.I * (r : ℂ)) / 2 =
        3 / 4 + Complex.I * (r / 2) := by
    ring
  rw [hsecondCoordinate, hhalfCoordinate]
  ring

/-! ## Laplace evaluation of the two elementary poles -/

/-- The reflected safe-line weight is continuous as well as absolutely
integrable. -/
theorem continuous_suzukiWeilSafeLineSpectralWeight
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Continuous (suzukiWeilSafeLineSpectralWeight t z) := by
  unfold suzukiWeilSafeLineSpectralWeight
  apply Continuous.add
  · apply continuous_comp_of_forall_analyticAt
      (suzukiWeilSpectralTransform t z)
      (fun r : ℝ ↦ (r : ℂ) - Complex.I) (by fun_prop)
    intro r
    apply analyticAt_suzukiWeilSpectralTransform_of_ne
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    linarith
  · apply continuous_comp_of_forall_analyticAt
      (suzukiWeilSpectralTransform t z)
      (fun r : ℝ ↦ (((-r : ℝ) : ℂ) + Complex.I)) (by fun_prop)
    intro r
    apply analyticAt_suzukiWeilSpectralTransform_of_ne
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    linarith

/-- A positive-real-part Cauchy factor is bounded on the real frequency
line. -/
theorem norm_inv_add_I_mul_le_inv
    {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ‖((a : ℂ) + Complex.I * (r : ℂ))⁻¹‖ ≤ a⁻¹ := by
  have hnorm : a ≤ ‖(a : ℂ) + Complex.I * (r : ℂ)‖ := by
    calc
      a = ((a : ℂ) + Complex.I * (r : ℂ)).re := by simp
      _ ≤ ‖(a : ℂ) + Complex.I * (r : ℂ)‖ := Complex.re_le_norm _
  have hnormPos : 0 < ‖(a : ℂ) + Complex.I * (r : ℂ)‖ :=
    ha.trans_le hnorm
  rw [norm_inv]
  exact (inv_le_inv₀ hnormPos ha).2 hnorm

/-- The safe-line weight times any positive-real-part Cauchy factor is
absolutely integrable. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {a : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) := by
  apply (integrable_suzukiWeilSafeLineSpectralWeight t hz).mul_bdd
    (show AEStronglyMeasurable (fun r : ℝ ↦
      (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) volume from
        (show Continuous (fun r : ℝ ↦
          (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) from
            (show Continuous (fun r : ℝ ↦
              (a : ℂ) + Complex.I * (r : ℂ)) by fun_prop).inv₀
                (fun r hzero ↦ by
                  have hre := congrArg Complex.re hzero
                  simp at hre
                  exact ha.ne' hre)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (norm_inv_add_I_mul_le_inv ha)

/-- Joint frequency/Laplace kernel used for the elementary safe-line poles. -/
def suzukiWeilSafeLineLaplaceJoint
    (t : ℝ) (z : ℂ) (a : ℝ) (p : ℝ × ℝ) : ℂ :=
  suzukiWeilSafeLineSpectralWeight t z p.1 *
    Complex.exp
      ((-(a : ℂ) - Complex.I * (p.1 : ℂ)) * (p.2 : ℂ))

/-- The joint Laplace kernel is absolutely integrable on frequency times the
positive time half-line. -/
theorem integrable_suzukiWeilSafeLineLaplaceJoint
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {a : ℝ} (ha : 0 < a) :
    Integrable (suzukiWeilSafeLineLaplaceJoint t z a)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hW := (integrable_suzukiWeilSafeLineSpectralWeight t hz).norm
  have hExp : Integrable (fun x : ℝ ↦ Real.exp (-a * x))
      (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn (fun x : ℝ ↦ Real.exp (-a * x)) (Ioi (0 : ℝ))
    convert integrableOn_exp_mul_Ioi (a := -a) (neg_lt_zero.mpr ha) 0 using 1
  have hmajor := hW.mul_prod hExp
  refine hmajor.mono' ?_ (Filter.Eventually.of_forall fun p ↦ ?_)
  · unfold suzukiWeilSafeLineLaplaceJoint
    exact ((continuous_suzukiWeilSafeLineSpectralWeight t hz).comp
      continuous_fst).mul (by fun_prop) |>.aestronglyMeasurable
  · unfold suzukiWeilSafeLineLaplaceJoint
    rw [norm_mul, Complex.norm_exp]
    rw [show
      ((-(a : ℂ) - Complex.I * (p.1 : ℂ)) * (p.2 : ℂ)).re =
        -a * p.2 by
      simp only [mul_re, sub_re, neg_re, ofReal_re, I_re, ofReal_im,
        sub_im, neg_im, I_im]
      ring]

/-- The positive-half-line Laplace transform of one real-frequency
oscillation is its Cauchy factor. -/
theorem integral_Ioi_suzukiWeilSafeLineLaplaceExponential
    {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (∫ x : ℝ in Ioi 0,
      Complex.exp
        ((-(a : ℂ) - Complex.I * (r : ℂ)) * (x : ℂ))) =
      ((a : ℂ) + Complex.I * (r : ℂ))⁻¹ := by
  have hreal : (-(a : ℂ) - Complex.I * (r : ℂ)).re < 0 := by
    simp
    exact ha
  rw [integral_exp_mul_complex_Ioi hreal 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show -(a : ℂ) - Complex.I * (r : ℂ) =
      -((a : ℂ) + Complex.I * (r : ℂ)) by ring,
    neg_div_neg_eq, one_div]

/-- Fubini and Fourier inversion evaluate an arbitrary positive-real-part
Cauchy factor against the reflected safe-line weight. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im)
    {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ in Ioi 0,
          (Real.exp (-a * x) : ℂ) *
            suzukiWeilSymmetricSafeLineTest t z (-x)) := by
  have hjoint := integrable_suzukiWeilSafeLineLaplaceJoint t hz ha
  have hswap := integral_integral_swap
    (f := fun r x ↦ suzukiWeilSafeLineLaplaceJoint t z a (r, x)) hjoint
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) =
      ∫ r : ℝ, ∫ x : ℝ in Ioi 0,
        suzukiWeilSafeLineLaplaceJoint t z a (r, x) := by
      apply integral_congr_ae
      filter_upwards with r
      unfold suzukiWeilSafeLineLaplaceJoint
      change suzukiWeilSafeLineSpectralWeight t z r *
          ((a : ℂ) + Complex.I * (r : ℂ))⁻¹ =
        ∫ x : ℝ in Ioi 0,
          suzukiWeilSafeLineSpectralWeight t z r *
            Complex.exp
              ((-(a : ℂ) - Complex.I * (r : ℂ)) * (x : ℂ))
      rw [integral_const_mul,
        integral_Ioi_suzukiWeilSafeLineLaplaceExponential ha]
    _ = ∫ x : ℝ in Ioi 0, ∫ r : ℝ,
        suzukiWeilSafeLineLaplaceJoint t z a (r, x) := hswap
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ in Ioi 0,
          (Real.exp (-a * x) : ℂ) *
            suzukiWeilSymmetricSafeLineTest t z (-x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      unfold suzukiWeilSafeLineLaplaceJoint
      have hexponential (r : ℝ) :
          Complex.exp
              ((-(a : ℂ) - Complex.I * (r : ℂ)) * (x : ℂ)) =
            (Real.exp (-a * x) : ℂ) *
              Complex.exp
                (Complex.I * (r : ℂ) * ((-x : ℝ) : ℂ)) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp_rw [hexponential]
      rw [show (fun r : ℝ ↦
          suzukiWeilSafeLineSpectralWeight t z r *
            ((Real.exp (-a * x) : ℂ) *
              Complex.exp
                (Complex.I * (r : ℂ) * ((-x : ℝ) : ℂ)))) =
        fun r : ℝ ↦ (Real.exp (-a * x) : ℂ) *
          (suzukiWeilSafeLineSpectralWeight t z r *
            Complex.exp
              (Complex.I * (r : ℂ) * ((-x : ℝ) : ℂ))) by
        funext r
        ring]
      rw [integral_const_mul,
        integral_suzukiWeilSafeLineSpectralWeight_mul_cexp ht hz (-x)]
      ring

/-- On positive reflected time, the symmetric safe-line test reduces to the
original positive-half-line Suzuki test with the exact exponential weight. -/
theorem suzukiWeilSymmetricSafeLineTest_neg_of_pos
    (t : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    suzukiWeilSymmetricSafeLineTest t z (-x) =
      (Real.exp x : ℂ) * suzukiWeilTest t z x := by
  unfold suzukiWeilSymmetricSafeLineTest
  rw [suzukiWeilTest_of_neg t z (neg_lt_zero.mpr hx)]
  simp

/-- The reflected time-domain Laplace integral is the original Suzuki test
with exponent shifted by one. -/
theorem integral_Ioi_exp_mul_suzukiWeilSymmetricSafeLineTest_neg
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) (a : ℝ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-a * x) : ℂ) *
        suzukiWeilSymmetricSafeLineTest t z (-x)) =
      ∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp ((1 - a) * x) : ℂ) := by
  calc
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-a * x) : ℂ) *
        suzukiWeilSymmetricSafeLineTest t z (-x)) =
      ∫ x : ℝ in Ioi 0,
        suzukiWeilTest t z x *
          (Real.exp ((1 - a) * x) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [suzukiWeilSymmetricSafeLineTest_neg_of_pos t z hx]
      calc
        (Real.exp (-a * x) : ℂ) *
            ((Real.exp x : ℂ) * suzukiWeilTest t z x) =
          (((Real.exp (-a * x) * Real.exp x : ℝ) : ℂ) *
            suzukiWeilTest t z x) := by push_cast; ring
        _ = (Real.exp ((1 - a) * x) : ℂ) *
            suzukiWeilTest t z x := by
          rw [← Real.exp_add]
          congr 2
          ring_nf
        _ = suzukiWeilTest t z x *
            (Real.exp ((1 - a) * x) : ℂ) := by ring
    _ = ∫ x : ℝ,
        suzukiWeilTest t z x *
          (Real.exp ((1 - a) * x) : ℂ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxle : x ≤ 0 := by simpa using hx
      rcases eq_or_lt_of_le hxle with hzero | hneg
      · subst x
        simp [suzukiWeilTest_zero ht]
      · rw [suzukiWeilTest_of_neg t z hneg, zero_mul]

/-- The safe-line pole with real part `3/2` gives the lower elementary
factor `exp(-x/2)`. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_threeHalfPole
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ,
          suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ)) := by
  rw [integral_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I ht hz
    (by norm_num : (0 : ℝ) < 3 / 2),
    integral_Ioi_exp_mul_suzukiWeilSymmetricSafeLineTest_neg ht z]
  congr 2
  funext x
  congr 1
  ring_nf

/-- The safe-line pole with real part `1/2` gives the upper elementary factor
`exp(x/2)`. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_oneHalfPole
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ,
          suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ)) := by
  rw [integral_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I ht hz
    (by norm_num : (0 : ℝ) < 1 / 2),
    integral_Ioi_exp_mul_suzukiWeilSymmetricSafeLineTest_neg ht z]
  congr 2
  funext x
  congr 1
  ring_nf

/-- The two elementary completed-zeta poles on the safe line evaluate to
`2π` times Suzuki's literal elementary integral. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_elementaryPoles
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        ((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) := by
  have hthree :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I t hz
      (by norm_num : (0 : ℝ) < 3 / 2)
  have hone :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I t hz
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hzSafe : z ∈ suzukiXiSafeUpperHalfPlane := by
    change (1 / 2 : ℝ) < z.im
    linarith
  have hupper := integrable_suzukiWeilUpperPoleIntegrand ht hzSafe
  have hlower := integrable_suzukiWeilLowerPoleIntegrand ht hzSafe
  rw [show (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        ((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹)) =
      (∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          (((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) +
      ∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ by
    rw [← integral_add hthree hone]
    apply integral_congr_ae
    filter_upwards with r
    ring]
  rw [integral_suzukiWeilSafeLineSpectralWeight_mul_threeHalfPole ht hz,
    integral_suzukiWeilSafeLineSpectralWeight_mul_oneHalfPole ht hz]
  rw [show (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) =
      (∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ)) +
      ∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ) by
    rw [← integral_add hupper hlower]
    apply integral_congr_ae
    filter_upwards with x
    unfold suzukiWeilElementaryIntegrand
    ring]
  ring

/-- The completed-zeta logarithmic constant contributes zero because the
reflected safe-line weight has zero mean.  Thus the complete elementary
spectral factor is exactly the literal elementary time integral. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_elementarySpectralTerms
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) -
            Complex.log Real.pi / 2)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) := by
  have hthree :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I t hz
      (by norm_num : (0 : ℝ) < 3 / 2)
  have hone :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I t hz
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hpoles : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹))) := by
    exact (hthree.add hone).congr (Filter.Eventually.of_forall fun r ↦ by
      simp only [Pi.add_apply]
      ring)
  have hconstant : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (Complex.log Real.pi / 2)) :=
    (integrable_suzukiWeilSafeLineSpectralWeight t hz).mul_const _
  rw [show (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) -
            Complex.log Real.pi / 2)) =
      (∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
            (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹))) -
      ∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          (Complex.log Real.pi / 2) by
    rw [← integral_sub hpoles hconstant]
    apply integral_congr_ae
    filter_upwards with r
    ring]
  rw [integral_suzukiWeilSafeLineSpectralWeight_mul_elementaryPoles ht hz]
  rw [integral_mul_const,
    integral_suzukiWeilSafeLineSpectralWeight_eq_zero ht hz]
  ring

/-! ## Gauss-series evaluation of the digamma factor -/

/-- A real exponential with the `n`th Archimedean decay rate is exactly the
Fourier exponential of Suzuki's `n`th lower-half-plane mode. -/
theorem integral_suzukiWeilTest_mul_archimedeanRealExponential
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) (n : ℕ) :
    (∫ x : ℝ,
      suzukiWeilTest t z x *
        (Real.exp (-(2 * (n : ℝ) + 1 / 2) * x) : ℂ)) =
      suzukiWeilArchimedeanModeTerm t z n := by
  rw [← integral_suzukiWeilArchimedeanMode ht hz n]
  apply integral_congr_ae
  filter_upwards with x
  unfold suzukiWeilFourierIntegrand
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  unfold suzukiWeilArchimedeanFrequency suzukiWeilArchimedeanShift
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Each three-quarter-line Euler summand is continuous in the vertical
frequency. -/
theorem continuous_suzukiWeilDigammaDifferenceSummand_threeQuarter
    (n : ℕ) :
    Continuous (fun r : ℝ ↦
      suzukiWeilDigammaDifferenceSummand
        (3 / 4 + Complex.I * (r / 2)) (3 / 4) n) := by
  unfold suzukiWeilDigammaDifferenceSummand
  have hden : Continuous (fun r : ℝ ↦
      (n : ℂ) + (3 / 4 + Complex.I * (r / 2))) := by
    fun_prop
  exact continuous_const.sub (hden.inv₀ fun r hzero ↦ by
    have hre := congrArg Complex.re hzero
    simp at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)

/-- One weighted Euler summand is bounded by its shifted `3/2` coefficient
times the common integrable square-root envelope. -/
theorem norm_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand_le
    (t : ℝ) (z : ℂ) (r : ℝ) (n : ℕ) :
    ‖suzukiWeilSafeLineSpectralWeight t z r *
        (suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)‖ ≤
      suzukiWeilThreeQuarterPSeries n *
        ‖suzukiWeilSafeLineSpectralWeight t z r *
          (Real.sqrt (|r| + 1) : ℂ)‖ := by
  have hterm :=
    norm_suzukiWeilDigammaDifferenceSummand_threeQuarter_le r n
  rw [norm_mul, norm_div]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo]
  have hhalf :
      ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ / 2 ≤
        Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeries n := by
    have hnorm : 0 ≤
        ‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ := norm_nonneg _
    linarith
  calc
    ‖suzukiWeilSafeLineSpectralWeight t z r‖ *
        (‖suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n‖ / 2) ≤
      ‖suzukiWeilSafeLineSpectralWeight t z r‖ *
        (Real.sqrt (|r| + 1) * suzukiWeilThreeQuarterPSeries n) :=
      mul_le_mul_of_nonneg_left hhalf (norm_nonneg _)
    _ = suzukiWeilThreeQuarterPSeries n *
        ‖suzukiWeilSafeLineSpectralWeight t z r *
          (Real.sqrt (|r| + 1) : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      ring

/-- Every weighted Euler summand is absolutely integrable on the safe
frequency line. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) (n : ℕ) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)) := by
  have hmajor :=
    (integrable_suzukiWeilSafeLineSpectralWeight_mul_sqrtGrowth t hz).norm
      |>.const_mul (suzukiWeilThreeQuarterPSeries n)
  refine hmajor.mono' ?_ (Filter.Eventually.of_forall fun r ↦ ?_)
  · exact ((continuous_suzukiWeilSafeLineSpectralWeight t hz).mul
      ((continuous_suzukiWeilDigammaDifferenceSummand_threeQuarter n).div_const
        (2 : ℂ))).aestronglyMeasurable
  · exact
      norm_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand_le
        t z r n

/-- The integrals of the weighted Euler summands are absolutely summable,
so Gauss's series may be integrated term by term. -/
theorem summable_integral_norm_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Summable (fun n : ℕ ↦ ∫ r : ℝ,
      ‖suzukiWeilSafeLineSpectralWeight t z r *
        (suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)‖) := by
  let A : ℝ := ∫ r : ℝ,
    ‖suzukiWeilSafeLineSpectralWeight t z r *
      (Real.sqrt (|r| + 1) : ℂ)‖
  have hbase : Summable (fun n : ℕ ↦
      suzukiWeilThreeQuarterPSeries n * A) :=
    summable_suzukiWeilThreeQuarterPSeries.mul_right A
  apply hbase.of_nonneg_of_le
  · intro n
    exact integral_nonneg fun _ ↦ norm_nonneg _
  · intro n
    have hterm :=
      integrable_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
        t hz n
    have hmajor :=
      (integrable_suzukiWeilSafeLineSpectralWeight_mul_sqrtGrowth t hz).norm
        |>.const_mul (suzukiWeilThreeQuarterPSeries n)
    calc
      (∫ r : ℝ,
        ‖suzukiWeilSafeLineSpectralWeight t z r *
          (suzukiWeilDigammaDifferenceSummand
            (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)‖) ≤
          ∫ r : ℝ, suzukiWeilThreeQuarterPSeries n *
            ‖suzukiWeilSafeLineSpectralWeight t z r *
              (Real.sqrt (|r| + 1) : ℂ)‖ := by
        apply integral_mono hterm.norm hmajor
        intro r
        exact
          norm_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand_le
            t z r n
      _ = suzukiWeilThreeQuarterPSeries n * A := by
        rw [integral_const_mul]

/-- One integrated Gauss-series summand is exactly minus `2π` times the
corresponding Archimedean mode.  The constant half of the Euler difference
vanishes by the zero-mean identity. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) (n : ℕ) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)) =
      -((2 * Real.pi : ℝ) : ℂ) *
        suzukiWeilArchimedeanModeTerm t z n := by
  let a : ℝ := 2 * (n : ℝ) + 3 / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hzSafe : z ∈ suzukiXiSafeUpperHalfPlane := by
    change (1 / 2 : ℝ) < z.im
    linarith
  have hconstant : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (((n : ℂ) + 3 / 4)⁻¹ / 2)) :=
    (integrable_suzukiWeilSafeLineSpectralWeight t hz).mul_const _
  have hmoving : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I t hz ha
  have hsplit (r : ℝ) :
      suzukiWeilSafeLineSpectralWeight t z r *
          (suzukiWeilDigammaDifferenceSummand
            (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2) =
        suzukiWeilSafeLineSpectralWeight t z r *
            (((n : ℂ) + 3 / 4)⁻¹ / 2) -
          suzukiWeilSafeLineSpectralWeight t z r *
            (((a : ℂ) + Complex.I * (r : ℂ))⁻¹) := by
    have hA0 : (a : ℂ) + Complex.I * (r : ℂ) ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      exact ha.ne' hre
    have hscale :
        (n : ℂ) + (3 / 4 + Complex.I * (r / 2)) =
          ((a : ℂ) + Complex.I * (r : ℂ)) / 2 := by
      dsimp [a]
      push_cast
      ring
    have hinvScale :
        ((n : ℂ) + (3 / 4 + Complex.I * (r / 2)))⁻¹ / 2 =
          ((a : ℂ) + Complex.I * (r : ℂ))⁻¹ := by
      rw [hscale]
      field_simp [hA0]
    unfold suzukiWeilDigammaDifferenceSummand
    rw [sub_div, mul_sub, hinvScale]
  have htime :
      (∫ x : ℝ,
        suzukiWeilTest t z x *
          (Real.exp ((1 - a) * x) : ℂ)) =
        suzukiWeilArchimedeanModeTerm t z n := by
    rw [← integral_suzukiWeilTest_mul_archimedeanRealExponential ht hzSafe n]
    apply integral_congr_ae
    filter_upwards with x
    have hexponent :
        (1 - a) * x = -(2 * (n : ℝ) + 1 / 2) * x := by
      dsimp [a]
      ring
    rw [hexponent]
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (suzukiWeilDigammaDifferenceSummand
          (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)) =
        (∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            (((n : ℂ) + 3 / 4)⁻¹ / 2)) -
          ∫ r : ℝ,
            suzukiWeilSafeLineSpectralWeight t z r *
              (((a : ℂ) + Complex.I * (r : ℂ))⁻¹) := by
      rw [← integral_sub hconstant hmoving]
      exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = -(∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            (((a : ℂ) + Complex.I * (r : ℂ))⁻¹)) := by
      rw [integral_mul_const,
        integral_suzukiWeilSafeLineSpectralWeight_eq_zero ht hz]
      ring
    _ = -(((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ,
          suzukiWeilTest t z x *
            (Real.exp ((1 - a) * x) : ℂ))) := by
      rw [integral_suzukiWeilSafeLineSpectralWeight_mul_inv_add_I ht hz ha,
        integral_Ioi_exp_mul_suzukiWeilSymmetricSafeLineTest_neg ht z]
    _ = -((2 * Real.pi : ℝ) : ℂ) *
        suzukiWeilArchimedeanModeTerm t z n := by
      rw [htime]
      rw [neg_mul]

/-- The complete safe-line digamma factor is exactly minus `2π` times
Suzuki's literal positive-time Archimedean integral.  This is obtained from
Gauss's convergent Euler series by an absolutely justified exchange of its
sum with the frequency integral. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_digammaFactor
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (Complex.digamma (3 / 4 + Complex.I * (r / 2)) / 2)) =
      -((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ in Ioi 0,
          suzukiWeilArchimedeanIntegrand t z x) := by
  let F : ℕ → ℝ → ℂ := fun n r ↦
    suzukiWeilSafeLineSpectralWeight t z r *
      (suzukiWeilDigammaDifferenceSummand
        (3 / 4 + Complex.I * (r / 2)) (3 / 4) n / 2)
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    exact
      integrable_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
        t hz n
  have hFnorm : Summable (fun n : ℕ ↦ ∫ r : ℝ, ‖F n r‖) := by
    simpa only [F] using
      summable_integral_norm_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
        t hz
  have hinterchange :
      (∑' n : ℕ, ∫ r : ℝ, F n r) =
        ∫ r : ℝ, ∑' n : ℕ, F n r :=
    integral_tsum_of_summable_integral_norm hFint hFnorm
  have hsum (r : ℝ) : HasSum (fun n : ℕ ↦ F n r)
      (suzukiWeilSafeLineSpectralWeight t z r *
        ((Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
          Complex.digamma (3 / 4)) / 2)) := by
    have hdifference := hasSum_suzukiWeilDigammaDifferenceSummand
      (a := 3 / 4 + Complex.I * (r / 2)) (b := 3 / 4)
      (by norm_num) (by norm_num)
    simpa only [F] using
      (hdifference.div_const (2 : ℂ)).mul_left
        (suzukiWeilSafeLineSpectralWeight t z r)
  have hzSafe : z ∈ suzukiXiSafeUpperHalfPlane := by
    change (1 / 2 : ℝ) < z.im
    linarith
  have hdifferenceIntegral :
      (∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          ((Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
            Complex.digamma (3 / 4)) / 2)) =
        -((2 * Real.pi : ℝ) : ℂ) *
          (∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x) := by
    calc
      (∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          ((Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
            Complex.digamma (3 / 4)) / 2)) =
          ∫ r : ℝ, ∑' n : ℕ, F n r := by
        apply integral_congr_ae
        filter_upwards with r
        exact (hsum r).tsum_eq.symm
      _ = ∑' n : ℕ, ∫ r : ℝ, F n r := hinterchange.symm
      _ = ∑' n : ℕ,
          (-((2 * Real.pi : ℝ) : ℂ) *
            suzukiWeilArchimedeanModeTerm t z n) := by
        apply tsum_congr
        intro n
        exact
          integral_suzukiWeilSafeLineSpectralWeight_mul_digammaDifferenceSummand
            ht.le hz n
      _ = -((2 * Real.pi : ℝ) : ℂ) *
          (∑' n : ℕ, suzukiWeilArchimedeanModeTerm t z n) :=
        tsum_mul_left
      _ = -((2 * Real.pi : ℝ) : ℂ) *
          (∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x) := by
        rw [integral_Ioi_suzukiWeilArchimedeanIntegrand_eq_tsum ht hzSafe]
  have hfull : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (Complex.digamma (3 / 4 + Complex.I * (r / 2)) / 2)) := by
    have h :=
      (integrable_suzukiWeilSafeLineSpectralWeight_mul_digamma t hz).mul_const
        ((2 : ℂ)⁻¹)
    exact h.congr (Filter.Eventually.of_forall fun r ↦ by ring)
  have hconstant : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (Complex.digamma (3 / 4) / 2)) :=
    (integrable_suzukiWeilSafeLineSpectralWeight t hz).mul_const _
  have hdifference : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        ((Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
          Complex.digamma (3 / 4)) / 2)) := by
    exact (hfull.sub hconstant).congr
      (Filter.Eventually.of_forall fun r ↦ by
        change
          suzukiWeilSafeLineSpectralWeight t z r *
                (Complex.digamma (3 / 4 + Complex.I * (r / 2)) / 2) -
              suzukiWeilSafeLineSpectralWeight t z r *
                (Complex.digamma (3 / 4) / 2) =
            suzukiWeilSafeLineSpectralWeight t z r *
              ((Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
                Complex.digamma (3 / 4)) / 2)
        ring)
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (Complex.digamma (3 / 4 + Complex.I * (r / 2)) / 2)) =
        (∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            ((Complex.digamma (3 / 4 + Complex.I * (r / 2)) -
              Complex.digamma (3 / 4)) / 2)) +
          ∫ r : ℝ,
            suzukiWeilSafeLineSpectralWeight t z r *
              (Complex.digamma (3 / 4) / 2) := by
      rw [← integral_add hdifference hconstant]
      apply integral_congr_ae
      filter_upwards with r
      ring
    _ = -((2 * Real.pi : ℝ) : ℂ) *
          (∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x) +
        ∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            (Complex.digamma (3 / 4) / 2) := by
      rw [hdifferenceIntegral]
    _ = -((2 * Real.pi : ℝ) : ℂ) *
        (∫ x : ℝ in Ioi 0,
          suzukiWeilArchimedeanIntegrand t z x) := by
      rw [integral_mul_const,
        integral_suzukiWeilSafeLineSpectralWeight_eq_zero ht.le hz]
      ring

/-! ## Assembly of the complete horizontal safe-line factor -/

/-- The complete Archimedean factor in the safe-line completed-zeta
decomposition is `2π` times the elementary integral minus the literal
positive-time Archimedean integral. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_archimedeanTerms
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        archimedeanSpectralTerms ((r : ℂ) - Complex.I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
          ∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x) := by
  have harch :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_archimedeanTerms t hz
  have hdigamma : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (Complex.digamma (3 / 4 + Complex.I * (r / 2)) / 2)) := by
    have h :=
      (integrable_suzukiWeilSafeLineSpectralWeight_mul_digamma t hz).mul_const
        ((2 : ℂ)⁻¹)
    exact h.congr (Filter.Eventually.of_forall fun r ↦ by ring)
  have helementary : Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) -
            Complex.log Real.pi / 2)) := by
    exact (harch.sub hdigamma).congr
      (Filter.Eventually.of_forall fun r ↦ by
        change
          suzukiWeilSafeLineSpectralWeight t z r *
                archimedeanSpectralTerms ((r : ℂ) - Complex.I) -
              suzukiWeilSafeLineSpectralWeight t z r *
                (Complex.digamma
                  (3 / 4 + Complex.I * (r / 2)) / 2) =
            suzukiWeilSafeLineSpectralWeight t z r *
              (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
                (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) -
                  Complex.log Real.pi / 2)
        unfold archimedeanSpectralTerms
        rw [completedSpectralCoordinate_safeLine]
        have hsecond :
            3 / 2 + Complex.I * (r : ℂ) - 1 =
              1 / 2 + Complex.I * (r : ℂ) := by ring
        have hhalf :
            (3 / 2 + Complex.I * (r : ℂ)) / 2 =
              3 / 4 + Complex.I * (r / 2) := by ring
        rw [hsecond, hhalf]
        push_cast
        ring)
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        archimedeanSpectralTerms ((r : ℂ) - Complex.I)) =
        (∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            (((((3 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹ +
              (((1 / 2 : ℝ) : ℂ) + Complex.I * (r : ℂ))⁻¹) -
                Complex.log Real.pi / 2)) +
          ∫ r : ℝ,
            suzukiWeilSafeLineSpectralWeight t z r *
              (Complex.digamma
                (3 / 4 + Complex.I * (r / 2)) / 2) := by
      rw [← integral_add helementary hdigamma]
      apply integral_congr_ae
      filter_upwards with r
      unfold archimedeanSpectralTerms
      rw [completedSpectralCoordinate_safeLine]
      have hsecond :
          3 / 2 + Complex.I * (r : ℂ) - 1 =
            1 / 2 + Complex.I * (r : ℂ) := by ring
      have hhalf :
          (3 / 2 + Complex.I * (r : ℂ)) / 2 =
            3 / 4 + Complex.I * (r / 2) := by ring
      rw [hsecond, hhalf]
      push_cast
      ring
    _ = ((2 * Real.pi : ℝ) : ℂ) *
          (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
        ((2 * Real.pi : ℝ) : ℂ) *
          (∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x) := by
      rw [integral_suzukiWeilSafeLineSpectralWeight_mul_elementarySpectralTerms
          ht.le hz,
        integral_suzukiWeilSafeLineSpectralWeight_mul_digammaFactor ht hz]
      ring
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
          ∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x) := by ring

/-- The actual spectral-xi negative logarithmic derivative on the lower safe
line is absolutely integrable against the reflected Suzuki weight. -/
theorem integrable_suzukiWeilSafeLineSpectralWeight_mul_xiSpectralNegativeLogDerivative
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I)) := by
  have hzeta :=
    integrable_suzukiWeilSafeLineWeight_mul_negLogDeriv_riemannZeta t hz
  have harch :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_archimedeanTerms t hz
  exact (hzeta.sub harch).congr
    (Filter.Eventually.of_forall fun r ↦ by
      change
        suzukiWeilSafeLineSpectralWeight t z r *
              (-deriv riemannZeta
                  (3 / 2 + Complex.I * (r : ℂ)) /
                riemannZeta (3 / 2 + Complex.I * (r : ℂ))) -
            suzukiWeilSafeLineSpectralWeight t z r *
              archimedeanSpectralTerms ((r : ℂ) - Complex.I) =
          suzukiWeilSafeLineSpectralWeight t z r *
            xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I)
      unfold xiSpectralNegativeLogDerivative
      rw [completedSpectralCoordinate_safeLine,
        negLogDeriv_riemannZeta_safeLine_eq_xi_add_archimedean]
      ring)

/-- The complete lower safe-line spectral-xi integral is exactly `-2π`
times Suzuki's independently constructed arithmetic function. -/
theorem integral_suzukiWeilSafeLineSpectralWeight_mul_xiSpectralNegativeLogDerivative
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I)) =
      -((2 * Real.pi : ℝ) : ℂ) *
        riemannXiSuzukiArithmeticPPositive t z := by
  have hzeta :=
    integrable_suzukiWeilSafeLineWeight_mul_negLogDeriv_riemannZeta t hz
  have harch :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_archimedeanTerms t hz
  have hzSafe : z ∈ suzukiXiSafeUpperHalfPlane := by
    change (1 / 2 : ℝ) < z.im
    linarith
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        xiSpectralNegativeLogDerivative ((r : ℂ) - Complex.I)) =
        (∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            (-deriv riemannZeta
                (3 / 2 + Complex.I * (r : ℂ)) /
              riemannZeta (3 / 2 + Complex.I * (r : ℂ)))) -
          ∫ r : ℝ,
            suzukiWeilSafeLineSpectralWeight t z r *
              archimedeanSpectralTerms ((r : ℂ) - Complex.I) := by
      rw [← integral_sub hzeta harch]
      apply integral_congr_ae
      filter_upwards with r
      unfold xiSpectralNegativeLogDerivative
      rw [completedSpectralCoordinate_safeLine,
        negLogDeriv_riemannZeta_safeLine_eq_xi_add_archimedean]
      ring
    _ = ((2 * Real.pi : ℝ) : ℂ) *
          ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
            ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) -
        ((2 * Real.pi : ℝ) : ℂ) *
          ((∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
            ∫ x : ℝ in Ioi 0,
              suzukiWeilArchimedeanIntegrand t z x) := by
      rw [integral_suzukiWeilSafeLineWeight_mul_negLogDeriv_riemannZeta
          ht.le hz,
        integral_suzukiWeilSafeLineSpectralWeight_mul_archimedeanTerms ht hz]
    _ = -((2 * Real.pi : ℝ) : ℂ) *
        ((∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
          ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
            ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) -
          (∫ x : ℝ in Ioi 0,
            suzukiWeilArchimedeanIntegrand t z x)) := by ring
    _ = -((2 * Real.pi : ℝ) : ℂ) *
        riemannXiSuzukiArithmeticPPositive t z := by
      rw [suzukiWeilLocalRHS_eq_riemannXiSuzukiArithmeticPPositive
        ht hzSafe]

/-- As the symmetric horizontal truncation tends to infinity, the genuine
Suzuki--xi horizontal boundary converges to `-2π` times the arithmetic
function.  This discharges the horizontal hypothesis of the global contour
meeting theorem. -/
theorem tendsto_suzukiXiWeilHorizontalBoundaryIntegral_atTop
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im) :
    Tendsto (fun T : ℝ ↦
      suzukiXiWeilHorizontalBoundaryIntegral t z T) atTop
      (𝓝 (-((2 * Real.pi : ℝ) : ℂ) *
        riemannXiSuzukiArithmeticPPositive t z)) := by
  have hintegrable :=
    integrable_suzukiWeilSafeLineSpectralWeight_mul_xiSpectralNegativeLogDerivative
      t hz
  have hlimit := intervalIntegral_tendsto_integral hintegrable
    tendsto_neg_atTop_atBot tendsto_id
  have hhorizontal : Tendsto (fun T : ℝ ↦
      suzukiXiWeilHorizontalBoundaryIntegral t z T) atTop
      (𝓝 (∫ r : ℝ,
        suzukiWeilSafeLineSpectralWeight t z r *
          xiSpectralNegativeLogDerivative
            ((r : ℂ) - Complex.I))) := by
    exact hlimit.congr' (Filter.Eventually.of_forall fun T ↦
      (suzukiXiWeilHorizontalBoundaryIntegral_eq_safeLineWeight
        t hz T).symm)
  rw [integral_suzukiWeilSafeLineSpectralWeight_mul_xiSpectralNegativeLogDerivative
    ht hz] at hhorizontal
  exact hhorizontal

/-- The quantitatively separated zero-free truncation sequence inherits the
proved horizontal limit. -/
theorem tendsto_suzukiXiWeilHorizontalBoundaryIntegral_quantitative
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im) :
    Tendsto (fun n : ℕ ↦
      suzukiXiWeilHorizontalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n)) atTop
      (𝓝 (-((2 * Real.pi : ℝ) : ℂ) *
        riemannXiSuzukiArithmeticPPositive t z)) :=
  (tendsto_suzukiXiWeilHorizontalBoundaryIntegral_atTop ht hz).comp
    tendsto_quantitativeSpectralBoundaryTruncation_atTop

/-- After the fully evaluated horizontal limit, the arithmetic--spectral
Suzuki meeting theorem has only the quantified vertical-side limit left as
an input. -/
theorem riemannXiSuzukiArithmeticPPositive_eq_spectral_of_quantitative_vertical_limit
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im)
    (hvertical : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n))
      atTop (𝓝 0)) :
    riemannXiSuzukiArithmeticPPositive t z =
      riemannXiSuzukiSpectralP t z := by
  exact
    riemannXiSuzukiArithmeticPPositive_eq_spectral_of_quantitative_limits
      t hz
        (tendsto_suzukiXiWeilHorizontalBoundaryIntegral_quantitative ht hz)
        hvertical

end

end RiemannGaussian
