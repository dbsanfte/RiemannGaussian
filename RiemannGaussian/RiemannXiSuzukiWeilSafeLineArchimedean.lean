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

end

end RiemannGaussian
