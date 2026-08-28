import RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

/-!
# Sub-square-root digamma growth on Suzuki's real axis

The completed critical-line logarithmic derivative has already been reduced
to a bounded carrier-xi term and the digamma value on
`1/4 + i r/2`.  A square-root bound for that value would leave only the
borderline nonsummable square tail after multiplication by Suzuki's
`1/|r|` screw quotient.  Here the Euler series is interpolated more sharply:
three copies of its uniform `1/d` bound and one copy of its
`|r|/d²` bound give a fourth-power estimate.  Taking fourth roots produces
growth of order `(|r|+1)^(1/4)` against a summable `d^(-5/4)` series.

This is weaker than the classical logarithmic asymptotic but already strong
enough for the eventual real-axis `L²` proof.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The shifted `5/4`-series used for the quarter-line digamma estimate. -/
def suzukiRealAxisQuarterPSeries (n : ℕ) : ℝ :=
  1 / |(n : ℝ) + 1 / 4| ^ (5 / 4 : ℝ)

/-- The shifted `5/4`-series is summable. -/
theorem summable_suzukiRealAxisQuarterPSeries :
    Summable suzukiRealAxisQuarterPSeries := by
  unfold suzukiRealAxisQuarterPSeries
  exact (Real.summable_one_div_nat_add_rpow (1 / 4) (5 / 4)).2
    (by norm_num)

/-- One Euler-series summand for the quarter-line digamma difference is
bounded by a summable `5/4`-power weight times a quarter power of height. -/
theorem norm_suzukiWeilDigammaDifferenceSummand_quarter_le
    (r : ℝ) (n : ℕ) :
    ‖suzukiWeilDigammaDifferenceSummand
        (1 / 4 + Complex.I * (r / 2)) (1 / 4) n‖ ≤
      2 * (|r| + 1) ^ (1 / 4 : ℝ) *
        suzukiRealAxisQuarterPSeries n := by
  let d : ℝ := (n : ℝ) + 1 / 4
  let u : ℝ :=
    ‖suzukiWeilDigammaDifferenceSummand
      (1 / 4 + Complex.I * (r / 2)) (1 / 4) n‖
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hb : (n : ℂ) + (1 / 4 : ℂ) = (d : ℂ) := by
    dsimp [d]
    push_cast
    ring
  have ha : (n : ℂ) + (1 / 4 + Complex.I * (r / 2)) =
      (d : ℂ) + Complex.I * (r / 2) := by
    dsimp [d]
    push_cast
    ring
  have hb0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
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
  have hhead : u ≤ 2 / d := by
    dsimp [u]
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
          (1 / 4 + Complex.I * (r / 2)) (1 / 4) n =
        (Complex.I * (r / 2)) /
          ((d : ℂ) * ((d : ℂ) + Complex.I * (r / 2))) := by
    unfold suzukiWeilDigammaDifferenceSummand
    rw [hb, ha]
    rw [inv_sub_inv hb0 ha0]
    congr 1
    ring
  have htail : u ≤ |r| / 2 / d ^ 2 := by
    dsimp [u]
    rw [hquotient, norm_div, norm_mul, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hrhalf : ‖(r : ℂ) / 2‖ = |r| / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hrhalf]
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd)
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hAre hd.le
  have huNonneg : 0 ≤ u := by
    dsimp [u]
    exact norm_nonneg _
  have hsqHead : u ^ 2 ≤ (2 / d) ^ 2 :=
    pow_le_pow_left₀ huNonneg hhead 2
  have hsqMixed : u ^ 2 ≤ |r| / d ^ 3 := by
    calc
      u ^ 2 = u * u := by ring
      _ ≤ (2 / d) * (|r| / 2 / d ^ 2) :=
        mul_le_mul hhead htail huNonneg (by positivity)
      _ = |r| / d ^ 3 := by field_simp [hd.ne']
  have hfourth : u ^ 4 ≤ 4 * |r| / d ^ 5 := by
    calc
      u ^ 4 = u ^ 2 * u ^ 2 := by ring
      _ ≤ (2 / d) ^ 2 * (|r| / d ^ 3) :=
        mul_le_mul hsqHead hsqMixed (sq_nonneg u) (by positivity)
      _ = 4 * |r| / d ^ 5 := by
        field_simp [hd.ne']
        ring
  let M : ℝ :=
    2 * (|r| + 1) ^ (1 / 4 : ℝ) / d ^ (5 / 4 : ℝ)
  have hR : 0 ≤ |r| + 1 := by positivity
  have hMNonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hRpow : ((|r| + 1) ^ (1 / 4 : ℝ)) ^ 4 = |r| + 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num
  have hdpow : (d ^ (5 / 4 : ℝ)) ^ 4 = d ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
  have hMfourth : M ^ 4 = 16 * (|r| + 1) / d ^ 5 := by
    dsimp [M]
    rw [div_pow, mul_pow, hRpow, hdpow]
    norm_num
  have hbound : u ≤ M := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hMNonneg
    rw [hMfourth]
    exact hfourth.trans (by
      apply div_le_div_of_nonneg_right
      · nlinarith [abs_nonneg r]
      · positivity)
  have hpSeries :
      suzukiRealAxisQuarterPSeries n = 1 / d ^ (5 / 4 : ℝ) := by
    unfold suzukiRealAxisQuarterPSeries
    rw [show |(n : ℝ) + 1 / 4| = d by
      rw [abs_of_pos hd]
    ]
  change u ≤
    2 * (|r| + 1) ^ (1 / 4 : ℝ) *
      suzukiRealAxisQuarterPSeries n
  calc
    u ≤ M := hbound
    _ = 2 * (|r| + 1) ^ (1 / 4 : ℝ) *
        suzukiRealAxisQuarterPSeries n := by
      dsimp [M]
      rw [hpSeries]
      ring

/-- The finite mass of the shifted `5/4`-series. -/
def suzukiRealAxisQuarterPSeriesMass : ℝ :=
  ∑' n : ℕ, suzukiRealAxisQuarterPSeries n

theorem suzukiRealAxisQuarterPSeriesMass_nonneg :
    0 ≤ suzukiRealAxisQuarterPSeriesMass := by
  unfold suzukiRealAxisQuarterPSeriesMass
  exact tsum_nonneg fun n ↦ by
    unfold suzukiRealAxisQuarterPSeries
    positivity

/-- The quarter-line digamma difference grows at most like the fourth root of
height. -/
theorem norm_digamma_quarter_vertical_sub_le_quarterPower (r : ℝ) :
    ‖Complex.digamma (1 / 4 + Complex.I * (r / 2)) -
        Complex.digamma (1 / 4)‖ ≤
      2 * (|r| + 1) ^ (1 / 4 : ℝ) *
        suzukiRealAxisQuarterPSeriesMass := by
  let D : ℕ → ℂ := fun n ↦
    suzukiWeilDigammaDifferenceSummand
      (1 / 4 + Complex.I * (r / 2)) (1 / 4) n
  have ha : 0 < (1 / 4 + Complex.I * (r / 2) : ℂ).re := by
    norm_num
  have hb : 0 < (1 / 4 : ℂ).re := by norm_num
  have hDnorm : Summable (fun n ↦ ‖D n‖) := by
    simpa only [D] using
      summable_norm_suzukiWeilDigammaDifferenceSummand ha hb
  have hmajor : Summable (fun n ↦
      2 * (|r| + 1) ^ (1 / 4 : ℝ) *
        suzukiRealAxisQuarterPSeries n) :=
    summable_suzukiRealAxisQuarterPSeries.mul_left _
  have hsum := hasSum_suzukiWeilDigammaDifferenceSummand ha hb
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, D n‖ ≤ ∑' n : ℕ, ‖D n‖ :=
      norm_tsum_le_tsum_norm hDnorm
    _ ≤ ∑' n : ℕ,
        2 * (|r| + 1) ^ (1 / 4 : ℝ) *
          suzukiRealAxisQuarterPSeries n :=
      hDnorm.tsum_le_tsum
        (fun n ↦
          norm_suzukiWeilDigammaDifferenceSummand_quarter_le r n)
        hmajor
    _ = 2 * (|r| + 1) ^ (1 / 4 : ℝ) *
        suzukiRealAxisQuarterPSeriesMass := by
      unfold suzukiRealAxisQuarterPSeriesMass
      exact summable_suzukiRealAxisQuarterPSeries.tsum_mul_left _

/-- A fixed nonnegative constant for quarter-line digamma growth. -/
def suzukiRealAxisQuarterDigammaGrowthConstant : ℝ :=
  2 * suzukiRealAxisQuarterPSeriesMass +
    ‖Complex.digamma (1 / 4)‖

theorem suzukiRealAxisQuarterDigammaGrowthConstant_nonneg :
    0 ≤ suzukiRealAxisQuarterDigammaGrowthConstant := by
  unfold suzukiRealAxisQuarterDigammaGrowthConstant
  positivity [suzukiRealAxisQuarterPSeriesMass_nonneg]

/-- The complete quarter-line digamma has a rigorous fourth-root vertical
growth bound. -/
theorem norm_digamma_quarter_vertical_le_quarterPower (r : ℝ) :
    ‖Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ ≤
      suzukiRealAxisQuarterDigammaGrowthConstant *
        (|r| + 1) ^ (1 / 4 : ℝ) := by
  have hpow : 1 ≤ (|r| + 1) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg r]) (by norm_num)
  calc
    ‖Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ =
        ‖(Complex.digamma (1 / 4 + Complex.I * (r / 2)) -
            Complex.digamma (1 / 4)) +
          Complex.digamma (1 / 4)‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.digamma (1 / 4 + Complex.I * (r / 2)) -
          Complex.digamma (1 / 4)‖ +
        ‖Complex.digamma (1 / 4)‖ := norm_add_le _ _
    _ ≤ 2 * (|r| + 1) ^ (1 / 4 : ℝ) *
          suzukiRealAxisQuarterPSeriesMass +
        ‖Complex.digamma (1 / 4)‖ := by
      gcongr
      exact norm_digamma_quarter_vertical_sub_le_quarterPower r
    _ ≤ 2 * (|r| + 1) ^ (1 / 4 : ℝ) *
          suzukiRealAxisQuarterPSeriesMass +
        (|r| + 1) ^ (1 / 4 : ℝ) *
          ‖Complex.digamma (1 / 4)‖ := by
      have hnorm : ‖Complex.digamma (1 / 4)‖ ≤
          (|r| + 1) ^ (1 / 4 : ℝ) *
            ‖Complex.digamma (1 / 4)‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpow
            (norm_nonneg (Complex.digamma (1 / 4)))
      exact add_le_add le_rfl hnorm
    _ = suzukiRealAxisQuarterDigammaGrowthConstant *
        (|r| + 1) ^ (1 / 4 : ℝ) := by
      unfold suzukiRealAxisQuarterDigammaGrowthConstant
      ring

/-- The digamma argument in the arithmetic formula is literally a point on
the quarter vertical line. -/
theorem suzukiArithmeticZetaArgument_ofReal_div_two
    (x : ℝ) :
    suzukiArithmeticZetaArgument (x : ℂ) / 2 =
      1 / 4 + Complex.I * ((-x : ℝ) / 2) := by
  unfold suzukiArithmeticZetaArgument
  push_cast
  ring

/-- Fourth-root growth of the exact digamma value occurring in Suzuki's
critical-line arithmetic formula. -/
theorem norm_digamma_suzukiArithmeticZetaArgument_ofReal_le_quarterPower
    (x : ℝ) :
    ‖Complex.digamma
        (suzukiArithmeticZetaArgument (x : ℂ) / 2)‖ ≤
      suzukiRealAxisQuarterDigammaGrowthConstant *
        (|x| + 1) ^ (1 / 4 : ℝ) := by
  rw [suzukiArithmeticZetaArgument_ofReal_div_two]
  simpa only [abs_neg] using
    norm_digamma_quarter_vertical_le_quarterPower (-x)

/-- The carrier-weighted critical-line zeta logarithmic derivative has a
sub-square-root, explicitly quarter-power growth bound. -/
theorem norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le_quarterPower
    (x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        logDeriv riemannZeta
          (suzukiArithmeticZetaArgument (x : ℂ))‖ ≤
      5 + ‖Complex.log Real.pi / 2‖ +
        (suzukiRealAxisQuarterDigammaGrowthConstant / 2) *
          (|x| + 1) ^ (1 / 4 : ℝ) := by
  have hdigamma :=
    norm_digamma_suzukiArithmeticZetaArgument_ofReal_le_quarterPower x
  calc
    ‖suzukiXiZeroCarrier (x : ℂ) *
        logDeriv riemannZeta
          (suzukiArithmeticZetaArgument (x : ℂ))‖ ≤
      5 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ :=
      norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le_digamma x
    _ = 5 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2)‖ / 2 := by
      rw [norm_div]
      norm_num
    _ ≤ 5 + ‖Complex.log Real.pi / 2‖ +
        (suzukiRealAxisQuarterDigammaGrowthConstant *
          (|x| + 1) ^ (1 / 4 : ℝ)) / 2 := by
      gcongr
    _ = 5 + ‖Complex.log Real.pi / 2‖ +
        (suzukiRealAxisQuarterDigammaGrowthConstant / 2) *
          (|x| + 1) ^ (1 / 4 : ℝ) := by
      ring

end

end RiemannGaussian
