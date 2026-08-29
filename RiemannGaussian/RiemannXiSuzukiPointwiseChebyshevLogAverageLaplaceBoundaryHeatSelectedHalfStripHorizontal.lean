import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripDecomposition
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourArchimedean
import RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# Horizontal decay on the selected spectral half-strip

This module proves that both horizontal sides of the canonical near-edge
rectangles vanish at every fixed positive heat time.  The proof extends the
quarter-line digamma estimate uniformly across the selected half-strip,
combines it with the separated-height logarithmic-derivative estimate for
`riemannXi`, and lets the Gaussian heat factor dominate the resulting
exponential response bound.  Consequently the five-term boundary-minus-bulk
frontier reduces unconditionally to its two vertical sides minus its bulk.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- A square-summable majorant for a digamma difference summand throughout
the wider real strip needed after shifting the selected half-strip. -/
theorem norm_suzukiWeilDigammaDifferenceSummand_horizontal_wide_le
    {x r : ℝ} (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 5 / 4) (n : ℕ) :
    ‖suzukiWeilDigammaDifferenceSummand
        (x + Complex.I * (r / 2))
        (1 / 4 + Complex.I * (r / 2)) n‖ ≤
      staticContourDigammaHorizontalSquareSeries n := by
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
  have hnum : ‖(((x - 1 / 4 : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hprod : d ^ 2 ≤ ‖b‖ * ‖a‖ := by
    simpa only [pow_two] using
      mul_le_mul hbNorm haNorm hd.le (norm_nonneg b)
  rw [hterm, norm_div, norm_mul]
  calc
    ‖(((x - 1 / 4 : ℝ) : ℂ))‖ / (‖b‖ * ‖a‖) ≤
        1 / d ^ 2 :=
      div_le_div₀ (by positivity) hnum (sq_pos_of_pos hd) hprod
    _ = staticContourDigammaHorizontalSquareSeries n := by
      unfold staticContourDigammaHorizontalSquareSeries
      have hdabs : |(n : ℝ) + 1 / 4| = d := by
        simpa [d] using (abs_of_pos hd)
      rw [hdabs]
      rw [Real.rpow_two]

/-- The digamma difference from the quarter vertical line is uniformly
bounded on the shifted selected half-strip. -/
theorem norm_digamma_horizontal_sub_quarter_vertical_wide_le
    {x r : ℝ} (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 5 / 4) :
    ‖Complex.digamma (x + Complex.I * (r / 2)) -
        Complex.digamma (1 / 4 + Complex.I * (r / 2))‖ ≤
      staticContourDigammaHorizontalSquareMass := by
  let D : ℕ → ℂ := fun n =>
    suzukiWeilDigammaDifferenceSummand
      (x + Complex.I * (r / 2))
      (1 / 4 + Complex.I * (r / 2)) n
  have ha : 0 < (x + Complex.I * (r / 2) : ℂ).re := by
    simpa using (show (0 : ℝ) < x by linarith)
  have hb : 0 < (1 / 4 + Complex.I * (r / 2) : ℂ).re := by norm_num
  have hDnorm : Summable (fun n => ‖D n‖) := by
    simpa only [D] using
      summable_norm_suzukiWeilDigammaDifferenceSummand ha hb
  have hmajor : Summable staticContourDigammaHorizontalSquareSeries :=
    summable_staticContourDigammaHorizontalSquareSeries
  have hsum := hasSum_suzukiWeilDigammaDifferenceSummand ha hb
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, D n‖ ≤ ∑' n : ℕ, ‖D n‖ :=
      norm_tsum_le_tsum_norm hDnorm
    _ ≤ ∑' n : ℕ, staticContourDigammaHorizontalSquareSeries n :=
      hDnorm.tsum_le_tsum
        (fun n =>
          norm_suzukiWeilDigammaDifferenceSummand_horizontal_wide_le
            hxlo hxhi n)
        hmajor
    _ = staticContourDigammaHorizontalSquareMass := by
      rfl

/-- The uniform digamma growth constant used on selected horizontal sides. -/
def selectedHalfStripDigammaGrowthConstant : ℝ :=
  suzukiRealAxisQuarterDigammaGrowthConstant +
    staticContourDigammaHorizontalSquareMass

/-- The selected-half-strip digamma growth constant is nonnegative. -/
theorem selectedHalfStripDigammaGrowthConstant_nonneg :
    0 ≤ selectedHalfStripDigammaGrowthConstant := by
  unfold selectedHalfStripDigammaGrowthConstant
  positivity [suzukiRealAxisQuarterDigammaGrowthConstant_nonneg,
    staticContourDigammaHorizontalSquareMass_nonneg]

/-- After one recurrence shift, digamma has quarter-power height growth
uniformly over the selected half-strip. -/
theorem norm_digamma_selectedHalfStrip_oneShift_le_quarterPower
    {x r : ℝ} (hxlo : 1 ≤ x) (hxhi : x ≤ 5 / 4) :
    ‖Complex.digamma (x + Complex.I * (r / 2))‖ ≤
      selectedHalfStripDigammaGrowthConstant *
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
    _ ≤ staticContourDigammaHorizontalSquareMass +
        suzukiRealAxisQuarterDigammaGrowthConstant * P := by
      exact add_le_add
        (norm_digamma_horizontal_sub_quarter_vertical_wide_le
          (by linarith) hxhi)
        (by simpa [P] using
          norm_digamma_quarter_vertical_le_quarterPower r)
    _ ≤ staticContourDigammaHorizontalSquareMass * P +
        suzukiRealAxisQuarterDigammaGrowthConstant * P := by
      have hmass : staticContourDigammaHorizontalSquareMass ≤
          staticContourDigammaHorizontalSquareMass * P := by
        calc
          staticContourDigammaHorizontalSquareMass =
              staticContourDigammaHorizontalSquareMass * 1 := by ring
          _ ≤ staticContourDigammaHorizontalSquareMass * P :=
            mul_le_mul_of_nonneg_left hP
              staticContourDigammaHorizontalSquareMass_nonneg
      exact add_le_add hmass le_rfl
    _ = selectedHalfStripDigammaGrowthConstant * P := by
      unfold selectedHalfStripDigammaGrowthConstant
      ring

/-- Digamma itself has quarter-power height growth on either selected
horizontal side, including points whose real part approaches `-1 / 2`. -/
theorem norm_digamma_selectedHalfStrip_horizontal_le_quarterPower
    {a r T : ℝ} (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0)
    (hr : |r| = T) (hT : 1 ≤ T) :
    ‖Complex.digamma
        (((a : ℂ) + (r : ℂ) * Complex.I + 1 / 2) / 2)‖ ≤
      (selectedHalfStripDigammaGrowthConstant + 2) *
        (T + 1) ^ (1 / 4 : ℝ) := by
  let w : ℂ := ((a : ℂ) + (r : ℂ) * Complex.I + 1 / 2) / 2
  let x : ℝ := w.re + 1
  have hTpos : 0 < T := by linarith
  have hr0 : r ≠ 0 := by
    intro hrzero
    rw [hrzero, abs_zero] at hr
    linarith
  have hwim : w.im = r / 2 := by
    dsimp [w]
    simp
  have hw0 : w ≠ 0 := by
    intro hwzero
    have him := congrArg Complex.im hwzero
    rw [hwim] at him
    simp only [Complex.zero_im] at him
    exact hr0 (by linarith)
  have hwNotPole : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m hwm
    have him := congrArg Complex.im hwm
    rw [hwim] at him
    simp at him
    exact hr0 (by linarith)
  have hwre : w.re = (a + 1 / 2) / 2 := by
    dsimp [w]
    simp
  have hxlo : 1 ≤ x := by
    dsimp [x]
    rw [hwre]
    linarith
  have hxhi : x ≤ 5 / 4 := by
    dsimp [x]
    rw [hwre]
    linarith
  have hwshift : w + 1 = x + Complex.I * (r / 2) := by
    apply Complex.ext
    · simp [x]
    · simp [hwim]
  have hshift : ‖Complex.digamma (w + 1)‖ ≤
      selectedHalfStripDigammaGrowthConstant *
        (T + 1) ^ (1 / 4 : ℝ) := by
    rw [hwshift]
    simpa [hr] using
      norm_digamma_selectedHalfStrip_oneShift_le_quarterPower
        hxlo hxhi (r := r)
  have hinv : ‖w⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rw [inv_le_comm₀ hwnorm (by norm_num : (0 : ℝ) < 2)]
    have himnorm := Complex.abs_im_le_norm w
    rw [hwim, abs_div, hr] at himnorm
    norm_num at himnorm ⊢
    linarith
  have hrec := Complex.digamma_apply_add_one w hwNotPole
  have hraw : ‖Complex.digamma w‖ ≤
      selectedHalfStripDigammaGrowthConstant *
          (T + 1) ^ (1 / 4 : ℝ) + 2 := by
    calc
      ‖Complex.digamma w‖ =
          ‖Complex.digamma (w + 1) - w⁻¹‖ := by
        rw [hrec]
        congr 1
        ring
      _ ≤ ‖Complex.digamma (w + 1)‖ + ‖w⁻¹‖ := norm_sub_le _ _
      _ ≤ selectedHalfStripDigammaGrowthConstant *
          (T + 1) ^ (1 / 4 : ℝ) + 2 := add_le_add hshift hinv
  let P : ℝ := (T + 1) ^ (1 / 4 : ℝ)
  have hP : 1 ≤ P := by
    dsimp [P]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  change ‖Complex.digamma w‖ ≤
    (selectedHalfStripDigammaGrowthConstant + 2) * P
  calc
    ‖Complex.digamma w‖ ≤
        selectedHalfStripDigammaGrowthConstant * P + 2 := by
      simpa [P] using hraw
    _ ≤ selectedHalfStripDigammaGrowthConstant * P + 2 * P := by
      have htwo : 2 ≤ 2 * P := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add le_rfl htwo
    _ = (selectedHalfStripDigammaGrowthConstant + 2) * P := by ring

/-- An explicit constant for the Archimedean regular-correction bound on
selected horizontal sides. -/
def selectedHalfStripRegularCorrectionExponentialConstant : ℝ :=
  5 + ‖Complex.log Real.pi‖ +
    (selectedHalfStripDigammaGrowthConstant + 2)

/-- The horizontal regular-correction constant is nonnegative. -/
theorem selectedHalfStripRegularCorrectionExponentialConstant_nonneg :
    0 ≤ selectedHalfStripRegularCorrectionExponentialConstant := by
  unfold selectedHalfStripRegularCorrectionExponentialConstant
  positivity [selectedHalfStripDigammaGrowthConstant_nonneg]

/-- The full regular correction is bounded by a fixed multiple of `exp (4*T)`
uniformly across either selected horizontal side at height magnitude `T`. -/
theorem norm_suzukiChebyshevLaplaceRegularCorrection_horizontal_le_exp
    {a r T : ℝ} (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0)
    (hr : |r| = T) (hT : 1 ≤ T) :
    ‖suzukiChebyshevLogAverageLaplaceRegularCorrection
        ((a : ℂ) + (r : ℂ) * Complex.I)‖ ≤
      selectedHalfStripRegularCorrectionExponentialConstant *
        Real.exp (4 * T) := by
  let p : ℂ := (a : ℂ) + (r : ℂ) * Complex.I
  let s : ℂ := p + 1 / 2
  let P : ℝ := (T + 1) ^ (1 / 4 : ℝ)
  let D : ℝ := selectedHalfStripDigammaGrowthConstant + 2
  let C : ℝ := selectedHalfStripRegularCorrectionExponentialConstant
  have hT0 : 0 ≤ T := by linarith
  have hsre : s.re = a + 1 / 2 := by
    simp [s, p]
  have hsim : s.im = r := by
    simp [s, p]
  have hsre0 : 0 ≤ s.re := by rw [hsre]; linarith
  have hsreHalf : s.re ≤ 1 / 2 := by rw [hsre]; linarith
  have hsNorm : ‖s‖ ≤ T + 1 := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + T := by rw [abs_of_nonneg hsre0, hsim, hr]
      _ ≤ T + 1 := by linarith
  have hinv : ‖1 / s‖ ≤ 1 := by
    rw [one_div, norm_inv]
    apply inv_le_one_of_one_le₀
    calc
      1 ≤ T := hT
      _ = |s.im| := by rw [hsim, hr]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hlogHalf : ‖Complex.log Real.pi / 2‖ ≤
      ‖Complex.log Real.pi‖ := by
    rw [norm_div]
    norm_num
  have hdigamma : ‖Complex.digamma (s / 2)‖ ≤ D * P := by
    dsimp [D, P, s, p]
    simpa [add_assoc] using
      norm_digamma_selectedHalfStrip_horizontal_le_quarterPower
        ha ha0 hr hT
  have hdigammaHalf : ‖Complex.digamma (s / 2) / 2‖ ≤ D * P := by
    calc
      ‖Complex.digamma (s / 2) / 2‖ ≤ ‖Complex.digamma (s / 2)‖ := by
        rw [norm_div]
        norm_num
      _ ≤ D * P := hdigamma
  have hlinear : ‖(4 : ℂ) * s‖ ≤ 4 * (T + 1) := by
    rw [norm_mul]
    norm_num
    linarith
  have hraw :
      ‖suzukiChebyshevLogAverageLaplaceRegularCorrection p‖ ≤
        1 + ‖Complex.log Real.pi‖ + D * P + 4 * (T + 1) := by
    unfold suzukiChebyshevLogAverageLaplaceRegularCorrection
    change ‖-(1 / s) + Complex.log Real.pi / 2 -
        Complex.digamma (s / 2) / 2 + 4 * s‖ ≤ _
    calc
      ‖-(1 / s) + Complex.log Real.pi / 2 -
          Complex.digamma (s / 2) / 2 + 4 * s‖ ≤
        ‖1 / s‖ + ‖Complex.log Real.pi / 2‖ +
          ‖Complex.digamma (s / 2) / 2‖ + ‖(4 : ℂ) * s‖ := by
        calc
          ‖-(1 / s) + Complex.log Real.pi / 2 -
              Complex.digamma (s / 2) / 2 + 4 * s‖ ≤
            ‖-(1 / s) + Complex.log Real.pi / 2 -
              Complex.digamma (s / 2) / 2‖ + ‖(4 : ℂ) * s‖ :=
              norm_add_le _ _
          _ ≤ (‖-(1 / s) + Complex.log Real.pi / 2‖ +
                ‖Complex.digamma (s / 2) / 2‖) + ‖(4 : ℂ) * s‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ ((‖-(1 / s)‖ + ‖Complex.log Real.pi / 2‖) +
                ‖Complex.digamma (s / 2) / 2‖) + ‖(4 : ℂ) * s‖ := by
            gcongr
            exact norm_add_le _ _
          _ = ‖1 / s‖ + ‖Complex.log Real.pi / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ + ‖(4 : ℂ) * s‖ := by
            rw [norm_neg]
      _ ≤ 1 + ‖Complex.log Real.pi‖ + D * P + 4 * (T + 1) := by
        gcongr
  have hPone : 1 ≤ T + 1 := by linarith
  have hPle : P ≤ T + 1 := by
    dsimp [P]
    exact Real.rpow_le_self_of_one_le hPone (by norm_num)
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity [selectedHalfStripDigammaGrowthConstant_nonneg]
  have hconstant0 : 0 ≤ 1 + ‖Complex.log Real.pi‖ := by positivity
  have hpoly :
      1 + ‖Complex.log Real.pi‖ + D * P + 4 * (T + 1) ≤
        C * (T + 1) := by
    calc
      1 + ‖Complex.log Real.pi‖ + D * P + 4 * (T + 1) ≤
          (1 + ‖Complex.log Real.pi‖) * (T + 1) +
            D * (T + 1) + 4 * (T + 1) := by
        have hconstant : 1 + ‖Complex.log Real.pi‖ ≤
            (1 + ‖Complex.log Real.pi‖) * (T + 1) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hPone hconstant0
        have hD : D * P ≤ D * (T + 1) :=
          mul_le_mul_of_nonneg_left hPle hD0
        exact add_le_add (add_le_add hconstant hD) le_rfl
      _ = C * (T + 1) := by
        dsimp [C, selectedHalfStripRegularCorrectionExponentialConstant, D]
        ring
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact selectedHalfStripRegularCorrectionExponentialConstant_nonneg
  calc
    ‖suzukiChebyshevLogAverageLaplaceRegularCorrection
        ((a : ℂ) + (r : ℂ) * Complex.I)‖ =
        ‖suzukiChebyshevLogAverageLaplaceRegularCorrection p‖ := by rfl
    _ ≤ 1 + ‖Complex.log Real.pi‖ + D * P + 4 * (T + 1) := hraw
    _ ≤ C * (T + 1) := hpoly
    _ ≤ C * Real.exp T :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp T) hC0
    _ ≤ C * Real.exp (4 * T) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact Real.exp_le_exp.mpr (by linarith)

/-- There is a uniform exponential bound for the pole-cleared arithmetic
response on the top and bottom selected sides at every quantitative
separated height. -/
theorem exists_norm_suzukiChebyshevLaplacePoleCleared_horizontal_le_exp :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ a : ℝ,
        -(1 / 2 : ℝ) < a → a ≤ 0 →
          ‖suzukiChebyshevLogAverageLaplacePoleClearedContinuation
              ((a : ℂ) +
                (quantitativeSpectralBoundaryTruncation n : ℂ) *
                  Complex.I)‖ ≤
            C * Real.exp
              (4 * quantitativeSpectralBoundaryTruncation n) ∧
          ‖suzukiChebyshevLogAverageLaplacePoleClearedContinuation
              ((a : ℂ) -
                (quantitativeSpectralBoundaryTruncation n : ℂ) *
                  Complex.I)‖ ≤
            C * Real.exp
              (4 * quantitativeSpectralBoundaryTruncation n) := by
  obtain ⟨A, hA, hgrowth⟩ := riemannXi_quadraticGrowth
  let B : ℝ := A / Real.log 2
  let Cxi : ℝ := 392 * A + 729 * B * (13 + 75 * B)
  let Creg : ℝ := selectedHalfStripRegularCorrectionExponentialConstant
  let C : ℝ := Cxi + Creg
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hCxi0 : 0 ≤ Cxi := by
    dsimp [Cxi]
    positivity
  have hCreg0 : 0 ≤ Creg := by
    dsimp [Creg]
    exact selectedHalfStripRegularCorrectionExponentialConstant_nonneg
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro n hn a ha ha0
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hT : 1 ≤ T := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hncast.trans (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hT0 : 0 ≤ T := by linarith
  have haylo : -1 ≤ -a := by linarith
  have hayhi : -a ≤ 1 := by linarith
  have haLo : -1 ≤ a := by linarith
  have haHi : a ≤ 1 := ha0.trans (by norm_num)
  have hxiTop :
      ‖logDeriv riemannXi
          ((a : ℂ) + (T : ℂ) * Complex.I + 1 / 2)‖ ≤
        Cxi * Real.exp (4 * T) := by
    calc
      ‖logDeriv riemannXi
          ((a : ℂ) + (T : ℂ) * Complex.I + 1 / 2)‖ =
        ‖logDeriv riemannXi
          (completedSpectralCoordinate
            ((T : ℂ) + (-a : ℂ) * Complex.I))‖ := by
          congr 2
          apply Complex.ext <;>
            simp [completedSpectralCoordinate, add_comm]
      _ ≤ (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
            (xiCanonicalRadius n / 4) +
          (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
            (2 / xiCanonicalRadius n +
              1 / spectralBoundarySeparation n) :=
        by
          simpa [T] using
            norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le_of_growth
              (A := A) hA hgrowth n (y := -a) haylo hayhi
      _ ≤ Cxi * Real.exp (4 * T) := by
        simpa [Cxi, B, T] using
          explicit_logDeriv_bound_le_exponential hA hgrowth n
  have hxiBottom :
      ‖logDeriv riemannXi
          ((a : ℂ) - (T : ℂ) * Complex.I + 1 / 2)‖ ≤
        Cxi * Real.exp (4 * T) := by
    let z : ℂ := (T : ℂ) + (a : ℂ) * Complex.I
    have hcoord : completedSpectralCoordinate (-z) =
        (a : ℂ) - (T : ℂ) * Complex.I + 1 / 2 := by
      dsimp [z]
      apply Complex.ext <;>
        simp [completedSpectralCoordinate, add_comm]
    calc
      ‖logDeriv riemannXi
          ((a : ℂ) - (T : ℂ) * Complex.I + 1 / 2)‖ =
        ‖logDeriv riemannXi (completedSpectralCoordinate (-z))‖ := by
          rw [hcoord]
      _ = ‖xiSpectralNegativeLogDerivative (-z)‖ := by
        exact (norm_xiSpectralNegativeLogDerivative (-z)).symm
      _ = ‖xiSpectralNegativeLogDerivative z‖ := by
        rw [xiSpectralNegativeLogDerivative_neg, norm_neg]
      _ = ‖logDeriv riemannXi (completedSpectralCoordinate z)‖ :=
        norm_xiSpectralNegativeLogDerivative z
      _ ≤ (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
            (xiCanonicalRadius n / 4) +
          (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
            (2 / xiCanonicalRadius n +
              1 / spectralBoundarySeparation n) := by
        dsimp [z]
        exact
          norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le_of_growth
            (A := A) hA hgrowth n (y := a) haLo haHi
      _ ≤ Cxi * Real.exp (4 * T) := by
        simpa [Cxi, B, T] using
          explicit_logDeriv_bound_le_exponential hA hgrowth n
  have hregTop :
      ‖suzukiChebyshevLogAverageLaplaceRegularCorrection
          ((a : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        Creg * Real.exp (4 * T) := by
    dsimp [Creg]
    exact
      norm_suzukiChebyshevLaplaceRegularCorrection_horizontal_le_exp
        ha ha0 (abs_of_nonneg hT0) hT
  have hregBottom :
      ‖suzukiChebyshevLogAverageLaplaceRegularCorrection
          ((a : ℂ) - (T : ℂ) * Complex.I)‖ ≤
        Creg * Real.exp (4 * T) := by
    dsimp [Creg]
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      norm_suzukiChebyshevLaplaceRegularCorrection_horizontal_le_exp
        ha ha0 (show |-T| = T by rw [abs_neg, abs_of_nonneg hT0]) hT
        (r := -T)
  constructor
  · unfold suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    calc
      ‖logDeriv riemannXi
            ((a : ℂ) + (T : ℂ) * Complex.I + 1 / 2) +
          suzukiChebyshevLogAverageLaplaceRegularCorrection
            ((a : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        ‖logDeriv riemannXi
          ((a : ℂ) + (T : ℂ) * Complex.I + 1 / 2)‖ +
          ‖suzukiChebyshevLogAverageLaplaceRegularCorrection
            ((a : ℂ) + (T : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ ≤ Cxi * Real.exp (4 * T) +
          Creg * Real.exp (4 * T) := add_le_add hxiTop hregTop
      _ = C * Real.exp (4 * T) := by dsimp [C]; ring
  · unfold suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    calc
      ‖logDeriv riemannXi
            ((a : ℂ) - (T : ℂ) * Complex.I + 1 / 2) +
          suzukiChebyshevLogAverageLaplaceRegularCorrection
            ((a : ℂ) - (T : ℂ) * Complex.I)‖ ≤
        ‖logDeriv riemannXi
          ((a : ℂ) - (T : ℂ) * Complex.I + 1 / 2)‖ +
          ‖suzukiChebyshevLogAverageLaplaceRegularCorrection
            ((a : ℂ) - (T : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ ≤ Cxi * Real.exp (4 * T) +
          Creg * Real.exp (4 * T) := add_le_add hxiBottom hregBottom
      _ = C * Real.exp (4 * T) := by dsimp [C]; ring

/-- A chosen uniform exponential constant for the pole-cleared response on
the selected horizontal sides. -/
noncomputable def selectedHalfStripPoleClearedHorizontalExponentialConstant : ℝ :=
  Classical.choose
    exists_norm_suzukiChebyshevLaplacePoleCleared_horizontal_le_exp

/-- The chosen pole-cleared horizontal exponential constant is nonnegative. -/
theorem selectedHalfStripPoleClearedHorizontalExponentialConstant_nonneg :
    0 ≤ selectedHalfStripPoleClearedHorizontalExponentialConstant :=
  (Classical.choose_spec
    exists_norm_suzukiChebyshevLaplacePoleCleared_horizontal_le_exp).1

/-- The pole-cleared response satisfies the chosen exponential bound on the
top selected side. -/
theorem norm_suzukiChebyshevLaplacePoleCleared_top_horizontal_le_exp
    (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0) :
    ‖suzukiChebyshevLogAverageLaplacePoleClearedContinuation
        ((a : ℂ) +
          (quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ ≤
      selectedHalfStripPoleClearedHorizontalExponentialConstant *
        Real.exp (4 * quantitativeSpectralBoundaryTruncation n) :=
  (Classical.choose_spec
    exists_norm_suzukiChebyshevLaplacePoleCleared_horizontal_le_exp).2
      n hn a ha ha0 |>.1

/-- The pole-cleared response satisfies the chosen exponential bound on the
bottom selected side. -/
theorem norm_suzukiChebyshevLaplacePoleCleared_bottom_horizontal_le_exp
    (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0) :
    ‖suzukiChebyshevLogAverageLaplacePoleClearedContinuation
        ((a : ℂ) -
          (quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ ≤
      selectedHalfStripPoleClearedHorizontalExponentialConstant *
        Real.exp (4 * quantitativeSpectralBoundaryTruncation n) :=
  (Classical.choose_spec
    exists_norm_suzukiChebyshevLaplacePoleCleared_horizontal_le_exp).2
      n hn a ha ha0 |>.2

/-- The bottom-side response bound in the additive negative-height form used
by the oriented interval integral. -/
theorem norm_suzukiChebyshevLaplacePoleCleared_bottom_add_neg_le_exp
    (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0) :
    ‖suzukiChebyshevLogAverageLaplacePoleClearedContinuation
        ((a : ℂ) +
          (-quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ ≤
      selectedHalfStripPoleClearedHorizontalExponentialConstant *
        Real.exp (4 * quantitativeSpectralBoundaryTruncation n) := by
  convert
    norm_suzukiChebyshevLaplacePoleCleared_bottom_horizontal_le_exp
      n hn ha ha0 using 1
  congr 2
  ring

/-- Across the closed selected half-strip, the moving boundary heat kernel is
bounded by its one-dimensional Gaussian in the height variable. -/
theorem norm_suzukiChebyshevLaplaceBoundaryHeatKernel_horizontal_le
    (x : ℝ) {tau a r : ℝ} (htau : 0 < tau)
    (haLo : -(1 / 2 : ℝ) ≤ a) (haHi : a ≤ 0) :
    ‖suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        ((a : ℂ) + (r : ℂ) * Complex.I)‖ ≤
      Real.exp (-tau * (x - r) ^ 2) := by
  have hcoef0 : 0 ≤ -2 * a := by linarith
  have hcoef : |-2 * a| ≤ 1 := by
    rw [abs_of_nonneg hcoef0]
    linarith
  have hextra : Real.exp (-tau * a ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a])
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [show -tau * ((x - r) ^ 2 + a ^ 2) =
      -tau * (x - r) ^ 2 + -tau * a ^ 2 by ring,
    Real.exp_add, abs_mul,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  calc
    |-2 * a| *
          (Real.exp (-tau * (x - r) ^ 2) *
            Real.exp (-tau * a ^ 2)) ≤
        1 * (Real.exp (-tau * (x - r) ^ 2) *
          Real.exp (-tau * a ^ 2)) := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ 1 * (Real.exp (-tau * (x - r) ^ 2) * 1) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hextra (Real.exp_pos _).le)
        (by norm_num)
    _ = Real.exp (-tau * (x - r) ^ 2) := by ring

/-- At fixed positive heat time, the top horizontal boundary integral tends
to zero along the quantitative separated heights. -/
theorem tendsto_separatedSelectedLaplaceTopBoundaryHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceTopBoundaryHeat x tau) atTop
      (𝓝 0) := by
  let C : ℝ := selectedHalfStripPoleClearedHorizontalExponentialConstant
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact selectedHalfStripPoleClearedHorizontalExponentialConstant_nonneg
  let M : ℝ → ℝ := fun T =>
    Real.exp (-tau * (x - T) ^ 2) * (C * Real.exp (4 * T))
  have hM : Tendsto M atTop (𝓝 0) := by
    have hbase :=
      tendsto_exp_neg_quadratic_add_linear_atTop htau x 4 0
    have hscaled : Tendsto
        (fun T : ℝ => C *
          Real.exp (-tau * (T - x) ^ 2 + 4 * T + 0))
        atTop (𝓝 0) := by
      simpa using hbase.const_mul C
    apply hscaled.congr'
    filter_upwards with T
    dsimp [M]
    rw [show -tau * (T - x) ^ 2 + 4 * T + 0 =
      -tau * (x - T) ^ 2 + 4 * T by ring,
      Real.exp_add]
    ring
  have hMnat := hM.comp
    tendsto_quantitativeSpectralBoundaryTruncation_atTop
  refine squeeze_zero_norm' ?_ hMnat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hlr : l < r :=
    selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n
  have hlEdge : -(1 / 2 : ℝ) < l :=
    (selectedLaplaceSeparatedLeftBoundary_spec n).1
  have hrEdge : r < 0 :=
    (selectedLaplaceSeparatedRightBoundary_spec n).2.1
  have hwidth : |r - l| ≤ 1 := by
    rw [abs_of_pos (sub_pos.mpr hlr)]
    linarith
  have hM0 : 0 ≤ M T := by
    dsimp [M]
    positivity
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := M T)
    (f := fun a : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
        ((a : ℂ) + (T : ℂ) * Complex.I)) (by
      intro a haInt
      rw [uIoc_of_le hlr.le] at haInt
      have haLeft : -(1 / 2 : ℝ) < a := hlEdge.trans haInt.1
      have haRight : a ≤ 0 := haInt.2.trans hrEdge.le
      unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      rw [norm_mul]
      exact mul_le_mul
        (norm_suzukiChebyshevLaplaceBoundaryHeatKernel_horizontal_le
          x htau haLeft.le haRight)
        (by
          have hpole :=
            norm_suzukiChebyshevLaplacePoleCleared_top_horizontal_le_exp
              n hn (a := a) haLeft haRight
          simpa only [C] using hpole)
        (norm_nonneg _)
        (Real.exp_pos _).le)
  change ‖separatedSelectedLaplaceTopBoundaryHeat x tau n‖ ≤
    M (quantitativeSpectralBoundaryTruncation n)
  unfold separatedSelectedLaplaceTopBoundaryHeat
    rectangularTopBoundaryIntegral
  dsimp only [l, r, T] at hIntegral ⊢
  rw [norm_neg]
  calc
    ‖∫ a : ℝ in
        selectedLaplaceSeparatedLeftBoundary n..
          selectedLaplaceSeparatedRightBoundary n,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((a : ℂ) +
            (quantitativeSpectralBoundaryTruncation n : ℂ) *
              Complex.I)‖ ≤
        M (quantitativeSpectralBoundaryTruncation n) *
          |selectedLaplaceSeparatedRightBoundary n -
            selectedLaplaceSeparatedLeftBoundary n| := by
      simpa only [Complex.ofReal_neg] using hIntegral
    _ ≤ M (quantitativeSpectralBoundaryTruncation n) * 1 :=
      mul_le_mul_of_nonneg_left hwidth hM0
    _ = M (quantitativeSpectralBoundaryTruncation n) := by ring

/-- The explicit Gaussian-times-exponential majorant for the bottom selected
side tends to zero. -/
theorem tendsto_selectedHalfStripBottomHorizontalMajorant_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripPoleClearedHorizontalExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n)))
      atTop (𝓝 0) := by
  let C : ℝ := selectedHalfStripPoleClearedHorizontalExponentialConstant
  let M : ℝ → ℝ := fun T =>
    Real.exp (-tau * (x + T) ^ 2) * (C * Real.exp (4 * T))
  have hbase :=
    tendsto_exp_neg_quadratic_add_linear_atTop htau (-x) 4 0
  have hscaled : Tendsto
      (fun T : ℝ => C *
        Real.exp (-tau * (T - (-x)) ^ 2 + 4 * T + 0))
      atTop (𝓝 0) := by
    simpa using hbase.const_mul C
  have hM : Tendsto M atTop (𝓝 0) := by
    apply hscaled.congr'
    filter_upwards with T
    dsimp [M]
    rw [show -tau * (T - (-x)) ^ 2 + 4 * T + 0 =
      -tau * (x + T) ^ 2 + 4 * T by ring,
      Real.exp_add]
    ring
  simpa [M, C, Function.comp_def] using
    hM.comp tendsto_quantitativeSpectralBoundaryTruncation_atTop

/-- A pointwise bottom-side bound for the heat-weighted pole-cleared
arithmetic response. -/
theorem norm_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_bottom_le
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) (hn : 1 ≤ n) {a : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (ha0 : a ≤ 0) :
    ‖suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
        ((a : ℂ) +
          (-quantitativeSpectralBoundaryTruncation n : ℂ) * Complex.I)‖ ≤
      Real.exp (-tau *
          (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripPoleClearedHorizontalExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
  rw [norm_mul]
  exact mul_le_mul
    (by
      have hk :=
        norm_suzukiChebyshevLaplaceBoundaryHeatKernel_horizontal_le
          x (r := -quantitativeSpectralBoundaryTruncation n)
            htau ha.le ha0
      simpa only [sub_neg_eq_add, Complex.ofReal_neg] using hk)
    (norm_suzukiChebyshevLaplacePoleCleared_bottom_add_neg_le_exp
      n hn ha ha0)
    (norm_nonneg _)
    (Real.exp_pos _).le

/-- The norm of the bottom horizontal integral is bounded by the explicit
Gaussian-times-exponential majorant. -/
theorem norm_separatedSelectedLaplaceBottomBoundaryHeat_le_majorant
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖separatedSelectedLaplaceBottomBoundaryHeat x tau n‖ ≤
      Real.exp (-tau *
          (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripPoleClearedHorizontalExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let C : ℝ := selectedHalfStripPoleClearedHorizontalExponentialConstant
  let M : ℝ := Real.exp (-tau * (x + T) ^ 2) *
    (C * Real.exp (4 * T))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact selectedHalfStripPoleClearedHorizontalExponentialConstant_nonneg
  have hlr : l < r :=
    selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n
  have hlEdge : -(1 / 2 : ℝ) < l :=
    (selectedLaplaceSeparatedLeftBoundary_spec n).1
  have hrEdge : r < 0 :=
    (selectedLaplaceSeparatedRightBoundary_spec n).2.1
  have hwidth : |r - l| ≤ 1 := by
    rw [abs_of_pos (sub_pos.mpr hlr)]
    linarith
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg hC0 (Real.exp_pos _).le)
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := M)
    (f := fun a : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
        ((a : ℂ) + (-T : ℂ) * Complex.I)) (by
      intro a haInt
      rw [uIoc_of_le hlr.le] at haInt
      have haLeft : -(1 / 2 : ℝ) < a := hlEdge.trans haInt.1
      have haRight : a ≤ 0 := haInt.2.trans hrEdge.le
      simpa only [C, T, M] using
        norm_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_bottom_le
          x htau n hn haLeft haRight)
  change ‖separatedSelectedLaplaceBottomBoundaryHeat x tau n‖ ≤
    Real.exp (-tau *
        (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
      (selectedHalfStripPoleClearedHorizontalExponentialConstant *
        Real.exp (4 * quantitativeSpectralBoundaryTruncation n))
  unfold separatedSelectedLaplaceBottomBoundaryHeat
    rectangularBottomBoundaryIntegral
  dsimp only [l, r, T, C, M] at hIntegral ⊢
  calc
    ‖∫ a : ℝ in
        selectedLaplaceSeparatedLeftBoundary n..
          selectedLaplaceSeparatedRightBoundary n,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((a : ℂ) +
            ((-quantitativeSpectralBoundaryTruncation n : ℝ) : ℂ) *
              Complex.I)‖ ≤
        (Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripPoleClearedHorizontalExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n))) *
          |selectedLaplaceSeparatedRightBoundary n -
            selectedLaplaceSeparatedLeftBoundary n| := by
      rw [Complex.ofReal_neg]
      exact hIntegral
    _ ≤ (Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripPoleClearedHorizontalExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n))) * 1 :=
      mul_le_mul_of_nonneg_left hwidth hM0
    _ = Real.exp (-tau *
          (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
        (selectedHalfStripPoleClearedHorizontalExponentialConstant *
          Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by ring

/-- Eventually, the bottom horizontal integral satisfies its vanishing
majorant along the natural-number exhaustion. -/
theorem eventually_norm_separatedSelectedLaplaceBottomBoundaryHeat_le_majorant
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    ∀ᶠ n : ℕ in atTop,
      ‖separatedSelectedLaplaceBottomBoundaryHeat x tau n‖ ≤
        Real.exp (-tau *
            (x + quantitativeSpectralBoundaryTruncation n) ^ 2) *
          (selectedHalfStripPoleClearedHorizontalExponentialConstant *
            Real.exp (4 * quantitativeSpectralBoundaryTruncation n)) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact norm_separatedSelectedLaplaceBottomBoundaryHeat_le_majorant
    x htau n hn

/-- At fixed positive heat time, the bottom horizontal boundary integral
tends to zero along the quantitative separated heights. -/
theorem tendsto_separatedSelectedLaplaceBottomBoundaryHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceBottomBoundaryHeat x tau) atTop
      (𝓝 0) := by
  exact squeeze_zero_norm'
    (eventually_norm_separatedSelectedLaplaceBottomBoundaryHeat_le_majorant
      x htau)
    (tendsto_selectedHalfStripBottomHorizontalMajorant_zero x htau)

/-- The sum of the bottom and top oriented horizontal boundary integrals. -/
def separatedSelectedLaplaceHorizontalBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceBottomBoundaryHeat x tau n +
    separatedSelectedLaplaceTopBoundaryHeat x tau n

/-- The two oriented vertical boundary integrals minus the rectangular bulk
term; this is the remaining live contour frontier after horizontal decay. -/
def separatedSelectedLaplaceVerticalSubBulkHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceRightBoundaryHeat x tau n +
    separatedSelectedLaplaceLeftBoundaryHeat x tau n -
    separatedSelectedLaplaceBoundaryHeatBulk x tau n

/-- The complete selected boundary-minus-bulk functional splits exactly into
its horizontal pair and its vertical-minus-bulk remainder. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_eq_horizontal_add_verticalSubBulk
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceBoundaryHeatFunctional x tau n =
      separatedSelectedLaplaceHorizontalBoundaryHeat x tau n +
        separatedSelectedLaplaceVerticalSubBulkHeat x tau n := by
  unfold separatedSelectedLaplaceBoundaryHeatFunctional
    separatedSelectedLaplaceHorizontalBoundaryHeat
    separatedSelectedLaplaceVerticalSubBulkHeat
  ring

/-- The combined horizontal contribution tends to zero at fixed positive
heat time. -/
theorem tendsto_separatedSelectedLaplaceHorizontalBoundaryHeat_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceHorizontalBoundaryHeat x tau) atTop
      (𝓝 0) := by
  change Tendsto
    (fun n : ℕ =>
      separatedSelectedLaplaceBottomBoundaryHeat x tau n +
        separatedSelectedLaplaceTopBoundaryHeat x tau n)
    atTop (𝓝 0)
  simpa using
    (tendsto_separatedSelectedLaplaceBottomBoundaryHeat_zero x htau).add
      (tendsto_separatedSelectedLaplaceTopBoundaryHeat_zero x htau)

/-- The vertical-minus-bulk remainder converges to `2*pi*I` times the complete
upper spectral heat detector, with no height normalization. -/
theorem tendsto_separatedSelectedLaplaceVerticalSubBulkHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceVerticalSubBulkHeat x tau) atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
  have hdiff :=
    (tendsto_separatedSelectedLaplaceBoundaryHeatFunctional x htau).sub
      (tendsto_separatedSelectedLaplaceHorizontalBoundaryHeat_zero x htau)
  have hdiff' : Tendsto
      (fun n : ℕ =>
        separatedSelectedLaplaceBoundaryHeatFunctional x tau n -
          separatedSelectedLaplaceHorizontalBoundaryHeat x tau n)
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
    simpa using hdiff
  apply hdiff'.congr'
  filter_upwards with n
  rw [separatedSelectedLaplaceBoundaryHeatFunctional_eq_horizontal_add_verticalSubBulk]
  ring

/-- The imaginary part of the vertical-minus-bulk remainder converges to
`2*pi` times the complete nonnegative detector. -/
theorem tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_im
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (separatedSelectedLaplaceVerticalSubBulkHeat x tau n).im)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit := tendsto_separatedSelectedLaplaceVerticalSubBulkHeat x htau
  have him := Complex.continuous_im.continuousAt.tendsto.comp hlimit
  convert him using 1
  · rfl
  · norm_num

/-- Vanishing of the limiting vertical-minus-bulk scalar is equivalent to RH.
This is a closure reformulation; it does not prove the vanishing premise. -/
theorem tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_im_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (separatedSelectedLaplaceVerticalSubBulkHeat x tau n).im)
      atTop (𝓝 0) ↔ RiemannHypothesis := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceVerticalSubBulkHeat_im x htau
  constructor
  · intro hzero
    have hscaled :
        2 * Real.pi * riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      tendsto_nhds_unique hlimit hzero
    have hscale : 2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (mul_eq_zero.mp hscaled).resolve_left hscale
    exact
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mp htotal
  · intro hRH
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mpr hRH
    simpa only [htotal, mul_zero] using hlimit

end

end RiemannGaussian
