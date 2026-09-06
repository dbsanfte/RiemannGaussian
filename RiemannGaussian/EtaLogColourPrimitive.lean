import RiemannGaussian.EtaZeroTiltWeightedReconstruction
import RiemannGaussian.EtaOverlapWallis

/-!
# The cumulative eta colour and its quantitative Wallis limit

The literal logarithmic support has signed colour `2*indicator-1`.
Integrating complete support/gap pairs gives the logarithm of a finite
Wallis product. The final partial pair retains a quantitative endpoint
error, yielding exponential convergence of the actual primitive.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Signed colour of the actual eta support, restricted to positive time
when interpreted as support minus gap. -/
def pairedEtaLogSignedColour (t : ℝ) : ℝ := 2 * pairedEtaLogIndicator t - 1

/-- The literal cumulative signed colour in logarithmic time. -/
def pairedEtaLogColourPrimitive (t : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..t, pairedEtaLogSignedColour w

/-- The actual signed colour is measurable. -/
theorem measurable_pairedEtaLogSignedColour : Measurable pairedEtaLogSignedColour :=
  measurable_pairedEtaLogIndicator.const_mul 2 |>.sub_const 1

/-- The signed colour has absolute value exactly one. -/
theorem abs_pairedEtaLogSignedColour (t : ℝ) : |pairedEtaLogSignedColour t| = 1 := by
  rcases pairedEtaLogIndicator_eq_zero_or_one t with ht | ht <;>
    norm_num [pairedEtaLogSignedColour, ht]

/-- The signed arithmetic colour is integrable on every finite interval. -/
theorem intervalIntegrable_pairedEtaLogSignedColour (a b : ℝ) :
    IntervalIntegrable pairedEtaLogSignedColour volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    measurable_pairedEtaLogSignedColour.aestronglyMeasurable
  exact Eventually.of_forall fun w ↦ by simp only [Real.norm_eq_abs, abs_pairedEtaLogSignedColour, le_refl]

/-- The actual cumulative colour is absolutely continuous on every finite interval. -/
theorem absolutelyContinuousOnInterval_pairedEtaLogColourPrimitive (b : ℝ) :
    AbsolutelyContinuousOnInterval pairedEtaLogColourPrimitive 0 b :=
  (intervalIntegrable_pairedEtaLogSignedColour 0 b).absolutelyContinuousOnInterval_intervalIntegral (by simp)

/-- The cumulative colour is continuous on the whole real line. -/
theorem continuous_pairedEtaLogColourPrimitive : Continuous pairedEtaLogColourPrimitive :=
  intervalIntegral.continuous_primitive intervalIntegrable_pairedEtaLogSignedColour 0

/-- The signed remainder after removing the evaluated Wallis endpoint constant. -/
def pairedEtaLogColourRemainder (t : ℝ) : ℝ :=
  pairedEtaLogColourPrimitive t - Real.log (Real.pi / 2)

/-- The signed Wallis remainder is continuous. -/
theorem continuous_pairedEtaLogColourRemainder : Continuous pairedEtaLogColourRemainder :=
  continuous_pairedEtaLogColourPrimitive.sub continuous_const

/-- The colour integral over one complete logarithmic cell is its signed width. -/
theorem integral_pairedEtaLogSignedColour_cell (n : ℕ) :
    (∫ w in Real.log ((n : ℝ) + 1)..Real.log ((n : ℝ) + 2), pairedEtaLogSignedColour w) =
      (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) * (2 * pairedEtaLogCellColour n - 1) := by
  have hab : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ _w in Ioc (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2)),
        2 * pairedEtaLogCellColour n - 1 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      rw [pairedEtaLogSignedColour, pairedEtaLogIndicator_eq_cellColour hw]
    _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]

/-- Complete actual support/gap pairs telescope to the finite Wallis product. -/
theorem pairedEtaLogColourPrimitive_log_odd (n : ℕ) :
    pairedEtaLogColourPrimitive (Real.log (2 * (n : ℝ) + 1)) = Real.log (Real.Wallis.W n) := by
  induction n with
  | zero => simp [pairedEtaLogColourPrimitive, Real.Wallis.W]
  | succ n ih =>
      have heven := integral_pairedEtaLogSignedColour_cell (2 * n)
      have hodd := integral_pairedEtaLogSignedColour_cell (2 * n + 1)
      norm_num [pairedEtaLogCellColour, Nat.even_add_one, add_assoc] at heven hodd
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_pairedEtaLogSignedColour 0 (Real.log (2 * (n : ℝ) + 1)))
        (intervalIntegrable_pairedEtaLogSignedColour (Real.log (2 * (n : ℝ) + 1)) (Real.log (2 * n + 3)))
      have hpair := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_pairedEtaLogSignedColour (Real.log (2 * (n : ℝ) + 1)) (Real.log (2 * n + 2)))
        (intervalIntegrable_pairedEtaLogSignedColour (Real.log (2 * (n : ℝ) + 2)) (Real.log (2 * n + 3)))
      rw [heven, hodd] at hpair
      rw [show 2 * ((n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 3 by push_cast; ring]
      change (∫ w in (0 : ℝ)..Real.log (2 * n + 3), pairedEtaLogSignedColour w) = _
      rw [← hsplit, ← hpair]
      change pairedEtaLogColourPrimitive (Real.log (2 * (n : ℝ) + 1)) + _ = _
      rw [ih, Real.Wallis.W_succ, Real.log_mul (Real.Wallis.W_pos n).ne' (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]

/-- The cumulative colour has a unit Lipschitz bound, including partial cells. -/
theorem abs_pairedEtaLogColourPrimitive_sub_le {a b : ℝ} (hab : a ≤ b) :
    |pairedEtaLogColourPrimitive b - pairedEtaLogColourPrimitive a| ≤ b - a := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_pairedEtaLogSignedColour 0 a) (intervalIntegrable_pairedEtaLogSignedColour a b)
  have hs : pairedEtaLogColourPrimitive b - pairedEtaLogColourPrimitive a =
      ∫ w in a..b, pairedEtaLogSignedColour w := by
    unfold pairedEtaLogColourPrimitive
    linarith
  rw [hs]
  calc
    _ ≤ ∫ w in a..b, |pairedEtaLogSignedColour w| := intervalIntegral.abs_integral_le_integral_abs hab
    _ = b - a := by simp only [abs_pairedEtaLogSignedColour, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- A positive logarithmic increment is at most its relative increment. -/
theorem log_add_sub_log_le_div {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) :
    Real.log (x + d) - Real.log x ≤ d / x := by
  rw [← Real.log_div (by positivity) hx.ne']
  have he := Real.log_le_sub_one_of_pos (by positivity : 0 < (x + d) / x)
  exact he.trans_eq (by field_simp; ring)

/-- Wallis' two product bounds give an explicit logarithmic endpoint error. -/
theorem log_wallis_error_le (n : ℕ) :
    |Real.log (Real.Wallis.W n) - Real.log (Real.pi / 2)| ≤ 1 / (2 * (n : ℝ) + 1) := by
  have hupper : Real.log (Real.Wallis.W n) ≤ Real.log (Real.pi / 2) :=
    Real.log_le_log (Real.Wallis.W_pos n) (Real.Wallis.W_le n)
  have hlower := Real.log_le_log
    (by positivity : 0 < ((2 : ℝ) * n + 1) / (2 * n + 2) * (Real.pi / 2)) (Real.Wallis.le_W n)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)] at hlower
  have hincr := log_add_sub_log_le_div (by positivity : 0 < 2 * (n : ℝ) + 1) (by norm_num : (0 : ℝ) ≤ 1)
  rw [show 2 * (n : ℝ) + 1 + 1 = 2 * n + 2 by ring] at hincr
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- At every real positive time the actual cumulative colour differs from
the Wallis constant by at most an explicit exponential tail. -/
theorem pairedEtaLogColourPrimitive_wallis_error_le {t : ℝ} (ht : 0 ≤ t) :
    |pairedEtaLogColourPrimitive t - Real.log (Real.pi / 2)| ≤ 9 * Real.exp (-t) := by
  let n : ℕ := ⌊(Real.exp t - 1) / 2⌋₊
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hlo : 2 * (n : ℝ) + 1 ≤ Real.exp t := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ (Real.exp t - 1) / 2)
    change (n : ℝ) ≤ (Real.exp t - 1) / 2 at hfloor
    linarith
  have hhi : Real.exp t < 2 * (n : ℝ) + 3 := by
    have hfloor := Nat.lt_floor_add_one ((Real.exp t - 1) / 2)
    change (Real.exp t - 1) / 2 < (n : ℝ) + 1 at hfloor
    linarith
  have hloglo : Real.log (2 * (n : ℝ) + 1) ≤ t := by
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hlo
  have hloghi : t ≤ Real.log (2 * (n : ℝ) + 3) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hhi.le
  have hinc : t - Real.log (2 * (n : ℝ) + 1) ≤ 2 / (2 * (n : ℝ) + 1) := by
    have hb := log_add_sub_log_le_div (by positivity : 0 < 2 * (n : ℝ) + 1) (by norm_num : (0 : ℝ) ≤ 2)
    rw [show 2 * (n : ℝ) + 1 + 2 = 2 * n + 3 by ring] at hb
    linarith
  have hratio : 1 / (2 * (n : ℝ) + 1) ≤ 3 / Real.exp t := by
    apply (div_le_div_iff₀ (by positivity) (Real.exp_pos t)).2
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  calc
    _ ≤ |pairedEtaLogColourPrimitive t - pairedEtaLogColourPrimitive (Real.log (2 * (n : ℝ) + 1))| +
        |pairedEtaLogColourPrimitive (Real.log (2 * (n : ℝ) + 1)) - Real.log (Real.pi / 2)| := abs_sub_le _ _ _
    _ ≤ 2 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 1) := by
      apply add_le_add ((abs_pairedEtaLogColourPrimitive_sub_le hloglo).trans hinc)
      rw [pairedEtaLogColourPrimitive_log_odd]
      exact log_wallis_error_le n
    _ = 3 * (1 / (2 * (n : ℝ) + 1)) := by ring
    _ ≤ 3 * (3 / Real.exp t) := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = _ := by rw [Real.exp_neg]; ring

end

end RiemannGaussian
