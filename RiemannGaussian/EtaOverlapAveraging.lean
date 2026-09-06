import RiemannGaussian.EtaAlternatingReal

/-!
# Quantitative freezing of the actual eta overlap

Inside a unit observation cell the slow displacement changes by at most
`epsilon`. Its mismatch is compared pointwise with the frozen channel by a
single next-boundary crossing. The complete-cell error is at most `epsilon`,
uniformly in both the frozen displacement and the observation-cell origin.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual overlap seen on a cell with a linearly drifting displacement. -/
def etaDriftingOverlapCell (epsilon a c x : ℝ) : ℝ :=
  etaUnitIntervalMismatch (a + epsilon * x) (x + c)

/-- The drifting overlap is measurable in its cell coordinate. -/
theorem measurable_etaDriftingOverlapCell (epsilon a c : ℝ) :
    Measurable (etaDriftingOverlapCell epsilon a c) := by
  change Measurable (fun x : ℝ ↦ etaUnitIntervalMismatch (a + epsilon * x) (x + c))
  have hc : Continuous (fun x : ℝ ↦ (a + epsilon * x, x + c)) := by fun_prop
  simpa only [Function.comp_def] using
    measurable_etaUnitIntervalMismatch.comp hc.measurable

/-- Every drifting overlap is nonnegative. -/
theorem etaDriftingOverlapCell_nonneg (epsilon a c x : ℝ) :
    0 ≤ etaDriftingOverlapCell epsilon a c x := etaUnitIntervalMismatch_nonneg _ _

/-- Every drifting overlap is at most one. -/
theorem etaDriftingOverlapCell_le_one (epsilon a c x : ℝ) :
    etaDriftingOverlapCell epsilon a c x ≤ 1 := etaUnitIntervalMismatch_le_one _ _

/-- The actual drifting channel is integrable on every finite interval. -/
theorem intervalIntegrable_etaDriftingOverlapCell (epsilon a c l u : ℝ) :
    IntervalIntegrable (etaDriftingOverlapCell epsilon a c) volume l u := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (measurable_etaDriftingOverlapCell epsilon a c).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    change ‖etaDriftingOverlapCell epsilon a c x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (etaDriftingOverlapCell_nonneg _ _ _ _)]
    exact etaDriftingOverlapCell_le_one _ _ _ _

/-- The frozen channel remains integrable after translating its observation cell. -/
theorem intervalIntegrable_etaUnitIntervalMismatch_translate (a c l u : ℝ) :
    IntervalIntegrable (fun x ↦ etaUnitIntervalMismatch a (x + c)) volume l u := by
  simpa only [add_sub_cancel_right] using
    (intervalIntegrable_etaUnitIntervalMismatch a (l + c) (u + c)).comp_add_right c

/-- Pointwise freezing retains the explicit next-boundary mismatch rather
than replacing the complete cell by a uniform pointwise error. -/
theorem abs_etaDriftingOverlapCell_sub_le {epsilon x : ℝ}
    (hepsilon : epsilon ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) (a c : ℝ) :
    |etaDriftingOverlapCell epsilon a c x - etaUnitIntervalMismatch a (x + c)| ≤
      etaUnitIntervalMismatch epsilon (x + c + a) := by
  unfold etaDriftingOverlapCell
  rw [abs_etaUnitIntervalMismatch_sub, add_sub_cancel_left]
  exact etaUnitIntervalMismatch_small_shift_mono (mul_nonneg hepsilon.1 hx.1)
    (mul_le_of_le_one_right hepsilon.1 hx.2) hepsilon.2 _

/-- Quantitative complete-cell averaging for the actual eta overlap.
The error is uniform in the slow displacement and the cell's origin. -/
theorem integral_etaDriftingOverlapCell_error_le {epsilon : ℝ}
    (hepsilon : epsilon ∈ Icc (0 : ℝ) 1) (a c : ℝ) :
    |(∫ x in 0..1, etaDriftingOverlapCell epsilon a c x) - etaOverlapProfile a| ≤ epsilon := by
  rw [← integral_etaUnitIntervalMismatch_translate a c,
    ← intervalIntegral.integral_sub (intervalIntegrable_etaDriftingOverlapCell epsilon a c 0 1)
      (intervalIntegrable_etaUnitIntervalMismatch_translate a c 0 1)]
  calc
    _ ≤ ∫ x in 0..1,
        |etaDriftingOverlapCell epsilon a c x - etaUnitIntervalMismatch a (x + c)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ x in 0..1, etaUnitIntervalMismatch epsilon (x + (c + a)) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        ((intervalIntegrable_etaDriftingOverlapCell epsilon a c 0 1).sub
          (intervalIntegrable_etaUnitIntervalMismatch_translate a c 0 1)).abs
        (intervalIntegrable_etaUnitIntervalMismatch_translate epsilon (c + a) 0 1)
      intro x hx
      simpa only [add_assoc] using abs_etaDriftingOverlapCell_sub_le hepsilon hx a c
    _ = etaOverlapProfile epsilon := integral_etaUnitIntervalMismatch_translate epsilon (c + a)
    _ = epsilon := etaOverlapProfile_eq_self hepsilon

/-- The averaged profile can also be frozen on the same slow cell. -/
theorem integral_etaOverlapProfile_cell_error_le {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (a : ℝ) :
    |(∫ x in 0..1, etaOverlapProfile (a + epsilon * x)) - etaOverlapProfile a| ≤ epsilon := by
  have hi : IntervalIntegrable (fun x ↦ etaOverlapProfile (a + epsilon * x)) volume 0 1 :=
    (continuous_etaOverlapProfile.comp (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [show etaOverlapProfile a = ∫ _x in (0 : ℝ)..1, etaOverlapProfile a by simp,
    ← intervalIntegral.integral_sub hi intervalIntegrable_const]
  calc
    _ ≤ ∫ x in 0..1, |etaOverlapProfile (a + epsilon * x) - etaOverlapProfile a| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ _x in (0 : ℝ)..1, epsilon := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hi.sub intervalIntegrable_const).abs intervalIntegrable_const
      intro x hx
      calc
        _ ≤ |a + epsilon * x - a| := abs_etaOverlapProfile_sub_le _ _
        _ = epsilon * x := by rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hepsilon hx.1)]
        _ ≤ epsilon := mul_le_of_le_one_right hepsilon hx.2
    _ = epsilon := by simp

/-- A complete cell of the actual overlap differs from the triangular
profile by at most twice the slow displacement scale. -/
theorem integral_etaDriftingOverlapCell_sub_profile_le {epsilon : ℝ}
    (hepsilon : epsilon ∈ Icc (0 : ℝ) 1) (a c : ℝ) :
    |(∫ x in 0..1, etaDriftingOverlapCell epsilon a c x) -
      ∫ x in 0..1, etaOverlapProfile (a + epsilon * x)| ≤ 2 * epsilon := by
  calc
    _ ≤ |(∫ x in 0..1, etaDriftingOverlapCell epsilon a c x) - etaOverlapProfile a| +
        |etaOverlapProfile a - ∫ x in 0..1, etaOverlapProfile (a + epsilon * x)| := abs_sub_le _ _ _
    _ ≤ epsilon + epsilon := by
      apply add_le_add (integral_etaDriftingOverlapCell_error_le hepsilon a c)
      rw [abs_sub_comm]
      exact integral_etaOverlapProfile_cell_error_le hepsilon.1 a
    _ = 2 * epsilon := by ring

/-- The literal overlap after the arithmetic rescaling `y = epsilon * exp t`.
The displacement remains `y`, and the fast coordinate is `y / epsilon`. -/
def etaRescaledOverlap (epsilon y : ℝ) : ℝ :=
  etaUnitIntervalMismatch y (y / epsilon)

/-- Exact connection between the literal logarithmic eta mismatch and the
rescaled arithmetic overlap, at every positive time and displacement. -/
theorem pairedEtaLogShiftMismatch_eq_rescaledOverlap {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    pairedEtaLogShiftMismatch r t =
      etaRescaledOverlap (Real.exp r - 1) ((Real.exp r - 1) * Real.exp t) := by
  rw [pairedEtaLogShiftMismatch_eq_unitIntervalMismatch ht (by linarith)]
  have he : Real.exp r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr))
  simp only [etaRescaledOverlap, mul_div_cancel_left₀ _ he]

/-- Measurability of the actual rescaled overlap. -/
theorem measurable_etaRescaledOverlap (epsilon : ℝ) :
    Measurable (etaRescaledOverlap epsilon) := by
  change Measurable (fun y : ℝ ↦ etaUnitIntervalMismatch y (y / epsilon))
  have hc : Continuous (fun y : ℝ ↦ (y, y / epsilon)) := by fun_prop
  simpa only [Function.comp_def] using measurable_etaUnitIntervalMismatch.comp hc.measurable

/-- The rescaled overlap is nonnegative. -/
theorem etaRescaledOverlap_nonneg (epsilon y : ℝ) :
    0 ≤ etaRescaledOverlap epsilon y := etaUnitIntervalMismatch_nonneg _ _

/-- The rescaled overlap is bounded by one. -/
theorem etaRescaledOverlap_le_one (epsilon y : ℝ) :
    etaRescaledOverlap epsilon y ≤ 1 := etaUnitIntervalMismatch_le_one _ _

/-- The actual overlap and its profile differ by at most one pointwise. -/
theorem abs_etaRescaledOverlap_sub_profile_le (epsilon y : ℝ) :
    |etaRescaledOverlap epsilon y - etaOverlapProfile y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [etaRescaledOverlap_nonneg epsilon y,
    etaRescaledOverlap_le_one epsilon y, etaOverlapProfile_nonneg y, etaOverlapProfile_le_one y]

/-- Genuine integrability of the rescaled overlap on finite intervals. -/
theorem intervalIntegrable_etaRescaledOverlap (epsilon a b : ℝ) :
    IntervalIntegrable (etaRescaledOverlap epsilon) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (measurable_etaRescaledOverlap epsilon).aestronglyMeasurable
  exact Eventually.of_forall fun y ↦ by
    change ‖etaRescaledOverlap epsilon y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (etaRescaledOverlap_nonneg _ _)]
    exact etaRescaledOverlap_le_one _ _

/-- Exact passage from the arithmetic rescaling to a drifting observation cell. -/
theorem etaRescaledOverlap_affine {epsilon : ℝ} (hepsilon : epsilon ≠ 0) (a x : ℝ) :
    etaRescaledOverlap epsilon (a + epsilon * x) =
      etaDriftingOverlapCell epsilon a (a / epsilon) x := by
  unfold etaRescaledOverlap etaDriftingOverlapCell
  congr 1
  field_simp
  ring

/-- On every real cell of length `epsilon`, the integral error between the
actual overlap and the triangular profile is at most `2 * epsilon ^ 2`.
The cell's origin is arbitrary; no rational scale restriction is used. -/
theorem integral_etaRescaledOverlap_cell_error_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (a : ℝ) :
    |∫ y in a..a + epsilon, etaRescaledOverlap epsilon y - etaOverlapProfile y| ≤
      2 * epsilon ^ 2 := by
  have heq := intervalIntegral.smul_integral_comp_add_mul
    (fun y ↦ etaRescaledOverlap epsilon y - etaOverlapProfile y) (a := (0 : ℝ)) (b := 1)
    epsilon a
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at heq
  rw [← heq]
  simp_rw [etaRescaledOverlap_affine hepsilon.ne']
  have hi : IntervalIntegrable (fun x ↦ etaOverlapProfile (a + epsilon * x)) volume 0 1 :=
    (continuous_etaOverlapProfile.comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_etaDriftingOverlapCell epsilon a (a / epsilon) 0 1)
    hi,
    abs_mul, abs_of_pos hepsilon]
  calc
    _ ≤ epsilon * (2 * epsilon) := mul_le_mul_of_nonneg_left
      (integral_etaDriftingOverlapCell_sub_profile_le ⟨hepsilon.le, hepsilon1⟩ a (a / epsilon))
      hepsilon.le
    _ = _ := by ring

/-- The unweighted primitive error is bounded by the interval length.
This controls the final incomplete observation cell. -/
theorem integral_etaRescaledOverlap_error_le_length (epsilon : ℝ) {a b : ℝ} (hab : a ≤ b) :
    |∫ y in a..b, etaRescaledOverlap epsilon y - etaOverlapProfile y| ≤ b - a := by
  calc
    _ ≤ ∫ y in a..b, |etaRescaledOverlap epsilon y - etaOverlapProfile y| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ _y in a..b, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hab
        ((intervalIntegrable_etaRescaledOverlap epsilon a b).sub
          (continuous_etaOverlapProfile.intervalIntegrable _ _)).abs intervalIntegrable_const
      exact fun y _ ↦ abs_etaRescaledOverlap_sub_profile_le epsilon y
    _ = b - a := by simp

/-- Summing complete real cells retains a quantitative primitive error. -/
theorem integral_etaRescaledOverlap_full_cells_error_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (a : ℝ) (n : ℕ) :
    |∫ y in a..a + n * epsilon, etaRescaledOverlap epsilon y - etaOverlapProfile y| ≤
      2 * epsilon * ((n : ℝ) * epsilon) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have heq : a + ((n + 1 : ℕ) : ℝ) * epsilon = (a + n * epsilon) + epsilon := by
        push_cast
        ring
      rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
        ((intervalIntegrable_etaRescaledOverlap epsilon a (a + n * epsilon)).sub
          (continuous_etaOverlapProfile.intervalIntegrable _ _))
        ((intervalIntegrable_etaRescaledOverlap epsilon (a + n * epsilon)
          (a + n * epsilon + epsilon)).sub (continuous_etaOverlapProfile.intervalIntegrable _ _))]
      calc
        _ ≤ |∫ y in a..a + n * epsilon, etaRescaledOverlap epsilon y - etaOverlapProfile y| +
            |∫ y in a + n * epsilon..a + n * epsilon + epsilon,
              etaRescaledOverlap epsilon y - etaOverlapProfile y| := abs_add_le _ _
        _ ≤ 2 * epsilon * ((n : ℝ) * epsilon) + 2 * epsilon ^ 2 :=
          add_le_add ih (integral_etaRescaledOverlap_cell_error_le hepsilon hepsilon1 _)
        _ = _ := by push_cast; ring

/-- A uniform primitive bound for every positive real scale at most one.
Full cells contribute `2 * epsilon * (b - a)` and the last partial cell
contributes at most `epsilon`. -/
theorem integral_etaRescaledOverlap_error_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    |∫ y in a..b, etaRescaledOverlap epsilon y - etaOverlapProfile y| ≤
      2 * epsilon * (b - a) + epsilon := by
  let n : ℕ := ⌊(b - a) / epsilon⌋₊
  have hn : (n : ℝ) * epsilon ≤ b - a := by
    exact (le_div_iff₀ hepsilon).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hepsilon.le))
  have hn' : b - a < ((n : ℝ) + 1) * epsilon := by
    exact (div_lt_iff₀ hepsilon).mp (Nat.lt_floor_add_one ((b - a) / epsilon))
  have hcb : a + n * epsilon ≤ b := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_etaRescaledOverlap epsilon a (a + n * epsilon)).sub
      (continuous_etaOverlapProfile.intervalIntegrable _ _))
    ((intervalIntegrable_etaRescaledOverlap epsilon (a + n * epsilon) b).sub
      (continuous_etaOverlapProfile.intervalIntegrable _ _))]
  calc
    _ ≤ |∫ y in a..a + n * epsilon, etaRescaledOverlap epsilon y - etaOverlapProfile y| +
        |∫ y in a + n * epsilon..b, etaRescaledOverlap epsilon y - etaOverlapProfile y| :=
      abs_add_le _ _
    _ ≤ 2 * epsilon * ((n : ℝ) * epsilon) + (b - (a + n * epsilon)) :=
      add_le_add (integral_etaRescaledOverlap_full_cells_error_le hepsilon hepsilon1 a n)
        (integral_etaRescaledOverlap_error_le_length epsilon hcb)
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * epsilon)
      linarith

end

end RiemannGaussian
