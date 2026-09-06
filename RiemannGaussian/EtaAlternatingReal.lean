import RiemannGaussian.EtaLogSupportShift
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The actual eta support in the positive real coordinate

The alternating logarithmic intervals become a two-periodic unit-interval
colour after `x = exp(t)`. The ceiling convention preserves the right closed
endpoints exactly. Its displacement kernel retains both colours before the
period average used in the arithmetic overlap estimate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The periodic eta colour on the real line, with right closed cells. -/
def etaUnitIntervalColour (x : ℝ) : ℝ := if Even (⌈x⌉ : ℤ) then 1 else 0

/-- Each periodic colour is zero or one. -/
theorem etaUnitIntervalColour_eq_zero_or_one (x : ℝ) :
    etaUnitIntervalColour x = 0 ∨ etaUnitIntervalColour x = 1 := by
  by_cases hx : Even (⌈x⌉ : ℤ) <;> simp [etaUnitIntervalColour, hx]

/-- The periodic colour is measurable, including at its integer endpoints. -/
theorem measurable_etaUnitIntervalColour : Measurable etaUnitIntervalColour := by
  have h : Measurable (fun n : ℤ ↦ if Even n then (1 : ℝ) else 0) :=
    measurable_of_countable _
  exact h.comp Int.measurable_ceil

/-- The colour on a right closed unit cell is the parity of its upper end. -/
theorem etaUnitIntervalColour_eq_on_cell {n : ℤ} {x : ℝ}
    (hx : x ∈ Ioc ((n : ℝ) - 1) n) :
    etaUnitIntervalColour x = if Even n then 1 else 0 := by
  simp only [etaUnitIntervalColour, Int.ceil_eq_iff.mpr hx]

/-- Translating by one exchanges the two actual interval colours. -/
theorem etaUnitIntervalColour_add_one (x : ℝ) :
    etaUnitIntervalColour (x + 1) = 1 - etaUnitIntervalColour x := by
  by_cases hx : Even (⌈x⌉ : ℤ)
  · simp [etaUnitIntervalColour, Int.ceil_add_one, hx]
  · simp [etaUnitIntervalColour, Int.ceil_add_one, hx]

/-- The real-coordinate eta colour has period two. -/
theorem etaUnitIntervalColour_periodic : Function.Periodic etaUnitIntervalColour 2 := by
  intro x
  calc
    etaUnitIntervalColour (x + 2) = etaUnitIntervalColour ((x + 1) + 1) := by congr 1; ring
    _ = 1 - (1 - etaUnitIntervalColour x) := by rw [etaUnitIntervalColour_add_one, etaUnitIntervalColour_add_one]
    _ = etaUnitIntervalColour x := by ring

/-- The actual logarithmic eta indicator is exactly its periodic real
colour after exponentiation, with no endpoint exception. -/
theorem pairedEtaLogIndicator_eq_unitIntervalColour_exp {t : ℝ} (ht : 0 < t) :
    pairedEtaLogIndicator t = etaUnitIntervalColour (Real.exp t) := by
  obtain ⟨n, hn⟩ := exists_pairedEtaLogCell ht
  have hexp : Real.exp t ∈ Ioc ((((n + 2 : ℕ) : ℤ) : ℝ) - 1) (((n + 2 : ℕ) : ℤ) : ℝ) := by
    constructor
    · have h := Real.exp_lt_exp.mpr hn.1
      rw [Real.exp_log (by positivity : (0 : ℝ) < n + 1)] at h
      norm_num at h ⊢
      linarith
    · have h := Real.exp_le_exp.mpr hn.2
      rw [Real.exp_log (by positivity : (0 : ℝ) < n + 2)] at h
      norm_num at h ⊢
      exact h
  rw [pairedEtaLogIndicator_eq_cellColour hn, etaUnitIntervalColour_eq_on_cell hexp]
  simp [pairedEtaLogCellColour]

/-- The actual two-colour mismatch at a real-coordinate shift. -/
def etaUnitIntervalMismatch (d x : ℝ) : ℝ :=
  (etaUnitIntervalColour (x + d) - etaUnitIntervalColour x) ^ 2

/-- The two-variable periodic mismatch is measurable. -/
theorem measurable_etaUnitIntervalMismatch :
    Measurable (fun p : ℝ × ℝ ↦ etaUnitIntervalMismatch p.1 p.2) := by
  exact ((measurable_etaUnitIntervalColour.comp (measurable_snd.add measurable_fst)).sub
    (measurable_etaUnitIntervalColour.comp measurable_snd)).pow_const 2

/-- Every actual periodic mismatch is nonnegative. -/
theorem etaUnitIntervalMismatch_nonneg (d x : ℝ) : 0 ≤ etaUnitIntervalMismatch d x :=
  sq_nonneg _

/-- Every actual periodic mismatch is at most one. -/
theorem etaUnitIntervalMismatch_le_one (d x : ℝ) : etaUnitIntervalMismatch d x ≤ 1 := by
  rcases etaUnitIntervalColour_eq_zero_or_one (x + d) with h | h <;>
    rcases etaUnitIntervalColour_eq_zero_or_one x with k | k <;>
    simp [etaUnitIntervalMismatch, h, k]

/-- Advancing the observation coordinate by one complements both colours
and leaves their squared mismatch unchanged. -/
theorem etaUnitIntervalMismatch_periodic (d : ℝ) :
    Function.Periodic (etaUnitIntervalMismatch d) 1 := by
  intro x
  unfold etaUnitIntervalMismatch
  rw [show x + 1 + d = (x + d) + 1 by ring,
    etaUnitIntervalColour_add_one, etaUnitIntervalColour_add_one]
  ring

/-- The mismatch is two-periodic in the displacement. -/
theorem etaUnitIntervalMismatch_shift_periodic (x : ℝ) :
    Function.Periodic (fun d ↦ etaUnitIntervalMismatch d x) 2 := by
  intro d
  change (etaUnitIntervalColour (x + (d + 2)) - etaUnitIntervalColour x) ^ 2 =
    (etaUnitIntervalColour (x + d) - etaUnitIntervalColour x) ^ 2
  rw [show x + (d + 2) = (x + d) + 2 by ring, etaUnitIntervalColour_periodic]

/-- Exact real-coordinate form of the literal logarithmic displacement. -/
theorem pairedEtaLogShiftMismatch_eq_unitIntervalMismatch {r t : ℝ}
    (ht : 0 < t) (htr : 0 < t + r) :
    pairedEtaLogShiftMismatch r t =
      etaUnitIntervalMismatch ((Real.exp r - 1) * Real.exp t) (Real.exp t) := by
  unfold pairedEtaLogShiftMismatch etaUnitIntervalMismatch
  rw [pairedEtaLogIndicator_eq_unitIntervalColour_exp htr,
    pairedEtaLogIndicator_eq_unitIntervalColour_exp ht, Real.exp_add]
  rw [show Real.exp t + (Real.exp r - 1) * Real.exp t = Real.exp t * Real.exp r by ring]

/-- Every fixed-displacement mismatch is integrable on each bounded interval. -/
theorem intervalIntegrable_etaUnitIntervalMismatch (d a b : ℝ) :
    IntervalIntegrable (etaUnitIntervalMismatch d) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((measurable_etaUnitIntervalMismatch.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun x ↦ by
    change ‖etaUnitIntervalMismatch d x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (etaUnitIntervalMismatch_nonneg d x)]
    exact etaUnitIntervalMismatch_le_one d x

/-- The actual periodic overlap averaged over one observation cell. -/
def etaOverlapProfile (d : ℝ) : ℝ := ∫ x in 0..1, etaUnitIntervalMismatch d x

/-- The period average is nonnegative. -/
theorem etaOverlapProfile_nonneg (d : ℝ) : 0 ≤ etaOverlapProfile d := by
  exact intervalIntegral.integral_nonneg (by norm_num)
    (fun x _ ↦ etaUnitIntervalMismatch_nonneg d x)

/-- The period average is at most one. -/
theorem etaOverlapProfile_le_one (d : ℝ) : etaOverlapProfile d ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_etaUnitIntervalMismatch d 0 1)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun x _ ↦ etaUnitIntervalMismatch_le_one d x)
  simpa [etaOverlapProfile] using h

/-- At a displacement between zero and one, precisely that fraction of
the observation cell changes its actual interval colour. -/
theorem etaOverlapProfile_eq_self {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1) :
    etaOverlapProfile d = d := by
  have hd0 := hd.1
  have hd1 := hd.2
  have hzero : (∫ x in 0..1 - d, etaUnitIntervalMismatch d x) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 1 - d)]
    calc
      _ = ∫ _x in Ioc (0 : ℝ) (1 - d), (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hx1 : x ∈ Ioc ((1 : ℤ) - 1 : ℝ) (1 : ℤ) := by norm_num; constructor <;> linarith [hx.1, hx.2]
        have hxd : x + d ∈ Ioc ((1 : ℤ) - 1 : ℝ) (1 : ℤ) := by norm_num; constructor <;> linarith [hx.1, hx.2]
        simp [etaUnitIntervalMismatch, etaUnitIntervalColour_eq_on_cell hx1,
          etaUnitIntervalColour_eq_on_cell hxd]
      _ = 0 := integral_zero _ _
  have hone : (∫ x in 1 - d..1, etaUnitIntervalMismatch d x) = d := by
    rw [intervalIntegral.integral_of_le (by linarith : (1 : ℝ) - d ≤ 1)]
    calc
      _ = ∫ _x in Ioc ((1 : ℝ) - d) 1, (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hx1 : x ∈ Ioc ((1 : ℤ) - 1 : ℝ) (1 : ℤ) := by norm_num; constructor <;> linarith [hx.1, hx.2]
        have hxd : x + d ∈ Ioc ((2 : ℤ) - 1 : ℝ) (2 : ℤ) := by norm_num; constructor <;> linarith [hx.1, hx.2]
        simp [etaUnitIntervalMismatch, etaUnitIntervalColour_eq_on_cell hx1,
          etaUnitIntervalColour_eq_on_cell hxd]
      _ = d := by simp [integral_const, hd.1]
  unfold etaOverlapProfile
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_etaUnitIntervalMismatch d 0 (1 - d))
    (intervalIntegrable_etaUnitIntervalMismatch d (1 - d) 1), hzero, hone, zero_add]

/-- Shifting the displacement by one complements the mismatch pointwise. -/
theorem etaUnitIntervalMismatch_shift_one (d x : ℝ) :
    etaUnitIntervalMismatch (d + 1) x = 1 - etaUnitIntervalMismatch d x := by
  unfold etaUnitIntervalMismatch
  rw [show x + (d + 1) = (x + d) + 1 by ring, etaUnitIntervalColour_add_one]
  rcases etaUnitIntervalColour_eq_zero_or_one (x + d) with h | h <;>
    rcases etaUnitIntervalColour_eq_zero_or_one x with k | k <;> simp [h, k]

/-- The overlap profile has complementary values at displacements a unit apart. -/
theorem etaOverlapProfile_add_one (d : ℝ) :
    etaOverlapProfile (d + 1) = 1 - etaOverlapProfile d := by
  simp only [etaOverlapProfile, etaUnitIntervalMismatch_shift_one]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegrable_etaUnitIntervalMismatch d 0 1)]
  simp

/-- The averaged overlap is two-periodic in its displacement. -/
theorem etaOverlapProfile_periodic : Function.Periodic etaOverlapProfile 2 := by
  intro d
  rw [show d + 2 = (d + 1) + 1 by ring, etaOverlapProfile_add_one, etaOverlapProfile_add_one]
  ring

/-- The descending half of the actual triangular overlap profile. -/
theorem etaOverlapProfile_eq_two_sub {d : ℝ} (hd : d ∈ Icc (1 : ℝ) 2) :
    etaOverlapProfile d = 2 - d := by
  have h : d - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
  rw [show d = (d - 1) + 1 by ring, etaOverlapProfile_add_one, etaOverlapProfile_eq_self h]
  ring

/-- The average over a complete observation period does not depend on its start. -/
theorem integral_etaUnitIntervalMismatch_translate (d c : ℝ) :
    (∫ x in 0..1, etaUnitIntervalMismatch d (x + c)) = etaOverlapProfile d := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [etaOverlapProfile, zero_add, add_comm 1 c] using
    (etaUnitIntervalMismatch_periodic d).intervalIntegral_add_eq c 0

/-- Reversing a displacement preserves its actual period average. -/
theorem etaOverlapProfile_neg (d : ℝ) : etaOverlapProfile (-d) = etaOverlapProfile d := by
  have heq : etaUnitIntervalMismatch (-d) = fun x ↦ etaUnitIntervalMismatch d (x + -d) := by
    funext x
    unfold etaUnitIntervalMismatch
    rw [show x + -d + d = x by ring]
    ring
  rw [etaOverlapProfile, heq, integral_etaUnitIntervalMismatch_translate]

/-- The overlap profile is bounded by the size of the displacement. -/
theorem etaOverlapProfile_le_abs (d : ℝ) : etaOverlapProfile d ≤ |d| := by
  by_cases hsmall : |d| ≤ 1
  · have habs : etaOverlapProfile d = etaOverlapProfile |d| := by
      rcases le_or_gt 0 d with hd | hd
      · rw [abs_of_nonneg hd]
      · rw [abs_of_neg hd, etaOverlapProfile_neg]
    rw [habs, etaOverlapProfile_eq_self ⟨abs_nonneg d, hsmall⟩]
  · exact (etaOverlapProfile_le_one d).trans (le_of_lt (lt_of_not_ge hsmall))

/-- For a displacement at most one, the actual mismatch records whether
the single next integer boundary has been crossed. -/
theorem etaUnitIntervalMismatch_small_shift {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    etaUnitIntervalMismatch d x = if (⌈x⌉ : ℝ) < x + d then 1 else 0 := by
  have hx : x ∈ Ioc ((⌈x⌉ : ℝ) - 1) (⌈x⌉ : ℝ) := Int.ceil_eq_iff.mp rfl
  by_cases hcross : (⌈x⌉ : ℝ) < x + d
  · have hnext : x + d ∈ Ioc (((⌈x⌉ + 1 : ℤ) : ℝ) - 1) ((⌈x⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      constructor <;> linarith [hx.2, hd.2]
    rw [if_pos hcross]
    unfold etaUnitIntervalMismatch
    rw [etaUnitIntervalColour_eq_on_cell hnext, etaUnitIntervalColour_eq_on_cell hx]
    by_cases he : Even (⌈x⌉ : ℤ) <;> simp [he]
  · have hsame : x + d ∈ Ioc ((⌈x⌉ : ℝ) - 1) (⌈x⌉ : ℝ) :=
      ⟨by linarith [hx.1, hd.1], le_of_not_gt hcross⟩
    simp only [if_neg hcross, etaUnitIntervalMismatch,
      etaUnitIntervalColour_eq_on_cell hsame, etaUnitIntervalColour_eq_on_cell hx,
      sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Up to one unit of displacement, enlarging the shift can only add a
crossing of the next boundary. -/
theorem etaUnitIntervalMismatch_small_shift_mono {d e : ℝ}
    (hd : 0 ≤ d) (hde : d ≤ e) (he : e ≤ 1) (x : ℝ) :
    etaUnitIntervalMismatch d x ≤ etaUnitIntervalMismatch e x := by
  rw [etaUnitIntervalMismatch_small_shift ⟨hd, hde.trans he⟩,
    etaUnitIntervalMismatch_small_shift ⟨hd.trans hde, he⟩]
  split_ifs <;> norm_num
  linarith

/-- Comparing two mismatch channels retains exactly the mismatch between
their shifted endpoint colours. -/
theorem abs_etaUnitIntervalMismatch_sub (d e x : ℝ) :
    |etaUnitIntervalMismatch d x - etaUnitIntervalMismatch e x| =
      etaUnitIntervalMismatch (d - e) (x + e) := by
  unfold etaUnitIntervalMismatch
  rw [show x + e + (d - e) = x + d by ring]
  rcases etaUnitIntervalColour_eq_zero_or_one (x + d) with h | h <;>
    rcases etaUnitIntervalColour_eq_zero_or_one (x + e) with k | k <;>
    rcases etaUnitIntervalColour_eq_zero_or_one x with l | l <;> norm_num [h, k, l]

/-- The averaged triangular overlap is one-Lipschitz. -/
theorem abs_etaOverlapProfile_sub_le (d e : ℝ) :
    |etaOverlapProfile d - etaOverlapProfile e| ≤ |d - e| := by
  rw [etaOverlapProfile, etaOverlapProfile,
    ← intervalIntegral.integral_sub (intervalIntegrable_etaUnitIntervalMismatch d 0 1)
      (intervalIntegrable_etaUnitIntervalMismatch e 0 1)]
  calc
    _ ≤ ∫ x in 0..1, |etaUnitIntervalMismatch d x - etaUnitIntervalMismatch e x| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ = etaOverlapProfile (d - e) := by
      simp_rw [abs_etaUnitIntervalMismatch_sub]
      exact integral_etaUnitIntervalMismatch_translate (d - e) e
    _ ≤ |d - e| := etaOverlapProfile_le_abs _

/-- Continuity of the actual overlap profile follows from its quantified
translation estimate, including at the integer corners. -/
theorem lipschitzWith_etaOverlapProfile : LipschitzWith 1 etaOverlapProfile := by
  apply LipschitzWith.of_dist_le_mul
  intro d e
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_etaOverlapProfile_sub_le d e

/-- The overlap profile is continuous on the whole real displacement line. -/
theorem continuous_etaOverlapProfile : Continuous etaOverlapProfile :=
  lipschitzWith_etaOverlapProfile.continuous

end

end RiemannGaussian
