import RiemannGaussian.EtaOverlapAveraging
import RiemannGaussian.EtaOverlapWallis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Quantitative averaging of the infinite eta overlap tail

The actual rescaled mismatch is integrated against the inverse-square
arithmetic weight. An exact integration-by-parts identity retains its signed
primitive. The complete-cell estimate then controls the infinite tail for
every positive real scale at most one.
-/

open Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The signed cumulative error between the actual rescaled eta overlap
and its triangular period average. -/
def etaOverlapErrorPrimitive (epsilon a b : ℝ) : ℝ :=
  ∫ y in a..b, etaRescaledOverlap epsilon y - etaOverlapProfile y

/-- The signed primitive is absolutely continuous on every finite interval. -/
theorem absolutelyContinuousOnInterval_etaOverlapErrorPrimitive (epsilon a b : ℝ) :
    AbsolutelyContinuousOnInterval (etaOverlapErrorPrimitive epsilon a) a b := by
  exact ((intervalIntegrable_etaRescaledOverlap epsilon a b).sub
    (continuous_etaOverlapProfile.intervalIntegrable _ _))
    |>.absolutelyContinuousOnInterval_intervalIntegral (by simp)

/-- The primitive retains the uniform real-scale averaging estimate. -/
theorem abs_etaOverlapErrorPrimitive_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    |etaOverlapErrorPrimitive epsilon a b| ≤ 2 * epsilon * (b - a) + epsilon :=
  integral_etaRescaledOverlap_error_le hepsilon hepsilon1 hab

/-- The inverse-square weight is continuously differentiable away from zero. -/
theorem hasDerivAt_etaOverlapInverseSquare {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ 1 / y ^ 2) (-2 / x ^ 3) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hx) using 1 <;>
    first | rfl | (simp only [Pi.pow_apply, id_eq]; field_simp; ring)

/-- Exact signed integration by parts, before any absolute-value estimate. -/
theorem integral_etaOverlapError_div_sq_eq_primitive (epsilon : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, (etaRescaledOverlap epsilon y - etaOverlapProfile y) / y ^ 2) =
      etaOverlapErrorPrimitive epsilon a b / b ^ 2 +
        ∫ y in a..b, 2 * etaOverlapErrorPrimitive epsilon a y / y ^ 3 := by
  let E : ℝ → ℝ := fun y ↦ etaRescaledOverlap epsilon y - etaOverlapProfile y
  let C : ℝ → ℝ := etaOverlapErrorPrimitive epsilon a
  let W : ℝ → ℝ := fun y ↦ 1 / y ^ 2
  have hE : IntervalIntegrable E volume a b :=
    (intervalIntegrable_etaRescaledOverlap epsilon a b).sub
      (continuous_etaOverlapProfile.intervalIntegrable _ _)
  have hC : AbsolutelyContinuousOnInterval C a b :=
    absolutelyContinuousOnInterval_etaOverlapErrorPrimitive epsilon a b
  have hW : AbsolutelyContinuousOnInterval W a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    apply contDiffOn_const.div (contDiffOn_id.pow 2)
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact pow_ne_zero _ (ha.trans_le hx.1).ne'
  have hleft : (∫ y in a..b, W y * deriv C y) = ∫ y in a..b, E y / y ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hE.ae_hasDerivAt_integral] with y hy hyab
    rw [show deriv C y = E y from
      (hy (uIoc_subset_uIcc hyab) a (by simp)).deriv]
    simp only [W, div_eq_mul_inv, mul_comm, mul_one]
  have hright : (∫ y in a..b, deriv W y * C y) = -∫ y in a..b, 2 * C y / y ^ 3 := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hab] at hy
    change deriv (fun y : ℝ ↦ 1 / y ^ 2) y * C y = -(2 * C y / y ^ 3)
    rw [(hasDerivAt_etaOverlapInverseSquare (ha.trans_le hy.1).ne').deriv]
    ring
  have hparts := hW.integral_mul_deriv_eq_deriv_mul hC
  have hCa : C a = 0 := by simp [C, etaOverlapErrorPrimitive]
  rw [hleft, hright, hCa] at hparts
  simpa only [E, C, W, mul_zero, sub_zero, sub_neg_eq_add, one_div,
    div_eq_mul_inv, mul_comm, mul_one] using hparts

/-- Integration of the positive envelope for the weighted primitive. -/
theorem integral_etaOverlapPrimitiveEnvelope {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (epsilon : ℝ) :
    (∫ y in a..b, 2 * (2 * epsilon * y + epsilon) / y ^ 3) =
      4 * epsilon / a + epsilon / a ^ 2 - (4 * epsilon / b + epsilon / b ^ 2) := by
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hab] at hy
    exact (ha.trans_le hy.1).ne'
  have hi : IntervalIntegrable (fun y : ℝ ↦ 2 * (2 * epsilon * y + epsilon) / y ^ 3) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuous_const.mul ((continuous_const.mul continuous_id).add continuous_const)).continuousOn.div
      (continuous_id.pow 3).continuousOn (fun y hy ↦ pow_ne_zero _ (hn y hy))
  have hd (y : ℝ) (hy : y ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ ↦ -(4 * epsilon / y + epsilon / y ^ 2))
        (2 * (2 * epsilon * y + epsilon) / y ^ 3) y := by
    convert (((hasDerivAt_const y (4 * epsilon)).div (hasDerivAt_id y) (hn y hy)).add
      ((hasDerivAt_const y epsilon).div ((hasDerivAt_id y).pow 2) (pow_ne_zero _ (hn y hy)))).neg
      using 1 <;> first | rfl | (simp only [Pi.pow_apply, id_eq]; field_simp [hn y hy]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Quantitative inverse-square averaging on a finite interval, with a
bound independent of its upper endpoint. -/
theorem integral_etaOverlapError_div_sq_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    |∫ y in a..b, (etaRescaledOverlap epsilon y - etaOverlapProfile y) / y ^ 2| ≤
      4 * epsilon / a + epsilon / a ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hbound (y : ℝ) (hy : a ≤ y) :
      |etaOverlapErrorPrimitive epsilon a y| ≤ 2 * epsilon * y + epsilon := by
    exact (abs_etaOverlapErrorPrimitive_le hepsilon hepsilon1 hy).trans
      (by nlinarith)
  have hc := (absolutelyContinuousOnInterval_etaOverlapErrorPrimitive epsilon a b).continuousOn
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hab] at hy
    exact (ha.trans_le hy.1).ne'
  have hi : IntervalIntegrable (fun y ↦ 2 * etaOverlapErrorPrimitive epsilon a y / y ^ 3) volume a b := by
    exact ((continuousOn_const.mul hc).div (continuous_id.pow 3).continuousOn
      (fun y hy ↦ pow_ne_zero _ (hn y hy))).intervalIntegrable
  have hj : IntervalIntegrable (fun y : ℝ ↦ 2 * (2 * epsilon * y + epsilon) / y ^ 3) volume a b := by
    exact ((continuous_const.mul ((continuous_const.mul continuous_id).add continuous_const)).continuousOn.div
      (continuous_id.pow 3).continuousOn (fun y hy ↦ pow_ne_zero _ (hn y hy))).intervalIntegrable
  rw [integral_etaOverlapError_div_sq_eq_primitive epsilon ha hab]
  calc
    _ ≤ |etaOverlapErrorPrimitive epsilon a b / b ^ 2| +
        |∫ y in a..b, 2 * etaOverlapErrorPrimitive epsilon a y / y ^ 3| := abs_add_le _ _
    _ ≤ (2 * epsilon * b + epsilon) / b ^ 2 +
        ∫ y in a..b, 2 * (2 * epsilon * y + epsilon) / y ^ 3 := by
      apply add_le_add
      · rw [abs_div, abs_of_nonneg (sq_nonneg b)]
        exact div_le_div_of_nonneg_right (hbound b hab) (sq_nonneg b)
      · apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
        apply intervalIntegral.integral_mono_on hab hi.abs hj
        intro y hy
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos (pow_pos (ha.trans_le hy.1) 3)]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound y hy.1) (by norm_num))
          (pow_pos (ha.trans_le hy.1) 3).le
    _ = 4 * epsilon / a + epsilon / a ^ 2 - 2 * epsilon / b := by
      rw [integral_etaOverlapPrimitiveEnvelope ha hab]
      field_simp
      ring
    _ ≤ _ := sub_le_self _ (by positivity)

/-- Genuine integrability of the signed inverse-square error on the
infinite arithmetic tail. -/
theorem integrableOn_etaOverlapError_div_sq (epsilon : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ ↦ (etaRescaledOverlap epsilon y - etaOverlapProfile y) / y ^ 2) (Ioi a) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  apply hi.mono' (((measurable_etaRescaledOverlap epsilon).sub
    continuous_etaOverlapProfile.measurable).div (continuous_id.pow 2).measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := ha.trans hy
  change ‖(etaRescaledOverlap epsilon y - etaOverlapProfile y) / y ^ 2‖ ≤ y ^ (-2 : ℝ)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg y),
    Real.rpow_neg hypos.le, Real.rpow_two, ← one_div]
  exact div_le_div_of_nonneg_right (abs_etaRescaledOverlap_sub_profile_le epsilon y) (sq_nonneg y)

/-- The actual infinite overlap tail converges to its triangular average
with an explicit bound valid at every real scale in `(0,1]`. -/
theorem integral_Ioi_etaOverlapError_div_sq_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) {a : ℝ} (ha : 0 < a) :
    |∫ y in Ioi a, (etaRescaledOverlap epsilon y - etaOverlapProfile y) / y ^ 2| ≤
      4 * epsilon / a + epsilon / a ^ 2 := by
  have ht := intervalIntegral_tendsto_integral_Ioi a
    (integrableOn_etaOverlapError_div_sq epsilon ha) (tendsto_id : Tendsto (fun b : ℝ ↦ b) atTop atTop)
  apply le_of_tendsto ht.abs
  filter_upwards [eventually_ge_atTop a] with b hb
  exact integral_etaOverlapError_div_sq_le hepsilon hepsilon1 ha hb

/-- The literal rescaled overlap itself has an integrable inverse-square
tail; the signed error integral never relies on totalized integration. -/
theorem integrableOn_etaRescaledOverlap_div_sq (epsilon : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ ↦ etaRescaledOverlap epsilon y / y ^ 2) (Ioi a) := by
  apply ((integrableOn_etaOverlapError_div_sq epsilon ha).add
    (integrableOn_etaOverlapProfile_div_sq ha)).congr_fun _ measurableSet_Ioi
  intro y _
  change (etaRescaledOverlap epsilon y - etaOverlapProfile y) / y ^ 2 +
    etaOverlapProfile y / y ^ 2 = etaRescaledOverlap epsilon y / y ^ 2
  ring

/-- Quantitative evaluation of the actual arithmetic tail at every lower
cutoff in `(0,1]`, with the logarithmic cutoff term kept explicit. -/
theorem integral_Ioi_etaRescaledOverlap_div_sq_error_le {epsilon a : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) :
    |(∫ y in Ioi a, etaRescaledOverlap epsilon y / y ^ 2) -
      (1 - Real.log (Real.pi / 2) - Real.log a)| ≤ 4 * epsilon / a + epsilon / a ^ 2 := by
  rw [← integral_Ioi_etaOverlapProfile_div_sq_of_le_one ha ha1,
    ← integral_sub (integrableOn_etaRescaledOverlap_div_sq epsilon ha)
      (integrableOn_etaOverlapProfile_div_sq ha)]
  simp_rw [← sub_div]
  exact integral_Ioi_etaOverlapError_div_sq_le hepsilon hepsilon1 ha

/-- The unit-cutoff arithmetic tail has the explicit Wallis value up to
an error of at most five times the real overlap scale. -/
theorem integral_Ioi_one_etaRescaledOverlap_div_sq_error_le {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    |(∫ y in Ioi (1 : ℝ), etaRescaledOverlap epsilon y / y ^ 2) -
      (1 - Real.log (Real.pi / 2))| ≤ 5 * epsilon := by
  simpa [show 4 * epsilon + epsilon = 5 * epsilon by ring] using
    integral_Ioi_etaRescaledOverlap_div_sq_error_le hepsilon hepsilon1 zero_lt_one le_rfl

end

end RiemannGaussian
