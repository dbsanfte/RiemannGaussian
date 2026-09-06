import RiemannGaussian.EtaLogEndpointControl

/-!
# The actual eta finite part at the two fixed logarithmic endpoints

The arithmetic cutoff cancels between the moving integral and the Wallis
tail. The remaining error is uniform in the complex test bound and
Lipschitz constant, and retains the offset `log(1/r)-R` needed by heat scaling.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exact cancellation of the two moving logarithmic cutoff coefficients. -/
theorem pairedEtaShiftBoundaryCutoff_endpoint_cancel {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) (R : ℝ) :
    (Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) - R) +
      (1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r)) -
      (1 - Real.log (Real.pi / 2) + (Real.log (1 / r) - R)) =
      (Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) - Real.log (pairedEtaShiftBoundaryCutoff r)) -
        Real.log ((Real.exp r - 1) / r) := by
  have he : Real.exp r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr))
  have hM : (pairedEtaShiftBoundaryCutoff r : ℝ) ≠ 0 := by
    have h := (pairedEtaShiftBoundaryCutoff_bounds hr hrsmall).1
    exact_mod_cast (show pairedEtaShiftBoundaryCutoff r ≠ 0 by omega)
  rw [Real.log_mul he hM, Real.log_div he hr.ne', Real.log_div one_ne_zero hr.ne', Real.log_one]
  ring

/-- Quantitative complex finite part at the fixed endpoints zero and one,
with its heat-scale offset retained and its harmonic coefficient explicit. -/
theorem pairedEtaWeightedMismatch_exp_endpoint_error_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - R • (∫ z in 0..1, F z) -
      ((harmonic (pairedEtaShiftBoundaryCutoff r) : ℝ) - 1 -
        Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1)) • F 0 -
      (1 - Real.log (Real.pi / 2) + (Real.log (1 / r) - R)) • F 1‖ ≤
      69 * r * B + ((K : ℝ) / R) * (38 + 6 * (Real.log (1 / r) - R) ^ 2) := by
  let M := pairedEtaShiftBoundaryCutoff r
  let L : ℝ := Real.log (M : ℝ)
  let U : ℝ := Real.log ((M : ℝ) + 1)
  let d : ℝ := Real.log (1 / r) - R
  let A : ℂ := ((harmonic M : ℝ) - 1 - U) • F 0
  let C : ℝ := 1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * M)
  let Q : ℝ := 1 - Real.log (Real.pi / 2) + d
  let I : ℂ := ∫ t in 0..U, F (t / R)
  let J : ℂ := R • (∫ z in 0..1, F z)
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have hC := pairedEtaShiftBoundaryCutoff_wallis_bounds hr hrsmall
  change C ∈ Icc (0 : ℝ) 4 at hC
  have hL := pairedEtaShiftBoundaryCutoff_log_distance_le hr hrsmall R
  change |L - R| ≤ |d| + 4 at hL
  have hU := pairedEtaShiftBoundaryCutoff_log_top_distance_le hr hrsmall R
  change |U - R| ≤ |d| + 3 at hU
  have hcut := pairedEtaWeightedMismatch_cutoff_endpoint_error_le hr hrsmall hR hF hB
  change ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - I - A - C • F (L / R)‖ ≤
    8 * (K : ℝ) / R + 32 * (Real.exp r - 1) * B at hcut
  have hI : ‖I - J - (U - R) • F 1‖ ≤ ((K : ℝ) / R) * (|d| + 3) ^ 2 := by
    have hc : Continuous (fun t : ℝ ↦ F (t / R)) := hF.continuous.comp (continuous_id.div_const R)
    have hscale : (∫ t in 0..R, F (t / R)) = J := by
      rw [intervalIntegral.integral_comp_div F hR.ne', zero_div, div_self hR.ne']
    have hid : I - J = ∫ t in R..U, F (t / R) := by
      rw [← hscale]
      exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    rw [hid]
    exact (integral_etaSlowTest_endpoint_error_le hR U hF).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hU 2) (by positivity))
  have htest : ‖C • (F (L / R) - F 1)‖ ≤ (4 * (K : ℝ) / R) * (|d| + 4) := by
    have hLip : ‖F (L / R) - F 1‖ ≤ ((K : ℝ) / R) * |L - R| := by
      have h := hF.dist_le_mul (L / R) 1
      simp only [dist_eq_norm, Real.norm_eq_abs] at h
      rw [show L / R - 1 = (L - R) / R by field_simp, abs_div, abs_of_pos hR] at h
      convert h using 1
      ring
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC.1]
    calc
      _ ≤ 4 * (((K : ℝ) / R) * |L - R|) := mul_le_mul hC.2 hLip (norm_nonneg _) (by norm_num)
      _ ≤ 4 * (((K : ℝ) / R) * (|d| + 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL (by positivity)) (by norm_num)
      _ = _ := by ring
  have hcoeff : ‖((U - R) + C - Q) • F 1‖ ≤ 5 * r * B := by
    have hs := pairedEtaShiftBoundaryCutoff_log_step_bounds hr hrsmall
    have he := etaExpDisplacement_log_ratio_bounds hr (by linarith)
    have hid : (U - R) + C - Q = (U - L) - Real.log ((Real.exp r - 1) / r) :=
      pairedEtaShiftBoundaryCutoff_endpoint_cancel hr hrsmall R
    have habs : |(U - R) + C - Q| ≤ 5 * r := by
      rw [hid, abs_le]
      change U - L ∈ Icc (0 : ℝ) (4 * r) at hs
      constructor <;> linarith [hs.1, hs.2, he.1, he.2]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul habs (hB 1) (norm_nonneg _) (by positivity)
  have he2 : Real.exp r - 1 ≤ 2 * r := by
    have hratio := etaExpDisplacement_ratio_error_bounds hr (by linarith)
    have h := (div_le_iff₀ hr).mp (show (Real.exp r - 1) / r ≤ r + 1 by linarith [hratio.2])
    nlinarith
  change ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - J - A - Q • F 1‖ ≤
    69 * r * B + ((K : ℝ) / R) * (38 + 6 * d ^ 2)
  have hid : (Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - J - A - Q • F 1 =
      (((Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - I - A - C • F (L / R)) +
        (I - J - (U - R) • F 1)) + C • (F (L / R) - F 1) + ((U - R) + C - Q) • F 1 := by
    simp only [smul_sub, add_smul, sub_smul]
    abel
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  apply (add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)).trans
  calc
    _ ≤ ((8 * (K : ℝ) / R + 32 * (Real.exp r - 1) * B) +
        ((K : ℝ) / R) * (|d| + 3) ^ 2) + (4 * (K : ℝ) / R) * (|d| + 4) + 5 * r * B :=
      add_le_add (add_le_add (add_le_add hcut hI) htest) hcoeff
    _ = (32 * (Real.exp r - 1) + 5 * r) * B +
        ((K : ℝ) / R) * (8 + (|d| + 3) ^ 2 + 4 * (|d| + 4)) := by ring
    _ ≤ 69 * r * B + ((K : ℝ) / R) * (38 + 6 * d ^ 2) := by
      apply add_le_add (mul_le_mul_of_nonneg_right (by linarith) hB0)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_abs d, sq_nonneg (|d| - 1)]

/-- The fixed-endpoint finite part at the original displacement scale has
an explicit remainder, uniform in the complex test and scale offset. -/
theorem pairedEtaWeightedMismatch_endpoint_error_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖r⁻¹ • pairedEtaWeightedMismatch r R F - R • (∫ z in 0..1, F z) -
      ((harmonic (pairedEtaShiftBoundaryCutoff r) : ℝ) - 1 -
        Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1)) • F 0 -
      (1 - Real.log (Real.pi / 2) + (Real.log (1 / r) - R)) • F 1‖ ≤
      r * B * (140 + R + |Real.log (1 / r) - R|) +
        ((K : ℝ) / R) * (76 + 12 * (Real.log (1 / r) - R) ^ 2) := by
  let M := pairedEtaShiftBoundaryCutoff r
  let d : ℝ := Real.log (1 / r) - R
  let A : ℝ := (harmonic M : ℝ) - 1 - Real.log ((M : ℝ) + 1)
  let Q : ℝ := 1 - Real.log (Real.pi / 2) + d
  let J : ℂ := ∫ z in 0..1, F z
  let Y : ℂ := R • J + A • F 0 + Q • F 1
  let q : ℝ := (Real.exp r - 1) / r
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have he : Real.exp r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hr))
  have hratio := etaExpDisplacement_ratio_error_bounds hr (by linarith)
  change q - 1 ∈ Icc (0 : ℝ) r at hratio
  have hq0 : 0 ≤ q := by linarith [hratio.1]
  have hq2 : q ≤ 2 := by linarith [hratio.2]
  have hM : 1 ≤ M := by
    have := (pairedEtaShiftBoundaryCutoff_bounds hr hrsmall).1
    dsimp [M]
    omega
  have hA : |A| ≤ 1 := by
    have h := logBoundary_harmonic_endpoint_bounds hM
    change A ∈ Icc (-1 : ℝ) 0 at h
    rw [abs_of_nonpos h.2]
    linarith [h.1]
  have hQ : |Q| ≤ 1 + |d| := by
    have hc : |1 - Real.log (Real.pi / 2)| ≤ 1 := by
      rw [abs_of_nonneg etaWallisEndpointConstant_bounds.1]
      exact etaWallisEndpointConstant_bounds.2
    exact (abs_add_le _ _).trans (add_le_add hc (le_refl _))
  have hJ : ‖J‖ ≤ B := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (f := F) (C := B) (fun z _ ↦ hB z)
  have hY : ‖Y‖ ≤ B * (R + 2 + |d|) := by
    have hRterm : ‖R • J‖ ≤ R * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left hJ hR.le
    have hAterm : ‖A • F 0‖ ≤ B := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul hA (hB 0) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hQterm : ‖Q • F 1‖ ≤ (1 + |d|) * B := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hQ (hB 1) (norm_nonneg _) (by positivity)
    change ‖R • J + A • F 0 + Q • F 1‖ ≤ _
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
    calc
      _ ≤ (R * B + B) + (1 + |d|) * B := add_le_add (add_le_add hRterm hAterm) hQterm
      _ = _ := by ring
  have herror : ‖(Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - Y‖ ≤
      69 * r * B + ((K : ℝ) / R) * (38 + 6 * d ^ 2) := by
    have h := pairedEtaWeightedMismatch_exp_endpoint_error_le hr hrsmall hR hF hB
    convert h using 1
    congr 1
    dsimp [Y]
    abel
  change ‖r⁻¹ • pairedEtaWeightedMismatch r R F - R • J - A • F 0 - Q • F 1‖ ≤ _
  rw [show r⁻¹ • pairedEtaWeightedMismatch r R F - R • J - A • F 0 - Q • F 1 =
      r⁻¹ • pairedEtaWeightedMismatch r R F - Y by dsimp [Y]; abel]
  have hid : r⁻¹ • pairedEtaWeightedMismatch r R F - Y =
      q • ((Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - Y) + (q - 1) • Y := by
    rw [smul_sub, smul_smul, sub_smul, one_smul,
      show q * (Real.exp r - 1)⁻¹ = r⁻¹ by dsimp [q]; field_simp]
    abel
  rw [hid]
  calc
    _ ≤ ‖q • ((Real.exp r - 1)⁻¹ • pairedEtaWeightedMismatch r R F - Y)‖ + ‖(q - 1) • Y‖ := norm_add_le _ _
    _ ≤ 2 * (69 * r * B + ((K : ℝ) / R) * (38 + 6 * d ^ 2)) + r * (B * (R + 2 + |d|)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio.1]
      exact add_le_add (mul_le_mul hq2 herror (norm_nonneg _) (by norm_num))
        (mul_le_mul hratio.2 hY (norm_nonneg _) hr.le)
    _ = _ := by ring

end

end RiemannGaussian
