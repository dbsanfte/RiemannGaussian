import RiemannGaussian.EtaLogTwoEndpointLimit
import RiemannGaussian.EtaPhaseMismatchBounds
import RiemannGaussian.EtaSupportGapGaussianProfile

/-!
# A global polynomial bound after subtracting the eta leading term

The earlier uniform weighted boundary error supplies domination of the
finite part, while the evaluated endpoint theorem supplies its limit.
The large-displacement region is controlled separately by the actual total
mass. No small-displacement restriction remains on the Gaussian coordinate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exponential heat width times its logarithmic scale is uniformly bounded. -/
theorem etaHeatWidth_mul_scale_le_one (R : ℝ) : Real.exp (-R) * R ≤ 1 := by
  calc
    _ ≤ Real.exp (-R) * Real.exp R := mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp R]) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Moving an endpoint of the logarithmic test integral costs only its
length times the test bound, retaining the exact scaled main integral. -/
theorem norm_integral_etaSlowTest_sub_scale_le {R : ℝ} (hR : 0 < R)
    (L : ℝ) {F : ℝ → ℂ} (hF : Continuous F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(∫ t in 0..L, F (t / R)) - R • (∫ z in 0..1, F z)‖ ≤ B * |L - R| := by
  have hc : Continuous (fun t : ℝ ↦ F (t / R)) := hF.comp (continuous_id.div_const R)
  have hscale : (∫ t in 0..R, F (t / R)) = R • (∫ z in 0..1, F z) := by
    rw [intervalIntegral.integral_comp_div F hR.ne', zero_div, div_self hR.ne']
  rw [← hscale, intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ ↦ hB (t / R))

/-- A global polynomial bound for the actual complex weighted finite part.
It holds for every positive Gaussian coordinate, including displacements
outside the range of the fine arithmetic cutoff estimate. -/
theorem norm_pairedEtaWeightedMismatch_finite_part_le {R v : ℝ} (hR : 1 ≤ R) (hv : 0 < v)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(Real.exp (-R))⁻¹ • pairedEtaWeightedMismatch (Real.exp (-R) * v) R F -
      (v * R) • (∫ z in 0..1, F z)‖ ≤
      B * (1 + 12 * v + 8 * v ^ 2) + 4 * (K : ℝ) * (1 + v + v ^ 2) := by
  let h := Real.exp (-R)
  let r := h * v
  let J := ∫ z in 0..1, F z
  have hh : 0 < h := Real.exp_pos _
  have hr : 0 < r := mul_pos hh hv
  have hR0 : 0 < R := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have hJ : ‖J‖ ≤ B := by
    simpa only [sub_zero, abs_one, mul_one] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (fun z _ ↦ hB z))
  have hhR : h * R ≤ 1 := etaHeatWidth_mul_scale_le_one R
  by_cases hsmall : r ≤ 1 / 8
  · let H := Real.log (1 / r)
    let I := ∫ t in 0..H, F (t / R)
    have hH : H = R - Real.log v := by
      dsimp [H, r, h]
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (Real.exp_ne_zero _) hv.ne', Real.log_exp]
      ring
    have hHratio : H / R ≤ 1 + |Real.log v| := by
      apply (div_le_iff₀ hR0).2
      rw [hH]
      have h := le_mul_of_one_le_right (abs_nonneg (Real.log v)) hR
      linarith [neg_le_abs (Real.log v)]
    have hfirst : ‖h⁻¹ • pairedEtaWeightedMismatch r R F - v • I‖ ≤
        v * (12 * B + 4 * (K : ℝ) * (1 + |Real.log v|)) := by
      have hid : h⁻¹ • pairedEtaWeightedMismatch r R F - v • I =
          h⁻¹ • (pairedEtaWeightedMismatch r R F - r • I) := by
        rw [smul_sub, smul_smul]
        congr 1
        dsimp [r]
        field_simp
      rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
      calc
        _ ≤ h⁻¹ * (r * (12 * B + 4 * (K : ℝ) / R * H)) :=
          mul_le_mul_of_nonneg_left (pairedEtaWeightedMismatch_critical_error_le hr hsmall hR0 hF hB)
            (inv_nonneg.mpr hh.le)
        _ = v * (12 * B + 4 * (K : ℝ) * (H / R)) := by dsimp [r]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hHratio (by positivity))) hv.le
    have hsecond : ‖v • I - (v * R) • J‖ ≤ v * (B * |Real.log v|) := by
      rw [← smul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hv]
      have hi := norm_integral_etaSlowTest_sub_scale_le hR0 H hF.continuous hB
      have hd : |H - R| = |Real.log v| := by rw [hH, sub_sub_cancel_left, abs_neg]
      rw [hd] at hi
      exact mul_le_mul_of_nonneg_left hi hv.le
    have hlog := mul_abs_log_le_one_add_sq hv
    have hlogB := mul_le_mul_of_nonneg_left hlog hB0
    have hlogK := mul_le_mul_of_nonneg_left hlog K.coe_nonneg
    have hsum := (norm_sub_le_norm_sub_add_norm_sub
      (h⁻¹ • pairedEtaWeightedMismatch r R F) (v • I) ((v * R) • J)).trans
      (add_le_add hfirst hsecond)
    change ‖h⁻¹ • pairedEtaWeightedMismatch r R F - (v * R) • J‖ ≤ _
    nlinarith [mul_nonneg hB0 (sq_nonneg v)]
  · have hinv : h⁻¹ ≤ 8 * v := by
      rw [← one_div]
      apply (div_le_iff₀ hh).2
      dsimp [r] at hsmall
      nlinarith
    have hRle : R ≤ 8 * v := by
      have hi : R ≤ h⁻¹ := by
        rw [← one_div]
        exact (le_div_iff₀ hh).2 (by nlinarith [hhR])
      exact hi.trans hinv
    have hmass : ‖pairedEtaWeightedMismatch r R F‖ ≤ B := by
      simpa only [pairedEtaWeightedMismatch, neg_zero, Real.exp_zero, mul_one] using
        norm_pairedEtaWeightedMismatch_time_tail_le hB r R 0
    have hfirst : ‖h⁻¹ • pairedEtaWeightedMismatch r R F‖ ≤ 8 * v * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
      exact mul_le_mul hinv hmass (norm_nonneg _) (by positivity)
    have hsecond : ‖(v * R) • J‖ ≤ 8 * v ^ 2 * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hv hR0)]
      have hvr := mul_le_mul_of_nonneg_left hRle hv.le
      exact (mul_le_mul hvr hJ (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have hsum := (norm_sub_le (h⁻¹ • pairedEtaWeightedMismatch r R F) ((v * R) • J)).trans
      (add_le_add hfirst hsecond)
    change ‖h⁻¹ • pairedEtaWeightedMismatch r R F - (v * R) • J‖ ≤ _
    nlinarith [mul_nonneg hB0 hv.le, mul_nonneg K.coe_nonneg (show 0 ≤ 1 + v + v ^ 2 by positivity)]

end

end RiemannGaussian
