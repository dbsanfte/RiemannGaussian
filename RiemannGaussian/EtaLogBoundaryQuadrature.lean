import RiemannGaussian.EtaLogSupportCritical

/-!
# Quantitative logarithmic boundary quadrature

The harmonic boundary measure is compared with ordinary logarithmic time
against a bounded Lipschitz complex test function. The complex test is kept
intact; the norm estimate is a downstream quadrature error, rather than a
replacement of the phase by its absolute value.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Consecutive positive logarithmic endpoints have nonnegative separation
at most the reciprocal left endpoint, and hence at most one. -/
theorem log_nat_step_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log ((n : ℝ) + 1) - Real.log n ∧
      Real.log ((n : ℝ) + 1) - Real.log n ≤ (n : ℝ)⁻¹ ∧
      (n : ℝ)⁻¹ ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
  rw [Real.log_div (by positivity) hn0.ne'] at hlog
  have hdiv : ((n : ℝ) + 1) / n - 1 = (n : ℝ)⁻¹ := by field_simp; ring
  rw [hdiv] at hlog
  exact ⟨sub_nonneg.mpr (Real.log_le_log hn0 (by linarith)), hlog,
    inv_le_one_of_one_le₀ hn1⟩

/-- The total logarithmic mesh length telescopes exactly. -/
theorem sum_log_nat_steps {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, (Real.log ((n : ℝ) + 1) - Real.log n)) =
      Real.log ((M : ℝ) + 1) := by
  have h := Finset.sum_Ico_sub (fun n : ℕ ↦ Real.log (n : ℝ))
    (show 1 ≤ M + 1 by omega)
  simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.cast_add, Nat.cast_one,
    Real.log_one, sub_zero] using h

/-- On one logarithmic cell, freezing a slowly varying Lipschitz test at
the left endpoint has an explicit error proportional to the cell length. -/
theorem logBoundary_cell_quadrature_error_le {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {n : ℕ} (hn : 1 ≤ n) :
    ‖(Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R) -
      ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), F (t / R)‖ ≤
      (K : ℝ) / R * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  obtain ⟨hstep0, hstep, hinv⟩ := log_nat_step_bounds hn
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by linarith
  have hc : Continuous (fun t : ℝ ↦ F (t / R)) :=
    hF.continuous.comp (continuous_id.div_const R)
  rw [← intervalIntegral.integral_const, ← intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := Real.log (n : ℝ)) (b := Real.log ((n : ℝ) + 1))
    (f := fun t ↦ F (Real.log n / R) - F (t / R)) (C := (K : ℝ) / R) (by
      intro t ht
      rw [uIoc_of_le hle] at ht
      have hd : |Real.log (n : ℝ) / R - t / R| ≤ 1 / R := by
        rw [← sub_div, abs_div, abs_of_pos hR,
          abs_of_nonpos (by linarith [ht.1] : Real.log (n : ℝ) - t ≤ 0)]
        apply div_le_div_of_nonneg_right _ hR.le
        linarith [ht.2]
      calc
        ‖F (Real.log (n : ℝ) / R) - F (t / R)‖ ≤
            (K : ℝ) * |Real.log (n : ℝ) / R - t / R| := by
          simpa only [dist_eq_norm, Real.norm_eq_abs] using hF.dist_le_mul (Real.log n / R) (t / R)
        _ ≤ (K : ℝ) * (1 / R) := mul_le_mul_of_nonneg_left hd K.coe_nonneg
        _ = (K : ℝ) / R := by ring)
  simpa only [abs_of_nonneg hstep0] using hb

/-- Harmonic weights differ from logarithmic cell lengths by at most one
unit of total mass. This bound preserves an arbitrary bounded complex test. -/
theorem logBoundary_harmonic_weights_error_le {M : ℕ} (hM : 1 ≤ M)
    {F : ℝ → ℂ} {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (R : ℝ) :
    ‖(∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      ∑ n ∈ Finset.Icc 1 M,
        (Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R)‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have hmass : (∑ n ∈ Finset.Icc 1 M,
      ((n : ℝ)⁻¹ - (Real.log ((n : ℝ) + 1) - Real.log n))) ≤ 1 := by
    rw [Finset.sum_sub_distrib, sum_log_nat_steps hM]
    have hh : (∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹) = (harmonic M : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [hh]
    have hlog : Real.log (M : ℝ) ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) (by linarith)
    linarith [harmonic_le_one_add_log M]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        ‖(n : ℝ)⁻¹ • F (Real.log n / R) -
          (Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        ((n : ℝ)⁻¹ - (Real.log ((n : ℝ) + 1) - Real.log n)) * B := by
      apply Finset.sum_le_sum
      intro n hn
      have hnonneg := sub_nonneg.mpr (log_nat_step_bounds (Finset.mem_Icc.mp hn).1).2.1
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left (hB _) hnonneg
    _ = (∑ n ∈ Finset.Icc 1 M,
        ((n : ℝ)⁻¹ - (Real.log ((n : ℝ) + 1) - Real.log n))) * B :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hB0

/-- Quantitative logarithmic quadrature for bounded Lipschitz complex
tests, with the horizontal rescaling and arithmetic cutoff independent. -/
theorem logBoundary_harmonic_quadrature_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)‖ ≤
      B + (K : ℝ) / R * Real.log ((M : ℝ) + 1) := by
  let L : ℂ := ∑ n ∈ Finset.Icc 1 M,
    (Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R)
  have hint : (∑ n ∈ Finset.Icc 1 M,
      ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), F (t / R)) =
      ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun n : ℕ ↦ Real.log (n : ℝ)) (show 1 ≤ M + 1 by omega)
      (f := fun t ↦ F (t / R)) (μ := volume)
      (fun _ _ ↦ (hF.continuous.comp (continuous_id.div_const R)).intervalIntegrable _ _)
    simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.cast_add, Nat.cast_one,
      Real.log_one] using h
  have hquad : ‖L - ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)‖ ≤
      (K : ℝ) / R * Real.log ((M : ℝ) + 1) := by
    rw [← hint]
    dsimp only [L]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 M,
          ‖(Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R) -
            ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), F (t / R)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 M,
          (K : ℝ) / R * (Real.log ((n : ℝ) + 1) - Real.log n) :=
        Finset.sum_le_sum fun n hn ↦
          logBoundary_cell_quadrature_error_le hR hF (Finset.mem_Icc.mp hn).1
      _ = _ := by rw [← Finset.mul_sum, sum_log_nat_steps hM]
  exact (norm_sub_le_norm_sub_add_norm_sub _ L _).trans
    (add_le_add (logBoundary_harmonic_weights_error_le hM hB R) hquad)

/-- Removing the non-crossed boundary at one costs at most one additional
test bound in logarithmic quadrature. -/
theorem logBoundary_crossing_quadrature_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)‖ ≤
      2 * B + (K : ℝ) / R * Real.log ((M : ℝ) + 1) := by
  have hs := Finset.sum_erase_add (Finset.Icc 1 M)
    (fun n : ℕ ↦ (n : ℝ)⁻¹ • F (Real.log n / R)) (Finset.left_mem_Icc.mpr hM)
  rw [Finset.Icc_erase_left] at hs
  have hset : Finset.Ioc 1 M = Finset.Icc 2 M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hs
  simp only [Nat.cast_one, inv_one, Real.log_one, zero_div, one_smul] at hs
  have heq : (∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R) =
      ((∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
        ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) - F 0 := by
    rw [← hs]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add
    (logBoundary_harmonic_quadrature_error_le hM hR hF hB) (hB 0)).trans (by ring_nf; rfl))

/-- The top logarithmic quadrature endpoint is within three of
`log (1/r)` at the actual displacement cutoff. -/
theorem pairedEtaShiftBoundaryCutoff_log_bounds {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) :
    Real.log (1 / r) - 3 ≤ Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) ∧
      Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) ≤ Real.log (1 / r) := by
  obtain ⟨hM, hlower, hupper⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hM0 : (0 : ℝ) < pairedEtaShiftBoundaryCutoff r := by
    exact_mod_cast (show 0 < pairedEtaShiftBoundaryCutoff r by omega)
  have hlow : Real.log (1 / r) - Real.log 4 ≤
      Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) := by
    calc
      _ = Real.log (1 / (4 * r)) := by
        rw [Real.log_div (by norm_num) hr.ne',
          Real.log_div (by norm_num) (by positivity),
          Real.log_mul (by norm_num) hr.ne', Real.log_one]
        ring
      _ ≤ _ := Real.log_le_log (by positivity) (hlower.trans (by linarith))
  have hup : (pairedEtaShiftBoundaryCutoff r : ℝ) + 1 ≤ 1 / r := by
    have hc : 1 / (2 * r) + 1 ≤ 1 / r := by
      apply (le_div_iff₀ hr).2
      field_simp
      nlinarith
    linarith
  exact ⟨by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)],
    Real.log_le_log (by positivity) hup⟩

end

end RiemannGaussian
