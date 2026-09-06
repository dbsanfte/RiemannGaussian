import RiemannGaussian.EtaLogBoundaryQuadrature

/-!
# Endpoint-preserving harmonic quadrature

The finite harmonic boundary sum retains its mass defect at the lower
logarithmic endpoint. The remaining error for a Lipschitz complex test
decays with its logarithmic scale, rather than staying bounded.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The positive mass defect between a harmonic boundary weight and its
exact logarithmic cell length. -/
def logBoundaryWeightDefect (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ - (Real.log ((n : ℝ) + 1) - Real.log n)

/-- Harmonic boundary weights dominate their logarithmic cell lengths. -/
theorem logBoundaryWeightDefect_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ logBoundaryWeightDefect n := sub_nonneg.mpr (log_nat_step_bounds hn).2.1

/-- The mass defect is bounded by a telescoping reciprocal difference. -/
theorem logBoundaryWeightDefect_le_inv_sub_inv {n : ℕ} (hn : 1 ≤ n) :
    logBoundaryWeightDefect n ≤ (n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < ((n : ℝ) + 1) / n)
  rw [Real.log_div (by positivity) hnpos.ne'] at h
  have heq : 1 - (((n : ℝ) + 1) / n)⁻¹ = ((n : ℝ) + 1)⁻¹ := by field_simp; ring
  rw [heq] at h
  exact sub_le_sub_left h _

/-- Reciprocal differences telescope even at the empty cutoff. -/
theorem sum_logBoundary_inv_sub_inv (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹)) =
      1 - ((M : ℝ) + 1)⁻¹ := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring

/-- A reciprocal square is dominated by twice a telescoping difference. -/
theorem logBoundary_inv_sq_le_telescoping {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ ^ 2 ≤ 2 * ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hidentity : 2 * ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) - (n : ℝ)⁻¹ ^ 2 =
      ((n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ ((n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by positivity
  linarith

/-- The finite reciprocal-square mesh mass is uniformly at most two. -/
theorem sum_logBoundary_inv_sq_le_two (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ ^ 2) ≤ 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M, 2 * ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) :=
      Finset.sum_le_sum fun n hn ↦ logBoundary_inv_sq_le_telescoping (Finset.mem_Icc.mp hn).1
    _ = 2 * (1 - ((M : ℝ) + 1)⁻¹) := by rw [← Finset.mul_sum, sum_logBoundary_inv_sub_inv]
    _ ≤ 2 := by
      have h : 0 ≤ ((M : ℝ) + 1)⁻¹ := by positivity
      linarith

/-- A discrete logarithmic first moment of the reciprocal differences has
a finite explicit envelope, with its upper endpoint retained. -/
theorem sum_logBoundary_inv_sub_inv_mul_log_le (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) * Real.log n) ≤
      1 - (1 + Real.log ((M : ℝ) + 1)) / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      apply (add_le_add ih (le_refl _)).trans
      push_cast
      have hstep : Real.log (((M : ℝ) + 1) + 1) - Real.log ((M : ℝ) + 1) ≤
          ((M : ℝ) + 1)⁻¹ := by
        simpa only [Nat.cast_add, Nat.cast_one] using (log_nat_step_bounds (n := M + 1) (by omega)).2.1
      have heq :
          1 - (1 + Real.log ((M : ℝ) + 1)) / ((M : ℝ) + 1) +
            (((M : ℝ) + 1)⁻¹ - (((M : ℝ) + 1) + 1)⁻¹) * Real.log ((M : ℝ) + 1) =
          1 - (1 + Real.log (((M : ℝ) + 1) + 1)) / (((M : ℝ) + 1) + 1) +
            (Real.log (((M : ℝ) + 1) + 1) - Real.log ((M : ℝ) + 1) -
              ((M : ℝ) + 1)⁻¹) / (((M : ℝ) + 1) + 1) := by
        field_simp
        ring
      rw [heq]
      exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))

/-- The mass defect has logarithmic first moment at most one, uniformly
in the arithmetic cutoff. -/
theorem sum_logBoundaryWeightDefect_mul_log_le_one (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, logBoundaryWeightDefect n * Real.log n) ≤ 1 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M, ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) * Real.log n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact mul_le_mul_of_nonneg_right (logBoundaryWeightDefect_le_inv_sub_inv hn1)
        (Real.log_nonneg (by exact_mod_cast hn1))
    _ ≤ 1 - (1 + Real.log ((M : ℝ) + 1)) / ((M : ℝ) + 1) :=
      sum_logBoundary_inv_sub_inv_mul_log_le M
    _ ≤ 1 := by
      have hlog : 0 ≤ Real.log ((M : ℝ) + 1) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
      exact sub_le_self _ (div_nonneg (by positivity) (by positivity))

/-- Exact total mass of the harmonic/logarithmic weight defect. -/
theorem sum_logBoundaryWeightDefect {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, logBoundaryWeightDefect n) =
      (harmonic M : ℝ) - Real.log ((M : ℝ) + 1) := by
  unfold logBoundaryWeightDefect
  rw [Finset.sum_sub_distrib, sum_log_nat_steps hM]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Freezing the positive mass defect at the lower logarithmic endpoint
costs at most `K/R`, retaining an arbitrary complex test. -/
theorem logBoundaryWeightDefect_test_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    ‖(∑ n ∈ Finset.Icc 1 M, logBoundaryWeightDefect n • F (Real.log n / R)) -
      ((harmonic M : ℝ) - Real.log ((M : ℝ) + 1)) • F 0‖ ≤ (K : ℝ) / R := by
  rw [← sum_logBoundaryWeightDefect hM, Finset.sum_smul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        ‖logBoundaryWeightDefect n • F (Real.log n / R) - logBoundaryWeightDefect n • F 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, ((K : ℝ) / R) * (logBoundaryWeightDefect n * Real.log n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hd := logBoundaryWeightDefect_nonneg hn1
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
      have hLip : ‖F (Real.log (n : ℝ) / R) - F 0‖ ≤ (K : ℝ) * (Real.log n / R) := by
        simpa only [dist_eq_norm, Real.norm_eq_abs, sub_zero,
          abs_of_nonneg (div_nonneg hlog hR.le)] using hF.dist_le_mul (Real.log n / R) 0
      calc
        _ ≤ logBoundaryWeightDefect n * ((K : ℝ) * (Real.log n / R)) :=
          mul_le_mul_of_nonneg_left hLip hd
        _ = _ := by ring
    _ = ((K : ℝ) / R) * ∑ n ∈ Finset.Icc 1 M, logBoundaryWeightDefect n * Real.log n :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) / R := by
      simpa using mul_le_mul_of_nonneg_left (sum_logBoundaryWeightDefect_mul_log_le_one M)
        (div_nonneg K.coe_nonneg hR.le)

/-- A logarithmic cell's freezing error is quadratic in its actual mesh
length, which makes the full quadrature remainder summable. -/
theorem logBoundary_cell_quadrature_sq_error_le {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {n : ℕ} (hn : 1 ≤ n) :
    ‖(Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R) -
      ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), F (t / R)‖ ≤
      (K : ℝ) / R * (Real.log ((n : ℝ) + 1) - Real.log n) ^ 2 := by
  have hstep0 := (log_nat_step_bounds hn).1
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by linarith
  have hc : Continuous (fun t : ℝ ↦ F (t / R)) :=
    hF.continuous.comp (continuous_id.div_const R)
  rw [← intervalIntegral.integral_const, ← intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := Real.log (n : ℝ)) (b := Real.log ((n : ℝ) + 1))
    (f := fun t ↦ F (Real.log n / R) - F (t / R))
    (C := (K : ℝ) / R * (Real.log ((n : ℝ) + 1) - Real.log n)) (by
      intro t ht
      rw [uIoc_of_le hle] at ht
      have hd : |Real.log (n : ℝ) / R - t / R| ≤
          (Real.log ((n : ℝ) + 1) - Real.log n) / R := by
        rw [← sub_div, abs_div, abs_of_pos hR,
          abs_of_nonpos (by linarith [ht.1] : Real.log (n : ℝ) - t ≤ 0)]
        exact div_le_div_of_nonneg_right (by linarith [ht.2]) hR.le
      calc
        ‖F (Real.log (n : ℝ) / R) - F (t / R)‖ ≤
            (K : ℝ) * |Real.log (n : ℝ) / R - t / R| := by
          simpa only [dist_eq_norm, Real.norm_eq_abs] using hF.dist_le_mul (Real.log n / R) (t / R)
        _ ≤ (K : ℝ) * ((Real.log ((n : ℝ) + 1) - Real.log n) / R) :=
          mul_le_mul_of_nonneg_left hd K.coe_nonneg
        _ = _ := by ring)
  rw [abs_of_nonneg hstep0] at hb
  convert hb using 1
  ring

/-- Uniform quadrature after weighting with the exact logarithmic cell
lengths: its complex error is at most `2K/R` at every finite cutoff. -/
theorem logBoundary_logarithmic_quadrature_uniform_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    ‖(∑ n ∈ Finset.Icc 1 M,
      (Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R)) -
      ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)‖ ≤ 2 * (K : ℝ) / R := by
  have hint : (∑ n ∈ Finset.Icc 1 M,
      ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), F (t / R)) =
      ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun n : ℕ ↦ Real.log (n : ℝ)) (show 1 ≤ M + 1 by omega)
      (f := fun t ↦ F (t / R)) (μ := volume)
      (fun _ _ ↦ (hF.continuous.comp (continuous_id.div_const R)).intervalIntegrable _ _)
    simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.cast_add, Nat.cast_one, Real.log_one] using h
  rw [← hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        ‖(Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R) -
          ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), F (t / R)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, (K : ℝ) / R * (n : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      apply (logBoundary_cell_quadrature_sq_error_le hR hF hn1).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg K.coe_nonneg hR.le)
      exact pow_le_pow_left₀ (log_nat_step_bounds hn1).1 (log_nat_step_bounds hn1).2.1 2
    _ = ((K : ℝ) / R) * ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ((K : ℝ) / R) * 2 := mul_le_mul_of_nonneg_left (sum_logBoundary_inv_sq_le_two M)
      (div_nonneg K.coe_nonneg hR.le)
    _ = _ := by ring

/-- The finite harmonic quadrature retains the complete lower-endpoint
mass defect, leaving a uniform `3K/R` complex remainder. -/
theorem logBoundary_harmonic_finite_part_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    ‖(∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      (∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) -
      ((harmonic M : ℝ) - Real.log ((M : ℝ) + 1)) • F 0‖ ≤ 3 * (K : ℝ) / R := by
  let D : ℂ := ∑ n ∈ Finset.Icc 1 M, logBoundaryWeightDefect n • F (Real.log n / R)
  let L : ℂ := ∑ n ∈ Finset.Icc 1 M,
    (Real.log ((n : ℝ) + 1) - Real.log n) • F (Real.log n / R)
  have hsum : (∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ • F (Real.log n / R)) = D + L := by
    dsimp only [D, L]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← add_smul]
    simp only [logBoundaryWeightDefect, sub_add_cancel]
  rw [hsum]
  have heq : D + L - (∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) -
      ((harmonic M : ℝ) - Real.log ((M : ℝ) + 1)) • F 0 =
      (D - ((harmonic M : ℝ) - Real.log ((M : ℝ) + 1)) • F 0) +
        (L - ∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (logBoundaryWeightDefect_test_error_le hM hR hF)
    (logBoundary_logarithmic_quadrature_uniform_error_le hM hR hF)).trans (by ring_nf; rfl))

/-- Removing the uncrossed boundary at one preserves the same vanishing
quadrature error and subtracts exactly one lower-endpoint mass. -/
theorem logBoundary_crossing_finite_part_error_le {M : ℕ} (hM : 1 ≤ M)
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    ‖(∑ n ∈ Finset.Icc 2 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      (∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) -
      ((harmonic M : ℝ) - 1 - Real.log ((M : ℝ) + 1)) • F 0‖ ≤ 3 * (K : ℝ) / R := by
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
      (∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) -
      ((harmonic M : ℝ) - 1 - Real.log ((M : ℝ) + 1)) • F 0 =
      (∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ • F (Real.log n / R)) -
      (∫ t in 0..Real.log ((M : ℝ) + 1), F (t / R)) -
      ((harmonic M : ℝ) - Real.log ((M : ℝ) + 1)) • F 0 := by
    rw [← hs]
    simp only [sub_smul, one_smul]
    abel
  rw [heq]
  exact logBoundary_harmonic_finite_part_error_le hM hR hF

end

end RiemannGaussian
