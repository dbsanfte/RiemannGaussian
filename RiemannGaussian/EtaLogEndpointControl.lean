import RiemannGaussian.EtaLogWeightedEndpoint

/-!
# Uniform control of the eta endpoint coefficients

The harmonic coefficient, Wallis coefficient, logarithmic mesh, and
exponential normalization are bounded before the cutoff is cancelled.
The Wallis coefficient retains its actual integral source.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The averaged inverse-square overlap tail is at most the reciprocal
lower endpoint, directly from its pointwise profile bound. -/
theorem integral_Ioi_etaOverlapProfile_div_sq_le_inv {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi a, etaOverlapProfile y / y ^ 2) ≤ a⁻¹ := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  calc
    _ ≤ ∫ y in Ioi a, y ^ (-2 : ℝ) := by
      apply integral_mono_ae (integrableOn_etaOverlapProfile_div_sq ha) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.rpow_neg (ha.trans hy).le, Real.rpow_two, ← one_div]
      exact div_le_div_of_nonneg_right (etaOverlapProfile_le_one y) (sq_nonneg y)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
      norm_num [Real.rpow_neg_one]

/-- The upper endpoint constant lies between zero and one, as an actual
nonnegative inverse-square overlap integral. -/
theorem etaWallisEndpointConstant_bounds :
    1 - Real.log (Real.pi / 2) ∈ Icc (0 : ℝ) 1 := by
  rw [← integral_Ioi_etaOverlapProfile_div_sq]
  exact ⟨integral_nonneg (fun y ↦ div_nonneg (etaOverlapProfile_nonneg y) (sq_nonneg y)),
    by simpa using integral_Ioi_etaOverlapProfile_div_sq_le_inv zero_lt_one⟩

/-- At the actual cutoff, the retained Wallis coefficient lies in `[0,4]`.
Its bound follows from the full integral rather than cancellation of norms. -/
theorem pairedEtaShiftBoundaryCutoff_wallis_bounds {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    1 - Real.log (Real.pi / 2) - Real.log ((Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r) ∈
      Icc (0 : ℝ) 4 := by
  obtain ⟨_, haL, haU⟩ := pairedEtaShiftBoundaryCutoff_rescaled_bounds hr hrsmall
  have ha : 0 < (Real.exp r - 1) * pairedEtaShiftBoundaryCutoff r := by linarith
  rw [← integral_Ioi_etaOverlapProfile_div_sq_of_le_one ha haU]
  constructor
  · exact integral_nonneg (fun y ↦ div_nonneg (etaOverlapProfile_nonneg y) (sq_nonneg y))
  · apply (integral_Ioi_etaOverlapProfile_div_sq_le_inv ha).trans
    simpa using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1 / 4) haL

/-- The lower finite harmonic coefficient stays in `[-1,0]`. -/
theorem logBoundary_harmonic_endpoint_bounds {M : ℕ} (hM : 1 ≤ M) :
    (harmonic M : ℝ) - 1 - Real.log ((M : ℝ) + 1) ∈ Icc (-1 : ℝ) 0 := by
  have hl := log_add_one_le_harmonic M
  simp only [Nat.cast_add, Nat.cast_one] at hl
  have hu := harmonic_le_one_add_log M
  have hlog := Real.log_le_log (by exact_mod_cast (show 0 < M by omega))
    (show (M : ℝ) ≤ (M : ℝ) + 1 by linarith)
  constructor <;> linarith

/-- The logarithm of the exponential/original displacement ratio is
nonnegative and at most the original displacement. -/
theorem etaExpDisplacement_log_ratio_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.log ((Real.exp r - 1) / r) ∈ Icc (0 : ℝ) r := by
  have h := etaExpDisplacement_ratio_error_bounds hr hr1
  have hratio : 1 ≤ (Real.exp r - 1) / r := by linarith [h.1]
  have hpos : 0 < (Real.exp r - 1) / r := by linarith
  exact ⟨Real.log_nonneg hratio, (Real.log_le_sub_one_of_pos hpos).trans h.2⟩

/-- The logarithmic mesh at the actual top boundary is at most `4r`. -/
theorem pairedEtaShiftBoundaryCutoff_log_step_bounds {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) - Real.log (pairedEtaShiftBoundaryCutoff r) ∈
      Icc (0 : ℝ) (4 * r) := by
  obtain ⟨hM, hlow, _⟩ := pairedEtaShiftBoundaryCutoff_bounds hr hrsmall
  have hMpos : (0 : ℝ) < pairedEtaShiftBoundaryCutoff r := by exact_mod_cast (show 0 < pairedEtaShiftBoundaryCutoff r by omega)
  have hstep := log_nat_step_bounds (show 1 ≤ pairedEtaShiftBoundaryCutoff r by omega)
  refine ⟨hstep.1, hstep.2.1.trans ?_⟩
  rw [← one_div]
  apply (div_le_iff₀ hMpos).mpr
  have h := (div_le_iff₀ (by positivity : 0 < 4 * r)).mp hlow
  nlinarith

/-- The actual logarithmic cutoff lies within four of `log(1/r)`. -/
theorem pairedEtaShiftBoundaryCutoff_log_lower_bounds {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    Real.log (1 / r) - 4 ≤ Real.log (pairedEtaShiftBoundaryCutoff r) ∧
      Real.log (pairedEtaShiftBoundaryCutoff r) ≤ Real.log (1 / r) := by
  obtain ⟨hlo, hhi⟩ := pairedEtaShiftBoundaryCutoff_log_bounds hr hrsmall
  have hstep := pairedEtaShiftBoundaryCutoff_log_step_bounds hr hrsmall
  constructor <;> linarith [hstep.1, hstep.2]

/-- Moving the top logarithmic integration endpoint from `R` has a
distance bound retaining the original scale offset. -/
theorem pairedEtaShiftBoundaryCutoff_log_top_distance_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) (R : ℝ) :
    |Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) - R| ≤ |Real.log (1 / r) - R| + 3 := by
  obtain ⟨hlo, hhi⟩ := pairedEtaShiftBoundaryCutoff_log_bounds hr hrsmall
  have hd : |Real.log ((pairedEtaShiftBoundaryCutoff r : ℝ) + 1) - Real.log (1 / r)| ≤ 3 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
    linarith
  exact (abs_sub_le _ (Real.log (1 / r)) _).trans ((add_le_add hd (le_refl _)).trans_eq (add_comm _ _))

/-- The endpoint test at the actual cutoff retains its distance from the
unit logarithmic endpoint, with the scale offset explicit. -/
theorem pairedEtaShiftBoundaryCutoff_log_distance_le {r : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1 / 8) (R : ℝ) :
    |Real.log (pairedEtaShiftBoundaryCutoff r) - R| ≤ |Real.log (1 / r) - R| + 4 := by
  obtain ⟨hlo, hhi⟩ := pairedEtaShiftBoundaryCutoff_log_lower_bounds hr hrsmall
  have hd : |Real.log (pairedEtaShiftBoundaryCutoff r) - Real.log (1 / r)| ≤ 4 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
    linarith
  exact (abs_sub_le _ (Real.log (1 / r)) _).trans ((add_le_add hd (le_refl _)).trans_eq (add_comm _ _))

/-- A slow complex test has a quadratic moving-endpoint integration error. -/
theorem integral_etaSlowTest_endpoint_error_le {R : ℝ} (hR : 0 < R) (L : ℝ)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    ‖(∫ t in R..L, F (t / R)) - (L - R) • F 1‖ ≤ (K : ℝ) / R * |L - R| ^ 2 := by
  have hc : Continuous (fun t : ℝ ↦ F (t / R)) := hF.continuous.comp (continuous_id.div_const R)
  rw [show (L - R) • F 1 = ∫ _t in R..L, F 1 by simp,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := R) (b := L) (C := (K : ℝ) / R * |L - R|) (f := fun t ↦ F (t / R) - F 1) (by
      intro t ht
      have hd : |t / R - 1| ≤ |L - R| / R := by
        rw [show t / R - 1 = (t - R) / R by field_simp, abs_div, abs_of_pos hR]
        exact div_le_div_of_nonneg_right (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc ht)) hR.le
      calc
        _ ≤ (K : ℝ) * |t / R - 1| := by
          simpa only [dist_eq_norm, Real.norm_eq_abs] using hF.dist_le_mul (t / R) 1
        _ ≤ (K : ℝ) * (|L - R| / R) := mul_le_mul_of_nonneg_left hd K.coe_nonneg
        _ = _ := by ring)
  convert hn using 1
  ring

end

end RiemannGaussian
