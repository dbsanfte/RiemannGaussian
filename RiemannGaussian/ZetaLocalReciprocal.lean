import RiemannGaussian.ZetaReciprocalGeometry

/-!
# Quantitative inversion of the complete local zeta factorization

The normalized residual logarithm and every canonical zero factor retain
an exact complex reconstruction. The actual pole distances then bound
the logarithmic cost of inversion in a strip extending to the left of
one. Only the final estimates discard the individual factor phases.
-/

open Complex MeromorphicOn Metric Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The actual residual logarithm stays quantitatively bounded on the larger inner disc. -/
theorem norm_localZetaCanonicalLog_le_forty (y : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 5 / 8) :
    ‖localZetaCanonicalLog y z‖ ≤ 40 * localZetaLogHeight y := by
  have hR := (localZetaCanonicalRadius_spec y).1
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have hmem : z ∈ ball 0 (localZetaCanonicalRadius y) := by
    rw [mem_ball, dist_zero_right]
    linarith
  apply (norm_localZetaCanonicalLog_le y hmem).trans
  rw [div_le_iff₀ (by linarith : 0 < localZetaCanonicalRadius y - ‖z‖)]
  nlinarith

/-- All local canonical factors and the normalized residual reconstruct the full complex function before inversion. -/
theorem localZetaPoleRemoved_mul_canonical_eq_exp (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (localZetaCanonicalRadius y)) (hf : localZetaPoleRemoved y z ≠ 0) :
    (∏ᶠ i, Complex.canonicalFactor (localZetaCanonicalRadius y) i z ^
      divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i) *
        localZetaPoleRemoved y z =
      Complex.exp (localZetaCanonicalLog y z) * localZetaCanonicalResidual y 0 := by
  have han := (analyticOnNhd_localZetaPoleRemoved_canonicalDisc y) z (ball_subset_closedBall hz)
  have ho : meromorphicOrderAt (localZetaPoleRemoved y) z = 0 :=
    han.meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf
  have he := (localZetaCanonicalResidual_decomp y).eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
    (ball_subset_closedBall hz) ho (localZetaCanonicalRadius_pos y)
  have he' : localZetaCanonicalResidual y z =
      (∏ᶠ i, Complex.canonicalFactor (localZetaCanonicalRadius y) i z ^
        divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i) *
          localZetaPoleRemoved y z := by
    simpa [divisor_localZetaPoleRemoved_sphere_eq_zero y, han.meromorphicTrailingCoeffAt_of_ne_zero hf,
      smul_eq_mul] using he
  exact he'.symm.trans (exp_localZetaCanonicalLog_mul_zero_eq y hz).symm

/-- The actual canonical factors have a common bound from the proved pole buffer, with no assumed zero distances. -/
theorem norm_localZetaCanonicalFactor_le_reciprocal (y : ℝ) (hy : 2 ≤ |y|) {i z : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i ≠ 0)
    (hz : ‖z‖ ≤ 5 / 8) (hzre : -(1 / 2 : ℝ) - zetaReciprocalStripWidth y ≤ z.re) :
    ‖Complex.canonicalFactor (localZetaCanonicalRadius y) i z‖ ≤ 2 / zetaReciprocalStripWidth y := by
  let R := localZetaCanonicalRadius y
  let e := zetaReciprocalStripWidth y
  have hR : 0 < R := localZetaCanonicalRadius_pos y
  have he : 0 < e := zetaReciprocalStripWidth_pos y
  have hiR : ‖i‖ ≤ R := by
    have himem := (divisor (localZetaPoleRemoved y) (ball 0 R)).supportWithinDomain hi
    exact (show ‖i‖ < R by simpa only [mem_ball, dist_zero_right] using himem).le
  have hd : e ≤ ‖z - i‖ := by
    linarith [three_mul_zetaReciprocalStripWidth_le_dist_localDivisor y hy hi hzre]
  have hstar : ‖starRingEnd ℂ i‖ = ‖i‖ := norm_star i
  have hn : ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ ≤ 2 * R := by
    apply (norm_sub_le _ _).trans
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, hstar]
    have hm := mul_le_mul_of_nonneg_right hiR (norm_nonneg z)
    have hRs : R < 7 / 8 := (localZetaCanonicalRadius_spec y).2.1
    nlinarith
  change ‖Complex.canonicalFactor R i z‖ ≤ 2 / e
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  calc
    _ ≤ (2 * R) / (R * ‖z - i‖) := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ (2 * R) / (R * e) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    _ = _ := by field_simp

/-- The complete canonical logarithmic cost is controlled by its actual Jensen multiplicity count. -/
theorem sum_localZetaCanonicalLogFactor_le (y : ℝ) (hy : 2 ≤ |y|) {z : ℂ}
    (hz : ‖z‖ ≤ 5 / 8) (hzre : -(1 / 2 : ℝ) - zetaReciprocalStripWidth y ≤ z.re) :
    (∑ᶠ i, (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i : ℝ) *
      Real.log ‖Complex.canonicalFactor (localZetaCanonicalRadius y) i z‖) ≤
        32 * localZetaLogHeight y * Real.log (2 / zetaReciprocalStripWidth y) := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  let B := Real.log (2 / zetaReciprocalStripWidth y)
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i :=
    ((analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).mono ball_subset_closedBall).divisor_nonneg
  have hB : 0 ≤ B := Real.log_nonneg ((one_le_div (zetaReciprocalStripWidth_pos y)).mpr
    (by linarith [zetaReciprocalStripWidth_le_eighth y]))
  have hp : ∀ i, (d i : ℝ) * Real.log ‖Complex.canonicalFactor (localZetaCanonicalRadius y) i z‖ ≤
      (d i : ℝ) * B := by
    intro i
    by_cases hi : d i = 0
    · simp [hi]
    · have himem := (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y))).supportWithinDomain hi
      have hzmem : z ∈ closedBall 0 (localZetaCanonicalRadius y) := by
        rw [mem_closedBall, dist_zero_right]
        linarith [(localZetaCanonicalRadius_spec y).1]
      have hzi : z ≠ i := by
        intro h
        have hd := three_mul_zetaReciprocalStripWidth_le_dist_localDivisor y hy hi hzre
        rw [h, sub_self, norm_zero] at hd
        linarith [zetaReciprocalStripWidth_pos y]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (norm_pos_iff.mpr (Complex.canonicalFactor_ne_zero himem hzmem hzi))
          (norm_localZetaCanonicalFactor_le_reciprocal y hy hi hz hzre)) (by exact_mod_cast hdnonneg i)
  have hf : (fun i ↦ (d i : ℝ) * Real.log ‖Complex.canonicalFactor (localZetaCanonicalRadius y) i z‖).HasFiniteSupport :=
    hd.subset (by intro i hi hdi; exact hi (by simp [hdi]))
  have hg : (fun i ↦ (d i : ℝ) * B).HasFiniteSupport :=
    hd.subset (by intro i hi hdi; exact hi (by simp [hdi]))
  have hs := finsum_le_finsum' hf hg hp
  have hmul : (∑ᶠ i, (d i : ℝ) * B) = ((∑ᶠ i, d i : ℤ) : ℝ) * B := by
    have hsub : Function.support (fun i ↦ (d i : ℝ) * B) ⊆ (hd.toFinset : Set ℂ) := by
      intro i hi
      apply hd.mem_toFinset.mpr
      intro hdi
      exact hi (by simp [hdi])
    rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum d hd, Int.cast_sum, Finset.sum_mul]
  rw [hmul] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (sum_divisor_localZetaPoleRemoved_canonicalBall_le y) hB)

/-- The complete residual has an explicit logarithmic lower bound throughout the larger inner disc. -/
theorem neg_log_sixteen_sub_le_log_norm_localZetaResidual (y : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 5 / 8) :
    -Real.log 16 - 40 * localZetaLogHeight y ≤ Real.log ‖localZetaCanonicalResidual y z‖ := by
  have hzmem : z ∈ ball 0 (localZetaCanonicalRadius y) := by
    rw [mem_ball, dist_zero_right]
    linarith [(localZetaCanonicalRadius_spec y).1]
  have hg0 : 0 < ‖localZetaCanonicalResidual y 0‖ := by
    linarith [sixteenth_le_norm_localZetaCanonicalResidual_zero y]
  have he := congrArg norm (exp_localZetaCanonicalLog_mul_zero_eq y hzmem)
  rw [norm_mul, Complex.norm_exp] at he
  have he' := congrArg Real.log he
  rw [Real.log_mul (Real.exp_pos _).ne' hg0.ne', Real.log_exp] at he'
  have hfloor : -Real.log 16 ≤ Real.log ‖localZetaCanonicalResidual y 0‖ := by
    simpa only [one_div, Real.log_inv] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 16) (sixteenth_le_norm_localZetaCanonicalResidual_zero y)
  have hlog := norm_localZetaCanonicalLog_le_forty y hz
  have hre := (abs_le.mp (Complex.abs_re_le_norm (localZetaCanonicalLog y z))).1
  linarith

/-- Inversion costs only the bounded residual logarithm and the complete canonical factor sum. -/
theorem norm_inv_localZetaPoleRemoved_le (y : ℝ) (hy : 2 ≤ |y|) {z : ℂ}
    (hz : ‖z‖ ≤ 5 / 8) (hzre : -(1 / 2 : ℝ) - zetaReciprocalStripWidth y ≤ z.re)
    (hf : localZetaPoleRemoved y z ≠ 0) :
    ‖(localZetaPoleRemoved y z)⁻¹‖ ≤
      16 * Real.exp (40 * localZetaLogHeight y +
        32 * localZetaLogHeight y * Real.log (2 / zetaReciprocalStripWidth y)) := by
  have hzmem : z ∈ closedBall 0 (localZetaCanonicalRadius y) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [(localZetaCanonicalRadius_spec y).1]
  have han := (analyticOnNhd_localZetaPoleRemoved_canonicalDisc y) z hzmem
  have ho : meromorphicOrderAt (localZetaPoleRemoved y) z = 0 :=
    han.meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf
  have he := (localZetaCanonicalResidual_decomp y).log_norm_eq hzmem ho (localZetaCanonicalRadius_pos y)
  simp [divisor_localZetaPoleRemoved_sphere_eq_zero y, han.meromorphicTrailingCoeffAt_of_ne_zero hf] at he
  have hlo := neg_log_sixteen_sub_le_log_norm_localZetaResidual y hz
  have hsum := sum_localZetaCanonicalLogFactor_le y hy hz hzre
  calc
    _ = Real.exp (-Real.log ‖localZetaPoleRemoved y z‖) := by
      rw [Real.exp_neg, Real.exp_log (norm_pos_iff.mpr hf), norm_inv]
    _ ≤ Real.exp (Real.log 16 + (40 * localZetaLogHeight y +
        32 * localZetaLogHeight y * Real.log (2 / zetaReciprocalStripWidth y))) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]

end

end RiemannGaussian
