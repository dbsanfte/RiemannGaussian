import RiemannGaussian.ZetaLocalCanonical

/-!
# Bounds for the complete local zero-free residual

Canonical factors preserve boundary norms and only increase the norm at
the safe center. Maximum modulus therefore transfers the actual eta upper
bound and the Möbius center floor to the complete local residual.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Removing every interior zero by its canonical factor preserves
the exact norm on the selected zero-free boundary. -/
theorem norm_localZetaCanonicalResidual_eq_on_sphere (y : ℝ) {z : ℂ}
    (hz : z ∈ sphere 0 (localZetaCanonicalRadius y)) :
    ‖localZetaCanonicalResidual y z‖ = ‖localZetaPoleRemoved y z‖ := by
  let f := localZetaPoleRemoved y
  let g := localZetaCanonicalResidual y
  let R := localZetaCanonicalRadius y
  have hR := localZetaCanonicalRadius_pos y
  have han := analyticOnNhd_localZetaPoleRemoved_canonicalDisc y
  have hfz := (localZetaCanonicalRadius_spec y).2.2 z
    (by simpa only [mem_sphere, dist_zero_right] using hz)
  have ho : meromorphicOrderAt f z = 0 :=
    (han z (sphere_subset_closedBall hz)).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hl := (localZetaCanonicalResidual_decomp y).log_norm_eq (sphere_subset_closedBall hz) ho hR
  have hcanonical : (∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
      Real.log ‖Complex.canonicalFactor R i z‖) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem := (divisor f (ball 0 R)).supportWithinDomain hi
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one himem hz, Real.log_one, mul_zero]
  have hS : divisor f (sphere 0 R) = 0 := divisor_localZetaPoleRemoved_sphere_eq_zero y
  have hsphere : (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) * Real.log ‖z - i‖) = 0 := by
    rw [hS]
    simp
  have ht : meromorphicTrailingCoeffAt f z = f z :=
    (han z (sphere_subset_closedBall hz)).meromorphicTrailingCoeffAt_of_ne_zero hfz
  change Real.log ‖g z‖ = _ at hl
  rw [hcanonical, hsphere, ht] at hl
  simp only [sub_zero, zero_add] at hl
  have hgp : 0 < ‖g z‖ := norm_pos_iff.mpr
    ((localZetaCanonicalResidual_decomp y).ne_zero z (sphere_subset_closedBall hz))
  have hfp : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
  simpa only [Real.exp_log hgp, Real.exp_log hfp] using congrArg Real.exp hl

/-- The actual local eta envelope bounds the complete residual
throughout the selected closed disc. -/
theorem norm_localZetaCanonicalResidual_le (y : ℝ) {z : ℂ}
    (hz : z ∈ closedBall 0 (localZetaCanonicalRadius y)) :
    ‖localZetaCanonicalResidual y z‖ ≤ 8 * (|y| + 22) ^ 2 := by
  have hR := localZetaCanonicalRadius_pos y
  have hdiff : DiffContOnCl ℂ (localZetaCanonicalResidual y) (ball 0 (localZetaCanonicalRadius y)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (localZetaCanonicalResidual_decomp y).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_localZetaCanonicalResidual_eq_on_sphere y hw]
    apply norm_localZetaPoleRemoved_le
    exact (closedBall_subset_closedBall (by linarith [(localZetaCanonicalRadius_spec y).2.1]))
      (sphere_subset_closedBall hw)
  · rwa [closure_ball 0 hR.ne']

/-- The exact safe-center norm is not diminished by removal of the
complete analytic divisor. -/
theorem norm_localZetaPoleRemoved_zero_le_residual (y : ℝ) :
    ‖localZetaPoleRemoved y 0‖ ≤ ‖localZetaCanonicalResidual y 0‖ := by
  let f := localZetaPoleRemoved y
  let g := localZetaCanonicalResidual y
  let R := localZetaCanonicalRadius y
  have hR := localZetaCanonicalRadius_pos y
  have hz : (0 : ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have han := analyticOnNhd_localZetaPoleRemoved_canonicalDisc y
  have hf0 := localZetaPoleRemoved_zero_ne_zero y
  have ho : meromorphicOrderAt f 0 = 0 :=
    (han 0 hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf0
  have hl := (localZetaCanonicalResidual_decomp y).log_norm_eq hz ho hR
  have hcanonical : 0 ≤ ∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
      Real.log ‖Complex.canonicalFactor R i 0‖ := by
    apply finsum_nonneg
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem := (divisor f (ball 0 R)).supportWithinDomain hi
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        apply hi
        rw [(han.mono ball_subset_closedBall).meromorphicOn.divisor_apply]
        · have ho' : meromorphicOrderAt (localZetaPoleRemoved y) 0 = 0 := ho
          simp [ho']
        · simpa only [mem_ball, dist_zero_right, norm_zero] using hR
      have hn : ‖i‖ < R := by simpa only [mem_ball, dist_zero_right] using himem
      have hfactor : 1 ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [norm_canonicalFactor_zero hR]
        exact (one_le_div (norm_pos_iff.mpr hi0)).mpr hn.le
      exact mul_nonneg (by exact_mod_cast (han.mono ball_subset_closedBall).divisor_nonneg i)
        (Real.log_nonneg hfactor)
  have hS : divisor f (sphere 0 R) = 0 := divisor_localZetaPoleRemoved_sphere_eq_zero y
  have hsphere : (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) * Real.log ‖0 - i‖) = 0 := by
    rw [hS]
    simp
  have ht : meromorphicTrailingCoeffAt f 0 = f 0 := (han 0 hz).meromorphicTrailingCoeffAt_of_ne_zero hf0
  change Real.log ‖g 0‖ = _ at hl
  rw [hsphere, ht] at hl
  have hlog : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by rw [hl]; linarith
  have hgp : 0 < ‖g 0‖ := norm_pos_iff.mpr ((localZetaCanonicalResidual_decomp y).ne_zero 0 hz)
  have hfp : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  simpa only [Real.exp_log hgp, Real.exp_log hfp] using Real.exp_le_exp.mpr hlog

/-- The complete residual retains the explicit safe-center floor. -/
theorem sixteenth_le_norm_localZetaCanonicalResidual_zero (y : ℝ) :
    (1 / 16 : ℝ) ≤ ‖localZetaCanonicalResidual y 0‖ :=
  (sixteenth_le_norm_localZetaPoleRemoved_zero y).trans (norm_localZetaPoleRemoved_zero_le_residual y)

end

end RiemannGaussian
