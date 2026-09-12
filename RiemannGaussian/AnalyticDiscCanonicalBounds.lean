/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# Canonical zero removal at every analytic disc scale

An analytic function nonzero at the center has a zero-free boundary at
some radius between one half and three quarters of its outer radius.
The complete canonical residual preserves the boundary norm and increases
the center norm. No separation between distinct zeros is needed.
-/

namespace RiemannGaussian.AnalyticDiscCanonicalBounds
noncomputable section
open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical

variable {f g : ℂ → ℂ} {R : ℝ}

/-- Nonvanishing at the center makes every order on the complete
analytic disc finite. -/
theorem order_ne_top (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    meromorphicOrderAt f z ≠ ⊤ := by
  have h0 : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have ho : meromorphicOrderAt f 0 = 0 :=
    (hf 0 h0).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf0
  have hall := (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
    (Metric.isConnected_closedBall hR.le)).mp ⟨⟨0, h0⟩, by simp [ho]⟩
  exact hall ⟨z, hz⟩

/-- A complete finite divisor leaves an available boundary at every scale. -/
theorem exists_zeroFree_sphere (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ∃ r : ℝ, R / 2 < r ∧ r < 3 * R / 4 ∧
      ∀ z : ℂ, ‖z‖ = r → f z ≠ 0 := by
  have hzeros : (closedBall 0 R ∩ f ⁻¹' {0}).Finite := by
    rw [hf.meromorphicNFOn.zero_set_eq_divisor_support
      (fun z ↦ order_ne_top hR hf hf0 z.property)]
    exact (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hnot : ¬Ioo (R / 2) (3 * R / 4) ⊆ (bad : Set ℝ) := by
    intro h
    exact (Set.Ioo_infinite (by linarith : R / 2 < 3 * R / 4))
      (bad.finite_toSet.subset h)
  obtain ⟨r, hr, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨r, hr.1, hr.2, fun z hz hzero ↦ ?_⟩
  apply hbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hzero⟩
  rw [mem_closedBall, dist_zero_right, hz]
  linarith [hr.2]

/-- The actual analytic function has a complete canonical decomposition. -/
theorem exists_decomp (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) : ∃ g : ℂ → ℂ, ECanonicalDecomp f g R :=
  hf.meromorphicOn.exists_ecanonicalDecomp (fun z ↦ order_ne_top hR hf hf0 z.property)

/-- A nonvanishing analytic boundary has zero divisor, including all
points outside that boundary's domain. -/
theorem divisor_sphere_eq_zero (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) : divisor f (sphere 0 R) = 0 := by
  have han := hf.mono (sphere_subset_closedBall (x := (0 : ℂ)) (ε := R))
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) R
  · have hfz := hs z (by simpa only [mem_sphere, dist_zero_right] using hz)
    have ho : meromorphicOrderAt f z = 0 :=
      (han z hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
    rw [han.meromorphicOn.divisor_apply hz, ho]
    rfl
  · change (if MeromorphicOn f (sphere 0 R) ∧ z ∈ sphere 0 R then _ else 0) = 0
    rw [if_neg (fun h ↦ hz h.2)]

/-- Removing the entire interior divisor preserves the boundary norm
exactly. -/
theorem norm_eq_on_sphere (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) (D : ECanonicalDecomp f g R)
    {z : ℂ} (hz : z ∈ sphere 0 R) : ‖g z‖ = ‖f z‖ := by
  have hfz := hs z (by simpa only [mem_sphere, dist_zero_right] using hz)
  have ho : meromorphicOrderAt f z = 0 :=
    (hf z (sphere_subset_closedBall hz)).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hl := D.log_norm_eq (sphere_subset_closedBall hz) ho hR
  have hcanonical : (∑ᶠ i : ℂ, (divisor f (ball 0 R) i : ℝ) *
      Real.log ‖Complex.canonicalFactor R i z‖) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · rw [Complex.norm_canonicalFactor_eval_circle_eq_one
        ((divisor f (ball 0 R)).supportWithinDomain hi) hz,
        Real.log_one, mul_zero]
  have hS := divisor_sphere_eq_zero hf hs
  have ht : meromorphicTrailingCoeffAt f z = f z :=
    (hf z (sphere_subset_closedBall hz)).meromorphicTrailingCoeffAt_of_ne_zero hfz
  rw [hcanonical, hS, ht] at hl
  simp at hl
  have hgp : 0 < ‖g z‖ := norm_pos_iff.mpr (D.ne_zero z (sphere_subset_closedBall hz))
  have hfp : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
  simpa only [Real.exp_log hgp, Real.exp_log hfp] using congrArg Real.exp hl

/-- Maximum modulus transfers any actual boundary envelope to the
complete zero-free residual. -/
theorem norm_le (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) (D : ECanonicalDecomp f g R)
    {B : ℝ} (hB : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ B)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : ‖g z‖ ≤ B := by
  have hd : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact D.analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_eq_on_sphere hR hf hs D hw]
    exact hB w hw
  · rwa [closure_ball 0 hR.ne']

/-- Complete canonical zero removal increases the actual center norm. -/
theorem center_norm_le (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0 : f 0 ≠ 0) (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0)
    (D : ECanonicalDecomp f g R) : ‖f 0‖ ≤ ‖g 0‖ := by
  have hz : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have ho : meromorphicOrderAt f 0 = 0 :=
    (hf 0 hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf0
  have hl := D.log_norm_eq hz ho hR
  have hcanonical : 0 ≤ ∑ᶠ i : ℂ, (divisor f (ball 0 R) i : ℝ) *
      Real.log ‖Complex.canonicalFactor R i 0‖ := by
    apply finsum_nonneg
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem := (divisor f (ball 0 R)).supportWithinDomain hi
      have hi0 : i ≠ 0 := by
        intro he
        subst i
        apply hi
        rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply
          (mem_ball_self hR), ho]
        rfl
      have hn : ‖i‖ < R := by simpa only [mem_ball, dist_zero_right] using himem
      have hfactor : 1 ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [norm_canonicalFactor_zero hR]
        exact (one_le_div (norm_pos_iff.mpr hi0)).mpr hn.le
      exact mul_nonneg (by exact_mod_cast (hf.mono ball_subset_closedBall).divisor_nonneg i)
        (Real.log_nonneg hfactor)
  rw [divisor_sphere_eq_zero hf hs,
    (hf 0 hz).meromorphicTrailingCoeffAt_of_ne_zero hf0] at hl
  simp at hl
  have hlog : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by rw [hl]; linarith
  have hgp : 0 < ‖g 0‖ := norm_pos_iff.mpr (D.ne_zero 0 hz)
  have hfp : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  simpa only [Real.exp_log hgp, Real.exp_log hfp] using Real.exp_le_exp.mpr hlog

end
end RiemannGaussian.AnalyticDiscCanonicalBounds
