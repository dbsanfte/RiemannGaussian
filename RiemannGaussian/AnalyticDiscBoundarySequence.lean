/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscCanonicalBounds

/-!
# Zero-free circles approaching the entire analytic radius

A complete finite analytic divisor leaves a zero-free sphere in every
nonempty radial interval. Such spheres approach the full outer radius,
even if that outer sphere itself contains zeros. This permits passage of
scalar bounds to the available radius without discarding a fixed fraction.
-/

namespace RiemannGaussian.AnalyticDiscBoundarySequence
noncomputable section
open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical

/-- Every nonempty radial interval inside the analytic disc contains
a complete zero-free sphere. Zeros on the outer boundary are allowed. -/
theorem exists_sphere_between {f : ℂ → ℂ} {R a b : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hab : a < b) (hbR : b ≤ R) :
    ∃ r : ℝ, a < r ∧ r < b ∧ ∀ z : ℂ, ‖z‖ = r → f z ≠ 0 := by
  have hzeros : (closedBall 0 R ∩ f ⁻¹' {0}).Finite := by
    rw [hf.meromorphicNFOn.zero_set_eq_divisor_support
      (fun z ↦ AnalyticDiscCanonicalBounds.order_ne_top hR hf hf0 z.property)]
    exact (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hnot : ¬Ioo a b ⊆ (bad : Set ℝ) := by
    intro h
    exact (Set.Ioo_infinite hab) (bad.finite_toSet.subset h)
  obtain ⟨r, hr, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨r, hr.1, hr.2, fun z hz hzero ↦ ?_⟩
  apply hbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hzero⟩
  rw [mem_closedBall, dist_zero_right, hz]
  exact hr.2.le.trans hbR

/-- A sequence of positive zero-free radii converges to the entire
outer analytic radius. No nonvanishing premise on the outer sphere is
needed, and every interior zero eventually lies inside these radii. -/
theorem exists_sphere_tendsto {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 R) ∧
      ∀ n : ℕ, 0 < r n ∧ r n < R ∧ ∀ z : ℂ, ‖z‖ = r n → f z ≠ 0 := by
  have hex (n : ℕ) : ∃ r : ℝ, R - R / ((n : ℝ) + 2) < r ∧ r < R ∧
      ∀ z : ℂ, ‖z‖ = r → f z ≠ 0 :=
    exists_sphere_between hR hf hf0
      (sub_lt_self _ (by have hn := Nat.cast_nonneg (α := ℝ) n; positivity)) le_rfl
  choose r hrlo hrhi hs using hex
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 2)
      tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ ↦ R - R / ((n : ℝ) + 2)) atTop (𝓝 R) := by
    simpa using tendsto_const_nhds.sub (hden.const_div_atTop R)
  refine ⟨r, tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n ↦ (hrlo n).le) (fun n ↦ (hrhi n).le), ?_⟩
  intro n
  have hsmall : R / ((n : ℝ) + 2) < R :=
    div_lt_self hR (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  exact ⟨by linarith [hrlo n], hrhi n, hs n⟩

end
end RiemannGaussian.AnalyticDiscBoundarySequence
