/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A real-part minimum principle on a complete right half-disc

The original analytic function remains complex. Bounds on its imaginary
diameter and curved boundary propagate to the entire closed half-disc by
the maximum-modulus principle applied to its negative exponential. Both
endpoints and the diameter's center remain in the actual compact domain.
-/

namespace RiemannGaussian.AnalyticHalfDiscMinimum
noncomputable section
open Complex Filter Metric Set
open scoped Topology

/-- Lower real-part data on the diameter and semicircle control every
point of the complete half-disc for an analytic function on its neighborhood. -/
theorem re_lower_bound {R C : ℝ} {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, ‖z‖ ≤ R → AnalyticAt ℂ F z)
    (hd : ∀ z : ℂ, ‖z‖ ≤ R → z.re = 0 → C ≤ (F z).re)
    (ha : ∀ z : ℂ, ‖z‖ = R → 0 ≤ z.re → C ≤ (F z).re)
    {z : ℂ} (hz : ‖z‖ ≤ R) (hzre : 0 ≤ z.re) : C ≤ (F z).re := by
  let U : Set ℂ := closedBall 0 R ∩ {w : ℂ | 0 ≤ w.re}
  have hclosed : IsClosed U := isClosed_closedBall.inter
    (isClosed_le continuous_const Complex.continuous_re)
  have hbounded : Bornology.IsBounded U := isBounded_closedBall.subset inter_subset_left
  have hdif : DifferentiableOn ℂ (fun w : ℂ => Complex.exp (-F w)) (closure U) := by
    rw [hclosed.closure_eq]
    intro w hw
    have hwR : ‖w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hw.1
    exact (Complex.differentiable_exp.differentiableAt.comp w
      (hF w hwR).differentiableAt.neg).differentiableWithinAt
  have hb : ∀ w ∈ frontier U, ‖Complex.exp (-F w)‖ ≤ Real.exp (-C) := by
    intro w hw
    have hwU : w ∈ U := hclosed.closure_eq ▸ frontier_subset_closure hw
    have hwR : ‖w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hwU.1
    have hwre : 0 ≤ w.re := hwU.2
    have hlower : C ≤ (F w).re := by
      rcases frontier_inter_subset (closedBall (0 : ℂ) R) {v : ℂ | 0 ≤ v.re} hw with h | h
      · have he : ‖w‖ = R := by
          simpa only [mem_sphere, dist_zero_right] using frontier_closedBall_subset_sphere h.1
        exact ha w he hwre
      · have he : w.re = 0 := by
          simpa only [Complex.frontier_setOfPred_le_re, mem_ofPred_eq] using h.2
        exact hd w hwR he
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (by linarith)
  have hzU : z ∈ closure U := by
    rw [hclosed.closure_eq]
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hz, hzre⟩
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le hbounded hdif.diffContOnCl hb hzU
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp] at h
  linarith

end
end RiemannGaussian.AnalyticHalfDiscMinimum
