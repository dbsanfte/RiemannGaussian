/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscBoundaryMoment
import RiemannGaussian.SignedCircleProjection

/-!
# Signed canonical control from opposite semicircle estimates

The exact complex boundary moment allows an upper logarithmic bound
on the left and a lower logarithmic bound on the right. Their signed
real-coordinate masses are evaluated before any inequality is taken.
The entire multiplicity-weighted canonical divisor stays in the bound.
-/

namespace RiemannGaussian.AnalyticDiscSignedBoundary
noncomputable section
open Complex Metric Set MeromorphicOn AnalyticDiscBoundaryMoment AnalyticDiscSignedDerivative

/-- Opposite bounds on the two semicircles control the negative real
boundary moment with the exact factor `2/pi`, at every positive radius. -/
theorem neg_moment_re_le {f : ℂ → ℂ} {R B C : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hne : ∀ z ∈ sphere 0 R, f z ≠ 0)
    (hleft : ∀ z ∈ sphere 0 R, z.re ≤ 0 → Real.log ‖f z‖ ≤ B)
    (hright : ∀ z ∈ sphere 0 R, 0 ≤ z.re → -Real.log ‖f z‖ ≤ C) :
    (-moment f R).re ≤ 2 * (B + C) / (Real.pi * R) := by
  have hlog : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 R :=
    ContinuousOn.circleIntegrable hR.le
      (hf.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hne z hz)))
  rw [neg_moment_re hR hf hne]
  apply (mul_le_mul_of_nonneg_left
    (SignedCircleProjection.signed_average_le hR.le hlog hleft hright)
    (by positivity : 0 ≤ 2 / R ^ 2)).trans_eq
  field_simp

/-- The full original logarithmic derivative retains every coupled
zero term while using only the directionally appropriate boundary data. -/
theorem neg_logDeriv_re_add_divisor_le {f : ℂ → ℂ} {R B C : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0)
    (hleft : ∀ z ∈ sphere 0 R, z.re ≤ 0 → Real.log ‖f z‖ ≤ B)
    (hright : ∀ z ∈ sphere 0 R, 0 ≤ z.re → -Real.log ‖f z‖ ≤ C) :
    (-logDeriv f 0).re + (∑ᶠ a, divisor f (ball 0 R) a • kernel R a).re ≤
      2 * (B + C) / (Real.pi * R) := by
  have hb := neg_moment_re_le hR (hf.continuousOn.mono sphere_subset_closedBall)
    (fun z hz ↦ hs z (by simpa only [mem_sphere, dist_zero_right] using hz)) hleft hright
  rw [logDeriv_eq_moment_add_divisor hR hf hf0 hs, neg_add, Complex.add_re, Complex.neg_re]
  simpa using hb

end
end RiemannGaussian.AnalyticDiscSignedBoundary
