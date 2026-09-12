/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscLogarithm
import RiemannGaussian.AnalyticDiscSignedDerivative

/-!
# Sharp canonical control at any eligible radius

Full canonical zero removal and the sharp center estimate apply at every
zero-free boundary, with the entire complex divisor identity retained.
The explicit radius, boundary growth and center cost can be supplied by
any proved analytic growth profile.
-/

namespace RiemannGaussian.AnalyticDiscCanonicalControl
noncomputable section
open Complex MeromorphicOn Metric Set AnalyticDiscCanonicalBounds AnalyticDiscSignedDerivative

/-- At every positive zero-free boundary, complete canonical removal
has the sharp radius-dependent residual bound and retains the exact
complex logarithmic derivative with its full multiplicity-weighted divisor. -/
theorem exists_controlled_decomp {f : ℂ → ℂ} {R B C : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) (hA : 0 < B + C)
    (hB : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ Real.exp B)
    (hC : -Real.log ‖f 0‖ ≤ C) :
    ∃ g : ℂ → ℂ, ECanonicalDecomp f g R ∧
      ‖logDeriv g 0‖ ≤ 2 * (B + C) / R ∧
      logDeriv f 0 = logDeriv g 0 +
        ∑ᶠ a, divisor f (ball 0 R) a • kernel R a := by
  obtain ⟨g, D⟩ := exists_decomp hR hf hf0
  have hbound : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ Real.exp B := by
    intro z hz
    exact AnalyticDiscCanonicalBounds.norm_le hR hf hs D
      (fun w hw ↦ hB w (sphere_subset_closedBall hw)) hz
  have hcenter : -Real.log ‖g 0‖ ≤ C := by
    have hn := center_norm_le hR hf hf0 hs D
    have hl := Real.log_le_log (norm_pos_iff.mpr hf0) hn
    linarith
  exact ⟨g, D, AnalyticDiscLogarithm.norm_logDeriv_center_le_sharp hR
    D.analyticOnNhd D.ne_zero hA hbound hcenter, logDeriv_center_eq hR hf hf0 hs D⟩

end
end RiemannGaussian.AnalyticDiscCanonicalControl
