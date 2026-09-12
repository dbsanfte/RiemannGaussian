/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripMap
import RiemannGaussian.AnalyticDiscBoundaryMoment
import RiemannGaussian.AnalyticDiscBoundarySequence

/-!
# Complete finite divisor identities exhausting a vertical strip

The physical strip function is composed with the proved arctangent map.
Each radius below one has a complete finite divisor and an exact complex
boundary identity. The divisor at each point retains the physical analytic
order. Zero-free circles approach one without assuming analyticity at the
two infinite ends of the strip. This does not assert convergence of their
boundary integrals.
-/

namespace RiemannGaussian.AnalyticStripDisc
noncomputable section
open Complex Filter Metric Set MeromorphicOn
open AnalyticDiscBoundaryMoment AnalyticDiscSignedDerivative
open scoped Topology

/-- The full physical open strip, with no imaginary-height cutoff. -/
def strip (c : ℂ) (η : ℝ) : Set ℂ := {z | |z.re - c.re| < η}

/-- The exact physical function represented in unit-disc coordinates. -/
def pullback (f : ℂ → ℂ) (c : ℂ) (η : ℝ) : ℂ → ℂ := f ∘ AnalyticStripMap.map c η

/-- The center value is unchanged by the coordinate map. -/
theorem pullback_zero (f : ℂ → ℂ) (c : ℂ) (η : ℝ) : pullback f c η 0 = f c := by
  simp [pullback, AnalyticStripMap.map_zero]

/-- Analyticity on the entire physical strip gives analyticity at
every interior disc point, with the branch domain discharged. -/
theorem analyticAt_pullback {f : ℂ → ℂ} {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (strip c η)) {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (pullback f c η) w :=
  (hf _ (AnalyticStripMap.map_mem_strip c hη hw)).comp (AnalyticStripMap.analyticAt_map c η hw)

/-- Every closed disc of radius strictly below one has a genuine
analytic neighborhood. No analyticity at the infinite strip ends is assumed. -/
theorem analyticOnNhd_pullback {f : ℂ → ℂ} {c : ℂ} {η r : ℝ} (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (strip c η)) (hr : r < 1) :
    AnalyticOnNhd ℂ (pullback f c η) (closedBall 0 r) := by
  intro w hw
  apply analyticAt_pullback hη hf
  have hw' : ‖w‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hw
  exact hw'.trans_lt hr

/-- The entire complex logarithmic derivative has the exact strip-scale
Jacobian. This equality precedes all signed projections and estimates. -/
theorem logDeriv_pullback_zero {f : ℂ → ℂ} {c : ℂ} (hf : DifferentiableAt ℂ f c) (η : ℝ) :
    logDeriv (pullback f c η) 0 = (4 * (η : ℂ) / Real.pi) * logDeriv f c := by
  have hm := AnalyticStripMap.hasDerivAt_map c η (w := 0) (by simp)
  have h := logDeriv_comp (g := AnalyticStripMap.map c η) (x := 0)
    (by simpa only [AnalyticStripMap.map_zero] using hf) hm.differentiableAt
  simpa [pullback, AnalyticStripMap.map_zero, hm.deriv, mul_comm] using h

/-- Every point of the finite disc divisor has exactly the same
multiplicity as its physical point in the complete strip divisor. -/
theorem divisor_pullback {f : ℂ → ℂ} {c : ℂ} {η r : ℝ} (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (strip c η)) (hr : r < 1) {w : ℂ} (hw : w ∈ ball 0 r) :
    divisor (pullback f c η) (ball 0 r) w =
      divisor f (strip c η) (AnalyticStripMap.map c η w) := by
  have hw' : ‖w‖ < 1 := (show ‖w‖ < r by simpa only [mem_ball, dist_zero_right] using hw).trans hr
  rw [((analyticOnNhd_pullback hη hf hr).mono ball_subset_closedBall).divisor_apply hw,
    hf.divisor_apply (AnalyticStripMap.map_mem_strip c hη hw')]
  congr 2
  exact AnalyticStripMap.analyticOrderAt_comp_map f c hη hw'

/-- Every eligible interior circle gives the complete original complex
logarithmic derivative, exact signed boundary moment and full finite divisor. -/
theorem logDeriv_eq_moment_add_divisor {f : ℂ → ℂ} {c : ℂ} {η r : ℝ} (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (strip c η)) (hf0 : f c ≠ 0) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → pullback f c η w ≠ 0) :
    (4 * (η : ℂ) / Real.pi) * logDeriv f c = moment (pullback f c η) r +
      ∑ᶠ w, divisor (pullback f c η) (ball 0 r) w • kernel r w := by
  have h := AnalyticDiscBoundaryMoment.logDeriv_eq_moment_add_divisor hr
    (analyticOnNhd_pullback hη hf hr1) (by simpa only [pullback_zero] using hf0) hs
  rw [logDeriv_pullback_zero (hf c (by simpa [strip] using hη)).differentiableAt] at h
  exact h

/-- There are zero-free circles approaching the full unit radius even
when the pullback is only analytic on the open disc. Their images exhaust
the strip; the two infinite ends are never treated as regular boundary points. -/
theorem exists_sphere_tendsto {f : ℂ → ℂ} {c : ℂ} {η : ℝ} (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (strip c η)) (hf0 : f c ≠ 0) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 1) ∧
      ∀ n, 0 < r n ∧ r n < 1 ∧ ∀ w : ℂ, ‖w‖ = r n → pullback f c η w ≠ 0 := by
  have hex (n : ℕ) : ∃ r : ℝ, 1 - 2 / ((n : ℝ) + 3) < r ∧
      r < 1 - 1 / ((n : ℝ) + 3) ∧ ∀ w : ℂ, ‖w‖ = r → pullback f c η w ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 3 := by linarith
    have hhi : 1 - 1 / ((n : ℝ) + 3) < 1 := sub_lt_self _ (by positivity)
    have hpos : 0 < 1 - 1 / ((n : ℝ) + 3) := by
      have h := (div_lt_one hden).mpr (show (1 : ℝ) < n + 3 by linarith)
      linarith
    exact AnalyticDiscBoundarySequence.exists_sphere_between hpos
      (analyticOnNhd_pullback hη hf hhi) (by simpa only [pullback_zero] using hf0)
      (sub_lt_sub_left (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) hden) 1) le_rfl
  choose r hlo hhi hs using hex
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 3)
      tendsto_natCast_atTop_atTop
  have hloLim : Tendsto (fun n : ℕ => 1 - 2 / ((n : ℝ) + 3)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hden.const_div_atTop 2)
  have hr1 (n : ℕ) : r n < 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hh : 0 < 1 / ((n : ℝ) + 3) := by positivity
    linarith [hhi n]
  refine ⟨r, tendsto_of_tendsto_of_tendsto_of_le_of_le hloLim tendsto_const_nhds
    (fun n => (hlo n).le) (fun n => (hr1 n).le), ?_⟩
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlow : 0 < 1 - 2 / ((n : ℝ) + 3) := by
    have hh := (div_lt_one (by positivity : 0 < (n : ℝ) + 3)).mpr
      (show (2 : ℝ) < n + 3 by linarith)
    linarith
  exact ⟨hlow.trans (hlo n), hr1 n, hs n⟩

/-- Every fixed physical strip point enters the finite disc windows
eventually along any sequence of radii approaching one. -/
theorem eventually_inverse_mem {c z : ℂ} {η : ℝ} (hη : 0 < η) (hz : z ∈ strip c η)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) :
    ∀ᶠ n in atTop, Complex.tan (Real.pi * (z - c) / (4 * η)) ∈ ball 0 (r n) := by
  have h := hr.eventually (lt_mem_nhds (AnalyticStripMap.norm_inverse_lt_one c hη hz))
  simpa only [mem_ball, dist_zero_right] using h

end
end RiemannGaussian.AnalyticStripDisc
