/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStripBoundaryLimit
import RiemannGaussian.ZetaStripCotangentSource
import RiemannGaussian.SechVerticalMoments

/-!
# An actual strip-zero constraint with complete vertical boundaries

The complete finite divisor has already been proved favorable outside the
selected zero. Only that zero's exact multiplicity-weighted source is passed
to the limit. The boundary is bounded by the full signed right integral and
the left integral clipped at an arbitrary negative depth. No infinite
divisor exchange, global left negative-part integrability, or unproved
boundary-limit premise is required.
-/

namespace RiemannGaussian.ZetaStripBoundaryConstraint
noncomputable section
open Complex Filter MeasureTheory Metric Set
open AnalyticStripBoundary AnalyticStripBoundaryIntegral AnalyticStripDisc
open ZetaGaussianLocalizer ZetaStripDisc ZetaStripBoundaryLimit
open AnalyticDiscBoundaryMoment AnalyticDiscSignedDerivative ZetaStripCotangentSource
open scoped Topology

/-- The exact physically normalized clipped boundary functional.
Both full vertical integrals retain their original signs. -/
def boundary (c : ℂ) (η M : ℝ) : ℝ := (1 / (4 * η)) *
  ((∫ u : ℝ, rightProjection c η 1 u) + (∫ u : ℝ, leftProjection c η M 1 u))

private theorem continuousOn_projection {c : ℂ} {η r : ℝ} (hη : 0 < η)
    (hleft : η < c.re) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0) :
    ContinuousOn (fun w : ℂ => -w.re * Real.log ‖carrier c η w‖) (sphere 0 r) := by
  have hf := (analyticOnNhd_carrier hη hleft hr1).continuousOn.mono sphere_subset_closedBall
  exact Complex.continuous_re.continuousOn.neg.mul
    (hf.norm.log (fun w hw => norm_ne_zero_iff.mpr (hs w (by simpa using hw))))

/-- On every actual zero-free finite circle, clipping only the left logarithm
majorizes the signed boundary moment, with the exact physical normalization. -/
theorem finite_boundary_le {c : ℂ} {η M r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hM : 0 ≤ M) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0) :
    (Real.pi / (4 * η)) * (-moment (carrier c η) r).re ≤ (1 / (4 * η * r ^ 2)) *
      ((∫ u : ℝ, rightProjection c η r u) + (∫ u : ℝ, leftProjection c η M r u)) := by
  have hf := (analyticOnNhd_carrier hη (by linarith) hr1).continuousOn.mono sphere_subset_closedBall
  have hs' : ∀ w ∈ sphere (0 : ℂ) r, carrier c η w ≠ 0 := fun w hw => hs w (by simpa using hw)
  have hp := continuousOn_projection hη (by linarith) hr1 hs
  have hp' : ContinuousOn (fun w : ℂ => -w.re * Real.log ‖carrier c η w‖) (sphere 0 |r|) :=
    (abs_of_pos hr).symm ▸ hp
  have hleftint := integrable_left hp'
  have hleftle :
      (∫ u : ℝ, (1 / Real.cosh u) * (-((r : ℂ) * left u).re *
        Real.log ‖carrier c η ((r : ℂ) * left u)‖)) ≤ ∫ u : ℝ, leftProjection c η M r u := by
    apply integral_mono hleftint (integrable_leftProjection hc hη hlo hhi hM hr.le hr1)
    intro u
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · apply ClippedLogNorm.log_norm_le
        apply hs
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, norm_left, mul_one]
      · simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, left_re, mul_neg, neg_neg]
        positivity
    · exact one_div_nonneg.mpr (Real.cosh_pos u).le
  rw [neg_moment_re hr hf hs', circleAverage_eq_vertical hp']
  change (Real.pi / (4 * η)) * (2 / r ^ 2 * ((2 * Real.pi)⁻¹ *
    ((∫ u : ℝ, rightProjection c η r u) + _))) ≤ _
  have he (x : ℝ) : (Real.pi / (4 * η)) * (2 / r ^ 2 * ((2 * Real.pi)⁻¹ * x)) =
      (1 / (4 * η * r ^ 2)) * x := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hleftle) (by positivity)

/-- The physically normalized finite clipped boundary converges to the
actual two-line functional; both improper tails are fully controlled. -/
theorem finite_boundary_tendsto {c : ℂ} {η M : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1) :
    Tendsto (fun n => (1 / (4 * η * r n ^ 2)) *
      ((∫ u : ℝ, rightProjection c η (r n) u) + (∫ u : ℝ, leftProjection c η M (r n) u)))
      atTop (𝓝 (boundary c η M)) := by
  have hnorm : Tendsto (fun n => 1 / (4 * η * r n ^ 2)) atTop (𝓝 (1 / (4 * η))) := by
    simpa only [one_pow, mul_one] using!
      tendsto_const_nhds.div ((hr.pow 2).const_mul (4 * η)) (by positivity : 4 * η * 1 ^ 2 ≠ 0)
  exact hnorm.mul ((integral_rightProjection_tendsto hc hη hlo hhi hr hr0 hr1).add
    (integral_leftProjection_tendsto hc hη hlo hhi hM hr hr0 hr1))

/-- Every finite phase channel obeys the same upper bound without requiring
a selected zero at that channel's ordinate. Its full divisor is favorable. -/
theorem finite_logDeriv_le {c : ℂ} {η M r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hM : 0 ≤ M) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0) :
    (-logDeriv riemannZeta c).re ≤ (1 / (4 * η * r ^ 2)) *
      ((∫ u : ℝ, rightProjection c η r u) + (∫ u : ℝ, leftProjection c η M r u)) +
        (1 / (c - 1) - 1 / (c + 1)).re := by
  have h := congrArg Complex.re (logarithmic_identity hc hη (by linarith) hr hr1 hs)
  have hz := source_nonneg hc hη (by linarith) hr hr1
  have he : 4 * (η : ℂ) / Real.pi = ((4 * η / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [he] at h
  have hu : (4 * η / Real.pi) * (-logDeriv riemannZeta c).re ≤
      (-moment (carrier c η) r).re + (4 * η / Real.pi) * (1 / (c - 1) - 1 / (c + 1)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.add_re, Complex.sub_re, Complex.neg_re] at h ⊢
    nlinarith
  have hu := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ Real.pi / (4 * η))
  have he : (Real.pi / (4 * η)) * (4 * η / Real.pi) = 1 := by field_simp
  simp only [mul_add, ← mul_assoc, he, one_mul] at hu
  exact hu.trans (add_le_add (finite_boundary_le hc hη hlo hhi hM hr hr1 hs) le_rfl)

/-- Every phase channel has a complete actual boundary bound, including
channels with no selected zero. This supplies the unmarked channels for
the subsequent full-family inequality. -/
theorem logDeriv_le_boundary {c : ℂ} {η M : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M) :
    (-logDeriv riemannZeta c).re ≤ boundary c η M + (1 / (c - 1) - 1 / (c + 1)).re := by
  obtain ⟨r, hr, hs⟩ := ZetaStripDisc.exists_sphere_tendsto hc hη (by linarith)
  have ht := (finite_boundary_tendsto hc hη hlo hhi hM hr
    (fun n => (hs n).1.le) (fun n => (hs n).2.1)).add_const (1 / (c - 1) - 1 / (c + 1)).re
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  exact Eventually.of_forall fun n => finite_logDeriv_le hc hη hlo hhi hM
    (hs n).1 (hs n).2.1 (hs n).2.2

/-- An actual zero forces a positive cotangent source bounded by the complete
signed right boundary and the arbitrarily depth-retaining left boundary.
All analytic limit hypotheses have been discharged for the literal zeta carrier. -/
theorem selected_zero_constraint (ρ : NontrivialZetaZero) {c : ℂ} {η M : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hlo : (1 / 2 : ℝ) ≤ c.re - η)
    (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M)
    (hρ : ρ.1 ∈ strip c η) (ht : c.im = ρ.1.im) :
    (-logDeriv riemannZeta c).re + (analyticZetaZeroMultiplicity ρ : ℝ) *
      (Real.pi / (2 * η)) * Real.cot (Real.pi * (c.re - ρ.1.re) / (2 * η)) ≤
      boundary c η M + (1 / (c - 1) - 1 / (c + 1)).re := by
  obtain ⟨r, hr, hs⟩ := ZetaStripDisc.exists_sphere_tendsto hc hη (by linarith)
  have hsource := (selected_source_tendsto ρ hc hη hρ ht hr).const_add
    (-logDeriv riemannZeta c).re
  have hbound := (finite_boundary_tendsto hc hη hlo hhi hM hr
    (fun n => (hs n).1.le) (fun n => (hs n).2.1)).add_const (1 / (c - 1) - 1 / (c + 1)).re
  apply le_of_tendsto_of_tendsto hsource hbound
  filter_upwards [eventually_coordinate_mem ρ hη hρ hr] with n hn
  exact (normalized_selected_constraint ρ hc hη (by linarith) (hs n).1 (hs n).2.1
    (hs n).2.2 hρ hn).trans
      (add_le_add (finite_boundary_le hc hη hlo hhi hM (hs n).1 (hs n).2.1 (hs n).2.2) le_rfl)

/-- The same boundary functional is the normalized secant-squared left-minus-right
integral in physical coordinates, with the exact factor needed by the phase theorem. -/
theorem boundary_eq_physical (c : ℂ) (η M : ℝ) :
    boundary c η M = (1 / (4 * η)) *
      ((∫ u : ℝ, (1 / Real.cosh u) ^ 2 * ClippedLogNorm.value M
        (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I))) -
       (∫ u : ℝ, (1 / Real.cosh u) ^ 2 * Real.log
        ‖regularized (c + η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I)‖)) := by
  simp only [boundary, leftProjection_one, rightProjection_one, integral_neg]
  ring

/-- The original normalized density appears with its exact `1/(2η)` factor. -/
theorem boundary_eq_density (c : ℂ) (η M : ℝ) :
    boundary c η M = (1 / (2 * η)) *
      ((∫ u : ℝ, SechVerticalKernel.density u * ClippedLogNorm.value M
        (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I))) -
       (∫ u : ℝ, SechVerticalKernel.density u * Real.log
        ‖regularized (c + η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I)‖)) := by
  have hw (u : ℝ) : (1 / Real.cosh u) ^ 2 = 2 * SechVerticalKernel.density u := by
    unfold SechVerticalKernel.density
    field_simp
  rw [boundary_eq_physical]
  simp_rw [hw, mul_assoc, integral_const_mul]
  ring

/-- The clipped physical left logarithm is integrable against the complete density. -/
theorem integrable_left_density {c : ℂ} {η M : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M) :
    Integrable (fun u : ℝ => SechVerticalKernel.density u * ClippedLogNorm.value M
      (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I))) := by
  have h := (integrable_leftBoundary hc hη hlo hhi hM).const_mul (1 / 2 : ℝ)
  convert! h using 1
  ext u
  rw [leftProjection_one]
  unfold SechVerticalKernel.density
  ring

/-- The full signed physical right logarithm is genuinely density-integrable. -/
theorem integrable_right_density {c : ℂ} {η : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) :
    Integrable (fun u : ℝ => SechVerticalKernel.density u * Real.log
      ‖regularized (c + η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I)‖) := by
  have h := (integrable_rightBoundary hc hη hlo hhi).const_mul (-1 / 2 : ℝ)
  convert! h using 1
  ext u
  rw [rightProjection_one]
  unfold SechVerticalKernel.density
  ring

/-- The actual positive cotangent source is bounded by the two complete
physical density integrals and the exact rational center correction. -/
theorem selected_zero_constraint_density (ρ : NontrivialZetaZero) {c : ℂ} {η M : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hlo : (1 / 2 : ℝ) ≤ c.re - η)
    (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M)
    (hρ : ρ.1 ∈ strip c η) (ht : c.im = ρ.1.im) :
    (-logDeriv riemannZeta c).re + (analyticZetaZeroMultiplicity ρ : ℝ) *
      (Real.pi / (2 * η)) * Real.cot (Real.pi * (c.re - ρ.1.re) / (2 * η)) ≤
      (1 / (2 * η)) *
        ((∫ u : ℝ, SechVerticalKernel.density u * ClippedLogNorm.value M
          (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I))) -
         (∫ u : ℝ, SechVerticalKernel.density u * Real.log
          ‖regularized (c + η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I)‖)) +
        (1 / (c - 1) - 1 / (c + 1)).re := by
  simpa only [boundary_eq_density] using selected_zero_constraint ρ hc hη hlo hhi hM hρ ht

/-- Retaining more of the left negative logarithm can only improve the complete
boundary bound. This comparison involves genuine full integrals on both sides. -/
theorem boundary_antitone_depth {c : ℂ} {η M N : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hM : 0 ≤ M) (hMN : M ≤ N) : boundary c η N ≤ boundary c η M := by
  have h :
      (∫ u : ℝ, SechVerticalKernel.density u * ClippedLogNorm.value N
        (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I))) ≤
      (∫ u : ℝ, SechVerticalKernel.density u * ClippedLogNorm.value M
        (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I))) := by
    apply integral_mono (integrable_left_density hc hη hlo hhi (hM.trans hMN))
      (integrable_left_density hc hη hlo hhi hM)
    intro u
    exact mul_le_mul_of_nonneg_left (ClippedLogNorm.antitone_depth _ hMN)
      (SechVerticalKernel.density_nonneg u)
  rw [boundary_eq_density, boundary_eq_density]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right h _) (by positivity)

end
end RiemannGaussian.ZetaStripBoundaryConstraint
