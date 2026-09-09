/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierParameter
import RiemannGaussian.ComplexResolventCircleAverage

/-!
# Averaging the complete Suzuki parameter family

A full circle of affine parameters acts as an exact magnitude cutoff
on the original complex carrier. This bounds the averaged part without
separating its eta numerator and denominator. It preserves the entire
local source germ at every xi zero, with analytic multiplicity intact.

The complementary large-value carrier is displayed explicitly. The
cutoff need not be holomorphic where its condition changes, so this
result does not justify a contour deformation across that interface.
At a pole on the parameter circle no integral formula is asserted.
-/

open Complex Filter Metric Real Set Topology
namespace RiemannGaussian
noncomputable section

/-- The uniform mean over every phase of the affine parameter circle.
Its use as a genuine average requires the integrability proved below. -/
def suzukiXiParameterCircleAverage (r : ℝ) (z : ℂ) : ℂ :=
  circleAverage (fun u : ℂ => suzukiXiAffineCarrier (1 + (r : ℂ) * u) z) 0 1

/-- The exact cutoff selected by a regular parameter circle. Boundary
values are assigned zero here, without interpreting a singular average. -/
def suzukiXiCircleProjection (r : ℝ) (z : ℂ) : ℂ :=
  if r * ‖suzukiXiZeroCarrier z‖ < 1 then suzukiXiZeroCarrier z else 0

private lemma parameter_function (r : ℝ) {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    (fun u : ℂ => suzukiXiAffineCarrier (1 + (r : ℂ) * u) z) =
      fun u : ℂ => suzukiXiZeroCarrier z / (1 - u * (I * (r : ℂ) * suzukiXiZeroCarrier z)) := by
  funext u
  rw [suzukiXiAffineCarrier_eq_resolvent _ hE]
  congr 2
  ring

private lemma parameter_norm {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖I * (r : ℂ) * suzukiXiZeroCarrier z‖ = r * ‖suzukiXiZeroCarrier z‖ := by
  simp [abs_of_nonneg hr]

/-- The excluded threshold is exactly a zero of the full denominator
on the parameter circle, rather than an artifact of the norm bound. -/
theorem exists_suzukiXiAffineDenominator_circle_zero_iff {r : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) :
    (∃ u : ℂ, ‖u‖ = 1 ∧ suzukiXiAffineDenominator (1 + (r : ℂ) * u) z = 0) ↔
      r * ‖suzukiXiZeroCarrier z‖ = 1 := by
  let b := I * (r : ℂ) * suzukiXiZeroCarrier z
  have he (u : ℂ) : suzukiXiAffineDenominator (1 + (r : ℂ) * u) z = 0 ↔ u * b = 1 := by
    rw [suzukiXiAffineDenominator_eq_resolvent _ hE, mul_eq_zero, or_iff_right hE, sub_eq_zero]
    dsimp [b]
    constructor <;> intro h <;> linear_combination -h
  rw [← parameter_norm hr z]
  change (∃ u : ℂ, ‖u‖ = 1 ∧ suzukiXiAffineDenominator (1 + (r : ℂ) * u) z = 0) ↔ ‖b‖ = 1
  constructor
  · rintro ⟨u, hu, hz⟩
    have hn := congrArg norm ((he u).mp hz)
    simpa [norm_mul, hu] using hn
  · intro hb
    have hb0 : b ≠ 0 := by intro h; simp [h] at hb
    exact ⟨b⁻¹, by simp [hb], (he _).mpr (inv_mul_cancel₀ hb0)⟩

/-- Away from the explicit threshold, the entire parameter family
has a genuine integrable circle trace. -/
theorem circleIntegrable_suzukiXiAffineCarrier {r : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) (hb : r * ‖suzukiXiZeroCarrier z‖ ≠ 1) :
    CircleIntegrable (fun u : ℂ => suzukiXiAffineCarrier (1 + (r : ℂ) * u) z) 0 1 := by
  rw [parameter_function r hE]
  exact circleIntegrable_parameterResolvent _ (by rwa [parameter_norm hr])

/-- Averaging every parameter phase is exactly the stated cutoff of
the original carrier, with its full complex phase retained. -/
theorem suzukiXiParameterCircleAverage_eq_projection {r : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) (hb : r * ‖suzukiXiZeroCarrier z‖ ≠ 1) :
    suzukiXiParameterCircleAverage r z = suzukiXiCircleProjection r z := by
  unfold suzukiXiParameterCircleAverage
  rw [parameter_function r hE, circleAverage_parameterResolvent _
    (by rwa [parameter_norm hr]), parameter_norm hr]
  rfl

/-- The projected part has a height-independent bound at every point;
this estimate makes no denominator-separation assumption. -/
theorem norm_suzukiXiCircleProjection_lt {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖suzukiXiCircleProjection r z‖ < 1 / r := by
  unfold suzukiXiCircleProjection
  split_ifs with h
  · exact (lt_div_iff₀ hr).mpr (by nlinarith)
  · simp only [norm_zero]
    positivity

/-- On every regular parameter circle, the bound is a bound for the
actual full-circle integral, not just for an algebraic surrogate. -/
theorem norm_suzukiXiParameterCircleAverage_lt {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) (hb : r * ‖suzukiXiZeroCarrier z‖ ≠ 1) :
    ‖suzukiXiParameterCircleAverage r z‖ < 1 / r := by
  rw [suzukiXiParameterCircleAverage_eq_projection hr.le hE hb]
  exact norm_suzukiXiCircleProjection_lt hr z

/-- The complete original carrier is retained as the bounded projection
plus its exact large-value part, including the threshold itself. -/
theorem suzukiXiZeroCarrier_eq_projection_add_complement (r : ℝ) (z : ℂ) :
    suzukiXiZeroCarrier z = suzukiXiCircleProjection r z +
      if 1 ≤ r * ‖suzukiXiZeroCarrier z‖ then suzukiXiZeroCarrier z else 0 := by
  unfold suzukiXiCircleProjection
  by_cases h : r * ‖suzukiXiZeroCarrier z‖ < 1
  · simp [h, not_le_of_gt h]
  · simp [h, le_of_not_gt h]

/-- A circle of radius less than one leaves the full safe-half-plane
carrier unchanged; regularity follows from the existing actual bound. -/
theorem suzukiXiParameterCircleAverage_eq_of_safe {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    suzukiXiParameterCircleAverage r z = suzukiXiZeroCarrier z := by
  have hs : r * ‖suzukiXiZeroCarrier z‖ < 1 :=
    (mul_le_mul_of_nonneg_left (norm_suzukiXiZeroCarrier_le_one_of_half_le_im hz) hr).trans_lt
      (by simpa using hr1)
  rw [suzukiXiParameterCircleAverage_eq_projection hr
    (suzukiXiEValue_ne_zero_of_half_le_im hz) hs.ne, suzukiXiCircleProjection, if_pos hs]

/-- Every xi zero has a punctured neighborhood on which the averaged
carrier agrees exactly with the original one. The original denominator
and every parameter-circle trace are proved regular there. -/
theorem suzukiXiParameterCircleAverage_eventuallyEq_at_zero
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
      suzukiXiEValue z ≠ 0 ∧
      CircleIntegrable (fun u : ℂ => suzukiXiAffineCarrier (1 + (r : ℂ) * u) z) 0 1 ∧
      suzukiXiParameterCircleAverage r z = suzukiXiZeroCarrier z ∧
      suzukiXiCircleProjection r z = suzukiXiZeroCarrier z := by
  obtain ⟨q, p, hq, _hp, _hq0, _hp0, hlocal⟩ := exists_suzukiXiCarrier_pair_local_model rho
  let alpha := zetaSpectralCoordinate rho.1
  have hc : ContinuousAt (fun z : ℂ => r * ‖(z - alpha) * q z‖) alpha :=
    continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).mul hq.continuousAt).norm
  have hsmall : ∀ᶠ z in 𝓝 alpha, r * ‖(z - alpha) * q z‖ < 1 :=
    hc.eventually (gt_mem_nhds (by simp))
  filter_upwards [hlocal, hsmall.filter_mono nhdsWithin_le_nhds] with z hz hs
  have hbound : r * ‖suzukiXiZeroCarrier z‖ < 1 := by rwa [hz.2.2.1]
  have hp : suzukiXiCircleProjection r z = suzukiXiZeroCarrier z := by
    simp only [suzukiXiCircleProjection, if_pos hbound]
  exact ⟨hz.1, circleIntegrable_suzukiXiAffineCarrier hr.le hz.1 hbound.ne,
    (suzukiXiParameterCircleAverage_eq_projection hr.le hz.1 hbound.ne).trans hp, hp⟩

/-- The exact source coefficient survives full-circle averaging for
every analytic multiplicity, with the original analytic remainder. -/
theorem exists_suzukiXiParameterCircleAverage_source_model
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) :
    ∃ p : ℂ → ℂ, AnalyticAt ℂ p (zetaSpectralCoordinate rho.1) ∧
      ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
        suzukiXiParameterCircleAverage r z / (z - zetaSpectralCoordinate rho.1) ^ 2 =
          (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ /
            (z - zetaSpectralCoordinate rho.1) + p z := by
  obtain ⟨p, q, hp, _hq, he⟩ := exists_suzukiXiCarrier_diagonal_polar_models rho
  refine ⟨p, hp, ?_⟩
  filter_upwards [he, suzukiXiParameterCircleAverage_eventuallyEq_at_zero rho hr] with z hz havg
  rw [havg.2.2.1]
  exact hz.1

end
end RiemannGaussian
