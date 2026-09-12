/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianBandExclusion
import RiemannGaussian.ZetaSquarefreeLocalWindow

/-!
# The explicit Gaussian band in the actual squarefree quotient

The exact local doubled-ordinate window places every possible denominator
zero inside the proved Gaussian band. The complete closed Cauchy radius
is `1+1/900000`; no unevaluated height threshold or low-zero margin is used.
The original marked arithmetic responses retain their signed prime phases.
-/

namespace RiemannGaussian.SquarefreeGaussianBand
noncomputable section
open Complex Filter Topology

/-- The full radius supplied by the explicit Gaussian zero margin. -/
def radius : ℝ := 1 + 1 / 900000

/-- The explicit center domain, with the doubled denominator height
and the full vertical allowance already included. -/
def ordinateBand : Set ℝ :=
  {y | 500002 ≤ |y| ∧ Real.log (2 * |y| + 5) ≤ 320000}

/-- The genuine radius is larger than one and below the uniform
two-harmonic remainder threshold. -/
theorem radius_bounds : 1 < radius ∧ radius < 9 / 8 := by
  norm_num [radius]

/-- The pole-separation cap is inactive throughout the explicit domain. -/
theorem radius_eq {y : ℝ} (hy : y ∈ ordinateBand) :
    SquarefreeEulerBand.radius y (1 / 450000) = radius := by
  rw [SquarefreeEulerBand.radius_eq (by have := hy.1; linarith) (by norm_num)]
  norm_num [radius]

/-- Every ordinate in the actual doubled window stays in the complete
proved Gaussian height band, for both signs of the center. -/
theorem window_heights {y t : ℝ} (hy : y ∈ ordinateBand)
    (ht : |t - 2 * y| ≤ 2 * radius) :
    1000000 ≤ |t| ∧ ZetaNearOneBudgetLimit.scale t ≤ 320000 := by
  have hdiff := abs_abs_sub_abs_le_abs_sub t (2 * y)
  have h := hdiff.trans ht
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor
  · have := hy.1
    norm_num [radius] at hl
    linarith
  · apply (Real.log_le_log (by positivity : 0 < |t| + 2) ?_).trans hy.2
    norm_num [radius] at hu
    linarith

/-- The local zero-window premise is discharged by the actual Gaussian
zero exclusion, without demanding a margin at any unrelated height. -/
theorem window_margin {y : ℝ} (hy : y ∈ ordinateBand)
    (ρ : NontrivialZetaZero)
    (hρ : |ρ.1.im - 2 * y| ≤ 2 * SquarefreeEulerBand.radius y (1 / 450000)) :
    ρ.1.re < 1 - 1 / 450000 := by
  rw [radius_eq hy] at hρ
  obtain ⟨ht, hL⟩ := window_heights hy hρ
  have h := ZetaGaussianBandExclusion.exact_margin ρ ht hL
  linarith

/-- The actual quotient is analytic on a neighbourhood of the entire
closed radius `1+1/900000` at every explicit admissible center. -/
theorem analyticOnNhd_response {y : ℝ} (hy : y ∈ ordinateBand) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) radius) := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.analyticOnNhd_response
    (by have := hy.1; linarith) (by norm_num) (by norm_num) (window_margin hy)

/-- The explicit two-sided center domain is compact; its finite upper
height is proved from the logarithmic condition. -/
theorem isCompact_ordinateBand : IsCompact ordinateBand := by
  have hc : Continuous (fun y : ℝ ↦ Real.log (2 * |y| + 5)) :=
    (by fun_prop : Continuous (fun y : ℝ ↦ 2 * |y| + 5)).log
      (fun y ↦ ne_of_gt (by positivity))
  have hclosed : IsClosed ordinateBand :=
    (isClosed_le continuous_const continuous_abs).inter (isClosed_le hc continuous_const)
  apply (isCompact_Icc (a := -Real.exp 320000) (b := Real.exp 320000)).of_isClosed_subset
    hclosed
  intro y hy
  have he := (Real.log_le_iff_le_exp (by positivity : 0 < 2 * |y| + 5)).mp hy.2
  exact abs_le.mp (by linarith [abs_nonneg y] : |y| ≤ Real.exp 320000)

/-- The union of every full closed Cauchy disc over the actual finite
height domain, retaining both signs of the center ordinate. -/
def discTube : Set ℂ :=
  (fun p : ℝ × ℂ ↦ (3 / 2 + I * p.1) + p.2) ''
    (ordinateBand ×ˢ Metric.closedBall (0 : ℂ) radius)

/-- Tube membership retains a genuine center and its exact full radius. -/
theorem mem_discTube_iff (s : ℂ) : s ∈ discTube ↔
    ∃ y ∈ ordinateBand, s ∈ Metric.closedBall (3 / 2 + I * y) radius := by
  constructor
  · rintro ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    simpa [mem_closedBall_iff_norm] using hz
  · rintro ⟨y, hy, hs⟩
    refine ⟨(y, s - (3 / 2 + I * y)), ⟨hy, ?_⟩, ?_⟩
    · apply mem_closedBall_iff_norm.mpr
      simpa only [sub_zero] using mem_closedBall_iff_norm.mp hs
    · dsimp
      ring

/-- The complete family of closed discs has a compact union, before
any quotient norm or prime-phase maximum is taken. -/
theorem isCompact_discTube : IsCompact discTube :=
  (isCompact_ordinateBand.prod (isCompact_closedBall (0 : ℂ) radius)).image (by fun_prop)

/-- Actual quotient analyticity holds throughout the complete compact
tube, with every denominator-zero and pole premise discharged. -/
theorem analyticOnNhd_discTube : AnalyticOnNhd ℂ squarefreeEulerResponse discTube := by
  intro s hs
  obtain ⟨y, hy, hs⟩ := (mem_discTube_iff s).mp hs
  exact analyticOnNhd_response hy s hs

/-- One quotient constant works for every center in the explicit band,
including moving ordinates. The constant is finite, not numerically evaluated. -/
theorem exists_uniform_quotient_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ ordinateBand,
      ∀ s ∈ Metric.closedBall (3 / 2 + I * y) radius,
        ‖squarefreeEulerResponse s‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_discTube.image_of_continuousOn
    analyticOnNhd_discTube.continuousOn.norm).isBounded.exists_norm_le
  refine ⟨|M|, abs_nonneg _, ?_⟩
  intro y hy s hs
  have h := hM _ ⟨s, (mem_discTube_iff s).mpr ⟨y, hy, hs⟩, rfl⟩
  rw [Real.norm_of_nonneg (norm_nonneg _)] at h
  exact h.trans (le_abs_self M)

/-- A single constant simultaneously controls every admissible center,
every smaller positive radius, every excluded prime set, every valid mark,
and every polynomial and order. Only the signed prime envelope varies. -/
theorem exists_uniform_response_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ ordinateBand,
      ∀ (r : ℝ), 0 < r → r ≤ radius →
        ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          ∀ (p : Polynomial ℂ) (N : ℕ),
            ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
              C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
                ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_quotient_bound
  exact SquarefreeEulerPhase.exists_uniform_response_bound_of_analytic ordinateBand radius M
    radius_bounds.2.le hM (fun _ hy ↦ analyticOnNhd_response hy) hb

/-- Every valid marked response inherits the explicit full radius and
the original signed two-harmonic envelope, with one constant per center. -/
theorem exists_response_bound {y : ℝ} (hy : y ∈ ordinateBand) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  SquarefreeEulerPhase.exists_response_bound_of_analytic y radius
    (by linarith [radius_bounds.1]) radius_bounds.2.le (analyticOnNhd_response hy)

end
end RiemannGaussian.SquarefreeGaussianBand
