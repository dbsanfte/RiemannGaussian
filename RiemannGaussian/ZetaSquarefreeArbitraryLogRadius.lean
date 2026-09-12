/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArbitraryLogZeroFree
import RiemannGaussian.ZetaSquarefreeEulerBandRadius

/-!
# Arbitrary logarithmic coefficients in the actual arithmetic radius

For each fixed positive coefficient, the actual squarefree quotient is
analytic on the full disc of radius `1+A/(2*log(2*abs(y)+3))` at every
sufficiently large ordinate. This transports the proved region through
the complete bounded-height divisor, with all pole exclusions checked.

Every finite excluded prime set, squarefree mark, complex polynomial and
moment order receives the larger Cauchy bound with its signed envelope
intact. For fixed marks, scaling by the radius of any smaller nonnegative
coefficient still gives decay. Thresholds depend on the coefficient, and
this supplies no independent lower bound for the ordinary-prime source.
-/

namespace RiemannGaussian.SquarefreeArbitraryLog
noncomputable section
open Complex Filter Topology

/-- The full common-band radius for a chosen logarithmic coefficient,
with the explicit cap excluding the numerator and denominator poles. -/
def radius (A y : ℝ) : ℝ :=
  SquarefreeEulerBand.radius y (A / Real.log (2 * |y| + 3))

/-- Every fixed positive coefficient supplies a genuine full analytic
disc at all sufficiently large positive and negative ordinates. -/
theorem exists_eventual_radius_spec {A : ℝ} (hA : 0 < A) :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      1 < radius A y ∧ radius A y = 1 + A / (2 * Real.log (2 * |y| + 3)) ∧
        radius A y < 9 / 8 ∧
        AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) (radius A y)) := by
  obtain ⟨H₀, _, hb⟩ := ZetaArbitraryLogZeroFree.exists_eventual_common_margin hA
  refine ⟨max (3 / 2) H₀, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyH : H₀ ≤ |y| := (le_max_right _ _).trans hy
  obtain ⟨hm, hmu, hz⟩ := hb (2 * |y| + 3) (by linarith)
  have hbounds := SquarefreeEulerBand.radius_bounds (by linarith : 1 < |y|) hm hmu
  refine ⟨hbounds.1, ?_, hbounds.2.2.1, ?_⟩
  · unfold radius
    rw [SquarefreeEulerBand.radius_eq hy1 hmu]
    ring
  · exact SquarefreeEulerBand.analyticOnNhd_response (by linarith) hm hmu
      (fun ρ hρ ↦ (hz ρ hρ).2)

/-- The improved radius reaches every actual marked response, retaining
the signed prime envelope and all polynomial and moment dependence. -/
theorem exists_eventual_response_bound {A : ℝ} (hA : 0 < A) :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius A y →
        ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          ∀ (p : Polynomial ℂ) (N : ℕ),
            ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
              C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
                ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨T, hT, hspec⟩ := exists_eventual_radius_spec hA
  refine ⟨T, hT, ?_⟩
  intro y hy
  obtain ⟨hr, _, hru, hQ⟩ := hspec y hy
  exact SquarefreeEulerPhase.exists_response_bound_of_analytic y (radius A y)
    (by linarith) hru.le hQ

/-- For every two fixed coefficients `0 ≤ A < B`, the proved larger
disc absorbs the entire geometric scale from coefficient `A`, for all
fixed valid marks and polynomials. The prime set does not grow in this
limit, and no uniform height threshold over `B` is asserted. -/
theorem exists_eventual_coefficient_scaled_decay {A B : ℝ} (hA : 0 ≤ A) (hAB : A < B) :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      radius A y < radius B y ∧
        ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ q ∈ P.primeFactors, q ∉ S) → ∀ p : Polynomial ℂ,
            Tendsto (fun N : ℕ ↦ ((radius A y ^ N : ℝ) : ℂ) *
              RoughSquarefreeBare.response p S P N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨H₀, _, hb⟩ :=
    ZetaArbitraryLogZeroFree.exists_eventual_common_margin (show 0 < B by linarith)
  refine ⟨max (3 / 2) H₀, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyH : H₀ ≤ |y| := (le_max_right _ _).trans hy
  obtain ⟨hm, hmu, hz⟩ := hb (2 * |y| + 3) (by linarith)
  have hl : 0 < Real.log (2 * |y| + 3) := Real.log_pos (by linarith [abs_nonneg y])
  have hdiv := div_lt_div_of_pos_right hAB hl
  have hma : A / Real.log (2 * |y| + 3) < 1 / 4 := hdiv.trans hmu
  have heA : radius A y = 1 + (A / Real.log (2 * |y| + 3)) / 2 :=
    SquarefreeEulerBand.radius_eq hy1 hma
  have heB : radius B y = 1 + (B / Real.log (2 * |y| + 3)) / 2 :=
    SquarefreeEulerBand.radius_eq hy1 hmu
  have hr : radius A y < radius B y := by rw [heA, heB]; linarith
  refine ⟨hr, ?_⟩
  intro S hS P hP hPS p
  apply SquarefreeEulerBand.tendsto_scaled_response (by linarith) hm hmu
    (fun ρ hρ ↦ (hz ρ hρ).2) ?_ hr S hS P hP hPS p
  rw [heA]
  positivity

end
end RiemannGaussian.SquarefreeArbitraryLog
