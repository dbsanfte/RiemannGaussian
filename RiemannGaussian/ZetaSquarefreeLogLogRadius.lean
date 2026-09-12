/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogZeroFree
import RiemannGaussian.ZetaSquarefreeEulerBandRadius

/-!
# The proved log-log region in the actual squarefree response

Each coefficient in the proved range supplies a complete analytic disc
of radius `1+A*log(log(H))/(2*log(H))`, where `H=2*abs(y)+3`. The entire
low divisor and every numerator or denominator pole are excluded first.
Every marked arithmetic response retains the signed prime-phase envelope.
At fixed marks, any smaller coefficient's full geometric scale decays.
-/

namespace RiemannGaussian.SquarefreeLogLog
noncomputable section
open Complex Filter Topology ZetaLogLogZeroFree

/-- The complete band radius supplied by the proved log-log width,
with its original cap excluding both zeta poles. -/
def radius (A y : ℝ) : ℝ :=
  SquarefreeEulerBand.radius y (ZetaLogLogWidth.width A (2 * |y| + 3))

/-- Every eligible positive log-log coefficient supplies the entire
actual analytic quotient disc at all sufficiently large ordinates. -/
theorem exists_eventual_radius_spec {A : ℝ} (hA : 0 < A) (hAlim : A < coefficientLimit) :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      1 < radius A y ∧
        radius A y = 1 + A * Real.log (Real.log (2 * |y| + 3)) /
          (2 * Real.log (2 * |y| + 3)) ∧
        radius A y < 9 / 8 ∧
        AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) (radius A y)) := by
  obtain ⟨H₀, _, hb⟩ := exists_eventual_common_margin hA hAlim
  refine ⟨max (3 / 2) H₀, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyH : H₀ ≤ |y| := (le_max_right _ _).trans hy
  obtain ⟨hm, hmu, hz⟩ := hb (2 * |y| + 3) (by linarith)
  have hbounds := SquarefreeEulerBand.radius_bounds (by linarith : 1 < |y|) hm hmu
  refine ⟨hbounds.1, ?_, hbounds.2.2.1, ?_⟩
  · unfold radius
    rw [SquarefreeEulerBand.radius_eq hy1 hmu]
    unfold ZetaLogLogWidth.width
    ring
  · exact SquarefreeEulerBand.analyticOnNhd_response (by linarith) hm hmu
      (fun ρ hρ ↦ (hz ρ hρ).2)

/-- The full log-log radius reaches every original marked response,
with a common constant independent of the finite prime set, valid mark,
polynomial and order. Their signed prime envelope remains explicit. -/
theorem exists_eventual_response_bound {A : ℝ} (hA : 0 < A) (hAlim : A < coefficientLimit) :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius A y →
        ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          ∀ (p : Polynomial ℂ) (N : ℕ),
            ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
              C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
                ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨T, hT, hspec⟩ := exists_eventual_radius_spec hA hAlim
  refine ⟨T, hT, ?_⟩
  intro y hy
  obtain ⟨hr, _, hru, hQ⟩ := hspec y hy
  exact SquarefreeEulerPhase.exists_response_bound_of_analytic y (radius A y)
    (by linarith) hru.le hQ

/-- For any fixed `0≤A<B` in the proved coefficient range, the
larger genuine disc absorbs the entire smaller log-log geometric scale
of every fixed valid arithmetic response. No growing-mark bound is
asserted, and the height threshold depends on the coefficients. -/
theorem exists_eventual_coefficient_scaled_decay {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A < B) (hBlim : B < coefficientLimit) :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      radius A y < radius B y ∧
        ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ q ∈ P.primeFactors, q ∉ S) → ∀ p : Polynomial ℂ,
            Tendsto (fun N : ℕ ↦ ((radius A y ^ N : ℝ) : ℂ) *
              RoughSquarefreeBare.response p S P N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨H₀, _, hb⟩ := exists_eventual_common_margin (show 0 < B by linarith) hBlim
  refine ⟨max (3 / 2) (max H₀ ZetaLogLogWidth.baseHeight), le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyH : H₀ ≤ |y| := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hybase : ZetaLogLogWidth.baseHeight ≤ |y| :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  obtain ⟨hm, hmu, hz⟩ := hb (2 * |y| + 3) (by linarith)
  have hfactor : 0 < Real.log (Real.log (2 * |y| + 3)) / Real.log (2 * |y| + 3) := by
    simpa only [ZetaLogLogWidth.width, one_mul] using
      ZetaLogLogWidth.width_pos (by norm_num : (0 : ℝ) < 1)
        (show ZetaLogLogWidth.baseHeight ≤ 2 * |y| + 3 by linarith)
  have hdiv : ZetaLogLogWidth.width A (2 * |y| + 3) <
      ZetaLogLogWidth.width B (2 * |y| + 3) := by
    simpa only [ZetaLogLogWidth.width, mul_div_assoc] using mul_lt_mul_of_pos_right hAB hfactor
  have hma := hdiv.trans hmu
  have heA : radius A y = 1 + ZetaLogLogWidth.width A (2 * |y| + 3) / 2 :=
    SquarefreeEulerBand.radius_eq hy1 hma
  have heB : radius B y = 1 + ZetaLogLogWidth.width B (2 * |y| + 3) / 2 :=
    SquarefreeEulerBand.radius_eq hy1 hmu
  have hr : radius A y < radius B y := by rw [heA, heB]; linarith
  have hwA : 0 ≤ ZetaLogLogWidth.width A (2 * |y| + 3) := by
    simpa only [ZetaLogLogWidth.width, mul_div_assoc] using mul_nonneg hA hfactor.le
  refine ⟨hr, ?_⟩
  intro S hS P hP hPS p
  apply SquarefreeEulerBand.tendsto_scaled_response (by linarith) hm hmu
    (fun ρ hρ ↦ (hz ρ hρ).2) ?_ hr S hS P hP hPS p
  rw [heA]
  positivity

end
end RiemannGaussian.SquarefreeLogLog
