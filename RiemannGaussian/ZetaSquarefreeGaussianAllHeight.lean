/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianAllHeight
import RiemannGaussian.ZetaSquarefreeLocalWindow

/-!
# The adaptive Gaussian region in the original squarefree response

Every center with `abs(y) ≥ 500002` now has an explicit Cauchy radius greater
than one, with no upper height ceiling. The full doubled-ordinate window is
included in the margin. The original marked responses retain their signed
two-harmonic prime envelope. The response constant may depend on the center;
no uniform constant over this unbounded domain or ordinary-prime floor is
asserted.
-/

namespace RiemannGaussian.SquarefreeGaussianAllHeight
noncomputable section
open Complex

/-- The explicit width at the largest enlarged height in the full
doubled-ordinate window. The plus five includes both enlargements. -/
def margin (y : ℝ) : ℝ :=
  min (1 / 450000) (32 / (45 * Real.log (2 * |y| + 5)))

/-- Every moving margin is positive and below the original width ceiling. -/
theorem margin_bounds (y : ℝ) : 0 < margin y ∧ margin y ≤ 1 / 450000 := by
  have hlog : 0 < Real.log (2 * |y| + 5) := Real.log_pos (by linarith [abs_nonneg y])
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _⟩

/-- The complete uncapped Cauchy radius provided by the moving margin. -/
def radius (y : ℝ) : ℝ := 1 + margin y / 2

/-- The actual radius always exceeds one and stays below the uniform
two-harmonic remainder threshold. -/
theorem radius_bounds (y : ℝ) : 1 < radius y ∧ radius y < 9 / 8 := by
  obtain ⟨hm, hmu⟩ := margin_bounds y
  unfold radius
  constructor <;> linarith

/-- Above the explicit starting height the pole-separation cap is inactive. -/
theorem radius_eq {y : ℝ} (hy : 500002 ≤ |y|) :
    SquarefreeEulerBand.radius y (margin y) = radius y := by
  exact SquarefreeEulerBand.radius_eq (by linarith)
    (by linarith [(margin_bounds y).2])

/-- Every ordinate in the complete doubled window lies above the proved
starting height and below the exact logarithmic ceiling used by its margin. -/
theorem window_heights {y t : ℝ} (hy : 500002 ≤ |y|)
    (ht : |t - 2 * y| ≤ 2 * radius y) :
    1000000 ≤ |t| ∧ ZetaNearOneBudgetLimit.scale t ≤ Real.log (2 * |y| + 5) := by
  have h := (abs_abs_sub_abs_le_abs_sub t (2 * y)).trans ht
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor
  · linarith [(radius_bounds y).2]
  · apply Real.log_le_log (by positivity : 0 < |t| + 2)
    linarith [(radius_bounds y).2]

/-- The adaptive zero-free theorem discharges the exact local denominator
window at every eligible center, including heights beyond the former ceiling. -/
theorem window_margin {y : ℝ} (hy : 500002 ≤ |y|) (ρ : NontrivialZetaZero)
    (hρ : |ρ.1.im - 2 * y| ≤ 2 * SquarefreeEulerBand.radius y (margin y)) :
    ρ.1.re < 1 - margin y := by
  rw [radius_eq hy] at hρ
  obtain ⟨ht, hL⟩ := window_heights hy hρ
  have hpositive : 0 < ZetaNearOneBudgetLimit.scale ρ.1.im :=
    lt_of_lt_of_le (by norm_num) (ZetaGaussianBandBudget.scale_lower ht)
  have hm : margin y ≤ ZetaGaussianAllHeight.explicitWidth ρ.1.im := by
    rw [ZetaGaussianAllHeight.explicitWidth_eq_min]
    apply min_le_min_left
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hz := ZetaGaussianAllHeight.exact_margin ρ ht
  linarith

/-- The literal quotient `zeta(s)/zeta(2*s)` is analytic on a
neighbourhood of the full explicit closed disc at every eligible height. -/
theorem analyticOnNhd_response {y : ℝ} (hy : 500002 ≤ |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) (radius y)) := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.analyticOnNhd_response (by linarith)
    (margin_bounds y).1 (by linarith [(margin_bounds y).2]) (window_margin hy)

/-- The original marked arithmetic responses inherit the full explicit
radius and signed prime envelope at every eligible center. The constant
depends on that center, uniformly over all the other stated parameters. -/
theorem exists_response_bound {y : ℝ} (hy : 500002 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.exists_response_bound (by linarith)
    (margin_bounds y).1 (by linarith [(margin_bounds y).2]) (window_margin hy)

end
end RiemannGaussian.SquarefreeGaussianAllHeight
