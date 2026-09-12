/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiModulatedZeroFree
import RiemannGaussian.ZetaSquarefreeEulerBandRadius

/-!
# The current modulated zero-free region in the arithmetic response

The proved `24/125` region gives the actual squarefree quotient an eventual
analytic radius `1+12/(125*log(2*abs(y)+3))`. This is strictly larger than
the earlier Fermi radius. Every polynomial, excluded prime set, and valid
squarefree mark receives the larger Cauchy bound with its signed phase
envelope intact. For fixed marks, even the old outer geometric rate now
gives a response tending to zero.

The displayed radius is proved valid beyond a finite, unevaluated height;
its definition alone does not assert validity at small heights. The old
all-height theorem remains available. No prime-tail lower bound or RH
claim follows from decay of the complete squarefree quotient.
-/

namespace RiemannGaussian.SquarefreeEulerModulated
noncomputable section
open Complex Filter Topology

/-- The larger of the old radius and the radius suggested by the actual
modulated region. Validity is proved eventually below, with no numerical
height certificate asserted. -/
def radius (y : ℝ) : ℝ :=
  SquarefreeEulerBand.radius y
    (max (zetaFermiZeroMargin (2 * |y| + 3)) (24 / (125 * Real.log (2 * |y| + 3))))

/-- Combining widths never discards any of the previous analytic disc. -/
theorem fermi_radius_le (y : ℝ) : squarefreeEulerFermiRadius y ≤ radius y :=
  SquarefreeEulerBand.radius_mono y (le_max_left _ _)

private theorem exists_eventual_margin_spec :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ H : ℝ, T ≤ H →
      0 < 24 / (125 * Real.log H) ∧ 24 / (125 * Real.log H) < 1 / 4 ∧
        zetaFermiZeroMargin H < 24 / (125 * Real.log H) ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          ρ.1.re < 1 - 24 / (125 * Real.log H) := by
  obtain ⟨T₀, hT₀, hband⟩ := GaussianFermiModulatedZeroFree.exists_eventual_common_margin
  obtain ⟨T₁, _, hold⟩ := exists_eventual_fermiZeroMargin_eq
  refine ⟨max T₀ (max T₁ (Real.exp 1)), hT₀.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hH₀ : T₀ ≤ H := (le_max_left _ _).trans hH
  have hH₁ : T₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHp : 0 < H := by linarith
  have hlog : 1 ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hH))
    simpa only [Real.log_exp] using h
  obtain ⟨hm, hmu, hz⟩ := hband H hH₀
  have he := (hold H (by simpa only [abs_of_pos hHp] using hH₁)).1
  rw [abs_of_pos hHp] at he
  refine ⟨hm, hmu, ?_, fun ρ hρ ↦ (hz ρ hρ).2⟩
  rw [he]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  linarith

/-- The stronger region supplies a strictly larger genuine analytic disc
at every sufficiently large ordinate. The exact formula and full closed
disc analyticity are proved together, including the pole exclusions. -/
theorem exists_eventual_radius_spec :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      squarefreeEulerFermiRadius y < radius y ∧
        radius y = 1 + 12 / (125 * Real.log (2 * |y| + 3)) ∧
        radius y < 9 / 8 ∧
        AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) (radius y)) := by
  obtain ⟨T, _, hT⟩ := exists_eventual_margin_spec
  refine ⟨max (3 / 2) T, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyT : T ≤ |y| := (le_max_right _ _).trans hy
  obtain ⟨hm, hmu, hgain, hband⟩ := hT (2 * |y| + 3) (by linarith)
  have he : radius y = SquarefreeEulerBand.radius y (24 / (125 * Real.log (2 * |y| + 3))) := by
    unfold radius
    rw [max_eq_right hgain.le]
  have hnew := SquarefreeEulerBand.radius_eq hy1 hmu
  have hold := SquarefreeEulerBand.radius_eq hy1 (zetaFermiZeroMargin_bounds (2 * |y| + 3)).2
  have hy' : 1 < |y| := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · change SquarefreeEulerBand.radius y (zetaFermiZeroMargin (2 * |y| + 3)) < radius y
    rw [he, hnew, hold]
    linarith
  · rw [he, hnew]
    ring
  · rw [he]
    exact (SquarefreeEulerBand.radius_bounds hy' hm hmu).2.2.1
  · rw [he]
    exact SquarefreeEulerBand.analyticOnNhd_response hy' hm hmu hband

/-- The larger actual disc reaches all marked arithmetic responses, with
one constant independent of the polynomial, moment order, excluded prime
set and squarefree mark. Their full signed phase envelope is retained. -/
theorem exists_eventual_response_bound :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y →
        ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          ∀ (p : Polynomial ℂ) (N : ℕ),
            ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
              C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
                ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨T, hT, hspec⟩ := exists_eventual_radius_spec
  refine ⟨T, hT, ?_⟩
  intro y hy
  obtain ⟨hgain, _, hru, hQ⟩ := hspec y hy
  have hy1 : 1 < |y| := by linarith
  exact SquarefreeEulerPhase.exists_response_bound_of_analytic y (radius y)
    (by linarith [(squarefreeEulerFermiRadius_bounds hy1).1]) hru.le hQ

/-- The gain is an actual stronger asymptotic estimate: with any fixed
valid arithmetic mark and complex polynomial, scaling by the entire old
Fermi outer radius to the moment order still leaves a response tending
to zero. Every zero-free and analytic premise is discharged. -/
theorem exists_eventual_fermi_scaled_decay :
    ∃ T : ℝ, 3 / 2 ≤ T ∧ ∀ y : ℝ, T ≤ |y| →
      ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ q ∈ P.primeFactors, q ∉ S) → ∀ p : Polynomial ℂ,
          Tendsto (fun N : ℕ ↦ ((squarefreeEulerFermiRadius y ^ N : ℝ) : ℂ) *
            RoughSquarefreeBare.response p S P N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨T₀, _, hmargin⟩ := exists_eventual_margin_spec
  obtain ⟨T₁, hT₁, hspec⟩ := exists_eventual_radius_spec
  refine ⟨max T₀ T₁, hT₁.trans (le_max_right _ _), ?_⟩
  intro y hy S hS P hP hPS p
  have hy₀ : T₀ ≤ |y| := (le_max_left _ _).trans hy
  have hy₁ : T₁ ≤ |y| := (le_max_right _ _).trans hy
  have hy1 : 1 < |y| := by linarith
  obtain ⟨hm, hmu, hgain, hband⟩ := hmargin (2 * |y| + 3) (by linarith)
  have he : radius y = SquarefreeEulerBand.radius y (24 / (125 * Real.log (2 * |y| + 3))) := by
    unfold radius
    rw [max_eq_right hgain.le]
  have hr := (hspec y hy₁).1
  rw [he] at hr
  exact SquarefreeEulerBand.tendsto_scaled_response hy1 hm hmu hband
    (by linarith [(squarefreeEulerFermiRadius_bounds hy1).1]) hr S hS P hP hPS p

end
end RiemannGaussian.SquarefreeEulerModulated
