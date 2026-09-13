/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVaughanLogAverage
import RiemannGaussian.ZetaSquarefreeVaughanBudget

/-!
# The original source in the complete logarithmic Vaughan average

The exact floor-cell measure is a finite probability mixture independent
of the tested integer. Its product budget vanishes at a concrete squared
near-inverse-source scale. The original finite band is therefore exactly
transported to the composite-restricted signed Riesz divisor sum.

The ordinary-prime correction remains explicit. No independent cofinal
signed bound is supplied by the averaging identity or the source limit.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.SquarefreeVaughanLogSource
noncomputable section
open VaughanLogAverage SquarefreeVaughanBudget SquarefreeVaughanProjection

/-- The normalized signed Riesz coefficient on the actual squarefree
composite support. Completing its prime deletion changes the carrier. -/
def coefficient (L : ℝ) (n : ℕ) : ℂ :=
  if Squarefree n ∧ ¬ n.Prime then ((-Real.log n * riesz L n / L : ℝ) : ℂ) else 0

/-- The explicit divisor coefficient equals the genuine continuous
average, with the prime and nonsquarefree deletions justified separately. -/
theorem coefficient_eq_average {L : ℝ} (hL : 0 < L) (n : ℕ) :
    coefficient L n = if Squarefree n then ((logarithmicAverage L n / L : ℝ) : ℂ) else 0 := by
  by_cases hn : Squarefree n
  · by_cases hp : n.Prime
    · simp [coefficient, hn, hp, logarithmicAverage_prime hL.le hp]
    · simp [coefficient, hn, hp, logarithmicAverage_eq_riesz_of_squarefree_composite hL.le hn hp]
  · simp [coefficient, hn]

/-- The continuous logarithmic average is the already controlled finite
mixture of whole squarefree Vaughan coefficients, with its exact weights. -/
theorem coefficient_eq_mixture {L : ℝ} (hL : 0 < L) (n : ℕ) :
    coefficient L n = mixture (cutoffPairs L) (cellWeight L) Prod.fst Prod.snd n := by
  rw [coefficient_eq_average hL, mixture]
  by_cases hn : Squarefree n
  · simp only [if_pos hn, logarithmicAverage_div_eq_mixture hL,
      Complex.ofReal_sum, Complex.ofReal_mul, squarefreePart]
  · simp [hn, squarefreePart]

/-- The complete normalized divisor coefficient keeps the original
uniform majorant and therefore the original finite-band error estimate. -/
theorem norm_coefficient_le {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ‖coefficient L n‖ ≤ zetaMoebiusLogMajorant n := by
  rw [coefficient_eq_mixture hL]
  exact norm_mixture_le _ _ _ _ (fun q _ ↦ cellWeight_nonneg hL q) (sum_cellWeight hL) n

/-- Completing the squarefree divisor sum restores precisely the
ordinary-prime logarithmic endpoint. It cannot be dropped in a bound. -/
theorem coefficient_eq_completed_with_prime {L : ℝ} (hL : 0 < L) (n : ℕ) :
    coefficient L n =
      (if Squarefree n then ((-Real.log n * riesz L n / L : ℝ) : ℂ) else 0) +
        (if n.Prime then ((Real.log n * min L (Real.log n) / L : ℝ) : ℂ) else 0) := by
  rw [coefficient_eq_average hL]
  by_cases hp : n.Prime
  · have he := logarithmicAverage_eq_riesz hL.le n
    rw [logarithmicAverage_prime hL.le hp, ArithmeticFunction.vonMangoldt_apply_prime hp] at he
    simp only [if_pos hp.squarefree, if_pos hp, logarithmicAverage_prime hL.le hp,
      zero_div, Complex.ofReal_zero, ← Complex.ofReal_add]
    have he' : -Real.log n * riesz L n / L + Real.log n * min L (Real.log n) / L = 0 := by
      rw [← add_div, ← he, zero_div]
    rw [he', Complex.ofReal_zero]
  · by_cases hn : Squarefree n
    · simp only [if_pos hn, if_neg hp, add_zero,
        logarithmicAverage_eq_riesz_of_squarefree_composite hL.le hn hp]
    · simp [hn, hp]

/-- A concrete logarithmic length reaches the square of the damped
inverse-source cutoff. The added two handles every early order positively. -/
def length (u : ℝ) (N : ℕ) : ℝ :=
  Real.log ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2)

/-- The concrete averaging interval has strictly positive length at
every order, so its normalization never invokes division at zero. -/
theorem length_pos (u : ℝ) (N : ℕ) : 0 < length u N := by
  apply Real.log_pos
  have h : (0 : ℝ) ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N := Nat.cast_nonneg _
  nlinarith

/-- Every actual floor cell at the squared cutoff costs at most twice
the shifted damped cutoff in the square-root product budget. -/
theorem cell_budget_le (u : ℝ) (N : ℕ) {q : ℕ × ℕ} (hq : q ∈ cutoffPairs (length u N)) :
    ZetaVaughanCutoffBudget.budget q.1 q.2 ≤
      2 * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) := by
  have h := cutoffPairs_product_le hq
  rw [length, Real.exp_log (by positivity)] at h
  rw [ZetaVaughanCutoffBudget.budget, ← Real.sqrt_mul (by positivity),
    Real.sqrt_le_left (by positivity)]
  push_cast at h
  have hD : (0 : ℝ) ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N := Nat.cast_nonneg _
  nlinarith

/-- The complete average budget tends to zero independently of any zero
hypothesis. All actual cells, weights and early orders are included. -/
theorem tendsto_average_budget {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N ↦ u ^ (N + 1) * ∑ q ∈ cutoffPairs (length u N),
      cellWeight (length u N) q * ZetaVaughanCutoffBudget.budget q.1 q.2) atTop (𝓝 0) := by
  have hD := ZetaVaughanCutoffBudget.tendsto_budget_linearDampedCutoff hu hu1
  have he (D : ℕ) : ZetaVaughanCutoffBudget.budget D D = (D : ℝ) + 1 := by
    rw [ZetaVaughanCutoffBudget.budget, Real.mul_self_sqrt (by positivity)]
  simp only [he] at hD
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hu.le hu1).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun N ↦ u ^ (N + 1) *
      (2 * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ))) atTop (𝓝 0) := by
    convert (hD.add hp).const_mul 2 using 1
    · funext N; simp only [Function.comp_apply]; ring
    · simp
  apply squeeze_zero (fun N ↦ mul_nonneg (by positivity) (Finset.sum_nonneg
    (fun q _ ↦ mul_nonneg (cellWeight_nonneg (length_pos u N) q)
      (ZetaVaughanCutoffBudget.budget_pos _ _).le))) (fun N ↦ ?_) hlim
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ q ∈ cutoffPairs (length u N), cellWeight (length u N) q *
        (2 * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ)) :=
      Finset.sum_le_sum (fun q hq ↦ mul_le_mul_of_nonneg_left (cell_budget_le u N hq)
        (cellWeight_nonneg (length_pos u N) q))
    _ = _ := by rw [← Finset.sum_mul, sum_cellWeight (length_pos u N), one_mul]

/-- The explicit composite-restricted Riesz divisor sum retains the
original negative-multiplicity source on the entire original finite band.
This is a conditional source identity, not its independent signed floor. -/
theorem tendsto_actual_riesz_band (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticBand
      (coefficient (length (3 / 2 - rho.1.re) N)) (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := tendsto_actual_mixture_band_of_budget rho hrho
    (fun N ↦ cutoffPairs (length (3 / 2 - rho.1.re) N))
    (fun N ↦ cellWeight (length (3 / 2 - rho.1.re) N)) (fun _ ↦ Prod.fst) (fun _ ↦ Prod.snd)
    (fun N q _ ↦ cellWeight_nonneg (length_pos _ N) q)
    (fun N ↦ sum_cellWeight (length_pos _ N))
    (tendsto_average_budget (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith))
  apply h.congr'
  filter_upwards [] with N
  congr 2
  funext n
  exact (coefficient_eq_mixture (length_pos _ N) n).symm

end
end RiemannGaussian.SquarefreeVaughanLogSource
