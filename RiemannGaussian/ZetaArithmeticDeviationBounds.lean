/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArithmeticLogWindow
import RiemannGaussian.LogarithmicDeviation

/-!
# Uniform arithmetic bounds from the deviation profile

Every admissible pair of cutoffs gives a common geometric error bound across a whole bounded radius interval, arbitrary heights and finite dominated coefficient families. Every fixed factorial filter retains its cost.
-/

namespace RiemannGaussian.ZetaArithmeticDeviationBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open LogarithmicDeviation
open ZetaArithmeticLogWindow

/-- A single normalized bound works for arbitrary dominated arithmetic
coefficients, finite selections and heights. The factorial filter is fixed
but keeps every coefficient and shift in its explicit finite cost. -/
theorem norm_normalized_sum_le (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u x σ : ℝ}
    (hu : 0 < u) (hx : 0 < x) (hσ : 1 < σ)
    (hlog : ∀ n ∈ S, (σ - 3 / 2 + x⁻¹) * Real.log n ≤
      (N : ℝ) * ((σ - 3 / 2 + x⁻¹) * x)) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ S,
      a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (u * (x * Real.exp ((σ - 3 / 2 + x⁻¹) * x))) ^ N *
        (u * tiltConstant P x⁻¹ σ) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hb := norm_sum_filter_of_log_bound S a ha P N y σ x⁻¹
    ((σ - 3 / 2 + x⁻¹) * x) hσ (inv_pos.mpr hx) hlog
  simp only [inv_inv] at hb
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by
    rw [pow_succ, mul_pow]
    ring)

/-- Every changing finite selection beyond any admissible upper cutoff
decays independently, including arbitrarily changing heights. -/
theorem tendsto_upper_of_deviation_cost (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, n ∈ S N → ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℕ → ℝ) {u x : ℝ} (hu : 0 < u) (hx : 2 < x)
    (hcost : Real.log (2 * u) < deviationCost x)
    (hS : ∀ N n, n ∈ S N → x * N ≤ Real.log n) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y N) n)
      atTop (nhds 0) := by
  obtain ⟨σ, hσ, hsign, hr⟩ := exists_upper_tilt hu hx hcost
  have hx0 : 0 < x := by linarith
  apply squeeze_zero_norm (fun N => norm_normalized_sum_le (S N) (a N) (ha N)
    P N (y N) hu hx0 hσ (fun n hn => by
      have hh := mul_le_mul_of_nonpos_left (hS N n hn) hsign.le
      nlinarith only [hh]))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).mul_const
      (u * tiltConstant P x⁻¹ σ)

/-- Every changing finite selection below any admissible lower cutoff
decays independently, with all original phases and arbitrary moving heights. -/
theorem tendsto_lower_of_deviation_cost (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, n ∈ S N → ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℕ → ℝ) {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (hx2 : x < 2)
    (hcost : Real.log (2 * u) < deviationCost x)
    (hS : ∀ N n, n ∈ S N → Real.log n ≤ x * N) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y N) n)
      atTop (nhds 0) := by
  obtain ⟨σ, hσ, hsign, hr⟩ := exists_lower_tilt hu hx hx2 hcost
  apply squeeze_zero_norm (fun N => norm_normalized_sum_le (S N) (a N) (ha N)
    P N (y N) hu hx hσ (fun n hn => by
      have hh := mul_le_mul_of_nonneg_left (hS N n hn) hsign.le
      nlinarith only [hh]))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).mul_const
      (u * tiltConstant P x⁻¹ σ)

/-- Every pair of admissible deviation cutoffs removes both complete
outer tails with independently vanishing error. The coefficients, masks
and heights may all vary with the order; no zero premise is used. -/
theorem tendsto_sub_deviationBand (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, n ∈ S N → ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℕ → ℝ) {u x₀ x₁ : ℝ}
    (hu : 0 < u) (hx₀ : 0 < x₀) (hx₀2 : x₀ < 2) (hx₁ : 2 < x₁)
    (hcost₀ : Real.log (2 * u) < deviationCost x₀)
    (hcost₁ : Real.log (2 * u) < deviationCost x₁) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ((∑ n ∈ S N, a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y N) n) -
        ∑ n ∈ deviationBand (S N) x₀ x₁ N,
          a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y N) n))
      atTop (nhds 0) := by
  have hl := tendsto_lower_of_deviation_cost
    (fun N => (S N).filter (fun n => Real.log n ≤ x₀ * N)) a
    (fun N n hn => ha N n (Finset.mem_filter.mp hn).1) P y hu hx₀ hx₀2 hcost₀
    (fun _ _ hn => (Finset.mem_filter.mp hn).2)
  have hh := tendsto_upper_of_deviation_cost
    (fun N => (S N).filter (fun n => x₁ * N < Real.log n)) a
    (fun N n hn => ha N n (Finset.mem_filter.mp hn).1) P y hu hx₁ hcost₁
    (fun _ _ hn => (Finset.mem_filter.mp hn).2.le)
  have h := hl.add hh
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [sum_sub_deviationBand (hab := by linarith)]
  ring

/-- A single strict geometric rate and finite constant bound the full
discarded window error for ALL radii in a prescribed bounded interval,
every height and finite dominated arithmetic selection, at every order.
The cutoff criterion is proved for every admissible pair, not sampled. -/
theorem exists_uniform_deviation_bound (P : Polynomial ℂ) {U x₀ x₁ : ℝ}
    (hU : 0 < U) (hx₀ : 0 < x₀) (hx₀2 : x₀ < 2) (hx₁ : 2 < x₁)
    (hcost₀ : Real.log (2 * U) < deviationCost x₀)
    (hcost₁ : Real.log (2 * U) < deviationCost x₁) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
        (∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n) →
        ∀ (y u : ℝ), 0 ≤ u → u ≤ U →
          ‖(u : ℂ) ^ (N + 1) *
            ((∑ n ∈ S, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
              ∑ n ∈ deviationBand S x₀ x₁ N,
                a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)‖ ≤ r ^ N * C := by
  obtain ⟨σ₀, hσ₀, hsign₀, hr₀⟩ := exists_lower_tilt hU hx₀ hx₀2 hcost₀
  obtain ⟨σ₁, hσ₁, hsign₁, hr₁⟩ := exists_upper_tilt hU hx₁ hcost₁
  have hx₁0 : 0 < x₁ := by linarith
  let r₀ := U * (x₀ * Real.exp ((σ₀ - 3 / 2 + x₀⁻¹) * x₀))
  let r₁ := U * (x₁ * Real.exp ((σ₁ - 3 / 2 + x₁⁻¹) * x₁))
  let C₀ := U * tiltConstant P x₀⁻¹ σ₀
  let C₁ := U * tiltConstant P x₁⁻¹ σ₁
  have hC₀ : 0 ≤ C₀ := mul_nonneg hU.le (tiltConstant_nonneg P (inv_pos.mpr hx₀))
  have hC₁ : 0 ≤ C₁ := mul_nonneg hU.le (tiltConstant_nonneg P (inv_pos.mpr hx₁0))
  have hr₀0 : 0 ≤ r₀ := by dsimp only [r₀]; positivity
  have hr₁0 : 0 ≤ r₁ := by dsimp only [r₁]; positivity
  refine ⟨max r₀ r₁, C₀ + C₁, hr₀0.trans (le_max_left _ _),
    max_lt hr₀ hr₁, add_nonneg hC₀ hC₁, ?_⟩
  intro N S a ha y u hu huU
  have hl := norm_normalized_sum_le
    (S.filter (fun (n : ℕ) => Real.log n ≤ x₀ * N)) a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) P N y hU hx₀ hσ₀ (by
      intro n hn
      have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hn).2 hsign₀.le
      nlinarith only [h])
  have hh := norm_normalized_sum_le
    (S.filter (fun (n : ℕ) => x₁ * N < Real.log n)) a
    (fun n hn => ha n (Finset.mem_filter.mp hn).1) P N y hU hx₁0 hσ₁ (by
      intro n hn
      have h := mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hn).2.le hsign₁.le
      nlinarith only [h])
  apply (sourceScale_norm_mono hu huU N _).trans
  rw [sum_sub_deviationBand (hab := by linarith), mul_add]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ r₀ ^ N * C₀ + r₁ ^ N * C₁ := add_le_add hl hh
    _ ≤ (max r₀ r₁) ^ N * C₀ + (max r₀ r₁) ^ N * C₁ := add_le_add
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr₀0 (le_max_left _ _) N) hC₀)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr₁0 (le_max_right _ _) N) hC₁)
    _ = _ := by ring

/-- The uniform arithmetic rate pays changing source radii without
assuming those radii converge. Heights, coefficients and masks may change
independently as well; the fixed filter cost is retained. -/
theorem tendsto_sub_deviationBand_moving_radius (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, n ∈ S N → ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y u : ℕ → ℝ) {U x₀ x₁ : ℝ}
    (hU : 0 < U) (hu : ∀ N, 0 ≤ u N ∧ u N ≤ U)
    (hx₀ : 0 < x₀) (hx₀2 : x₀ < 2) (hx₁ : 2 < x₁)
    (hcost₀ : Real.log (2 * U) < deviationCost x₀)
    (hcost₁ : Real.log (2 * U) < deviationCost x₁) :
    Tendsto (fun N : ℕ => (u N : ℂ) ^ (N + 1) *
      ((∑ n ∈ S N, a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y N) n) -
        ∑ n ∈ deviationBand (S N) x₀ x₁ N,
          a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y N) n))
      atTop (nhds 0) := by
  obtain ⟨r, C, hr0, hr1, _, hb⟩ := exists_uniform_deviation_bound P hU hx₀ hx₀2 hx₁ hcost₀ hcost₁
  apply squeeze_zero_norm (fun N => hb N (S N) (a N) (ha N) (y N) (u N) (hu N).1 (hu N).2)
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C

end
end RiemannGaussian.ZetaArithmeticDeviationBounds
