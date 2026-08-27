import RiemannGaussian.FiniteToEntireRadialShellTransport
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Summable radial heat shells

This file proves that the explicit quadratic-Gaussian bound for the selected
radial shells is genuinely summable.  It also records a reusable triangular
array form of Tannery's theorem: pointwise limits can be summed when every
entry before the moving cutoff is bounded by one fixed summable sequence.

The radial majorant uses a nonnegative clearance `max (r - ‖z‖) 0`, so it
covers the finitely many initial shells that need not yet surround the
observation point.  Eventually the selected radius exceeds the observation
norm, and a quadratic Gaussian is compared directly with a linear
exponential tail times a quadratic polynomial.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The stage-independent bound used for the `m`th selected radial heat
shell.  The positive-part clearance handles initial shells uniformly. -/
def selectedRadialHeatShellMajorant
    (K : ℝ) (z : ℂ) (tau : ℝ) (m : ℕ) : ℝ :=
  (K *
      (2 * (quantitativeSpectralRadialBoundary (m + 1) + 1) + 1) ^ 2 /
        Real.log 2) *
    (tau⁻¹ * Real.exp
      (-((max
        (quantitativeSpectralRadialBoundary m - ‖z‖) 0) ^ 2 * tau)))

/-- The selected radial shell majorant is nonnegative for nonnegative growth
constant and positive proper time. -/
theorem selectedRadialHeatShellMajorant_nonneg
    {K : ℝ} (hK : 0 ≤ K) (z : ℂ) {tau : ℝ} (htau : 0 < tau)
    (m : ℕ) :
    0 ≤ selectedRadialHeatShellMajorant K z tau m := by
  unfold selectedRadialHeatShellMajorant
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  positivity

/-- A quadratic polynomial times a positive linear exponential tail is
summable with the shift needed by the selected outer radii. -/
theorem summable_shiftedQuadratic_mul_exp_neg_nat
    (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ ↦
      C * (2 * ((n : ℝ) + 3) + 1) ^ 2 *
        Real.exp (-c * (n : ℝ)) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hc
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hc
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 hc
  have hpoly : Summable fun n : ℕ ↦
      (2 * ((n : ℝ) + 3) + 1) ^ 2 *
        Real.exp (-c * (n : ℝ)) := by
    refine ((h2.mul_left 4).add
      ((h1.mul_left 28).add (h0.mul_left 49))).congr fun n ↦ ?_
    norm_num
    ring
  refine (hpoly.mul_left C).congr fun n ↦ ?_
  ring

/-- For every fixed observation point and positive proper time, the exact
quadratic-Gaussian selected-shell majorant is summable. -/
theorem summable_selectedRadialHeatShellMajorant
    {K : ℝ} (hK : 0 ≤ K) (z : ℂ) {tau : ℝ} (htau : 0 < tau) :
    Summable (selectedRadialHeatShellMajorant K z tau) := by
  let c : ℝ := tau / 4
  let C : ℝ := (K / Real.log 2) * tau⁻¹
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  have hcomparison : Summable fun n : ℕ ↦
      C * (2 * ((n : ℝ) + 3) + 1) ^ 2 *
        Real.exp (-c * (n : ℝ)) :=
    summable_shiftedQuadratic_mul_exp_neg_nat C hc
  apply hcomparison.of_norm_bounded_eventually_nat
  obtain ⟨N, hN⟩ := exists_nat_ge (max (2 * ‖z‖) 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have htwoNorm : 2 * ‖z‖ ≤ (n : ℝ) :=
    (le_max_left _ _).trans hN |>.trans hNn
  have hnOne : 1 ≤ (n : ℝ) :=
    (le_max_right _ _).trans hN |>.trans hNn
  have hrLower : (n : ℝ) < quantitativeSpectralRadialBoundary n :=
    (quantitativeSpectralRadialBoundary_spec n).1
  have hclearance :
      0 ≤ quantitativeSpectralRadialBoundary n - ‖z‖ := by
    nlinarith
  have hclearanceSq :
      (n : ℝ) / 4 ≤
        (quantitativeSpectralRadialBoundary n - ‖z‖) ^ 2 := by
    have hhalf :
        (n : ℝ) / 2 ≤
          quantitativeSpectralRadialBoundary n - ‖z‖ := by
      nlinarith
    nlinarith [sq_nonneg
      (quantitativeSpectralRadialBoundary n - ‖z‖ - (n : ℝ) / 2)]
  have houter :
      quantitativeSpectralRadialBoundary (n + 1) < (n : ℝ) + 2 := by
    have h := (quantitativeSpectralRadialBoundary_spec (n + 1)).2.1
    norm_num [Nat.cast_add] at h
    linarith
  have hpoly :
      (2 * (quantitativeSpectralRadialBoundary (n + 1) + 1) + 1) ^ 2 ≤
        (2 * ((n : ℝ) + 3) + 1) ^ 2 := by
    have hleft :
        0 ≤ 2 * (quantitativeSpectralRadialBoundary (n + 1) + 1) + 1 := by
      have hpos := quantitativeSpectralRadialBoundary_pos (n + 1)
      positivity
    nlinarith
  have hexp :
      Real.exp
          (-((quantitativeSpectralRadialBoundary n - ‖z‖) ^ 2 * tau)) ≤
        Real.exp (-c * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (selectedRadialHeatShellMajorant_nonneg hK z htau n)]
  unfold selectedRadialHeatShellMajorant
  rw [max_eq_left hclearance]
  calc
    (K *
          (2 * (quantitativeSpectralRadialBoundary (n + 1) + 1) + 1) ^ 2 /
            Real.log 2) *
        (tau⁻¹ * Real.exp
          (-((quantitativeSpectralRadialBoundary n - ‖z‖) ^ 2 * tau))) =
        C *
          (2 * (quantitativeSpectralRadialBoundary (n + 1) + 1) + 1) ^ 2 *
            Real.exp
              (-((quantitativeSpectralRadialBoundary n - ‖z‖) ^ 2 * tau)) := by
      dsimp [C]
      ring
    _ ≤ C * (2 * ((n : ℝ) + 3) + 1) ^ 2 *
          Real.exp
            (-((quantitativeSpectralRadialBoundary n - ‖z‖) ^ 2 * tau)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_nonneg _)
    _ ≤ C * (2 * ((n : ℝ) + 3) + 1) ^ 2 *
          Real.exp (-c * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hC (sq_nonneg _))

/-- A triangular-array form of Tannery's theorem for real series.  Only the
entries before the moving cutoff must satisfy the domination hypothesis;
entries after it are replaced by zero.  The conclusion records both
summability of the pointwise limit and convergence of the moving finite sums. -/
theorem summable_limit_and_tendsto_sum_range_of_dominated
    (a : ℕ → ℕ → ℝ) (g bound : ℕ → ℝ)
    (hboundNonneg : ∀ m, 0 ≤ bound m)
    (hboundSummable : Summable bound)
    (hlimit : ∀ m, Tendsto (fun n ↦ a n m) atTop (nhds (g m)))
    (hdominated : ∀ n m, m < n → |a n m| ≤ bound m) :
    Summable g ∧
      Tendsto (fun n ↦ ∑ m ∈ Finset.range n, a n m)
        atTop (nhds (∑' m, g m)) := by
  have hgBound (m : ℕ) : ‖g m‖ ≤ bound m := by
    apply le_of_tendsto (tendsto_norm.comp (hlimit m))
    filter_upwards [eventually_gt_atTop m] with n hmn
    simpa [Real.norm_eq_abs] using hdominated n m hmn
  have hgSummable : Summable g :=
    hboundSummable.of_norm_bounded hgBound
  let f : ℕ → ℕ → ℝ := fun n m ↦
    if m < n then a n m else 0
  have hfLimit (m : ℕ) :
      Tendsto (fun n ↦ f n m) atTop (nhds (g m)) := by
    apply (hlimit m).congr'
    filter_upwards [eventually_gt_atTop m] with n hmn
    simp [f, hmn]
  have hfBound : ∀ᶠ n in atTop, ∀ m, ‖f n m‖ ≤ bound m := by
    filter_upwards with n m
    by_cases hmn : m < n
    · simpa [f, hmn, Real.norm_eq_abs] using hdominated n m hmn
    · simp [f, hmn, hboundNonneg m]
  have hTannery := tendsto_tsum_of_dominated_convergence
    hboundSummable hfLimit hfBound
  refine ⟨hgSummable, hTannery.congr' ?_⟩
  exact Eventually.of_forall fun n ↦ by
    calc
      (∑' m, f n m) = ∑ m ∈ Finset.range n, f n m := by
        apply tsum_eq_sum
        intro m hm
        have hmn : ¬m < n := by
          simpa [Finset.mem_range] using hm
        simp [f, hmn]
      _ = ∑ m ∈ Finset.range n, a n m := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [f, Finset.mem_range.mp hm]

end

end RiemannGaussian
