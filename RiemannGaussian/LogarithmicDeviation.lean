/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# The ideal logarithmic deviation profile

The exact profile classifies all successful positive exponential tilts. Every summability and convexity cost remains explicit. It does not classify signed arithmetic methods.
-/

namespace RiemannGaussian.LogarithmicDeviation
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The exact scalar deviation cost for the logarithmic integer scale.
It does not contain any zero or arithmetic cancellation hypothesis. -/
def deviationCost (x : ℝ) : ℝ := x / 2 - 1 - Real.log (x / 2)

/-- Source normalization enters the same scalar profile as the full
factorial moment, before any outer-tail estimate is made. -/
theorem log_rate_eq_deviation {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    Real.log (u * x) + 1 - x / 2 = Real.log (2 * u) - deviationCost x := by
  rw [Real.log_mul (ne_of_gt hu) (ne_of_gt hx),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hu)]
  unfold deviationCost
  rw [Real.log_div (ne_of_gt hx) (by norm_num)]
  ring

/-- Any upper cutoff with a positive deviation margin supplies an
admissible summable tilt with a strictly subunit normalized rate. This
constructs the tilt from the margin and covers every such cutoff. -/
theorem exists_upper_tilt {u x : ℝ} (hu : 0 < u) (hx : 2 < x)
    (hcost : Real.log (2 * u) < deviationCost x) :
    ∃ σ : ℝ, 1 < σ ∧ σ - 3 / 2 + x⁻¹ < 0 ∧
      u * (x * Real.exp ((σ - 3 / 2 + x⁻¹) * x)) < 1 := by
  let δ := deviationCost x - Real.log (2 * u)
  let b := min (δ / 2) ((x - 2) / 4)
  have hx0 : 0 < x := by linarith
  have hδ : 0 < δ := sub_pos.mpr hcost
  have hb : 0 < b := lt_min (by positivity) (by linarith)
  have hbδ : b ≤ δ / 2 := min_le_left _ _
  have hbx : b ≤ (x - 2) / 4 := min_le_right _ _
  refine ⟨1 + b / x, by linarith [div_pos hb hx0], ?_, ?_⟩
  · have he : (1 + b / x - 3 / 2 + x⁻¹) * x = 1 - x / 2 + b := by
      field_simp
      ring
    have hneg : (1 + b / x - 3 / 2 + x⁻¹) * x < 0 := by rw [he]; linarith
    by_contra h
    have hp := mul_nonneg (le_of_not_gt h) hx0.le
    linarith
  · have he : (1 + b / x - 3 / 2 + x⁻¹) * x = 1 - x / 2 + b := by
      field_simp
      ring
    have hr := log_rate_eq_deviation hu hx0
    have hex : Real.log (u * x) + (1 + b / x - 3 / 2 + x⁻¹) * x < 0 := by
      rw [he]
      dsimp only [δ] at hbδ hδ
      linarith
    calc
      _ = Real.exp (Real.log (u * x) + (1 + b / x - 3 / 2 + x⁻¹) * x) := by
        rw [Real.exp_add, Real.exp_log (mul_pos hu hx0)]
        ring
      _ < 1 := Real.exp_lt_one_iff.mpr hex

/-- Any positive lower cutoff below two with a positive deviation
margin also supplies its own admissible strictly decaying tilt. -/
theorem exists_lower_tilt {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (hx2 : x < 2)
    (hcost : Real.log (2 * u) < deviationCost x) :
    ∃ σ : ℝ, 1 < σ ∧ 0 < σ - 3 / 2 + x⁻¹ ∧
      u * (x * Real.exp ((σ - 3 / 2 + x⁻¹) * x)) < 1 := by
  let δ := deviationCost x - Real.log (2 * u)
  have hδ : 0 < δ := sub_pos.mpr hcost
  have he : (1 + δ / (2 * x) - 3 / 2 + x⁻¹) * x = 1 - x / 2 + δ / 2 := by
    field_simp
    ring
  refine ⟨1 + δ / (2 * x), by linarith [div_pos hδ (show 0 < 2 * x by positivity)], ?_, ?_⟩
  · have hp : 0 < (1 + δ / (2 * x) - 3 / 2 + x⁻¹) * x := by rw [he]; linarith
    exact (mul_pos_iff_of_pos_right hx).mp hp
  · have hr := log_rate_eq_deviation hu hx
    have hex : Real.log (u * x) + (1 + δ / (2 * x) - 3 / 2 + x⁻¹) * x < 0 := by
      rw [he]
      dsimp only [δ] at hδ ⊢
      linarith
    calc
      _ = Real.exp (Real.log (u * x) + (1 + δ / (2 * x) - 3 / 2 + x⁻¹) * x) := by
        rw [Real.exp_add, Real.exp_log (mul_pos hu hx)]
        ring
      _ < 1 := Real.exp_lt_one_iff.mpr hex

/-- The deviation cost is nonnegative on its genuine logarithmic domain. -/
theorem deviationCost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ deviationCost x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 2 by positivity)
  unfold deviationCost
  linarith

/-- The central logarithmic scale has exactly zero scalar deviation cost. -/
theorem deviationCost_two : deviationCost 2 = 0 := by
  norm_num [deviationCost]

/-- The scalar majorant cannot pay the central scale on right-half
source radii. The signed arithmetic information inside the window is
therefore still needed by this method. -/
theorem central_scale_not_admissible {u : ℝ} (hu : 1 / 2 ≤ u) :
    ¬ Real.log (2 * u) < deviationCost 2 := by
  rw [deviationCost_two]
  exact not_lt.mpr (Real.log_nonneg (by linarith))

/-- A concrete lower endpoint improves the earlier two-fifths slope,
uniformly for every source radius at most one. -/
theorem universal_lower_cost : Real.log 2 < deviationCost (9 / 20) := by
  have hr := log_rate_eq_deviation (u := 1) (x := 9 / 20) (by norm_num) (by norm_num)
  norm_num only [mul_one, one_mul] at hr
  have he : Real.log (9 / 20 : ℝ) = Real.log (9 / 10 : ℝ) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / 10)
  rw [he] at hr
  linarith [Real.log_two_gt_d9]

/-- A concrete upper endpoint improves the earlier eight-log-two slope.
The exponential comparison is checked by a finite exact Taylor lower sum. -/
theorem universal_upper_cost : Real.log 2 < deviationCost (11 / 2) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4) 6
  norm_num [Finset.sum_range_succ] at he
  have hl : Real.log (11 / 2 : ℝ) < 7 / 4 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)
  have hr := log_rate_eq_deviation (u := 1) (x := 11 / 2) (by norm_num) (by norm_num)
  norm_num only [mul_one, one_mul] at hr
  linarith

/-- Both improved universal cutoffs satisfy the entire radius interval;
no hypothetical zero is used to prove the tail costs. -/
theorem universal_costs {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Real.log (2 * u) < deviationCost (9 / 20) ∧
      Real.log (2 * u) < deviationCost (11 / 2) := by
  have hl : Real.log (2 * u) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith)
  exact ⟨hl.trans_lt universal_lower_cost, hl.trans_lt universal_upper_cost⟩

/-- Every source-sensitive window is intersected with the existing
finite support, preserving its arithmetic restrictions and exact endpoints. -/
def deviationBand (S : Finset ℕ) (a b : ℝ) (N : ℕ) : Finset ℕ :=
  S.filter (fun n => a * N < Real.log n ∧ Real.log n ≤ b * N)

/-- The exact signed decomposition retains both outer sums, with no
overlap or discarded boundary fibre at any integer order. -/
theorem sum_sub_deviationBand (S : Finset ℕ) (f : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    (∑ n ∈ S, f n) - (∑ n ∈ deviationBand S a b N, f n) =
      (∑ n ∈ S.filter (fun (n : ℕ) => Real.log n ≤ a * N), f n) +
      (∑ n ∈ S.filter (fun (n : ℕ) => b * N < Real.log n), f n) := by
  have hordered : a * (N : ℝ) ≤ b * N := mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)
  simp only [deviationBand, Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hl : a * N < Real.log n
  · by_cases hh : Real.log n ≤ b * N
    · simp [hl, hh, not_le.mpr hl, not_lt.mpr hh]
    · simp [hl, hh, not_le.mpr hl, lt_of_not_ge hh]
  · have hh : Real.log n ≤ b * N := (le_of_not_gt hl).trans hordered
    simp [hl, le_of_not_gt hl, not_lt.mpr hh]

/-- Both universal endpoints strictly improve the older logarithmic
window. This compares support slopes, not locations of zeta zeros. -/
theorem universal_window_strictly_narrower :
    (2 / 5 : ℝ) < 9 / 20 ∧ (11 / 2 : ℝ) < 8 * Real.log 2 := by
  constructor
  · norm_num
  · linarith [Real.log_two_gt_d9]

/-- The normalization norm is monotone in a nonnegative source radius;
this permits one common arithmetic bound on a whole radius interval. -/
theorem sourceScale_norm_mono {u U : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (N : ℕ) (z : ℂ) :
    ‖(u : ℂ) ^ (N + 1) * z‖ ≤ ‖(U : ℂ) ^ (N + 1) * z‖ := by
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, abs_of_nonneg (hu.trans huU)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huU _) (norm_nonneg z)

/-- The logarithm of EVERY positive exponential tilt splits into the
same source-deviation profile, a nonnegative logarithmic convexity cost,
and the summability slack. This retains all three costs exactly. -/
theorem log_tilt_rate_decomposition {u x q : ℝ} (hu : 0 < u) (hx : 0 < x) (hq : 0 < q)
    (σ : ℝ) :
    Real.log (u * q⁻¹) + (σ - 3 / 2 + q) * x =
      Real.log (2 * u) - deviationCost x +
        (q * x - 1 - Real.log (q * x)) + (σ - 1) * x := by
  rw [← log_rate_eq_deviation hu hx,
    Real.log_mul (ne_of_gt hu) (by positivity : q⁻¹ ≠ 0), Real.log_inv,
    Real.log_mul (ne_of_gt hu) (ne_of_gt hx),
    Real.log_mul (ne_of_gt hq) (ne_of_gt hx)]
  ring

/-- The deviation profile is a lower bound on the exponent of every
admissible positive tilt. Changing the tilt cannot evade this scalar cost. -/
theorem log_tilt_rate_ge_profile {u x q σ : ℝ}
    (hu : 0 < u) (hx : 0 < x) (hq : 0 < q) (hσ : 1 ≤ σ) :
    Real.log (2 * u) - deviationCost x ≤
      Real.log (u * q⁻¹) + (σ - 3 / 2 + q) * x := by
  rw [log_tilt_rate_decomposition hu hx hq]
  have hc := Real.log_le_sub_one_of_pos (mul_pos hq hx)
  have hs := mul_nonneg (sub_nonneg.mpr hσ) hx.le
  linarith

/-- A subunit positive-tilt rate necessarily has positive deviation
margin. This is an audit of this estimate class, not of every possible
signed arithmetic method. -/
theorem deviation_cost_of_subunit_tilt {u x q σ : ℝ}
    (hu : 0 < u) (hx : 0 < x) (hq : 0 < q) (hσ : 1 ≤ σ)
    (hr : u * (q⁻¹ * Real.exp ((σ - 3 / 2 + q) * x)) < 1) :
    Real.log (2 * u) < deviationCost x := by
  have he : Real.exp (Real.log (u * q⁻¹) + (σ - 3 / 2 + q) * x) < 1 := by
    rw [Real.exp_add, Real.exp_log (mul_pos hu (inv_pos.mpr hq))]
    simpa only [mul_assoc] using hr
  have hl := Real.exp_lt_one_iff.mp he
  have hb := log_tilt_rate_ge_profile hu hx hq hσ
  linarith

/-- The ideal deviation criterion exactly characterizes the existence
of a successful summable upper-tail tilt over ALL positive tilt parameters.
The sufficiency constructs a tilt; necessity uses its full convexity cost. -/
theorem exists_upper_tilt_iff {u x : ℝ} (hu : 0 < u) (hx : 2 < x) :
    (∃ σ q : ℝ, 1 < σ ∧ 0 < q ∧ σ - 3 / 2 + q < 0 ∧
      u * (q⁻¹ * Real.exp ((σ - 3 / 2 + q) * x)) < 1) ↔
      Real.log (2 * u) < deviationCost x := by
  constructor
  · rintro ⟨σ, q, hσ, hq, _, hr⟩
    exact deviation_cost_of_subunit_tilt hu (by linarith) hq hσ.le hr
  · intro hc
    obtain ⟨σ, hσ, hs, hr⟩ := exists_upper_tilt hu hx hc
    refine ⟨σ, x⁻¹, hσ, inv_pos.mpr (by linarith), hs, ?_⟩
    simpa only [inv_inv] using hr

/-- The same ideal criterion exactly characterizes ALL successful
summable lower-tail tilts. No enumeration of weights or sampled parameters
is needed to determine the scope of this positive majorant method. -/
theorem exists_lower_tilt_iff {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (hx2 : x < 2) :
    (∃ σ q : ℝ, 1 < σ ∧ 0 < q ∧ 0 < σ - 3 / 2 + q ∧
      u * (q⁻¹ * Real.exp ((σ - 3 / 2 + q) * x)) < 1) ↔
      Real.log (2 * u) < deviationCost x := by
  constructor
  · rintro ⟨σ, q, hσ, hq, _, hr⟩
    exact deviation_cost_of_subunit_tilt hu hx hq hσ.le hr
  · intro hc
    obtain ⟨σ, hσ, hs, hr⟩ := exists_lower_tilt hu hx hx2 hc
    refine ⟨σ, x⁻¹, hσ, inv_pos.mpr hx, hs, ?_⟩
    simpa only [inv_inv] using hr

end
end RiemannGaussian.LogarithmicDeviation
