/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianSimplePoleHeat

/-!
# The accumulated upper-order pole contribution on a complete order band

At the original quadratic width, the upper-order recurrence weights over
orders `N` through `2N-1` have exact total `3cN/(N+2)`. The pole attenuation
at every required upper order is at least `exp(-4c)`. Thus a complete band
retains a positive source budget even though each fixed neighbour's
coefficient tends to zero. All orders share the original width.
-/

namespace RiemannGaussian.GaussianSimplePoleHeat
noncomputable section
open Filter Topology

/-- The normalized upper-order recurrence coefficient at order `N+j`,
with the original `N`-th quadratic width kept fixed. -/
def quadraticBandWeight (c : ℝ) (N j : ℕ) : ℝ :=
  2 * c * ((N : ℝ) + (j : ℝ) + 2) / (((N : ℝ) + 1) * ((N : ℝ) + 2))

/-- The band weights are nonnegative for every nonnegative relative width. -/
theorem quadraticBandWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (N j : ℕ) :
    0 ≤ quadraticBandWeight c N j := by unfold quadraticBandWeight; positivity

private theorem sum_range_natCast (N : ℕ) :
    ∑ j ∈ Finset.range N, (j : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The complete band's recurrence coefficients have an exact total;
it tends to `3c`, despite decay at every fixed neighbouring order. -/
theorem sum_quadraticBandWeight (c : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, quadraticBandWeight c N j = 3 * c * (N : ℝ) / ((N : ℝ) + 2) := by
  have hs : ∑ j ∈ Finset.range N, ((N : ℝ) + (j : ℝ) + 2) =
      (N : ℝ) * (3 * (N : ℝ) + 3) / 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sum_range_natCast]
    ring
  unfold quadraticBandWeight
  rw [← Finset.sum_div, ← Finset.mul_sum, hs]
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- The exact accumulated coefficient budget converges to `3c`; it
does not vanish merely because each fixed neighbouring coefficient does. -/
theorem tendsto_sum_quadraticBandWeight (c : ℝ) :
    Tendsto (fun N ↦ ∑ j ∈ Finset.range N, quadraticBandWeight c N j) atTop (𝓝 (3 * c)) := by
  simp_rw [sum_quadraticBandWeight]
  simpa only [mul_one, mul_div_assoc] using (tendsto_natCast_div_add_atTop (2 : ℝ)).const_mul (3 * c)

/-- Every nonempty band has a coefficient budget between `c` and `3c`. -/
theorem sum_quadraticBandWeight_bounds {c : ℝ} (hc : 0 ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    c ≤ ∑ j ∈ Finset.range N, quadraticBandWeight c N j ∧
      (∑ j ∈ Finset.range N, quadraticBandWeight c N j) ≤ 3 * c := by
  rw [sum_quadraticBandWeight]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < N + 2)).mpr
    nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < N + 2)).mpr
    nlinarith

/-- All upper orders in the complete band have second-moment loss
budget at most `4c`, at the same original quadratic width. -/
theorem quadraticWidth_mul_secondMoment_band_le {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u)
    {N j : ℕ} (hj : j < N) :
    quadraticWidth c u N * secondMoment (N + j + 2) u ≤ 4 * c := by
  have he : quadraticWidth c u N * secondMoment (N + j + 2) u =
      c * (((N : ℝ) + (j : ℝ) + 3) * ((N : ℝ) + (j : ℝ) + 4)) /
        (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    unfold quadraticWidth secondMoment
    push_cast
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N + 1) * (N + 2))).mpr
  have hjr : (j : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hj)
  calc
    c * (((N : ℝ) + (j : ℝ) + 3) * ((N : ℝ) + (j : ℝ) + 4)) ≤
        c * ((2 * ((N : ℝ) + 1)) * (2 * ((N : ℝ) + 2))) := by gcongr <;> linarith
    _ = _ := by ring

/-- The exact pole source stays uniformly positive throughout every
complete upper-order band at the original quadratic width. -/
theorem exp_neg_four_mul_le_attenuation_band {c u : ℝ} (hc : 0 < c) (hu : 0 < u)
    {N j : ℕ} (hj : j < N) :
    Real.exp (-4 * c) ≤ attenuation (N + j + 2) u (quadraticWidth c u N) := by
  have hb := quadraticWidth_mul_secondMoment_band_le hc.le hu hj
  exact (Real.exp_le_exp.mpr (by linarith : -4 * c ≤
    -quadraticWidth c u N * secondMoment (N + j + 2) u)).trans
      (exp_neg_secondMoment_le_attenuation (N + j + 2) hu (quadraticWidth_pos hc hu N).le)

/-- The complete weighted upper-order pole contribution has a fixed
positive floor. It cannot be discarded when iterating the recurrence. -/
theorem weighted_attenuation_band_lower {c u : ℝ} (hc : 0 < c) (hu : 0 < u)
    {N : ℕ} (hN : 1 ≤ N) :
    c * Real.exp (-4 * c) ≤ ∑ j ∈ Finset.range N,
      quadraticBandWeight c N j * attenuation (N + j + 2) u (quadraticWidth c u N) := by
  calc
    c * Real.exp (-4 * c) ≤
        (∑ j ∈ Finset.range N, quadraticBandWeight c N j) * Real.exp (-4 * c) :=
      mul_le_mul_of_nonneg_right (sum_quadraticBandWeight_bounds hc.le hN).1 (Real.exp_pos _).le
    _ = ∑ j ∈ Finset.range N, quadraticBandWeight c N j * Real.exp (-4 * c) := by rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
      (exp_neg_four_mul_le_attenuation_band hc hu (Finset.mem_range.mp hj))
      (quadraticBandWeight_nonneg hc.le N j)

end
end RiemannGaussian.GaussianSimplePoleHeat
