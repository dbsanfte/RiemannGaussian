/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompletion

/-!
# Summing the derivative-weighted small-prime prefix

A fixed admissible tilt bounds every selected derivative-weighted order sum by a square-root allowance. The actual polynomial prime cutoff and all complex moments remain unchanged.
-/

namespace RiemannGaussian.ZetaRieszLowHeadPrefix
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletion ZetaExposedPrimeMoments

/-- A fixed tilt gives a sublinear prefix envelope at every order,
including the orders below the linear completion range. -/
theorem norm_smallPrimeMoment_sqrt (N k : ℕ) (y : ℝ) :
    ‖smallPrimeMoment N k y‖ ≤ (5 / 8 : ℝ)⁻¹ ^ k *
      Real.sqrt (N + 1) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  let L : ℝ := 2 * Real.log (N + 1)
  have hlog : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hA : ∀ p ∈ Nat.primesLE (N ^ 2), Real.log p ≤ L := by
    intro p hp
    obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
    have hc : (p : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by
      have hh : (p : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hpN
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hh := Real.log_le_log (by exact_mod_cast hprime.pos : (0 : ℝ) < p) hc
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hb := ZetaRieszPairOrders.norm_finiteMoment_le_tilt (Nat.primesLE (N ^ 2)) k y L
    (q := 5 / 8) (σ := 1025 / 1024) (by norm_num) (by norm_num) (by norm_num) hA
  have he : Real.exp ((5 / 8 + 1025 / 1024 - 3 / 2 : ℝ) * L) ≤ Real.sqrt (N + 1) := by
    calc
      _ ≤ Real.exp (Real.log (N + 1) / 2) := by
        apply Real.exp_le_exp.mpr
        dsimp only [L]
        nlinarith
      _ = _ := by rw [Real.exp_half, Real.exp_log (by positivity)]
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by positivity))
      (tsum_nonneg (fun _ => (Real.exp_pos _).le)))

/-- At the actual annular radius the same prefix has a strict geometric
order ratio, while keeping its literal polynomial cutoff. -/
theorem norm_weighted_smallPrimeMoment (N k : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ ≤ (24 / 25 : ℝ) ^ k *
      Real.sqrt (N + 1) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  have hur : u * (5 / 8 : ℝ)⁻¹ ≤ 24 / 25 := by
    have hh := ZetaRieszHeadAdaptive.annular_radius_le_three_fifths huh
    norm_num
    linarith
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ ≤ u ^ k * ((5 / 8 : ℝ)⁻¹ ^ k * Real.sqrt (N + 1) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n) :=
      mul_le_mul_of_nonneg_left (norm_smallPrimeMoment_sqrt N k y) (pow_nonneg hu _)
    _ = (u * (5 / 8 : ℝ)⁻¹) ^ k * Real.sqrt (N + 1) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hur k)
        (Real.sqrt_nonneg _)) (tsum_nonneg (fun _ => (Real.exp_pos _).le))

/-- All derivative-weighted small-prime orders can be paid together.
The bound is independent of the size and shape of the selected order set,
and uniform in height; no hypothetical zero is assumed. -/
theorem sum_norm_weighted_smallPrimeMoment (N : ℕ) (S : Finset ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    (∑ k ∈ S, ‖(k : ℂ) * ((u : ℂ) ^ k * smallPrimeMoment N k y)‖) ≤
      600 * Real.sqrt (N + 1) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  have hs : HasSum (fun k : ℕ => (k : ℝ) * (24 / 25 : ℝ) ^ k) 600 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one
      (by norm_num : ‖(24 / 25 : ℝ)‖ < 1) using 1
    norm_num
  have hS : (∑ k ∈ S, (k : ℝ) * (24 / 25 : ℝ) ^ k) ≤ 600 := by
    exact (hs.summable.sum_le_tsum S (fun _ _ => by positivity)).trans_eq hs.tsum_eq
  calc
    _ ≤ ∑ k ∈ S, ((k : ℝ) * (24 / 25 : ℝ) ^ k) *
        (Real.sqrt (N + 1) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_weighted_smallPrimeMoment N k y hu huh) (Nat.cast_nonneg (α := ℝ) k)
    _ = (∑ k ∈ S, (k : ℝ) * (24 / 25 : ℝ) ^ k) *
        (Real.sqrt (N + 1) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by
      rw [Finset.sum_mul]
    _ ≤ 600 * (Real.sqrt (N + 1) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by
      have hz : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n :=
        tsum_nonneg (fun _ => (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_right hS (mul_nonneg (Real.sqrt_nonneg _) hz)
    _ = _ := by ring

end
end RiemannGaussian.ZetaRieszLowHeadPrefix
