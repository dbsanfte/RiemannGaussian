/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRetainedSource

/-!
# Retaining the prime cutoff in the missing allocation tails

The upper missing binomial tail is small for a cofactor logarithm at most
seven twentieths of the product logarithm. The other tail keeps its actual
prime cutoff inside the factorial envelope. No lower cofactor-log cutoff is
required for this joint estimate.
-/

namespace RiemannGaussian.ZetaRieszDominantAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation

/-- A summable reference exponent shared by both allocation-tail estimates. -/
def referenceExponent : ℝ := 12001 / 12000

/-- The source-normalized upper-tail rate on the full reserve radius range. -/
def upperRate : ℝ := (503 / 1000 : ℝ) * (12000 / 5999 : ℝ) * Real.exp (-(1 / 160 : ℝ))

/-- The cutoff-coupled lower-tail rate. -/
def lowerRate : ℝ := Real.exp (-(1 / 2000 : ℝ))

/-- Both complete-arithmetic rates are strictly below one, with rational certificates. -/
theorem rates_bounds : (0 ≤ upperRate ∧ upperRate < 1) ∧ (0 ≤ lowerRate ∧ lowerRate < 1) := by
  constructor
  · constructor
    · unfold upperRate; positivity
    · rw [upperRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
      have h := Real.add_one_le_exp (1 / 160 : ℝ)
      linarith
  · exact ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by norm_num)⟩

/-- The upper missing tail remains geometrically small after the full source scaling. -/
theorem upper_scalar (N : ℕ) {u : ℝ} (hu : 0 ≤ u) (huhi : u ≤ 503 / 1000) :
    u ^ (N + 1) * ((87 / 80 : ℝ) * Real.exp (-(N : ℝ) / 160)) *
      (12000 / 5999 : ℝ) ^ N ≤ upperRate ^ N := by
  have he : Real.exp (-(N : ℝ) / 160) = Real.exp (-(1 / 160 : ℝ)) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ (503 / 1000 : ℝ) ^ (N + 1) * ((87 / 80 : ℝ) * Real.exp (-(N : ℝ) / 160)) *
        (12000 / 5999 : ℝ) ^ N := by gcongr
    _ = ((503 / 1000 : ℝ) * (87 / 80 : ℝ)) * upperRate ^ N := by
      rw [he, upperRate, mul_pow, mul_pow, pow_succ]
      ring
    _ ≤ _ := by nlinarith [pow_nonneg rates_bounds.1.1 N]

private theorem upper_log_rate :
    Real.log (87 / 80 : ℝ) - (13 / 32 : ℝ) * Real.log (5 / 4 : ℝ) ≤ -(1 / 160 : ℝ) := by
  have hlog : Real.log (87 / 80 : ℝ) ≤ 84 / 1000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 84 / 1000) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  linarith [log_tilt_bounds.1]

/-- The missing allocation retains a logarithm-dependent lower tail instead of replacing it by a constant sector bound. -/
theorem missing_allocation_cutoff_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) (hxhi : x ≤ 7 / 20) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) ≤
      (87 / 80 : ℝ) * Real.exp (-(N : ℝ) / 160) +
      Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) *
        ((5 / 6 : ℝ) * x + (1 - x)) ^ (N + 1) := by
  have hx1 : x ≤ 1 := by linarith
  have ht : 0 ≤ Real.log (5 / 4 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h := missed_mass_bound N hN hx hx1
    (Real.exp_pos (-(13 / 32 : ℝ) * N * Real.log (5 / 4 : ℝ))).le
    (Real.exp_pos (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))).le
    (by norm_num : (0 : ℝ) ≤ 5 / 4) (by norm_num : (0 : ℝ) ≤ 5 / 6) ?_ ?_
  · apply h.trans
    apply add_le_add _ le_rfl
    have hb : ((5 / 4 : ℝ) * x + (1 - x)) ^ (N + 1) ≤ (87 / 80 : ℝ) ^ (N + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp (-(13 / 32 : ℝ) * N * Real.log (5 / 4 : ℝ)) *
        (87 / 80 : ℝ) ^ (N + 1) = (87 / 80 : ℝ) *
          Real.exp ((N : ℝ) * (Real.log (87 / 80 : ℝ) -
            (13 / 32 : ℝ) * Real.log (5 / 4 : ℝ))) := by
      rw [pow_succ]
      have hp : (87 / 80 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (87 / 80 : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hp, show (N : ℝ) * (Real.log (87 / 80 : ℝ) -
        (13 / 32 : ℝ) * Real.log (5 / 4 : ℝ)) =
          -(13 / 32 : ℝ) * N * Real.log (5 / 4 : ℝ) +
            (N : ℝ) * Real.log (87 / 80 : ℝ) by ring, Real.exp_add]
      ring
    calc
      _ ≤ Real.exp (-(13 / 32 : ℝ) * N * Real.log (5 / 4 : ℝ)) * (87 / 80 : ℝ) ^ (N + 1) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left upper_log_rate (Nat.cast_nonneg (α := ℝ) N)]))
          (by norm_num)
  · intro k hk hcut
    have hc : (13 / 32 : ℝ) * N ≤ k := by
      have hn : 13 * N < 32 * k := by omega
      have hnR : (13 : ℝ) * N < 32 * k := by exact_mod_cast hn
      linarith
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4),
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  · intro k hk hcut
    have hkN : k ≤ N + 1 := by have := Finset.mem_range.mp hk; omega
    have hc : (k : ℝ) ≤ (N : ℝ) / 5 + 1 := by
      have hn : 5 * k ≤ N + 5 := by omega
      have hnR : (5 : ℝ) * k ≤ N + 5 := by exact_mod_cast hn
      linarith
    have he : (5 / 6 : ℝ) = Real.exp (-Real.log (6 / 5 : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hl]

private theorem cutoff_log_rate : Real.log (5030 / 5999 : ℝ) +
    (1 / 5 : ℝ) * Real.log (6 / 5 : ℝ) + (5999 / 10000 : ℝ) * (139 / 100 : ℝ) / 6 ≤
      -(1 / 2000 : ℝ) := by
  have hlog : Real.log (5030 / 5999 : ℝ) ≤ -(1761 / 10000 : ℝ) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 969 / 11029)
      (by norm_num : (969 / 11029 : ℝ) < 1) 2
    norm_num [Finset.sum_range_succ] at h
    have he : Real.log (5030 / 5999 : ℝ) = -Real.log (5999 / 5030 : ℝ) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
      ring
    rw [he]
    linarith
  have h6 : Real.log (6 / 5 : ℝ) ≤ 183 / 1000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show Real.log (6 : ℝ) = Real.log 2 + Real.log 3 by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9]
  linarith

/-- Source scaling, the missing lower allocation orders and the literal prime cutoff jointly have a strict geometric saving. -/
theorem cutoff_scalar (N : ℕ) {u L : ℝ} (hu : 0 ≤ u) (huhi : u ≤ 503 / 1000)
    (hL : L ≤ (139 / 100 : ℝ) * N) :
    u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) *
      (10000 / 5999 : ℝ) ^ N * Real.exp ((5999 / 10000 : ℝ) * L / 6) ≤ lowerRate ^ N := by
  have hpow := pow_le_pow_left₀ hu huhi (N + 1)
  have he : (503 / 1000 : ℝ) ^ (N + 1) *
      Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) * (10000 / 5999 : ℝ) ^ N *
      Real.exp ((5999 / 10000 : ℝ) * L / 6) =
      ((503 / 1000 : ℝ) * (6 / 5 : ℝ)) * Real.exp ((N : ℝ) *
        (Real.log (5030 / 5999 : ℝ) + (1 / 5 : ℝ) * Real.log (6 / 5 : ℝ)) +
          (5999 / 10000 : ℝ) * L / 6) := by
    have ht : Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) =
        (6 / 5 : ℝ) * Real.exp ((N : ℝ) / 5 * Real.log (6 / 5 : ℝ)) := by
      rw [show ((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ) =
        Real.log (6 / 5 : ℝ) + (N : ℝ) / 5 * Real.log (6 / 5 : ℝ) by ring,
        Real.exp_add, Real.exp_log (by norm_num)]
    rw [pow_succ, ht]
    have hp : (503 / 1000 : ℝ) ^ N * (10000 / 5999 : ℝ) ^ N =
        Real.exp ((N : ℝ) * Real.log (5030 / 5999 : ℝ)) := by
      rw [← mul_pow, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      congr 1
      norm_num
    calc
      _ = ((503 / 1000 : ℝ) * (6 / 5 : ℝ)) *
          ((503 / 1000 : ℝ) ^ N * (10000 / 5999 : ℝ) ^ N) *
          Real.exp ((N : ℝ) / 5 * Real.log (6 / 5 : ℝ)) *
          Real.exp ((5999 / 10000 : ℝ) * L / 6) := by ring
      _ = _ := by rw [hp, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hexp : Real.exp ((N : ℝ) *
      (Real.log (5030 / 5999 : ℝ) + (1 / 5 : ℝ) * Real.log (6 / 5 : ℝ)) +
        (5999 / 10000 : ℝ) * L / 6) ≤ lowerRate ^ N := by
    rw [lowerRate, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left cutoff_log_rate (Nat.cast_nonneg (α := ℝ) N)]
  calc
    _ ≤ (503 / 1000 : ℝ) ^ (N + 1) *
        Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) * (10000 / 5999 : ℝ) ^ N *
        Real.exp ((5999 / 10000 : ℝ) * L / 6) := by gcongr
    _ = _ := he
    _ ≤ _ := by nlinarith [Real.exp_pos ((N : ℝ) *
      (Real.log (5030 / 5999 : ℝ) + (1 / 5 : ℝ) * Real.log (6 / 5 : ℝ)) +
        (5999 / 10000 : ℝ) * L / 6)]

/-- A logarithm-dependent allocation weight passes through the exact factorial kernel before any arithmetic summation. -/
theorem weighted_kernel_bound (N n : ℕ) (y : ℝ) {w q σ B : ℝ}
    (hw : 0 ≤ w) (hq : 0 < q)
    (hcut : (q * w - 3 / 2 + σ) * Real.log n ≤ B) :
    w ^ N * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      q⁻¹ ^ N * Real.exp B * zetaPrimeExpWeight σ n := by
  have h := logMoment_exp_envelope N
    (mul_nonneg hw (Real.log_natCast_nonneg n)) hq 0
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, zero_sub, neg_neg] at h
  have he : Real.exp (q * (w * Real.log n)) * Real.exp (-(3 / 2 : ℝ) * Real.log n) ≤
      Real.exp B * zetaPrimeExpWeight σ n := by
    rw [zetaPrimeExpWeight, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [norm_zetaPrimeLogKernel]
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs, zetaPrimeExpWeight]
  calc
    _ = (w * Real.log n) ^ N / (N.factorial : ℝ) *
        Real.exp (-(3 / 2 : ℝ) * Real.log n) := by rw [mul_pow]; ring
    _ ≤ q⁻¹ ^ N * Real.exp (q * (w * Real.log n)) *
        Real.exp (-(3 / 2 : ℝ) * Real.log n) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ q⁻¹ ^ N)

end
end RiemannGaussian.ZetaRieszDominantAllocation
