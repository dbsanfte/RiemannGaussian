/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterTail
import Mathlib

/-!
# Stronger generic source-layout guards at the actual integer schedule

This module concerns the generic complete-block constructor's numerical guards.
Its spectral interval is the published Q-1-trial interval, not the Python
Q-trial interval. No external source module is imported or equated silently.
-/
set_option autoImplicit false
noncomputable section
namespace RiemannGaussian.SemiprimeSourceLayoutRate
open Filter
open scoped Topology
open RiemannGaussian.SemiprimeCounterRate
open RiemannGaussian.SemiprimeCounterTail

/-- A literal real upper bound for the actual binary ceiling logarithm. -/
theorem clog_two_cast_le_log {n : ℕ} (hn : 1 < n) :
    (Nat.clog 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
  have hc : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by decide) hn
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hpR : (2 : ℝ) ^ (Nat.clog 2 n - 1) ≤ (n : ℝ) := by
    exact_mod_cast le_of_lt hp
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (Nat.clog 2 n - 1)) hpR
  rw [Real.log_pow, Nat.cast_sub hc] at hl
  simp only [Nat.cast_one] at hl
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hd : (Nat.clog 2 n : ℝ) - 1 ≤ Real.log (n : ℝ) / Real.log 2 :=
    (le_div_iff₀ h2).mpr (by nlinarith)
  linarith

/-- Every fixed power of the binary ceiling logarithm is eventually below any
positive real power. This is proved for the actual integer ceil, not assumed. -/
theorem eventually_clog_power_le_rpow (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (Nat.clog 2 n : ℝ) ^ k ≤ (n : ℝ) ^ δ := by
  let K : ℝ := 1 / Real.log 2 + 1
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim : Tendsto (fun x : ℝ => K ^ k * (Real.log x) ^ k / x ^ δ)
      atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).tendsto_div_nhds_zero).const_mul (K ^ k)
    simpa only [Real.rpow_natCast, mul_zero, ← mul_div_assoc] using h
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))),
    (Real.tendsto_log_atTop.comp ht).eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (1 : ℕ)] with n hn hlog hn1
  change 1 ≤ Real.log (n : ℝ) at hlog
  have hLambda := clog_two_cast_le_log hn1
  have hceil : (Nat.clog 2 n : ℝ) ≤ K * Real.log (n : ℝ) := by
    have he : K * Real.log (n : ℝ) = Real.log (n : ℝ) / Real.log 2 + Real.log (n : ℝ) := by
      dsimp [K]
      ring
    rw [he]
    linarith
  have hpow : (Nat.clog 2 n : ℝ) ^ k ≤ K ^ k * (Real.log (n : ℝ)) ^ k := by
    rw [← mul_pow]
    gcongr
  have hsmall : K ^ k * (Real.log (n : ℝ)) ^ k ≤ (n : ℝ) ^ δ := by
    have hpos : (0 : ℝ) < (n : ℝ) ^ δ := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
    simpa using (div_le_iff₀ hpos).mp (le_of_lt hn)
  exact hpow.trans hsmall

private theorem sixteen_sq_le_pow_pred {k : ℕ} (hk : 16 ≤ k) :
    16 * k ^ 2 ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      16 * (k + 1) ^ 2 ≤ 2 * (16 * k ^ 2) := by nlinarith
      _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ k := by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ = 2 ^ (k + 1 - 1) := by simp

/-- The stronger published group-balance constant holds for actual scheduled
r,Q, without using the earlier weaker two-times balance guard. -/
theorem source_group_balance {n : ℕ} (hn : 2 ^ 16 < n) :
    16 * scheduledPointCount (Nat.clog 2 n) * scheduledGroupCount (Nat.clog 2 n) ^ 2 ≤ n := by
  let lam := Nat.clog 2 n
  have hlarge : 16 ≤ lam := by
    have := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr hn
    omega
  have hq : scheduledPointCount lam ≤ lam := Nat.div_le_self _ _
  have hr : scheduledGroupCount lam ^ 2 ≤ lam :=
    (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans (Nat.sqrt_le' lam)
  have hm := Nat.mul_le_mul hq hr
  have hpoly := sixteen_sq_le_pow_pred hlarge
  have hpow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < n by omega)
  simp only [Nat.pred_eq_sub_one] at hpow
  change 16 * scheduledPointCount lam * scheduledGroupCount lam ^ 2 ≤ n
  change 2 ^ (lam - 1) < n at hpow
  nlinarith

/-- A uniform logarithmic bound sufficient for the published Q-1 spectral
interval. It uses only the actual integer dyadic budgets. -/
theorem log_spectral_budget {r lam ν : ℕ} (hr : 2 ≤ r) (hν : 1 ≤ ν)
    (hrlam : r ≤ lam) (hlam : lam ≤ 2 ^ ν) :
    Real.log (2 * (r : ℝ) * lam) ≤ 64 * (ν : ℝ) := by
  have hrpos : 0 < r := by omega
  have hlampos : 0 < lam := by omega
  have hprod : 2 * r * lam ≤ 2 ^ (2 * ν + 1) := by
    have hm := Nat.mul_le_mul (hrlam.trans hlam) hlam
    have he : (2 ^ ν : ℕ) * 2 ^ ν * 2 = 2 ^ (2 * ν + 1) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    nlinarith
  have hprodR : (2 * (r : ℝ) * lam) ≤ (2 : ℝ) ^ (2 * ν + 1) := by exact_mod_cast hprod
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 * r * lam) hprodR
  rw [Real.log_pow] at hl
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ (2 * ν + 1 : ℕ) by positivity)
  have hνR : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  push_cast at hl hm
  nlinarith

/-- The stronger source constructor's spectral-width test holds at exactly
our R,Q,r,lambda, using its own Q-1-trial convention. -/
theorem source_spectral_width {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    32 * ((scheduledPointCount lam - 1 : ℕ) : ℝ) *
      Real.log (2 * (scheduledGroupCount lam : ℝ) * lam) ≤ (scheduledDegree lam : ℝ) ^ 2 := by
  have hranges := scheduled_parameter_ranges hν
  have hrLam : scheduledGroupCount lam ≤ lam :=
    (Nat.div_le_self _ _).trans (Nat.sqrt_le_self lam)
  have hl := log_spectral_budget hranges.1 (by omega) hrLam (Nat.le_pow_clog (by decide) lam)
  have hQ : 128 * Nat.clog 2 lam * (scheduledPointCount lam - 1) ≤ lam := by
    calc
      128 * Nat.clog 2 lam * (scheduledPointCount lam - 1) ≤
          128 * Nat.clog 2 lam * scheduledPointCount lam :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ lam := by
        simpa [scheduledPointCount, Nat.mul_comm] using Nat.div_mul_le_self lam (128 * Nat.clog 2 lam)
  have hQR : 128 * (Nat.clog 2 lam : ℝ) * (scheduledPointCount lam - 1 : ℕ) ≤ lam := by exact_mod_cast hQ
  have hR : 16 * (lam : ℝ) ≤ (scheduledDegree lam : ℝ) ^ 2 := by
    have h := scheduledCeilSqrt_sq_ge lam
    unfold scheduledDegree
    exact_mod_cast (show 16 * lam ≤ (4 * scheduledCeilSqrt lam) ^ 2 by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hl
    (show (0 : ℝ) ≤ 32 * (scheduledPointCount lam - 1 : ℕ) by positivity)
  nlinarith

private theorem tendsto_source_load_zero (C : ℝ) :
    Tendsto (fun x : ℝ => (2 + C * x ^ (3 / 4 : ℝ)) *
      (8 * x ^ (1 / 32 : ℝ)) / x) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 31 / 32 by norm_num)).const_mul 16
  have h2 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 7 / 32 by norm_num)).const_mul (8 * C)
  have hlim := h1.add h2
  simp only [mul_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he1 : x ^ (1 / 32 : ℝ) / x = x ^ (-(31 / 32) : ℝ) := by
    rw [show (-(31 / 32) : ℝ) = 1 / 32 - 1 by norm_num, Real.rpow_sub hx, Real.rpow_one]
  have he2 : x ^ (3 / 4 : ℝ) * x ^ (1 / 32 : ℝ) / x = x ^ (-(7 / 32) : ℝ) := by
    rw [← Real.rpow_add hx]
    rw [show (-(7 / 32) : ℝ) = (3 / 4 + 1 / 32) - 1 by norm_num,
      Real.rpow_sub hx, Real.rpow_one]
  calc
    16 * x ^ (-(31 / 32) : ℝ) + 8 * C * x ^ (-(7 / 32) : ℝ) =
      16 * (x ^ (1 / 32 : ℝ) / x) + 8 * C * (x ^ (3 / 4 : ℝ) * x ^ (1 / 32 : ℝ) / x) := by
        rw [he1, he2]
    _ = _ := by ring

/-- The stronger published packing load, including the entire epsilon^-2
factor, holds for the SAME actual schedule and growing arity. -/
theorem eventually_source_incidence_balance (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ,
      (w : ℝ) ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) →
      4 * (2 + w) * scheduledDimension n ^ 2 *
        (scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n) ^ 2 ≤ 2 * n := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_clog_power_le_rpow 4 (1 / 64) (by norm_num),
    ht.eventually ((tendsto_source_load_zero C).eventually (gt_mem_nhds (show (0 : ℝ) < 2 by norm_num))),
    eventually_gt_atTop (1 : ℕ)] with n hclog hload hn w hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : scheduledGroupCount (Nat.clog 2 n) ≤ Nat.clog 2 n :=
    (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
  have hrR : (scheduledGroupCount (Nat.clog 2 n) : ℝ) ≤ Nat.clog 2 n := by exact_mod_cast hr
  have hclock : ((scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n : ℕ) : ℝ) ^ 2 ≤
      (n : ℝ) ^ (1 / 64 : ℝ) := by
    calc
      _ ≤ (Nat.clog 2 n : ℝ) ^ 4 := by
        push_cast
        calc
          ((scheduledGroupCount (Nat.clog 2 n) : ℝ) * Nat.clog 2 n) ^ 2 ≤
              ((Nat.clog 2 n : ℝ) * Nat.clog 2 n) ^ 2 := by gcongr
          _ = _ := by ring
      _ ≤ _ := hclog
  have hD := scheduled_dimension_square_le hn
  have hprod : (scheduledDimension n : ℝ) ^ 2 *
      ((scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n : ℕ) : ℝ) ^ 2 ≤
      2 * (n : ℝ) ^ (1 / 32 : ℝ) := by
    calc
      _ ≤ (2 * (n : ℝ) ^ (1 / 64 : ℝ)) * (n : ℝ) ^ (1 / 64 : ℝ) :=
        mul_le_mul hD hclock (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hnR]; norm_num
  have hbound : (2 + C * (n : ℝ) ^ (3 / 4 : ℝ)) * (8 * (n : ℝ) ^ (1 / 32 : ℝ)) ≤ 2 * n :=
    (div_le_iff₀ hnR).mp (le_of_lt hload)
  have htotal : 4 * (2 + (w : ℝ)) * (scheduledDimension n : ℝ) ^ 2 *
      ((scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n : ℕ) : ℝ) ^ 2 ≤ 2 * n := by
    calc
      _ = (4 * (2 + (w : ℝ))) * ((scheduledDimension n : ℝ) ^ 2 *
          ((scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ (4 * (2 + C * (n : ℝ) ^ (3 / 4 : ℝ))) * (2 * (n : ℝ) ^ (1 / 32 : ℝ)) :=
        mul_le_mul (by linarith) hprod (by positivity) (by positivity)
      _ = (2 + C * (n : ℝ) ^ (3 / 4 : ℝ)) * (8 * (n : ℝ) ^ (1 / 32 : ℝ)) := by ring
      _ ≤ _ := hbound
  exact_mod_cast htotal

/-- The published packing/constraint-rank budget, at our actual lambda. -/
def sourceEpsilon (lam : ℕ) : ℝ := 1 / ((scheduledGroupCount lam : ℝ) * lam)

theorem sourceEpsilon_bounds {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    0 < sourceEpsilon lam ∧ sourceEpsilon lam ≤ 1 / 2 := by
  have hr := (scheduled_parameter_ranges hν).1
  have hrlam : scheduledGroupCount lam ≤ lam := (Nat.div_le_self _ _).trans (Nat.sqrt_le_self lam)
  have hrR : (2 : ℝ) ≤ scheduledGroupCount lam := by exact_mod_cast hr
  have hlamR : (1 : ℝ) ≤ lam := by exact_mod_cast (show 1 ≤ lam by omega)
  have hden : (2 : ℝ) ≤ (scheduledGroupCount lam : ℝ) * lam := by nlinarith
  unfold sourceEpsilon
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (by norm_num) hden

/-- Exact stronger numerical hypotheses for the generic published constructor,
M=2n and occurrence B=2. Its interval is centered on Q-1, not Python's Q. -/
def sourceLayoutGuard (n w : ℕ) : Prop :=
  let lam := Nat.clog 2 n
  let r := scheduledGroupCount lam
  let Q := scheduledPointCount lam
  let R := scheduledDegree lam
  0 < n ∧ 0 < w ∧ 2 ≤ r ∧ 2 ≤ Q ∧ 4 ≤ R ∧ 4 * R ≤ Q ∧
    0 < sourceEpsilon lam ∧ sourceEpsilon lam ≤ 1 / 2 ∧
    4 * (2 + w) * scheduledDimension n ^ 2 * (r * lam) ^ 2 ≤ 2 * n ∧
    16 * Q * r ^ 2 ≤ n ∧
    32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / sourceEpsilon lam) ≤ (R : ℝ) ^ 2

/-- All stronger published-constructor guards hold eventually at the SAME
actual integer schedule, for every w<=C*n^(3/4). No old-guard implication or
assumed spectral/packing hypothesis is used. -/
theorem eventually_source_layout_guard (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ, 0 < w →
      (w : ℝ) ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) → sourceLayoutGuard n w := by
  have ht := tendsto_clog_two_atTop.comp tendsto_clog_two_atTop
  filter_upwards [eventually_source_incidence_balance C hC,
    ht.eventually (eventually_ge_atTop 64), eventually_gt_atTop (2 ^ 16 : ℕ)]
      with n hinc hν hn w hwpos hw
  have hranges := scheduled_parameter_ranges hν
  have heps := sourceEpsilon_bounds hν
  have hwidth := source_spectral_width hν
  have hnpos : 0 < n := by omega
  refine ⟨hnpos, hwpos, hranges.1, ?_, ?_, ?_, heps.1, heps.2,
    hinc w hw, source_group_balance hn, ?_⟩
  · omega
  · omega
  · omega
  · simpa [sourceEpsilon, div_eq_mul_inv, mul_assoc] using hwidth

/-- Literal integer coefficient-height budget after the B=2 owner pullback. -/
def sourceHeight (lam : ℕ) : ℕ :=
  4 * (8 * scheduledPointCount lam) ^ (2 * scheduledDegree lam)

/-- The actual concentration-range margin also controls the full exponent
of the source coefficient height; no hidden exp(D) bound is substituted. -/
theorem source_height_exponent {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    2 * scheduledDegree lam * (Nat.clog 2 lam + 3) ≤ lam := by
  have hranges := scheduled_parameter_ranges hν
  have hQ : 128 * Nat.clog 2 lam * scheduledPointCount lam ≤ lam := by
    simpa [scheduledPointCount, Nat.mul_comm] using Nat.div_mul_le_self lam (128 * Nat.clog 2 lam)
  have hm := Nat.mul_le_mul_left (128 * Nat.clog 2 lam) hranges.2.2
  have hνsmall : Nat.clog 2 lam + 3 ≤ 4 * Nat.clog 2 lam := by omega
  have hpoly := Nat.mul_le_mul_left (2 * scheduledDegree lam) hνsmall
  nlinarith

/-- Exact dyadic height bound, at the SAME R and Q. -/
theorem source_height_le_power {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    sourceHeight lam ≤ 2 ^ (lam + 2) := by
  have hQ : scheduledPointCount lam ≤ 2 ^ Nat.clog 2 lam :=
    (Nat.div_le_self _ _).trans (Nat.le_pow_clog (by decide) lam)
  have hbase : 8 * scheduledPointCount lam ≤ 2 ^ (Nat.clog 2 lam + 3) := by
    rw [pow_add]
    norm_num
    nlinarith
  have he := source_height_exponent hν
  unfold sourceHeight
  calc
    4 * (8 * scheduledPointCount lam) ^ (2 * scheduledDegree lam) ≤
        4 * (2 ^ (Nat.clog 2 lam + 3)) ^ (2 * scheduledDegree lam) := by gcongr
    _ = 4 * 2 ^ ((Nat.clog 2 lam + 3) * (2 * scheduledDegree lam)) := by rw [← pow_mul]
    _ ≤ 4 * 2 ^ lam := by
      gcongr
      nlinarith
    _ = 2 ^ (lam + 2) := by rw [pow_add]; norm_num; ring

/-- A common explicit summary-box radius base for all groups. -/
def sourceSignatureBase (n : ℕ) : ℕ := 2 * n * sourceHeight (Nat.clog 2 n) + 1

/-- Its literal integer range has only O(lambda) binary description bits. -/
theorem source_signature_base_le_power {n : ℕ} (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    sourceSignatureBase n ≤ 2 ^ (6 * Nat.clog 2 n) := by
  let lam := Nat.clog 2 n
  have hW := source_height_le_power hν
  have hn : n ≤ 2 ^ lam := Nat.le_pow_clog (by decide) n
  have hlampos : 1 ≤ lam := by
    have hr := (scheduled_parameter_ranges hν).1
    change 2 ≤ scheduledGroupCount lam at hr
    have hrLam : scheduledGroupCount lam ≤ lam :=
      (Nat.div_le_self _ _).trans (Nat.sqrt_le_self lam)
    omega
  have hp : 2 * n * sourceHeight lam ≤ 2 ^ (2 * lam + 3) := by
    calc
      _ ≤ 2 * 2 ^ lam * 2 ^ (lam + 2) := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hnext : sourceSignatureBase n ≤ 2 ^ (2 * lam + 4) := by
    have hpos : 1 ≤ 2 ^ (2 * lam + 3) := Nat.one_le_pow _ _ (by decide)
    have he : 2 ^ (2 * lam + 4) = 2 ^ (2 * lam + 3) * 2 := by rw [show 2 * lam + 4 = (2 * lam + 3) + 1 by omega, pow_succ]
    change 2 * n * sourceHeight lam + 1 ≤ _
    omega
  exact hnext.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Explicit natural logarithm budget; no asymptotic notation hides W. -/
theorem source_signature_log_le {n : ℕ} (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    Real.log (sourceSignatureBase n : ℝ) ≤ 6 * (Nat.clog 2 n : ℝ) * Real.log 2 := by
  have hb := source_signature_base_le_power hν
  have hpos : 0 < sourceSignatureBase n := by unfold sourceSignatureBase; omega
  have hlog := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ) < sourceSignatureBase n)
    (show (sourceSignatureBase n : ℝ) ≤ (2 : ℝ) ^ (6 * Nat.clog 2 n) by exact_mod_cast hb)
  rw [Real.log_pow] at hlog
  simpa using hlog

/-- Total selected rank c with the source's exact budget has a summary
logarithm bounded explicitly by 24*n/r. This charges the literal integer box. -/
theorem source_summary_log_budget {n c : ℕ} (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 n))
    (hc : c * (scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n) ≤ 4 * n) :
    (c : ℝ) * Real.log (sourceSignatureBase n : ℝ) ≤
      (24 * (n : ℝ) / scheduledGroupCount (Nat.clog 2 n)) * Real.log 2 := by
  have hr := (scheduled_parameter_ranges hν).1
  have hrpos : (0 : ℝ) < scheduledGroupCount (Nat.clog 2 n) := by exact_mod_cast (show 0 < scheduledGroupCount (Nat.clog 2 n) by omega)
  have hlog := source_signature_log_le hν
  have hcr : (c : ℝ) * ((scheduledGroupCount (Nat.clog 2 n) : ℝ) * Nat.clog 2 n) ≤ 4 * n := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ (c : ℝ) * scheduledGroupCount (Nat.clog 2 n) by positivity)
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb := mul_le_mul_of_nonneg_right hcr (show 0 ≤ 6 * Real.log 2 by positivity)
  have hden : ((c : ℝ) * Real.log (sourceSignatureBase n : ℝ)) *
      scheduledGroupCount (Nat.clog 2 n) ≤ 24 * (n : ℝ) * Real.log 2 := by nlinarith
  have hd := (le_div_iff₀ hrpos).mpr hden
  convert hd using 1
  ring

/-- Exact inverse-floor budget for the actual group count, with no asymptotic
replacement of floor(sqrt(lambda)/nu^2) by a real expression. -/
theorem source_inverse_group_budget {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    1 / (scheduledGroupCount lam : ℝ) ≤
      2 * (Nat.clog 2 lam : ℝ) ^ 2 / Real.sqrt (lam : ℝ) := by
  let ν := Nat.clog 2 lam
  let r := scheduledGroupCount lam
  let s := Nat.sqrt lam
  have hr : 2 ≤ r := (scheduled_parameter_ranges hν).1
  have hνpos : 0 < ν ^ 2 := by dsimp [ν]; positivity
  have hdiv : s < ν ^ 2 * (r + 1) := Nat.lt_mul_div_succ s hνpos
  have hs : s + 1 ≤ 2 * ν ^ 2 * r := by nlinarith
  have hrLam : r ≤ lam := (Nat.div_le_self _ _).trans (Nat.sqrt_le_self lam)
  have hlampos : (0 : ℝ) < lam := by exact_mod_cast (show 0 < lam by omega)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hsqrtpos := Real.sqrt_pos.mpr hlampos
  have hroot : Real.sqrt (lam : ℝ) ≤ (s : ℝ) + 1 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    exact_mod_cast le_of_lt (Nat.lt_succ_sqrt' lam)
  have hsR : (s : ℝ) + 1 ≤ 2 * (ν : ℝ) ^ 2 * r := by exact_mod_cast hs
  apply (div_le_div_iff₀ hrpos hsqrtpos).mpr
  change 1 * Real.sqrt (lam : ℝ) ≤ (2 * (ν : ℝ) ^ 2) * r
  linarith

/-- The source's total-rank budget gives a completely explicit binary-log
counter envelope, with the actual integer lambda, nu and r throughout. -/
theorem source_summary_binary_rate {n c : ℕ} (hν : 64 ≤ Nat.clog 2 (Nat.clog 2 n))
    (hc : c * (scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n) ≤ 4 * n) :
    (c : ℝ) * Real.log (sourceSignatureBase n : ℝ) ≤
      (48 * (n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 /
        Real.sqrt (Nat.clog 2 n : ℝ)) * Real.log 2 := by
  have hs := source_summary_log_budget hν hc
  have hi := source_inverse_group_budget hν
  have hm := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ 24 * n by positivity)
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl := mul_le_mul_of_nonneg_right hm hlog2
  calc
    _ ≤ (24 * (n : ℝ) / scheduledGroupCount (Nat.clog 2 n)) * Real.log 2 := hs
    _ ≤ _ := by
      convert hl using 1 <;> ring

end RiemannGaussian.SemiprimeSourceLayoutRate
