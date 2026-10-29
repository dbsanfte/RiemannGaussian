/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Rate obligations for the growing-arity shared-summary counter

These results establish analytic decay and the incidence-balance implication.
They do not identify an implementation with a machine or assert acceptance of
unformalized integer schedule/tail checks.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannGaussian.SemiprimeCounterRate

/-- The displayed ordinary-bit counter rate, in the bit-length parameter. -/
def rho (x : ℝ) : ℝ := (Real.log (Real.log x)) ^ 2 / Real.sqrt (Real.log x)

theorem tendsto_rho_zero : Tendsto rho atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hc := h.comp Real.tendsto_log_atTop
  change Tendsto (fun x : ℝ => (Real.log (Real.log x)) ^ 2 / Real.sqrt (Real.log x)) atTop (𝓝 0)
  simpa [Function.comp_def, Real.sqrt_eq_rpow, Real.rpow_two] using hc

/-- Every fixed polynomial prefactor and constant in the displayed exponent
are absorbed into any positive exponential rate in bit length. -/
theorem eventually_polynomial_exp_rho_le (d A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ d * Real.exp (A * x * rho x) ≤ Real.exp (ε * x) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlim : Tendsto (fun x : ℝ => d * (Real.log x / x) + A * rho x)
      atTop (𝓝 0) := by
    simpa using (hlog.const_mul d).add (tendsto_rho_zero.const_mul A)
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_right (le_of_lt hx) (le_of_lt hxpos)
  field_simp at he
  nlinarith

/-- A fixed multiplicative constant (including a finite exceptional-input
constant) is also absorbed without changing the arbitrary target exponent. -/
theorem eventually_constant_polynomial_exp_rho_le (C d A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ d * Real.exp (A * x * rho x) ≤ Real.exp (ε * x) := by
  filter_upwards [eventually_polynomial_exp_rho_le (d + 1) A ε hε,
    eventually_ge_atTop C, eventually_gt_atTop (0 : ℝ)] with x hx hCx hxpos
  calc
    C * x ^ d * Real.exp (A * x * rho x) ≤
        x * x ^ d * Real.exp (A * x * rho x) := by gcongr
    _ = x ^ (d + 1) * Real.exp (A * x * rho x) := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
      ring
    _ ≤ _ := hx

/-- The actual growing-arity overhead exp(B*x^(3/4)) is absorbed as well. -/
theorem eventually_polynomial_counter_with_arity_le (d A B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ d * Real.exp (A * x * rho x + B * x ^ (3 / 4 : ℝ)) ≤
        Real.exp (ε * x) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have harity := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul B
  have hlim : Tendsto (fun x : ℝ => d * (Real.log x / x) + A * rho x +
      B * x ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) := by
    simpa using ((hlog.const_mul d).add (tendsto_rho_zero.const_mul A)).add harity
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_right (le_of_lt hx) (le_of_lt hxpos)
  have hp : x ^ (-(1 / 4) : ℝ) * x = x ^ (3 / 4 : ℝ) := by
    calc
      x ^ (-(1 / 4) : ℝ) * x = x ^ (-(1 / 4) : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (-(1 / 4) + 1 : ℝ) := (Real.rpow_add hxpos _ _).symm
      _ = _ := by norm_num
  have hdiv : (Real.log x / x) * x = Real.log x := div_mul_cancel₀ _ (ne_of_gt hxpos)
  simp only [add_mul, mul_assoc, hdiv, hp] at he
  nlinarith

/-- Fixed leading constants and the growing-arity cost can be charged together. -/
theorem eventually_constant_polynomial_counter_with_arity_le (C d A B ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ d * Real.exp (A * x * rho x + B * x ^ (3 / 4 : ℝ)) ≤
        Real.exp (ε * x) := by
  filter_upwards [eventually_polynomial_counter_with_arity_le (d + 1) A B ε hε,
    eventually_ge_atTop C, eventually_gt_atTop (0 : ℝ)] with x hx hCx hxpos
  calc
    C * x ^ d * Real.exp (A * x * rho x + B * x ^ (3 / 4 : ℝ)) ≤
        x * x ^ d * Real.exp (A * x * rho x + B * x ^ (3 / 4 : ℝ)) := by gcongr
    _ = x ^ (d + 1) * Real.exp (A * x * rho x + B * x ^ (3 / 4 : ℝ)) := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
      ring
    _ ≤ _ := hx

/-- The same bound in the integer-size parameter: every positive power wins. -/
theorem eventually_log_polynomial_counter_subpower (d A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop,
      (Real.log N) ^ d * Real.exp (A * Real.log N * rho (Real.log N)) ≤ N ^ ε := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_polynomial_exp_rho_le d A ε hε), eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  simpa only [Real.rpow_def_of_pos hNpos, mul_comm ε (Real.log N)] using hN

/-- In particular, the proposed algorithm-level bound is eventually sixth-rate.
This is an analytic bound, not a supplied running-time theorem. -/
theorem eventually_log_polynomial_counter_sixth (d A : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      (Real.log N) ^ d * Real.exp (A * Real.log N * rho (Real.log N)) ≤
        N ^ (1 / 6 : ℝ) :=
  eventually_log_polynomial_counter_subpower d A (1 / 6) (by norm_num)

/-- Full analytic envelope, including a fixed leading constant and growing
arity overhead, is eventually bounded by every positive power of N. -/
theorem eventually_full_counter_bound_subpower (C d A B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop,
      C * (Real.log N) ^ d * Real.exp (A * Real.log N * rho (Real.log N) +
        B * (Real.log N) ^ (3 / 4 : ℝ)) ≤ N ^ ε := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_constant_polynomial_counter_with_arity_le C d A B ε hε),
    eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  simpa only [Real.rpow_def_of_pos hNpos, mul_comm ε (Real.log N)] using hN

/-- Exact integer budget, before any real asymptotic estimates. -/
theorem integer_dimension_budget {r ν Q lam : ℕ}
    (hr : r ^ 2 ≤ 2 ^ ν) (hQ : 128 * ν * Q ≤ lam) :
    (r ^ (2 * Q)) ^ 128 ≤ 2 ^ lam := by
  calc
    (r ^ (2 * Q)) ^ 128 = (r ^ 2) ^ (128 * Q) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ (2 ^ ν) ^ (128 * Q) := Nat.pow_le_pow_left hr _
    _ = 2 ^ (128 * ν * Q) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ 2 ^ lam := Nat.pow_le_pow_right (by decide) hQ

/-- The actual integer-floor formulas in `shared_parameters.py`. -/
def scheduledGroupCount (lam : ℕ) : ℕ := Nat.sqrt lam / (Nat.clog 2 lam) ^ 2

/-- The scheduled number Q of nonzero interpolation nodes. -/
def scheduledPointCount (lam : ℕ) : ℕ := lam / (128 * Nat.clog 2 lam)

theorem scheduled_dimension_budget (lam : ℕ) :
    (scheduledGroupCount lam ^ (2 * scheduledPointCount lam)) ^ 128 ≤ 2 ^ lam := by
  apply integer_dimension_budget
  · exact (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans
      ((Nat.sqrt_le' lam).trans (Nat.le_pow_clog (by decide) lam))
  · simpa [scheduledPointCount, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self lam (128 * Nat.clog 2 lam)

/-- For the bit-count parameter n, the scheduled auxiliary dimension satisfies
an exact polynomial-size budget, even before any eventual guard hypotheses. -/
theorem scheduled_dimension_budget_input {n : ℕ} (hn : 1 < n) :
    (scheduledGroupCount (Nat.clog 2 n) ^ (2 * scheduledPointCount (Nat.clog 2 n))) ^ 128 < 2 * n := by
  apply lt_of_le_of_lt (scheduled_dimension_budget (Nat.clog 2 n))
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  simp only [Nat.pred_eq_sub_one] at hp
  have hc : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by decide) hn
  calc
    2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hc]
    _ < 2 * n := by omega

/-- The real normalized load corresponding to occurrence two and arity
O(n^(3/4)) tends to zero under the scheduled dimension exponent. -/
theorem tendsto_incidence_load_zero (C A : ℝ) :
    Tendsto (fun x : ℝ => (2 + C * x ^ (3 / 4 : ℝ)) *
      (A * x ^ (1 / 64 : ℝ)) / x) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 63 / 64 by norm_num)).const_mul (2 * A)
  have h2 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 15 / 64 by norm_num)).const_mul (C * A)
  have hlim := h1.add h2
  simp only [mul_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he1 : x ^ (1 / 64 : ℝ) / x = x ^ (-(63 / 64) : ℝ) := by
    rw [show (-(63 / 64) : ℝ) = 1 / 64 - 1 by norm_num,
      Real.rpow_sub hx, Real.rpow_one]
  have he2 : x ^ (3 / 4 : ℝ) * x ^ (1 / 64 : ℝ) / x =
      x ^ (-(15 / 64) : ℝ) := by
    rw [← Real.rpow_add hx]
    rw [show (-(15 / 64) : ℝ) = (3 / 4 + 1 / 64) - 1 by norm_num,
      Real.rpow_sub hx, Real.rpow_one]
  calc
    2 * A * x ^ (-(63 / 64) : ℝ) + C * A * x ^ (-(15 / 64) : ℝ) =
        2 * A * (x ^ (1 / 64 : ℝ) / x) +
          C * A * (x ^ (3 / 4 : ℝ) * x ^ (1 / 64 : ℝ) / x) := by rw [he1, he2]
    _ = _ := by ring

/-- Genuine eventual load balance; no assumption that the guard succeeds.
Only its separately proved numerical dimension budget is an input here. -/
theorem eventually_incidence_balance (C A : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ w d : ℝ,
      0 ≤ w → 0 ≤ d → w ≤ C * x ^ (3 / 4 : ℝ) →
      d ≤ A * x ^ (1 / 64 : ℝ) → 2 * (2 + w) * d ≤ 2 * x := by
  filter_upwards [(tendsto_incidence_load_zero C A).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)), eventually_gt_atTop (0 : ℝ)]
      with x hx hxpos w d hw hd hwbound hdbound
  have hbound : (2 + C * x ^ (3 / 4 : ℝ)) * (A * x ^ (1 / 64 : ℝ)) ≤ x :=
    by simpa using (div_le_iff₀ hxpos).mp (le_of_lt hx)
  have hmul : (2 + w) * d ≤ (2 + C * x ^ (3 / 4 : ℝ)) *
      (A * x ^ (1 / 64 : ℝ)) :=
    mul_le_mul (by linarith) hdbound hd (by positivity)
  linarith

/-- The auxiliary array cardinality for the exact floor/square-root schedule. -/
def scheduledDimension (n : ℕ) : ℕ :=
  scheduledGroupCount (Nat.clog 2 n) ^ (2 * scheduledPointCount (Nat.clog 2 n))

/-- The real budget required by the growing-arity balance theorem follows from
integer schedule arithmetic; it is not an extra asymptotic hypothesis. -/
theorem scheduled_dimension_square_le {n : ℕ} (hn : 1 < n) :
    (scheduledDimension n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ (1 / 64 : ℝ) := by
  have hp : ((scheduledDimension n : ℝ) ^ 2) ^ (64 : ℝ) ≤ 2 * (n : ℝ) := by
    rw [Real.rpow_ofNat, ← pow_mul]
    norm_num
    exact_mod_cast (le_of_lt (scheduled_dimension_budget_input hn))
  have hr := (Real.le_rpow_inv_iff_of_pos
    (sq_nonneg (scheduledDimension n : ℝ))
    (show 0 ≤ 2 * (n : ℝ) by positivity) (show (0 : ℝ) < 64 by norm_num)).mpr hp
  have htwo : (2 : ℝ) ^ (1 / 64 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  calc
    (scheduledDimension n : ℝ) ^ 2 ≤ (2 * (n : ℝ)) ^ (1 / 64 : ℝ) := by
      simpa only [one_div] using hr
    _ = (2 : ℝ) ^ (1 / 64 : ℝ) * (n : ℝ) ^ (1 / 64 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * (n : ℝ) ^ (1 / 64 : ℝ) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)

/-- Eventual acceptance of the actual incidence-load inequality for every
arity bounded by C*n^(3/4), proved for the scheduled integer D itself.
The other schedule tests (group balance and spectral tail) are separate. -/
theorem eventually_scheduled_incidence_balance (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ,
      (w : ℝ) ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) →
      2 * (2 + w) * scheduledDimension n ^ 2 ≤ 2 * n := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_incidence_balance C 2 hC),
    eventually_gt_atTop (1 : ℕ)] with n hn hnp w hw
  have hb := hn (w : ℝ) ((scheduledDimension n : ℝ) ^ 2)
    (by positivity) (by positivity) hw (scheduled_dimension_square_le hnp)
  exact_mod_cast hb

private theorem twice_sq_le_pow_pred {k : ℕ} (hk : 16 ≤ k) :
    2 * k ^ 2 ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      2 * (k + 1) ^ 2 ≤ 2 * (2 * k ^ 2) := by nlinarith
      _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ k := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ = 2 ^ (k + 1 - 1) := by simp

/-- An explicit eventual bound for the second numerical balance test. No
binomial estimate or eventual-guard assumption enters this theorem. -/
theorem scheduled_group_balance {n : ℕ} (hn : 2 ^ 16 < n) :
    2 * scheduledPointCount (Nat.clog 2 n) * scheduledGroupCount (Nat.clog 2 n) ^ 2 ≤ n := by
  let lam := Nat.clog 2 n
  have hlarge : 16 ≤ lam := by
    have := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr hn
    omega
  have hq : scheduledPointCount lam ≤ lam := Nat.div_le_self _ _
  have hr : scheduledGroupCount lam ^ 2 ≤ lam :=
    (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans (Nat.sqrt_le' lam)
  have hmul := Nat.mul_le_mul hq hr
  have hpoly := twice_sq_le_pow_pred hlarge
  have hpow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (show 1 < n by omega)
  simp only [Nat.pred_eq_sub_one] at hpow
  change 2 * scheduledPointCount lam * scheduledGroupCount lam ^ 2 ≤ n
  change 2 ^ (lam - 1) < n at hpow
  nlinarith

private theorem quartic_le_pow_pred {k : ℕ} (hk : 64 ≤ k) :
    65536 * k ^ 4 ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h8 : 8 ≤ k := by omega
    have h1 := Nat.mul_le_mul_right (k ^ 3) h8
    have h2 := Nat.mul_le_mul_right (k ^ 2) h8
    have h3 := Nat.mul_le_mul_right k h8
    have hstep : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by nlinarith
    calc
      65536 * (k + 1) ^ 4 ≤ 65536 * (2 * k ^ 4) := Nat.mul_le_mul_left _ hstep
      _ = 2 * (65536 * k ^ 4) := by ring
      _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ k := by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ = 2 ^ (k + 1 - 1) := by simp

/-- Exact ceiling square root used in the Python schedule. -/
def scheduledCeilSqrt (lam : ℕ) : ℕ :=
  Nat.sqrt lam + if Nat.sqrt lam ^ 2 = lam then 0 else 1

/-- The scheduled degree R=4*ceil(sqrt(lambda)); this is not the group count r. -/
def scheduledDegree (lam : ℕ) : ℕ := 4 * scheduledCeilSqrt lam

/-- Explicit large-log range tests, without assuming any guard or tail bound. -/
theorem scheduled_parameter_ranges {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    2 ≤ scheduledGroupCount lam ∧ 32 ≤ scheduledDegree lam ∧
      6 * scheduledDegree lam ≤ scheduledPointCount lam := by
  let ν := Nat.clog 2 lam
  let s := Nat.sqrt lam
  have hν64 : 64 ≤ ν := hν
  have hlam : 1 < lam := by
    by_contra h
    have : lam ≤ 1 := by omega
    have hz := Nat.clog_of_right_le_one this 2
    omega
  have hpow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hlam
  simp only [Nat.pred_eq_sub_one] at hpow
  have hquart := quartic_le_pow_pred hν64
  have hs : 256 * ν ^ 2 ≤ s := by
    apply Nat.le_sqrt'.mpr
    change 2 ^ (ν - 1) < lam at hpow
    nlinarith
  have hνpos : 0 < ν ^ 2 := by positivity
  have hr : 2 ≤ scheduledGroupCount lam := by
    apply (Nat.le_div_iff_mul_le hνpos).mpr
    change 2 * ν ^ 2 ≤ s
    nlinarith
  have hslarge : 6144 * ν ≤ s := by nlinarith
  have hspos : 1 ≤ s := by nlinarith
  have hnorm : 3072 * ν * (s + 1) ≤ lam := by
    have hsq : s ^ 2 ≤ lam := Nat.sqrt_le' lam
    have hm := Nat.mul_le_mul_right s hslarge
    nlinarith
  have hQ : 24 * (s + 1) ≤ scheduledPointCount lam := by
    apply (Nat.le_div_iff_mul_le (show 0 < 128 * ν by positivity)).mpr
    nlinarith
  have hc : s ≤ scheduledCeilSqrt lam ∧ scheduledCeilSqrt lam ≤ s + 1 := by
    dsimp [scheduledCeilSqrt, s]
    split_ifs <;> omega
  refine ⟨hr, ?_, ?_⟩
  · dsimp [scheduledDegree]
    nlinarith
  · dsimp [scheduledDegree]
    nlinarith

/-- The integer ceiling binary logarithm itself tends to infinity. -/
theorem tendsto_clog_two_atTop : Tendsto (Nat.clog 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_gt_atTop (2 ^ b)] with n hn
  exact le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr hn)

/-- Thus the exact positivity and concentration-range tests hold eventually
for the actual double-ceiling-log integer schedule. -/
theorem eventually_scheduled_parameter_ranges :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ scheduledGroupCount (Nat.clog 2 n) ∧
      32 ≤ scheduledDegree (Nat.clog 2 n) ∧
      6 * scheduledDegree (Nat.clog 2 n) ≤ scheduledPointCount (Nat.clog 2 n) := by
  have ht := tendsto_clog_two_atTop.comp tendsto_clog_two_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop 64)] with n hn
  exact scheduled_parameter_ranges hn

/-- The nonnegative numerator of the actual centered interval formula. -/
theorem interval_numerator_nonnegative {r Q R : ℕ} (hr : 2 ≤ r) (hQR : 6 * R ≤ Q) :
    r * (R - 1) ≤ Q * (r - 1) := by
  have hs : r ≤ 2 * (r - 1) := by omega
  have h1 := Nat.mul_le_mul_right Q hs
  have h2 := Nat.mul_le_mul_right r hQR
  have h3 := Nat.mul_le_mul_left r (Nat.sub_le R 1)
  nlinarith

/-- Centered interval start; the preceding lemma makes natural subtraction
identical to the signed numerator used by Python on accepted ranges. -/
def intervalStart (r Q R : ℕ) : ℕ :=
  (Q * (r - 1) - r * (R - 1)) / (2 * r)

/-- The interval is contained in 0,...,Q under the actual range tests. -/
theorem interval_contained {r Q R : ℕ} (hQR : 6 * R ≤ Q) :
    intervalStart r Q R + R ≤ Q + 1 := by
  have hsmall : Q ≤ 2 * (Q + 1 - R) := by omega
  have hm := Nat.mul_le_mul_right r hsmall
  have hnum : Q * (r - 1) - r * (R - 1) ≤ (2 * r) * (Q + 1 - R) := by
    have hsub := Nat.sub_le (Q * (r - 1)) (r * (R - 1))
    have hmul := Nat.mul_le_mul_left Q (Nat.sub_le r 1)
    nlinarith
  have hd := Nat.div_le_of_le_mul hnum
  change intervalStart r Q R ≤ Q + 1 - R at hd
  omega

/-- The exact scheduled interval passes its containment check eventually. -/
theorem eventually_scheduled_interval_contained :
    ∀ᶠ n : ℕ in atTop,
      intervalStart (scheduledGroupCount (Nat.clog 2 n))
        (scheduledPointCount (Nat.clog 2 n)) (scheduledDegree (Nat.clog 2 n)) +
        scheduledDegree (Nat.clog 2 n) ≤ scheduledPointCount (Nat.clog 2 n) + 1 := by
  filter_upwards [eventually_scheduled_parameter_ranges] with n hn
  exact interval_contained hn.2.2

/-- Combined eventual acceptance of all displayed numerical schedule checks
except the binomial-tail test. The arity grows as n^(3/4); no fixed-width or
polylogarithmic-arity premise is used. -/
theorem eventually_non_tail_schedule_checks (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ,
      (w : ℝ) ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) →
      2 ≤ scheduledGroupCount (Nat.clog 2 n) ∧
      32 ≤ scheduledDegree (Nat.clog 2 n) ∧
      6 * scheduledDegree (Nat.clog 2 n) ≤ scheduledPointCount (Nat.clog 2 n) ∧
      scheduledDegree (Nat.clog 2 n) < scheduledPointCount (Nat.clog 2 n) ∧
      2 ≤ scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n ∧
      2 * (2 + w) * scheduledDimension n ^ 2 ≤ 2 * n ∧
      2 * scheduledPointCount (Nat.clog 2 n) *
        scheduledGroupCount (Nat.clog 2 n) ^ 2 ≤ n ∧
      intervalStart (scheduledGroupCount (Nat.clog 2 n))
        (scheduledPointCount (Nat.clog 2 n)) (scheduledDegree (Nat.clog 2 n)) +
        scheduledDegree (Nat.clog 2 n) ≤ scheduledPointCount (Nat.clog 2 n) + 1 := by
  filter_upwards [eventually_scheduled_parameter_ranges,
    eventually_scheduled_incidence_balance C hC,
    eventually_gt_atTop (2 ^ 16 : ℕ)] with n hr hi hn w hw
  have hn1 : 1 < n := by omega
  have hlog : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by decide) hn1
  have hden : 2 ≤ scheduledGroupCount (Nat.clog 2 n) * Nat.clog 2 n := by
    simpa using Nat.mul_le_mul hr.1 hlog
  refine ⟨hr.1, hr.2.1, hr.2.2, ?_, hden, hi w hw,
    scheduled_group_balance hn, interval_contained hr.2.2⟩
  omega

end RiemannGaussian.SemiprimeCounterRate
