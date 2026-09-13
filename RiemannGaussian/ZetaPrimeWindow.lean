/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ChebyshevMoebiusCancellation
import RiemannGaussian.SuzukiProperPrimePowerWork
import RiemannGaussian.ZetaPrimeFilterCalculus
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Ordinary-prime windows with retained complex phase

The unconditional prime number theorem gives the logarithmic mass of
actual primes in each fixed multiplicative interval. Exact kernel phase
identities and a coarse Stirling bound prepare a test of local cancellation.
These ingredients are classical; no zero-free improvement is claimed here.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.PrimeWindow
noncomputable section

/-- Ordinary primes satisfy the same qualitative prime number theorem
as the prime powers, since the latter's additional mass is square-root bounded. -/
theorem theta_div_tendsto_one :
    Tendsto (fun x : ℝ ↦ Chebyshev.theta x / x) atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - Chebyshev.theta x) / x)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ ↦ 18 / Real.sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    apply squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) (by linarith)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : 0 < x := by linarith
      have h := div_le_div_of_nonneg_right (chebyshevPsi_sub_theta_le_eighteen_sqrt hx) hx0.le
      calc
        _ ≤ 18 * Real.sqrt x / x := h
        _ = 18 / Real.sqrt x := by rw [mul_div_assoc, Real.sqrt_div_self, div_eq_mul_inv]
  have h := chebyshevPsi_div_tendsto_one.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with x
  ring

/-- Every fixed multiplicative interval has its full asymptotic prime
logarithmic mass; no complex oscillation has been discarded in deriving this fact. -/
theorem theta_interval_div_tendsto {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ ↦ (Chebyshev.theta (A * x) - Chebyshev.theta x) / x)
      atTop (𝓝 (A - 1)) := by
  have h := ((theta_div_tendsto_one.comp (tendsto_id.const_mul_atTop hA)).mul_const A).sub
    theta_div_tendsto_one
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp
  field_simp

/-- The finite interval below is literally a set of ordinary primes. -/
def primesInWindow (x A : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊A * x⌋₊).filter Nat.Prime

/-- Its log mass equals the difference of the two exact Chebyshev sums. -/
theorem sum_log_primesInWindow {x A : ℝ} (hx : 0 ≤ x) (hA : 1 ≤ A) :
    ∑ p ∈ primesInWindow x A, Real.log p = Chebyshev.theta (A * x) - Chebyshev.theta x := by
  have hfloor : ⌊x⌋₊ ≤ ⌊A * x⌋₊ := Nat.floor_mono (by nlinarith)
  have hs : Finset.Icc 0 ⌊x⌋₊ ⊆ Finset.Icc 0 ⌊A * x⌋₊ :=
    Finset.Icc_subset_Icc le_rfl hfloor
  have hd : Finset.Icc 0 ⌊A * x⌋₊ \ Finset.Icc 0 ⌊x⌋₊ = Finset.Ioc ⌊x⌋₊ ⌊A * x⌋₊ := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := fun n : ℕ ↦ if n.Prime then Real.log n else 0) hs
  rw [hd] at h
  simpa only [primesInWindow, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter] using
    (eq_sub_iff_add_eq.mpr h)

/-- Prime membership supplies both real interval endpoints, without
rounding the logarithmic phase. -/
theorem mem_primesInWindow_bounds {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) {p : ℕ}
    (hp : p ∈ primesInWindow x A) :
    x < p ∧ (p : ℝ) ≤ A * x ∧ p.Prime := by
  obtain ⟨hp, hprime⟩ := Finset.mem_filter.mp hp
  have h := Finset.mem_Ioc.mp hp
  exact ⟨(Nat.floor_lt hx).mp h.1,
    (Nat.le_floor_iff (mul_nonneg hA hx)).mp h.2, hprime⟩

/-- A logarithmic window of phase width at most one keeps a positive
projection onto its left endpoint's phase. -/
theorem cos_phase_window_lower {t h y l : ℝ} (hl : t ≤ l) (hu : l ≤ t + h)
    (hy : |y| * h ≤ 1) : 1 / 2 ≤ Real.cos (y * (t - l)) := by
  have ha : |y * (t - l)| ≤ 1 := by
    rw [abs_mul, abs_of_nonpos (by linarith : t - l ≤ 0)]
    calc
      _ ≤ |y| * h := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ 1 := hy
  have hs : (y * (t - l)) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (y * (t - l)), abs_nonneg (y * (t - l))]
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := y * (t - l))]

/-- Exact phase projection of the original kernel for the constant
polynomial. This equality precedes every estimate. -/
theorem rotated_kernel_one_re (N : ℕ) (y t x : ℝ) :
    (Complex.exp (I * y * t) * zetaPrimeFilterKernel 1 N (3 / 2 + I * y) x).re =
      Real.log x ^ N / (N.factorial : ℝ) * Real.exp (-(3 / 2 : ℝ) * Real.log x) *
        Real.cos (y * (t - Real.log x)) := by
  have hp : zetaFactorialPolynomial 1 N (Real.log x : ℂ) =
      (Real.log x : ℂ) ^ N / (N.factorial : ℂ) := by
    simpa only [Polynomial.monomial_zero_one, Nat.add_zero, one_mul] using
      zetaFactorialPolynomial_monomial 0 1 N (Real.log x : ℂ)
  rw [zetaPrimeFilterKernel, hp, mul_left_comm, ← Complex.exp_add]
  have he : I * (y : ℂ) * t + -(3 / 2 + I * y) * (Real.log x : ℂ) =
      (-(3 / 2 : ℝ) * Real.log x : ℝ) + I * (y * (t - Real.log x) : ℝ) := by
    push_cast
    ring
  rw [he]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    Complex.mul_re, Complex.exp_re, mul_assoc]

/-- A deliberately coarse global upper Stirling bound is enough to
test exponential source-scale growth, with no numerical certificate. -/
theorem factorial_le_six_mul_stirling {N : ℕ} (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ 6 * N * ((N : ℝ) / Real.exp 1) ^ N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hseq := Stirling.stirlingSeq'_antitone (show 0 ≤ n from Nat.zero_le _)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add,
    Stirling.stirlingSeq_one] at hseq
  have hsqrt : 1 ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hseq3 : Stirling.stirlingSeq (n + 1) ≤ 3 := hseq.trans (by
    apply (div_le_self (Real.exp_pos 1).le hsqrt).trans
    exact Real.exp_one_lt_three.le)
  have hden : 0 < Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) *
      (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1) := by positivity
  have hfact := (div_le_iff₀ hden).mp hseq3
  have hs : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  change ((n + 1).factorial : ℝ) ≤ _ at hfact
  calc
    _ ≤ 3 * (Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) *
      (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1)) := hfact
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_right hs
        (show 0 ≤ (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1) by positivity)
      simpa only [Nat.succ_eq_add_one] using (by nlinarith [hb] :
        3 * (Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) *
          (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1)) ≤
          6 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1))

end
end RiemannGaussian.PrimeWindow
