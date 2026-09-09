/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentEnvelope
import RiemannGaussian.ZetaZeroModeFilter
import RiemannGaussian.SuzukiProperPrimePowerWork
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Independent decay of the proper-prime-power moment contribution

The unconditional square-root estimate for `psi - theta` gives absolute
convergence of the proper-prime-power Dirichlet series beyond one half.
Elementary factorial envelopes then show that every fixed polynomial
filter of these moments vanishes at the scale of any right-half zero.
The surviving ordinary-prime sum retains its exact complex phase.
-/

open Complex Filter Topology Asymptotics
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The actual von Mangoldt coefficient restricted to proper prime powers. -/
def zetaProperPrimePowerCoefficient (m : ℕ) : ℝ :=
  if m.Prime then 0 else ArithmeticFunction.vonMangoldt m

/-- Proper-prime-power coefficients are nonnegative. -/
theorem zetaProperPrimePowerCoefficient_nonneg (m : ℕ) :
    0 ≤ zetaProperPrimePowerCoefficient m := by
  unfold zetaProperPrimePowerCoefficient
  split_ifs <;> positivity

/-- The coefficient at zero vanishes. -/
@[simp] theorem zetaProperPrimePowerCoefficient_zero : zetaProperPrimePowerCoefficient 0 = 0 := by
  simp [zetaProperPrimePowerCoefficient]

/-- The partial coefficient sum is the literal Chebyshev difference. -/
theorem sum_zetaProperPrimePowerCoefficient (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, zetaProperPrimePowerCoefficient m) =
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  have he : Finset.Icc 1 N = Finset.Ioc 0 N := by ext m; simp; omega
  rw [he]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.Prime <;> simp [zetaProperPrimePowerCoefficient, hm]

/-- The complete proper-prime-power Dirichlet series converges absolutely
throughout the half-plane strictly right of one half. -/
theorem LSeriesSummable_zetaProperPrimePower {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (fun m ↦ (zetaProperPrimePowerCoefficient m : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (r := (1 / 2 : ℝ)) _ zetaProperPrimePowerCoefficient_nonneg (by norm_num) hs
  refine isBigO_iff.mpr ⟨18, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun m _ ↦ zetaProperPrimePowerCoefficient_nonneg m)),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
    sum_zetaProperPrimePowerCoefficient, ← Real.sqrt_eq_rpow]
  exact chebyshevPsi_sub_theta_le_eighteen_sqrt (by exact_mod_cast hN)

/-- A finite absolute Dirichlet mass for the proper-prime-power error. -/
def zetaProperPrimePowerExpMass (σ : ℝ) : ℝ :=
  ∑' m, zetaProperPrimePowerCoefficient m * zetaPrimeExpWeight σ m

/-- The defining error mass is genuinely summable beyond one half. -/
theorem summable_zetaProperPrimePowerExpMass {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun m ↦ zetaProperPrimePowerCoefficient m * zetaPrimeExpWeight σ m) :=
  summable_zetaPrimeExpWeight_mul _ zetaProperPrimePowerCoefficient_zero
    (LSeriesSummable_zetaProperPrimePower (by simpa using hσ))

/-- The independent proper-prime-power error mass is nonnegative. -/
theorem zetaProperPrimePowerExpMass_nonneg (σ : ℝ) : 0 ≤ zetaProperPrimePowerExpMass σ :=
  tsum_nonneg (fun m ↦ mul_nonneg (zetaProperPrimePowerCoefficient_nonneg m) (Real.exp_pos _).le)

/-- The actual complex log moment contributed by all proper prime powers. -/
def zetaProperPrimePowerMoment (k : ℕ) (s : ℂ) : ℂ :=
  ∑' m, (zetaProperPrimePowerCoefficient m : ℂ) * zetaPrimeLogKernel k s m

/-- Every proper-prime-power log moment converges in the stronger half-plane. -/
theorem summable_zetaProperPrimePowerMoment (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun m ↦ (zetaProperPrimePowerCoefficient m : ℂ) * zetaPrimeLogKernel k s m) := by
  let q := (s.re - 1 / 2) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  apply summable_mul_zetaPrimeLogKernel _ zetaProperPrimePowerCoefficient_nonneg k s hq
  apply summable_zetaProperPrimePowerExpMass
  dsimp [q]
  linarith

/-- The independent arithmetic moment bound is uniform in the ordinate. -/
theorem norm_zetaProperPrimePowerMoment_le (k : ℕ) (y : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    ‖zetaProperPrimePowerMoment k (3 / 2 + I * y)‖ ≤
      q⁻¹ ^ k * zetaProperPrimePowerExpMass (3 / 2 - q) := by
  have hs : (3 / 2 + I * (y : ℂ)).re = 3 / 2 := by simp
  have h := norm_tsum_mul_zetaPrimeLogKernel_le _ zetaProperPrimePowerCoefficient_nonneg
    k (3 / 2 + I * y) hq (by
      rw [hs]
      exact summable_zetaProperPrimePowerExpMass (by linarith))
  simpa only [hs, zetaProperPrimePowerMoment, zetaProperPrimePowerExpMass] using h

/-- The exact finite filter of proper-prime-power moments. -/
def zetaProperPrimePowerFilter (p : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * zetaProperPrimePowerMoment (N + k) s

/-- The whole filtered proper-prime-power error has a geometric bound
from arithmetic alone, without a zero hypothesis. -/
theorem norm_zetaProperPrimePowerFilter_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    ‖zetaProperPrimePowerFilter p N (3 / 2 + I * y)‖ ≤
      q⁻¹ ^ N * (zetaProperPrimePowerExpMass (3 / 2 - q) *
        ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ *
        (q⁻¹ ^ (N + k) * zetaProperPrimePowerExpMass (3 / 2 - q)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_zetaProperPrimePowerMoment_le (N + k) y hq hq1)
        (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum, pow_add]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Every fixed proper-prime-power filter vanishes at every exponential
scale strictly below one. This is an independent arithmetic decay theorem. -/
theorem tendsto_zetaProperPrimePowerFilter_mul_pow (p : Polynomial ℂ) (y : ℝ)
    {a : ℂ} (ha : ‖a‖ < 1) :
    Tendsto (fun N : ℕ ↦ a ^ (N + 1) * zetaProperPrimePowerFilter p N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨q, haq, hq1⟩ := exists_between ha
  have hq : 0 < q := lt_of_le_of_lt (norm_nonneg a) haq
  let C := ‖a‖ * (zetaProperPrimePowerExpMass (3 / 2 - q) *
    ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k)
  have hlim : Tendsto (fun N : ℕ ↦ (‖a‖ / q) ^ N * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ ‖a‖ / q)
        ((div_lt_one hq).mpr haq)).mul_const C
  apply squeeze_zero_norm (fun N ↦ ?_) hlim
  rw [norm_mul, norm_pow]
  apply (mul_le_mul_of_nonneg_left (norm_zetaProperPrimePowerFilter_le p N y hq hq1)
    (pow_nonneg (norm_nonneg _) _)).trans_eq
  dsimp only [C]
  rw [div_pow, inv_pow, pow_succ]
  ring

/-- The surviving moment over ordinary primes, with its full complex phase. -/
def zetaOrdinaryPrimeLogMoment (k : ℕ) (s : ℂ) : ℂ :=
  ∑' m, if m.Prime then (ArithmeticFunction.vonMangoldt m : ℂ) * zetaPrimeLogKernel k s m else 0

/-- The ordinary-prime moment is a genuinely convergent arithmetic series. -/
theorem summable_zetaOrdinaryPrimeLogMoment (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun m ↦ if m.Prime then
      (ArithmeticFunction.vonMangoldt m : ℂ) * zetaPrimeLogKernel k s m else 0) := by
  have h := (hasSum_zetaPrimeLogMoment hs k).summable.indicator {m | m.Prime}
  apply h.congr
  intro m
  by_cases hm : m.Prime <;> simp [zetaPrimeLogKernel, hm, mul_assoc]

/-- Exact arithmetic splitting retains ordinary primes and all proper
prime powers without losing an endpoint or a phase. -/
theorem zetaPrimeLogMoment_eq_prime_add_proper (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPrimeLogMoment k s = zetaOrdinaryPrimeLogMoment k s + zetaProperPrimePowerMoment k s := by
  have hp := summable_zetaOrdinaryPrimeLogMoment k hs
  have hq := summable_zetaProperPrimePowerMoment k (show 1 / 2 < s.re by linarith)
  rw [zetaOrdinaryPrimeLogMoment, zetaProperPrimePowerMoment, ← hp.tsum_add hq]
  rw [← (hasSum_zetaPrimeLogMoment hs k).tsum_eq]
  apply tsum_congr
  intro m
  by_cases hm : m.Prime <;> simp [zetaProperPrimePowerCoefficient, zetaPrimeLogKernel, hm, mul_assoc]

/-- The finite filter on the surviving ordinary-prime moments. -/
def zetaOrdinaryPrimeLogFilter (p : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * zetaOrdinaryPrimeLogMoment (N + k) s

/-- Exact filtered splitting keeps the independently controlled arithmetic error. -/
theorem zetaPrimeLogFilter_eq_prime_add_proper (p : Polynomial ℂ) (N : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    zetaPrimeLogFilter p N s = zetaOrdinaryPrimeLogFilter p N s + zetaProperPrimePowerFilter p N s := by
  simp only [zetaPrimeLogFilter, zetaOrdinaryPrimeLogFilter, zetaProperPrimePowerFilter,
    zetaPrimeLogMoment_eq_prime_add_proper _ hs, mul_add, Finset.sum_add_distrib]

/-- The complete off-critical zero signal is carried by ordinary primes:
the proper-prime-power part has been removed by an independent arithmetic estimate. -/
theorem tendsto_zetaRightHalfOrdinaryPrimeLogFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaOrdinaryPrimeLogFilter (zetaRightHalfZeroModeFilter rho hrho) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have ha : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow (zetaRightHalfZeroModeFilter rho hrho) rho.1.im ha
  have he (N : ℕ) : zetaOrdinaryPrimeLogFilter (zetaRightHalfZeroModeFilter rho hrho) N
      (3 / 2 + I * rho.1.im) = zetaPrimeLogFilter (zetaRightHalfZeroModeFilter rho hrho) N
      (3 / 2 + I * rho.1.im) - zetaProperPrimePowerFilter (zetaRightHalfZeroModeFilter rho hrho) N
      (3 / 2 + I * rho.1.im) := by
    rw [zetaPrimeLogFilter_eq_prime_add_proper _ _ (by norm_num : 1 < (3 / 2 + I * (rho.1.im : ℂ)).re)]
    ring
  simp_rw [he, mul_sub]
  simpa only [sub_zero] using (tendsto_zetaRightHalfZeroModeFilter rho hrho).sub hp

end

end RiemannGaussian
