/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompletion

/-!
# The exposed phase of the actual finite prime array

Independent completion errors transport complete prime phases to every
permitted moving finite order. All exposed-zero assumptions and exact
derivative weights remain explicit; the whole signed floor stays open.
-/

namespace RiemannGaussian.ZetaRieszPrimeCompletionPhase
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedPrimeMoments ZetaRieszPrimeCompletion
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint

/-- The genuine complete ordinary-prime moments retain the full exposed
source after the independently controlled proper powers are removed. -/
theorem tendsto_ordinary_prime_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaOrdinaryPrimeLogMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ))) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho])]
    dsimp [u]
    linarith
  have hsupport : (1 : Polynomial ℂ).support = {0} := by
    ext k
    by_cases hk : k = 0 <;> simp [Polynomial.mem_support_iff, Polynomial.coeff_one, hk]
  have h := (ZetaExposedPrimeFilter.tendsto_primeFilter_one_exposed rho hrho hexposed).sub
    (tendsto_zetaProperPrimePowerFilter_mul_pow (1 : Polynomial ℂ) rho.1.im hu)
  simp only [sub_zero, zetaPrimeLogFilter, zetaProperPrimePowerFilter, hsupport,
    Finset.sum_singleton, Polynomial.coeff_one_zero, one_mul, Nat.add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaPrimeLogMoment_eq_prime_add_proper N (by norm_num)]
  dsimp [u]
  ring

/-- The unlogged prime array retains the exposed phase when its exact
factorial derivative weight is included. -/
theorem tendsto_weighted_complete (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (fun k : ℕ => (k : ℂ) *
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ k *
        ordinaryPrimeMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ))))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (tendsto_ordinary_prime_source rho hrho hexposed).congr'
  filter_upwards [] with k
  rw [ordinaryPrimeMoment_succ (by norm_num)]
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp [hk]

/-- Every permitted moving derivative order still pays the independent
completion error; its extra polynomial factor is absorbed geometrically. -/
theorem tendsto_weighted_completion_error (k : ℕ → ℕ) (y : ℕ → ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 128 * k N ≤ 65 * N) :
    Tendsto (fun N : ℕ => (k N : ℂ) * ((u : ℂ) ^ k N *
      (finiteMoment (intermediatePrimes u N) (k N) (3 / 2 + Complex.I * y N) -
        ordinaryPrimeMoment (k N) (3 / 2 + Complex.I * y N)))) atTop (nhds 0) := by
  let r : ℝ := Real.exp (-(17 / 12288 : ℝ))
  let Z : ℝ := ∑' n, zetaPrimeExpWeight (1025 / 1024) n
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have he (N : ℕ) : Real.exp (-(17 / 12288 : ℝ) * N) = r ^ N := by
    rw [mul_comm, Real.exp_nat_mul]
  apply squeeze_zero_norm' (a := fun N : ℕ => (N + 1 : ℝ) ^ 2 * r ^ N * (2 * Z)) (by
    filter_upwards [eventually_norm_finite_sub_complete_le hu huh, hk] with N hN hkN
    have hNk : k N ≤ N := by omega
    have hc : (k N : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by
      have hcast : (k N : ℝ) ≤ N := by exact_mod_cast hNk
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (k N : ℝ) * (2 * Real.exp (-(17 / 12288 : ℝ) * N) * Z) :=
        mul_le_mul_of_nonneg_left (hN (k N) hkN.1 hkN.2 (y N)) (Nat.cast_nonneg _)
      _ = (k N : ℝ) * r ^ N * (2 * Z) := by rw [he]; ring
      _ ≤ (N + 1 : ℝ) ^ 2 * r ^ N * (2 * Z) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 _)) (by positivity))
  simpa only [zero_mul] using
    (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric hr0 hr1).mul_const (2 * Z)

/-- The actual moving finite prime array inherits the full exposed
negative phase on the independently completable order band. -/
theorem tendsto_weighted_finite (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    (k : ℕ → ℕ)
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 128 * k N ≤ 65 * N) :
    Tendsto (fun N : ℕ => (k N : ℂ) *
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ k N *
        finiteMoment (intermediatePrimes (3 / 2 - rho.1.re) N) (k N)
          (3 / 2 + Complex.I * (rho.1.im : ℂ))))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hk, eventually_ge_atTop (3 * b)] with N hkN hNb
    omega
  have hu : 0 < (3 / 2 : ℝ) - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := ((tendsto_weighted_complete rho hrho hexposed).comp hkt).add
    (tendsto_weighted_completion_error k (fun _ => rho.1.im) hu huh hk)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszPrimeCompletionPhase
