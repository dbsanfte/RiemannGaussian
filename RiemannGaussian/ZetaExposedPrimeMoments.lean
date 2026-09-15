/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaExposedZero

/-!
# Complete prime moments at exposed zeros

The full canonical divisor, reflected modes, pole and analytic remainder
give uniform source-normalized bounds for the genuine complete prime
moments at an exposed right-half zero. Proper prime powers are paid
independently. Logged and unlogged prime moments retain actual summability,
their exact factorial relation and the unlogged order-zero term.
No cancellation bound for arbitrary prime subbands is asserted.
-/

namespace RiemannGaussian.ZetaExposedPrimeMoments
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero

/-- At an exposed right-half zero, the unfiltered actual prime
moments are uniformly bounded at the selected source scale. The complete
finite divisor, pole, reflected modes and analytic residual are all paid.
This is a bound on prime moments, not yet on the signed Riesz remainder. -/
theorem exists_normalized_prime_moment_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaPrimeLogMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ ≤ C := by
  let r := zetaRightHalfDiscParameter rho hrho
  let u : ℝ := 3 / 2 - rho.1.re
  have hu0 : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hR : u < adaptiveZetaCanonicalRadius r rho.1.im := by
    have hr := (adaptiveZetaCanonicalRadius_spec r rho.1.im).1
    change 5 / 4 - rho.1.re / 2 < _ at hr
    dsimp [u]
    linarith
  have ha : ‖(u : ℂ)‖ < adaptiveZetaCanonicalRadius r rho.1.im := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0] using hR
  obtain ⟨A, hA⟩ := (tendsto_adaptiveZetaResidualMoment_mul_pow r rho.1.im ha).norm.bddAbove_range
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA ⟨0, rfl⟩)
  let S := adaptiveZetaZeroSupport r rho.1.im
  let d (i : ℂ) : ℂ := (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) i : ℂ)
  have hpow (z : ℂ) (hz : ‖(u : ℂ) * z‖ ≤ 1) (N : ℕ) :
      ‖(u : ℂ) ^ (N + 1) * z ^ (N + 1)‖ ≤ 1 := by
    rw [← mul_pow, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz
  have hpole : ‖(u : ℂ) * (1 / 2 + Complex.I * (rho.1.im : ℂ))⁻¹‖ ≤ 1 := by
    have hy : 1 < ‖(1 / 2 + Complex.I * (rho.1.im : ℂ))‖ := by
      apply (nontrivialZetaZero_one_lt_abs_im rho).trans_le
      simpa using Complex.abs_im_le_norm (1 / 2 + Complex.I * (rho.1.im : ℂ))
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      ← div_eq_mul_inv]
    exact (div_le_one (by linarith)).mpr (hu1.le.trans hy.le)
  have hmode (N : ℕ) (i : ℂ) (hi : i ∈ S) :
      ‖(u : ℂ) ^ (N + 1) * (d i *
        ((-i⁻¹) ^ (N + 1) -
          (-starRingEnd ℂ i / (adaptiveZetaCanonicalRadius r rho.1.im : ℂ) ^ 2) ^ (N + 1)))‖ ≤
        2 * ‖d i‖ := by
    have hui : u ≤ ‖i‖ := canonical_support_norm_ge_exposed hexposed r hi
    have hdirect : ‖(u : ℂ) * (-i⁻¹)‖ ≤ 1 := by
      rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
        ← div_eq_mul_inv]
      exact (div_le_one (hu0.trans_le hui)).mpr hui
    have href := norm_mul_adaptiveZetaReflectedMode_lt_one r rho.1.im ha hi
    calc
      _ = ‖d i * ((u : ℂ) ^ (N + 1) * (-i⁻¹) ^ (N + 1) -
          (u : ℂ) ^ (N + 1) *
            (-starRingEnd ℂ i / (adaptiveZetaCanonicalRadius r rho.1.im : ℂ) ^ 2) ^ (N + 1))‖ := by
        congr 1
        ring
      _ ≤ ‖d i‖ * (1 + 1) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (add_le_add (hpow _ hdirect N) (hpow _ href.le N))) (norm_nonneg _)
      _ = _ := by ring
  refine ⟨1 + A + ∑ i ∈ S, 2 * ‖d i‖, by positivity, ?_⟩
  intro N
  change ‖(u : ℂ) ^ (N + 1) * zetaPrimeLogMoment N _‖ ≤ _
  rw [zetaPrimeLogMoment_eq_adaptive_modes r, mul_sub, mul_sub]
  have hsum : ‖(u : ℂ) ^ (N + 1) * ∑ i ∈ S, d i *
      ((-i⁻¹) ^ (N + 1) -
        (-starRingEnd ℂ i / (adaptiveZetaCanonicalRadius r rho.1.im : ℂ) ^ 2) ^ (N + 1))‖ ≤
      ∑ i ∈ S, 2 * ‖d i‖ := by
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hmode N i hi))
  exact (norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add (hpow _ hpole N) (hA ⟨N, rfl⟩))) hsum)

/-- Removing the independently controlled proper prime powers leaves
uniform source-scale bounds for the complete ordinary-prime moments.
No bound for arbitrary prime subbands is asserted. -/
theorem exists_normalized_ordinary_prime_moment_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaOrdinaryPrimeLogMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ ≤ C := by
  obtain ⟨A, hA0, hA⟩ := exists_normalized_prime_moment_bound rho hrho hexposed
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho])]
    dsimp [u]
    linarith
  have hsupport : (1 : Polynomial ℂ).support = {0} := by
    ext k
    by_cases hk : k = 0 <;> simp [Polynomial.mem_support_iff, Polynomial.coeff_one, hk]
  have ht : Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      zetaProperPrimePowerMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ))) atTop (𝓝 0) := by
    simpa only [zetaProperPrimePowerFilter, hsupport, Finset.sum_singleton,
      Polynomial.coeff_one_zero, one_mul, Nat.add_zero] using
      tendsto_zetaProperPrimePowerFilter_mul_pow (1 : Polynomial ℂ) rho.1.im hu
  obtain ⟨B, hB⟩ := ht.norm.bddAbove_range
  refine ⟨A + B, add_nonneg hA0 ((norm_nonneg _).trans (hB ⟨0, rfl⟩)), ?_⟩
  intro N
  have he := zetaPrimeLogMoment_eq_prime_add_proper N
    (by norm_num : 1 < (3 / 2 + Complex.I * (rho.1.im : ℂ)).re)
  have hsub : zetaOrdinaryPrimeLogMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ)) =
      zetaPrimeLogMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ)) -
      zetaProperPrimePowerMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ)) := by
    rw [he]
    ring
  rw [hsub, mul_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hA N) (hB ⟨N, rfl⟩))

/-- The ordinary-prime moment without a logarithmic coefficient.
Its convergence is proved below, including the order-zero case. -/
def ordinaryPrimeMoment (N : ℕ) (s : ℂ) : ℂ :=
  ∑' p : ℕ, if p.Prime then zetaPrimeLogKernel N s p else 0

/-- The unlogged prime moments are genuinely absolutely convergent
in the Euler half-plane. Prime logarithms dominate log(2)>0. -/
theorem summable_ordinaryPrimeMoment {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    Summable (fun p : ℕ => if p.Prime then zetaPrimeLogKernel N s p else 0) := by
  have h := (summable_zetaOrdinaryPrimeLogMoment N hs).norm.div_const (Real.log 2)
  apply h.of_norm_bounded
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, norm_mul, ArithmeticFunction.vonMangoldt_apply_prime hp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg p)]
    have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith [norm_nonneg (zetaPrimeLogKernel N s p)]
  · simp [hp]

/-- One extra factorial order exactly absorbs the prime logarithm.
The divisor k+1 is nonzero, and order zero is kept separately. -/
theorem ordinaryPrimeMoment_succ {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    ordinaryPrimeMoment (N + 1) s = zetaOrdinaryPrimeLogMoment N s / ((N + 1 : ℕ) : ℂ) := by
  apply HasSum.tsum_eq
  have h := (summable_zetaOrdinaryPrimeLogMoment N hs).hasSum.div_const ((N + 1 : ℕ) : ℂ)
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp,
      zetaPrimeLogKernel, pow_succ, Nat.factorial_succ, Nat.cast_mul]
    ring
  · simp [hp]

/-- The complete unlogged prime sequence also has a uniform
source-scale bound, with its genuine order-zero series included. -/
theorem exists_normalized_unlogged_prime_moment_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ordinaryPrimeMoment N (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_normalized_ordinary_prime_moment_bound rho hrho hexposed
  let u : ℝ := 3 / 2 - rho.1.re
  let s : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ)
  have hu0 : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  let A := ‖(u : ℂ) * ordinaryPrimeMoment 0 s‖
  refine ⟨A + C, add_nonneg (norm_nonneg _) hC, ?_⟩
  intro N
  cases N with
  | zero => simpa only [zero_add, pow_one] using le_add_of_nonneg_right hC
  | succ k =>
    rw [ordinaryPrimeMoment_succ (by norm_num : 1 <
      (3 / 2 + Complex.I * (rho.1.im : ℂ)).re)]
    have he : (u : ℂ) ^ (k + 1 + 1) *
        (zetaOrdinaryPrimeLogMoment k s / ((k + 1 : ℕ) : ℂ)) =
        ((u : ℂ) / ((k + 1 : ℕ) : ℂ)) *
          ((u : ℂ) ^ (k + 1) * zetaOrdinaryPrimeLogMoment k s) := by
      rw [pow_succ]
      ring
    change ‖(u : ℂ) ^ (k + 1 + 1) * (_ / _)‖ ≤ _
    rw [he, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hu0, Complex.norm_natCast]
    have hfrac : u / (k + 1 : ℕ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact hu1.trans (by exact_mod_cast Nat.succ_pos k)
    calc
      _ ≤ 1 * C := mul_le_mul hfrac (hb k) (norm_nonneg _) (by norm_num)
      _ ≤ A + C := by
        dsimp [A]
        linarith [norm_nonneg ((u : ℂ) * ordinaryPrimeMoment 0 s)]

end
end RiemannGaussian.ZetaExposedPrimeMoments
