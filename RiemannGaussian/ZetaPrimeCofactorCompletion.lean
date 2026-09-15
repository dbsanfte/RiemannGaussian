/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaExposedPrimeMoments

/-!
# Exact prime completion with a variable cofactor

The factorial convolution retains every complementary order and cofactor
phase. At an exposed right-half zero beta+i*gamma, completing one prime
factor costs C*a^(-beta), uniformly in the cofactor and moment order.
The product logarithm retains both log(a) and log(p), all series have proved
summability, and every fixed polynomial filter keeps its coefficient cost.
Completed cofactor sums are not identified with the original finite band here.
-/

namespace RiemannGaussian.ZetaPrimeCofactorCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments

/-- The additive factorial law retains every complementary order.
It transports a product of integer factors into an exact convolution. -/
theorem factorial_add_pow (x y : ℂ) (N : ℕ) :
    (x + y) ^ N / (N.factorial : ℂ) =
      ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℂ) *
        (y ^ (N - k) / ((N - k).factorial : ℂ)) := by
  rw [add_pow, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ N := by simpa using Finset.mem_range.mp hk
  have hc : (N.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'
  have he := Nat.choose_mul_factorial_mul_factorial hkn
  rw [← he, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv]
  simp only [mul_left_comm (N.choose k : ℂ), mul_assoc,
    mul_left_comm (N.choose k : ℂ)⁻¹, mul_comm (N.choose k : ℂ)]
  rw [inv_mul_cancel₀ hc]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

/-- The actual product kernel retains both prime-factor phases and
every factorial order, with positivity assumptions on both integers. -/
theorem logKernel_product (N : ℕ) (s : ℂ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    zetaPrimeLogKernel N s (a * b) = zetaPrimeFeature s a *
      ∑ k ∈ Finset.range (N + 1),
        (Real.log a : ℂ) ^ k / (k.factorial : ℂ) * zetaPrimeLogKernel (N - k) s b := by
  have hlog : Real.log ((a * b : ℕ) : ℝ) = Real.log a + Real.log b := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rw [zetaPrimeLogKernel, hlog, Complex.ofReal_add, factorial_add_pow,
    CoprimeEulerPhase.feature_mul s ha hb]
  simp only [zetaPrimeLogKernel, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- A bounded normalized sequence remains controlled after exact
factorial translation. The bound charges exp(u*x), not an order factor. -/
theorem norm_factorial_convolution_le {u x C : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x)
    (w : ℕ → ℂ) (hw : ∀ k : ℕ, ‖(u : ℂ) ^ (k + 1) * w k‖ ≤ C) (N : ℕ) :
    ‖(u : ℂ) ^ (N + 1) * ∑ k ∈ Finset.range (N + 1),
      (x : ℂ) ^ k / (k.factorial : ℂ) * w (N - k)‖ ≤ C * Real.exp (u * x) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        (u * x) ^ k / (k.factorial : ℝ) * C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ N := by simpa using Finset.mem_range.mp hk
      have he : (u : ℂ) ^ (N + 1) * ((x : ℂ) ^ k / (k.factorial : ℂ) * w (N - k)) =
          (((u * x : ℝ) : ℂ) ^ k / (k.factorial : ℂ)) *
            ((u : ℂ) ^ (N - k + 1) * w (N - k)) := by
        rw [show N + 1 = k + (N - k + 1) by omega, pow_add,
          Complex.ofReal_mul, mul_pow]
        ring
      rw [he, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hu hx), Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hw (N - k)) (by positivity)
    _ = C * ∑ k ∈ Finset.range (N + 1), (u * x) ^ k / (k.factorial : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.sum_le_exp_of_nonneg (mul_nonneg hu hx) (N + 1)) hC

/-- The completed prime-factor sum is a genuinely convergent series,
with its exact cofactor phase and factorial convolution retained. -/
theorem hasSum_prime_log_product {s : ℂ} (hs : 1 < s.re) (N : ℕ)
    {a : ℕ} (ha : 0 < a) :
    HasSum (fun p : ℕ => if p.Prime then
      (ArithmeticFunction.vonMangoldt p : ℂ) * zetaPrimeLogKernel N s (a * p) else 0)
      (zetaPrimeFeature s a * ∑ k ∈ Finset.range (N + 1),
        (Real.log a : ℂ) ^ k / (k.factorial : ℂ) * zetaOrdinaryPrimeLogMoment (N - k) s) := by
  have h := (hasSum_sum (s := Finset.range (N + 1)) (fun k _ =>
    (summable_zetaOrdinaryPrimeLogMoment (N - k) hs).hasSum.mul_left
      ((Real.log a : ℂ) ^ k / (k.factorial : ℂ)))).mul_left (zetaPrimeFeature s a)
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, logKernel_product N s ha hp.pos, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · simp [hp]

/-- At an exposed zero, completing one prime factor costs only the
cofactor's beta-power. The constant is uniform in both moment order and
positive integer cofactor; it controls the complete signed prime sum. -/
theorem exists_prime_log_product_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ), 0 < a → ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ∑' p : ℕ, if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ) *
          zetaPrimeLogKernel N (3 / 2 + Complex.I * (rho.1.im : ℂ)) (a * p) else 0‖ ≤
        C * Real.exp (-rho.1.re * Real.log a) := by
  obtain ⟨C, hC, hb⟩ := exists_normalized_ordinary_prime_moment_bound rho hrho hexposed
  refine ⟨C, hC, ?_⟩
  intro a ha N
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  rw [(hasSum_prime_log_product (by norm_num : 1 <
    (3 / 2 + Complex.I * (rho.1.im : ℂ)).re) N ha).tsum_eq]
  have h := norm_factorial_convolution_le hu (Real.log_natCast_nonneg a)
    (fun k => zetaOrdinaryPrimeLogMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ))) hb N
  calc
    _ = ‖zetaPrimeFeature (3 / 2 + Complex.I * (rho.1.im : ℂ)) a‖ *
        ‖(u : ℂ) ^ (N + 1) * ∑ k ∈ Finset.range (N + 1),
          (Real.log a : ℂ) ^ k / (k.factorial : ℂ) *
            zetaOrdinaryPrimeLogMoment (N - k) (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ := by
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ ‖zetaPrimeFeature (3 / 2 + Complex.I * (rho.1.im : ℂ)) a‖ *
        (C * Real.exp (u * Real.log a)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by
      rw [norm_zetaPrimeFeature]
      simp only [zetaPrimeExpWeight, Complex.add_re, Complex.div_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re]
      norm_num
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      dsimp [u]
      ring

/-- The completed unlogged prime-factor sum is a genuinely convergent series,
with its exact cofactor phase and factorial convolution retained. -/
theorem hasSum_unlogged_prime_product {s : ℂ} (hs : 1 < s.re) (N : ℕ)
    {a : ℕ} (ha : 0 < a) :
    HasSum (fun p : ℕ => if p.Prime then
      zetaPrimeLogKernel N s (a * p) else 0)
      (zetaPrimeFeature s a * ∑ k ∈ Finset.range (N + 1),
        (Real.log a : ℂ) ^ k / (k.factorial : ℂ) * ordinaryPrimeMoment (N - k) s) := by
  have h := (hasSum_sum (s := Finset.range (N + 1)) (fun k _ =>
    (summable_ordinaryPrimeMoment hs (N - k)).hasSum.mul_left
      ((Real.log a : ℂ) ^ k / (k.factorial : ℂ)))).mul_left (zetaPrimeFeature s a)
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, logKernel_product N s ha hp.pos, Finset.mul_sum]
  · simp [hp]

/-- At an exposed zero, completing an unlogged prime factor costs only the
cofactor's beta-power. The constant is uniform in both moment order and
positive integer cofactor; it controls the complete signed prime sum. -/
theorem exists_unlogged_prime_product_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ), 0 < a → ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ∑' p : ℕ, if p.Prime then zetaPrimeLogKernel N (3 / 2 + Complex.I * (rho.1.im : ℂ)) (a * p) else 0‖ ≤
        C * Real.exp (-rho.1.re * Real.log a) := by
  obtain ⟨C, hC, hb⟩ := exists_normalized_unlogged_prime_moment_bound rho hrho hexposed
  refine ⟨C, hC, ?_⟩
  intro a ha N
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  rw [(hasSum_unlogged_prime_product (by norm_num : 1 <
    (3 / 2 + Complex.I * (rho.1.im : ℂ)).re) N ha).tsum_eq]
  have h := norm_factorial_convolution_le hu (Real.log_natCast_nonneg a)
    (fun k => ordinaryPrimeMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ))) hb N
  calc
    _ = ‖zetaPrimeFeature (3 / 2 + Complex.I * (rho.1.im : ℂ)) a‖ *
        ‖(u : ℂ) ^ (N + 1) * ∑ k ∈ Finset.range (N + 1),
          (Real.log a : ℂ) ^ k / (k.factorial : ℂ) *
            ordinaryPrimeMoment (N - k) (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ := by
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ ‖zetaPrimeFeature (3 / 2 + Complex.I * (rho.1.im : ℂ)) a‖ *
        (C * Real.exp (u * Real.log a)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by
      rw [norm_zetaPrimeFeature]
      simp only [zetaPrimeExpWeight, Complex.add_re, Complex.div_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re]
      norm_num
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      dsimp [u]
      ring

/-- The full logarithmic mark log(a*p), including both cofactor and
prime logarithms, on the complete prime-factor series. -/
def completedPrimeProductMoment (a N : ℕ) (s : ℂ) : ℂ :=
  ∑' p : ℕ, if p.Prime then (Real.log ((a * p : ℕ) : ℝ) : ℂ) *
    zetaPrimeLogKernel N s (a * p) else 0

/-- The two logarithmic components are genuinely summable and add
back to the literal product logarithm, with no deleted prime or phase. -/
theorem hasSum_completedPrimeProductMoment {s : ℂ} (hs : 1 < s.re)
    {a : ℕ} (ha : 0 < a) (N : ℕ) :
    HasSum (fun p : ℕ => if p.Prime then (Real.log ((a * p : ℕ) : ℝ) : ℂ) *
      zetaPrimeLogKernel N s (a * p) else 0)
      ((Real.log a : ℂ) * (∑' p : ℕ, if p.Prime then zetaPrimeLogKernel N s (a * p) else 0) +
        ∑' p : ℕ, if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ) *
          zetaPrimeLogKernel N s (a * p) else 0) := by
  have h := ((hasSum_unlogged_prime_product hs N ha).summable.hasSum.mul_left
    (Real.log a : ℂ)).add (hasSum_prime_log_product hs N ha).summable.hasSum
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, Nat.cast_mul, Real.log_mul (by positivity : (a : ℝ) ≠ 0)
      (show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero), Complex.ofReal_add, ArithmeticFunction.vonMangoldt_apply_prime hp]
    ring
  · simp [hp]

/-- Uniform source-scale control of the completed prime-factor
response with its full product logarithm, for every positive cofactor. -/
theorem exists_completedPrimeProductMoment_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ), 0 < a → ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        completedPrimeProductMoment a N (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ ≤
        C * (1 + Real.log a) * Real.exp (-rho.1.re * Real.log a) := by
  obtain ⟨C, hC, hb⟩ := exists_prime_log_product_bound rho hrho hexposed
  obtain ⟨D, hD, hd⟩ := exists_unlogged_prime_product_bound rho hrho hexposed
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro a ha N
  let u : ℝ := 3 / 2 - rho.1.re
  let s : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ)
  rw [completedPrimeProductMoment, (hasSum_completedPrimeProductMoment
    (by norm_num : 1 < (3 / 2 + Complex.I * (rho.1.im : ℂ)).re) ha N).tsum_eq, mul_add]
  have he : (u : ℂ) ^ (N + 1) * ((Real.log a : ℂ) *
      (∑' p : ℕ, if p.Prime then zetaPrimeLogKernel N s (a * p) else 0)) =
      (Real.log a : ℂ) * ((u : ℂ) ^ (N + 1) *
        (∑' p : ℕ, if p.Prime then zetaPrimeLogKernel N s (a * p) else 0)) := by ring
  change ‖(u : ℂ) ^ (N + 1) * ((Real.log a : ℂ) * _) + _‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg a)]
  apply (add_le_add (mul_le_mul_of_nonneg_left (hd a ha N)
    (Real.log_natCast_nonneg a)) (hb a ha N)).trans
  have hlog := Real.log_natCast_nonneg a
  have hexp := (Real.exp_pos (-rho.1.re * Real.log a)).le
  nlinarith [mul_nonneg (mul_nonneg hC hlog) hexp, mul_nonneg hD hexp]

/-- Every coefficient of the original arbitrary fixed filter remains
on its original factorial order in the completed prime-factor sum. -/
def completedPrimeProductFilter (a : ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * completedPrimeProductMoment a (N + k) s

/-- The full factorial filter has an explicit coefficient cost at
source distance u. No filter or cofactor needs to be chosen numerically. -/
theorem exists_completedPrimeProductFilter_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ), 0 < a → ∀ (P : Polynomial ℂ) (N : ℕ),
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        completedPrimeProductFilter a P N (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ ≤
        C * (1 + Real.log a) * Real.exp (-rho.1.re * Real.log a) *
          ∑ k ∈ P.support, ‖P.coeff k‖ * (3 / 2 - rho.1.re)⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_completedPrimeProductMoment_bound rho hrho hexposed
  refine ⟨C, hC, ?_⟩
  intro a ha P N
  let u : ℝ := 3 / 2 - rho.1.re
  let s : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ)
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [completedPrimeProductFilter, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ P.support, (‖P.coeff k‖ * u⁻¹ ^ k) *
        (C * (1 + Real.log a) * Real.exp (-rho.1.re * Real.log a)) := by
      apply Finset.sum_le_sum
      intro k _
      have he : (u : ℂ) ^ (N + 1) * (P.coeff k * completedPrimeProductMoment a (N + k) s) =
          (P.coeff k * (u : ℂ)⁻¹ ^ k) *
            ((u : ℂ) ^ (N + k + 1) * completedPrimeProductMoment a (N + k) s) := by
        rw [show N + k + 1 = k + (N + 1) by omega, pow_add, inv_pow]
        field_simp
        simp only [pow_add, pow_one]
        ring
      change ‖(u : ℂ) ^ (N + 1) * (P.coeff k * completedPrimeProductMoment a (N + k) s)‖ ≤ _
      rw [he, norm_mul, norm_mul, norm_pow, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hu]
      exact mul_le_mul_of_nonneg_left (hb a ha (N + k)) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The literal completed cofactor sum retains the Riesz prefactor
-log(a)/L. In its physical semiprime range this is the actual coefficient;
transferring the completion back to the finite band is a separate task. -/
def completedCofactorHead (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ∑ a ∈ A, -((Real.log a : ℂ) / (L : ℂ)) * completedPrimeProductFilter a P N s

/-- A complete cofactor head has an explicit arithmetic mass bound.
Prime cancellation is performed inside each complete factor series before
the cofactor sum is bounded. The physical 1/L factor remains visible. -/
theorem exists_completedCofactorHead_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      ∀ (P : Polynomial ℂ) (N : ℕ) (L : ℝ), 0 < L →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        completedCofactorHead A P N (3 / 2 + Complex.I * (rho.1.im : ℂ)) L‖ ≤
        C * (∑ k ∈ P.support, ‖P.coeff k‖ * (3 / 2 - rho.1.re)⁻¹ ^ k) / L *
          ∑ a ∈ A, Real.log a * (1 + Real.log a) * Real.exp (-rho.1.re * Real.log a) := by
  obtain ⟨C, hC, hb⟩ := exists_completedPrimeProductFilter_bound rho hrho hexposed
  refine ⟨C, hC, ?_⟩
  intro A hA P N L hL
  let u : ℝ := 3 / 2 - rho.1.re
  let s : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ)
  rw [completedCofactorHead, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ A, (Real.log a / L) *
        (C * (1 + Real.log a) * Real.exp (-rho.1.re * Real.log a) *
          ∑ k ∈ P.support, ‖P.coeff k‖ * u⁻¹ ^ k) := by
      apply Finset.sum_le_sum
      intro a ha
      have he : (u : ℂ) ^ (N + 1) *
          (-((Real.log a : ℂ) / (L : ℂ)) * completedPrimeProductFilter a P N s) =
          -((Real.log a : ℂ) / (L : ℂ)) *
            ((u : ℂ) ^ (N + 1) * completedPrimeProductFilter a P N s) := by ring
      change ‖(u : ℂ) ^ (N + 1) * (-((Real.log a : ℂ) / (L : ℂ)) * _)‖ ≤ _
      rw [he, norm_mul, norm_neg, norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg a), abs_of_pos hL]
      exact mul_le_mul_of_nonneg_left (hb a (hA a ha) P N) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by ring)

/-- The completed arbitrary factorial filter is the actual convergent
prime series with log(a*p), including all original complex coefficients. -/
theorem hasSum_completedPrimeProductFilter {s : ℂ} (hs : 1 < s.re)
    {a : ℕ} (ha : 0 < a) (P : Polynomial ℂ) (N : ℕ) :
    HasSum (fun p : ℕ => if p.Prime then (Real.log ((a * p : ℕ) : ℝ) : ℂ) *
      zetaPrimeFilterKernel P N s (a * p : ℕ) else 0) (completedPrimeProductFilter a P N s) := by
  have h := hasSum_sum (s := P.support) (fun k _ =>
    (hasSum_completedPrimeProductMoment hs ha (N + k)).summable.hasSum.mul_left (P.coeff k))
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, zetaPrimeFilterKernel_nat, Finset.mul_sum, zetaPrimeLogKernel]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · simp [hp]

end
end RiemannGaussian.ZetaPrimeCofactorCompletion
