/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeClearedHeatSource

/-!
# Global Euler-line bounds for the actual cleared residual

Absolute convergence bounds the original prime continuation uniformly on a
fixed Euler half-plane. The complete clearing polynomial contributes only
polynomial vertical growth. Cauchy's estimate on quarter-radius discs then
bounds every actual factorial residual moment, with one constant and one
vertical degree for all orders. The exact signed source identity remains
available upstream; the norm estimate here is only for its Gaussian tails.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Metric Set Topology
open scoped Classical

/-- Absolute Euler convergence gives a single bound on the actual prime
tail throughout the closed half-plane with real part at least 5/4. -/
theorem exists_primeTailContinuation_euler_bound {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 5 / 4 ≤ z.re → ‖primeTailContinuation D S z‖ ≤ C := by
  let f := primeCorrectionCoefficient D S
  have hsum : Summable (LSeries.term f (5 / 4 : ℂ)) :=
    (LSeriesHasSum_primeTailContinuation hD S hS (by norm_num : 1 < (5 / 4 : ℂ).re)).summable
  let A := ∑' n, ‖LSeries.term f (5 / 4 : ℂ) n‖
  have hA : 0 ≤ A := tsum_nonneg (fun _ ↦ norm_nonneg _)
  refine ⟨A + 1, by positivity, fun z hz ↦ ?_⟩
  have hre : (5 / 4 : ℂ).re ≤ z.re := by simpa using hz
  have hs : Summable (LSeries.term f z) := LSeriesSummable.of_re_le_re hre hsum
  rw [primeTailContinuation_eq_LSeries hD S hS (by linarith)]
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re f hre) hsum.norm).trans (by linarith))

private theorem polynomial_eval_bound (q : Polynomial ℂ) {z : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖q.eval z‖ ≤ (∑ k ∈ q.support, ‖q.coeff k‖) * R ^ q.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) hz _).trans
    (pow_le_pow_right₀ hR (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)))

/-- Any complex polynomial has one polynomial vertical envelope on all
quarter-discs about a fixed vertical line, including every coefficient. -/
theorem exists_polynomial_quarterDisc_bound (q : Polynomial ℂ) (s : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ) (z : ℂ),
      z ∈ closedBall (s - I * y) (1 / 4) →
      ‖q.eval z‖ ≤ C * (1 + y ^ 2) ^ q.natDegree := by
  let A := ‖s‖ + 2
  let K := ∑ k ∈ q.support, ‖q.coeff k‖
  have hA : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg s]
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  refine ⟨(K + 1) * A ^ q.natDegree, by positivity, fun y z hz ↦ ?_⟩
  have hy : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  have hbase : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have hn : ‖z - (s - I * y)‖ ≤ 1 / 4 := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hsz : ‖s - I * y‖ ≤ ‖s‖ + |y| := by
    simpa [norm_mul, norm_sub_rev, add_comm] using norm_sub_le s (I * (y : ℂ))
  have ht := norm_add_le (z - (s - I * y)) (s - I * y)
  rw [sub_add_cancel] at ht
  have hzR : ‖z‖ ≤ A * (1 + y ^ 2) := by
    dsimp [A]
    nlinarith [norm_nonneg s, sq_nonneg y]
  have hR : 1 ≤ A * (1 + y ^ 2) := by nlinarith
  calc
    ‖q.eval z‖ ≤ K * (A * (1 + y ^ 2)) ^ q.natDegree := polynomial_eval_bound q hR hzR
    _ ≤ (K + 1) * (A * (1 + y ^ 2)) ^ q.natDegree := by gcongr; linarith
    _ = _ := by rw [mul_pow]; ring

private theorem quarterDisc_re {rho : NontrivialZetaZero} {y : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (zetaWronskianMomentCenter rho - I * y) (1 / 4)) :
    5 / 4 ≤ z.re := by
  have hn : ‖z - (zetaWronskianMomentCenter rho - I * y)‖ ≤ 1 / 4 := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hre := (abs_le.mp ((abs_re_le_norm _).trans hn)).1
  norm_num [zetaWronskianMomentCenter] at hre
  linarith

/-- The actual residual has polynomial growth on every Euler
quarter-disc. Its selected principal part is uniformly separated from its
pole there; the polynomial degree and constant do not depend on the order. -/
theorem exists_clearedPrimeRemainder_quarterDisc_bound {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ) (z : ℂ),
      z ∈ closedBall (zetaWronskianMomentCenter rho - I * y) (1 / 4) →
      ‖clearedPrimeRemainder D S rho z‖ ≤ C *
        (1 + y ^ 2) ^ (normalizedPrimeTailClearingPolynomial D S rho).natDegree := by
  obtain ⟨A, hA, hprime⟩ := exists_primeTailContinuation_euler_bound hD S hS
  obtain ⟨Q, hQ, hpoly⟩ := exists_polynomial_quarterDisc_bound
    (normalizedPrimeTailClearingPolynomial D S rho) (zetaWronskianMomentCenter rho)
  let m := (analyticZetaZeroMultiplicity rho : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  refine ⟨Q * A + 4 * m, by positivity, fun y z hz ↦ ?_⟩
  have hre := quarterDisc_re hz
  have hden : 1 / 4 ≤ ‖z - rho.1‖ := by
    have hd := re_le_norm (z - rho.1)
    rw [Complex.sub_re] at hd
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hpole : ‖(analyticZetaZeroMultiplicity rho : ℂ) / (z - rho.1)‖ ≤ 4 * m := by
    rw [norm_div, Complex.norm_natCast]
    change m / ‖z - rho.1‖ ≤ 4 * m
    apply (div_le_iff₀ (by linarith : 0 < ‖z - rho.1‖)).mpr
    nlinarith
  have hbase : 1 ≤ (1 + y ^ 2) ^ (normalizedPrimeTailClearingPolynomial D S rho).natDegree :=
    one_le_pow₀ (by nlinarith [sq_nonneg y])
  unfold clearedPrimeRemainder
  calc
    _ ≤ ‖(normalizedPrimeTailClearingPolynomial D S rho).eval z‖ * ‖primeTailContinuation D S z‖ +
        ‖(analyticZetaZeroMultiplicity rho : ℂ) / (z - rho.1)‖ := by
      simpa only [norm_mul] using norm_add_le
        ((normalizedPrimeTailClearingPolynomial D S rho).eval z * primeTailContinuation D S z)
        ((analyticZetaZeroMultiplicity rho : ℂ) / (z - rho.1))
    _ ≤ (Q * (1 + y ^ 2) ^ (normalizedPrimeTailClearingPolynomial D S rho).natDegree) * A + 4 * m :=
      add_le_add (mul_le_mul (hpoly y z hz) (hprime z hre) (norm_nonneg _) (by positivity)) hpole
    _ ≤ _ := by nlinarith

/-- A single exponential-in-order, polynomial-in-frequency bound holds
for all normalized moments of the literal cleared residual on the entire
Euler line. It supplies the outer Gaussian tails, without altering the
stronger geometric bound near the selected source. -/
theorem exists_clearedPrimeRemainder_global_bound {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (y : ℝ),
      ‖(clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
        signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)‖ ≤
      C * (4 * clearedPrimeSourceDistance rho) ^ N *
        (1 + y ^ 2) ^ (normalizedPrimeTailClearingPolynomial D S rho).natDegree := by
  obtain ⟨A, hA, hdisc⟩ := exists_clearedPrimeRemainder_quarterDisc_bound hD S hS rho
  have hu := clearedPrimeSourceDistance_pos rho
  refine ⟨A * clearedPrimeSourceDistance rho, by positivity, fun N y ↦ ?_⟩
  have hd : DiffContOnCl ℂ (clearedPrimeRemainder D S rho)
      (ball (zetaWronskianMomentCenter rho - I * y) (1 / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    exact (show AnalyticOnNhd ℂ (clearedPrimeRemainder D S rho)
      (closedBall (zetaWronskianMomentCenter rho - I * y) (1 / 4)) from
      fun z hz ↦ analyticAt_clearedPrimeRemainder D S rho (by linarith [quarterDisc_re hz])).differentiableOn
  have hb := norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 1 / 4) hd
    (fun z hz ↦ hdisc y z (sphere_subset_closedBall hz)) N
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ clearedPrimeSourceDistance rho ^ (N + 1) *
        (A * (1 + y ^ 2) ^ (normalizedPrimeTailClearingPolynomial D S rho).natDegree / (1 / 4) ^ N) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [div_pow, one_pow, div_div_eq_mul_div, div_one, mul_pow, pow_succ]; ring

end
end RiemannGaussian.SquarefreeEulerQuadratic
