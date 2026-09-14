/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeNonlinearFactor

/-!
# The nonlinear prime correction has a vanishing arithmetic tail

At every fixed real part greater than one half, the integrated nonlinear
multiplicative correction is bounded by a nonnegative, decreasing arithmetic
allowance that tends to zero. The bound is uniform in imaginary height and
all finite prime selections above the threshold. The coupled first-order
exponential and the original filtered signed floor remain open.
-/

namespace RiemannGaussian.ZetaPrimeNonlinearTail
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
open ZetaPrimeCharacterRemainder ZetaSquarefreeSignedTail ZetaPrimeNonlinearFactor

/-- The literal nonnegative prime-square logarithmic weight, extended to
natural labels only to obtain a convergent majorant. -/
def squareLogWeight (sigma : ℝ) (n : ℕ) : ℝ :=
  zetaPrimeExpWeight (2 * sigma) n * Real.log n

/-- The prime-square weight is the exact integrated local-error weight. -/
theorem squareLogWeight_eq (s : ℂ) (n : ℕ) :
    squareLogWeight s.re n = ‖zetaPrimeFeature s n‖ ^ 2 * |Real.log n| := by
  rw [norm_zetaPrimeFeature, abs_of_nonneg (Real.log_natCast_nonneg n),
    squareLogWeight, pow_two]
  unfold zetaPrimeExpWeight
  rw [← Real.exp_add]
  congr 2
  ring

/-- These local-error weights are summable for every fixed real part
strictly greater than one half. -/
theorem summable_squareLogWeight {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (squareLogWeight sigma) := by
  have h (n : ℕ) : squareLogWeight sigma n ≤
      (sigma - 1 / 2)⁻¹ * zetaPrimeExpWeight (sigma + 1 / 2) n := by
    have he : squareLogWeight sigma n =
        ‖zetaPrimeLogKernel 1 ((2 * sigma : ℝ) : ℂ) n‖ := by
      rw [norm_zetaPrimeLogKernel]
      simp only [squareLogWeight, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
        Complex.ofReal_re]
      ring
    rw [he]
    have hb := norm_zetaPrimeLogKernel_le 1 ((2 * sigma : ℝ) : ℂ) n
      (by linarith : 0 < sigma - 1 / 2)
    simpa only [pow_one, Complex.ofReal_re,
      show 2 * sigma - (sigma - 1 / 2) = sigma + 1 / 2 by ring] using hb
  exact Summable.of_nonneg_of_le (fun n =>
    mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n)) h
    ((summable_zetaPrimeExpWeight (by linarith : 1 < sigma + 1 / 2)).mul_left _)

/-- The unpaid prime-square logarithmic mass after an explicit integer
threshold. Its series is convergent in the stated half-plane. -/
def squareLogTail (sigma : ℝ) (K : ℕ) : ℝ :=
  (∑' n, squareLogWeight sigma n) - ∑ n ∈ Finset.range K, squareLogWeight sigma n

/-- Each threshold increment pays exactly its own arithmetic weight. -/
theorem squareLogTail_succ (sigma : ℝ) (K : ℕ) :
    squareLogTail sigma (K + 1) = squareLogTail sigma K - squareLogWeight sigma K := by
  simp only [squareLogTail, Finset.sum_range_succ]
  ring

/-- The certified error allowance decreases with the threshold. -/
theorem squareLogTail_antitone (sigma : ℝ) : Antitone (squareLogTail sigma) := by
  apply antitone_nat_of_succ_le
  intro K
  rw [squareLogTail_succ]
  exact sub_le_self _ (mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg K))

/-- The remaining local-error mass is nonnegative. -/
theorem squareLogTail_nonneg {sigma : ℝ} (hsigma : 1 / 2 < sigma) (K : ℕ) :
    0 ≤ squareLogTail sigma K := by
  apply sub_nonneg.mpr
  exact (summable_squareLogWeight hsigma).sum_le_tsum _ (fun n _ =>
    mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n))

/-- Moving the threshold to infinity exhausts the entire summable
prime-square logarithmic error allowance. -/
theorem tendsto_squareLogTail {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Tendsto (squareLogTail sigma) atTop (𝓝 0) := by
  change Tendsto (fun K => (∑' n, squareLogWeight sigma n) -
    ∑ n ∈ Finset.range K, squareLogWeight sigma n) atTop (𝓝 0)
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' n, squareLogWeight sigma n)).sub
      (summable_squareLogWeight hsigma).hasSum.tendsto_sum_nat

/-- Every finite prime selection above the threshold is bounded by the
same remaining mass; no density or sign assumption is imposed. -/
theorem sum_squareLogWeight_le_tail (Q : Finset ℕ) {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (K : ℕ) (hQ : ∀ p ∈ Q, K ≤ p) :
    (∑ p ∈ Q, squareLogWeight sigma p) ≤ squareLogTail sigma K := by
  have hd : Disjoint Q (Finset.range K) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpr
    exact (Nat.not_lt.mpr (hQ p hp)) (Finset.mem_range.mp hpr)
  have h := (summable_squareLogWeight hsigma).sum_le_tsum (Q ∪ Finset.range K)
    (fun n _ => mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n))
  rw [Finset.sum_union hd] at h
  exact le_sub_iff_add_le.mpr h

/-- The complete finite log remainder is bounded uniformly in frequency
and in the finite prime selection. -/
theorem norm_actual_logRemainder_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) (xi : ℝ) :
    ‖logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi‖ ≤
      4 * ∑' n, zetaPrimeExpWeight (2 * s.re) n := by
  rw [logRemainder, Finset.sum_sub_distrib]
  exact norm_sum_actual_prime_character_error_le Q
    (fun p => Complex.exp (((Real.log p * xi : ℝ) : ℂ) * Complex.I)) hQ
    (fun p _hp => (Complex.norm_exp_ofReal_mul_I _).le) hs

/-- The integrated nonlinear multiplicative correction costs only the
remaining square-log mass above the prime threshold. -/
theorem integral_norm_nonlinearFactor_le_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re)
    (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) :
    (∫ xi : ℝ in Ioi 0,
      ‖(Complex.exp (logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi) - 1) /
        (xi : ℂ) ^ 2‖) ≤
      (2 + Real.exp (4 * ∑' n, zetaPrimeExpWeight (2 * s.re) n)) *
        (Real.pi * squareLogTail s.re K) := by
  have h := integral_norm_exp_logRemainder_sub_one_div_le Q (zetaPrimeFeature s)
    (fun p => Real.log p) (fun p hp => norm_primeFeature_le_quarter hs.le (h16 p hp))
    (norm_actual_logRemainder_le Q h16 hs)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  simp_rw [← squareLogWeight_eq]
  exact sum_squareLogWeight_le_tail Q hs K hK

/-- At every fixed real part greater than one half, the integrated
nonlinear correction can be made arbitrarily small uniformly in height
and in all finite prime selections above one threshold. -/
theorem exists_uniform_nonlinearFactor_tail_lt {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℕ, 16 ≤ K ∧ ∀ (s : ℂ), s.re = sigma → ∀ (Q : Finset ℕ),
      (∀ p ∈ Q, K ≤ p) →
        (∫ xi : ℝ in Ioi 0,
          ‖(Complex.exp (logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi) - 1) /
            (xi : ℂ) ^ 2‖) < eps := by
  have ht : Tendsto (fun K =>
      (2 + Real.exp (4 * ∑' n, zetaPrimeExpWeight (2 * sigma) n)) *
        (Real.pi * squareLogTail sigma K)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((tendsto_squareLogTail hsigma).const_mul Real.pi).const_mul
      (2 + Real.exp (4 * ∑' n, zetaPrimeExpWeight (2 * sigma) n))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  refine ⟨max 16 K, le_max_left _ _, ?_⟩
  intro s hs Q hQ
  have h16 (p : ℕ) (hp : p ∈ Q) : 16 ≤ p := (le_max_left _ _).trans (hQ p hp)
  have h := integral_norm_nonlinearFactor_le_tail Q h16 (s := s) (by simpa only [hs] using hsigma)
    (max 16 K) hQ
  rw [hs] at h
  exact h.trans_lt (hK (max 16 K) (le_max_right _ _))

end
end RiemannGaussian.ZetaPrimeNonlinearTail
