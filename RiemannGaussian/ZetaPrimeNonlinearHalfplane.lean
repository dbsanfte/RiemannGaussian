/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeNonlinearTail

/-!
# Uniform nonlinear prime allowance on a closed half-plane

The vanishing square-logarithmic tail allowance is uniform on every closed
half-plane strictly to the right of one half. This controls the isolated
nonlinear multiplier; its first-order exponential coupling and original
high-order factorial filter remain unpaid.
-/

namespace RiemannGaussian.ZetaPrimeNonlinearHalfplane
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
open ZetaPrimeNonlinearTail ZetaPrimeCharacterRemainder

/-- Increasing the real part can only decrease every real feature weight. -/
theorem expWeight_mono {sigma tau : ℝ} (hst : sigma ≤ tau) (n : ℕ) :
    zetaPrimeExpWeight tau n ≤ zetaPrimeExpWeight sigma n := by
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (Real.log_natCast_nonneg n)]

/-- The same monotonicity retains the actual square-logarithmic weight. -/
theorem squareLogWeight_mono {sigma tau : ℝ} (hst : sigma ≤ tau) (n : ℕ) :
    squareLogWeight tau n ≤ squareLogWeight sigma n :=
  mul_le_mul_of_nonneg_right (expWeight_mono (by linarith) n) (Real.log_natCast_nonneg n)

/-- The convergent total-minus-prefix definition is the ordinary shifted
tail series, retaining every unpaid natural weight. -/
theorem squareLogTail_eq_tsum {sigma : ℝ} (hsigma : 1 / 2 < sigma) (K : ℕ) :
    squareLogTail sigma K = ∑' n, squareLogWeight sigma (n + K) := by
  have h := (summable_squareLogWeight hsigma).sum_add_tsum_nat_add K
  unfold squareLogTail
  linarith only [h]

/-- The entire unpaid allowance decreases as the real part increases. -/
theorem squareLogTail_mono {sigma tau : ℝ} (hsigma : 1 / 2 < sigma)
    (hst : sigma ≤ tau) (K : ℕ) : squareLogTail tau K ≤ squareLogTail sigma K := by
  rw [squareLogTail_eq_tsum (hsigma.trans_le hst), squareLogTail_eq_tsum hsigma]
  exact ((summable_nat_add_iff K).mpr (summable_squareLogWeight (hsigma.trans_le hst))).tsum_le_tsum
    (fun n => squareLogWeight_mono hst (n + K))
    ((summable_nat_add_iff K).mpr (summable_squareLogWeight hsigma))

/-- The frequency-independent exponent ceiling also decreases with the
real part throughout its convergent domain. -/
theorem expWeight_tsum_mono {sigma tau : ℝ} (hsigma : 1 < sigma) (hst : sigma ≤ tau) :
    (∑' n, zetaPrimeExpWeight tau n) ≤ ∑' n, zetaPrimeExpWeight sigma n :=
  (summable_zetaPrimeExpWeight (hsigma.trans_le hst)).tsum_le_tsum (expWeight_mono hst)
    (summable_zetaPrimeExpWeight hsigma)

/-- One vanishing arithmetic allowance controls the nonlinear correction
throughout a whole closed half-plane, not just one vertical line. -/
theorem integral_norm_nonlinearFactor_le_halfplane_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) :
    (∫ xi : ℝ in Ioi 0,
      ‖(Complex.exp (logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi) - 1) /
        (xi : ℂ) ^ 2‖) ≤
      (2 + Real.exp (4 * ∑' n, zetaPrimeExpWeight (2 * sigma) n)) *
        (Real.pi * squareLogTail sigma K) := by
  apply (integral_norm_nonlinearFactor_le_tail Q h16 (hsigma.trans_le hs) K hK).trans
  apply mul_le_mul _ _ (mul_nonneg Real.pi_pos.le
    (squareLogTail_nonneg (hsigma.trans_le hs) K)) (by positivity)
  · apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (expWeight_tsum_mono (by linarith) (by linarith)) (by norm_num)
  · exact mul_le_mul_of_nonneg_left (squareLogTail_mono hsigma hs K) Real.pi_pos.le

/-- The threshold is uniform over every complex point in the closed
half-plane and every finite larger-prime selection. -/
theorem exists_uniform_halfplane_nonlinear_tail_lt {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℕ, 16 ≤ K ∧ ∀ (s : ℂ), sigma ≤ s.re → ∀ (Q : Finset ℕ),
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
  exact (integral_norm_nonlinearFactor_le_halfplane_tail Q h16 hsigma hs (max 16 K) hQ).trans_lt
    (hK (max 16 K) (le_max_right _ _))


end
end RiemannGaussian.ZetaPrimeNonlinearHalfplane
