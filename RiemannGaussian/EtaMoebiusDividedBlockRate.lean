import RiemannGaussian.MoebiusFiniteMellinRate
import RiemannGaussian.EtaMoebiusDividedBlockCancellation

/-!
# Quantitative cancellation on the original completed eta quotient blocks

The explicit finite Möbius remainder is carried through literal integer
quotient blocks and absorbed above a stated cubic logarithmic cutoff.
The original completed zeroth eta blocks retain their complex coefficient,
completion factor, and unpaired endpoint decay. A common scale threshold
works for every actual zero; the constants and cutoff retain their full
dependence on the zero. The complete reflected inverse energy remains open.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- Literal integer quotient blocks have a quantitative exponential gain above the specified arithmetic scale, uniformly in both cutoffs and with the weight dependence explicit. -/
theorem exists_complexMoebiusDividedCutoffBlock_cubic_rate :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ h : ℝ, H ≤ h → ∀ M q : ℕ, 0 < q →
      Real.exp (2 * moebiusFiniteContourCenter h / (1 - s.re)) ≤ ((M / q : ℕ) + 1 : ℝ) →
        ‖complexMoebiusDividedCutoffBlock s M q‖ ≤
          2 * moebiusFiniteMellinCancellationConstant s *
            ((M / q : ℕ) + 1 : ℝ) ^ (1 - s.re) * Real.exp (-h / 2) := by
  obtain ⟨H, hH, hprefix⟩ := exists_complexMoebiusFinitePrefix_cubic_remainder
  refine ⟨H, hH, fun s hs hsone h hh M q hq hsize ↦ ?_⟩
  have hC := moebiusFiniteCancellationConstant_pos
  have hZ := moebiusMellinDerivativeMass_nonneg s
  have hcut : M / (q + 1) ≤ M / q := Nat.div_le_div_left (by omega : q ≤ q + 1) hq
  have hpower : ((M / (q + 1) : ℕ) + 1 : ℝ) ^ (1 - s.re) ≤
      ((M / q : ℕ) + 1 : ℝ) ^ (1 - s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ hcut) (by linarith)
  have hsecond := (hprefix s hs hsone h hh (M / (q + 1))).trans
    (add_le_add (mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ (moebiusFiniteCancellationConstant * (1 + ‖s‖ / (1 - s.re))) * Real.exp (-h / 2)
        by positivity)) le_rfl)
  have hrem := exp_moebiusFiniteContourCenter_le_saved_power hsone (hH.trans hh)
    (show (0 : ℝ) < (M / q : ℕ) + 1 by positivity) hsize
  have hb := mul_le_mul_of_nonneg_right hrem
    (show 0 ≤ 1 + ‖s‖ * moebiusMellinDerivativeMass s by positivity)
  rw [complexMoebiusDividedCutoffBlock_eq_prefix_sub s M hq]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (hprefix s hs hsone h hh (M / q)) hsecond).trans
  apply (add_le_add (add_le_add le_rfl hb) (add_le_add le_rfl hb)).trans_eq
  unfold moebiusFiniteMellinCancellationConstant
  ring

/-- The actual completed zeroth eta quotient blocks have a quantitative exponential-scale coefficient with no additive remainder above the stated cutoff, retaining every original completion and endpoint factor. -/
theorem exists_pairedEtaCompletedMoebius_divided_block_cubic_rate :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ rho : NontrivialZetaZero, ∀ h : ℝ, H ≤ h → ∀ (a : ℝ) (M q : ℕ), 0 < q →
      Real.exp (2 * moebiusFiniteContourCenter h / (1 - rho.1.re)) ≤ ((M / q : ℕ) + 1 : ℝ) →
        ‖∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ M / d = q),
          pairedEtaCompletedMomentMoebiusTerm rho 0 a M d‖ ≤
            (2 * moebiusFiniteMellinCancellationConstant rho.1 *
              ((M / q : ℕ) + 1 : ℝ) ^ (1 - rho.1.re) * Real.exp (-h / 2)) *
            (‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) * (q : ℝ) ^ (-rho.1.re)) := by
  obtain ⟨H, hH, hblock⟩ := exists_complexMoebiusDividedCutoffBlock_cubic_rate
  refine ⟨H, hH, fun rho h hh a M q hq hsize ↦ ?_⟩
  have hb := hblock rho.1 (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho)
    h hh M q hq hsize
  have hfactor : ‖pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix q rho.1‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ * (‖rho.1‖ / rho.1.re + 1) * (q : ℝ) ^ (-rho.1.re) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_pairedEtaUnpairedDirichletPrefix_le rho hq)
      (norm_nonneg _)).trans_eq (by ring)
  have hC := moebiusFiniteMellinCancellationConstant_pos (NontrivialZetaZero.re_lt_one rho)
  rw [sum_pairedEtaCompletedMomentMoebiusTerm_zero_divided_block, norm_mul]
  exact mul_le_mul hb hfactor (norm_nonneg _) (by positivity)

end

end RiemannGaussian
