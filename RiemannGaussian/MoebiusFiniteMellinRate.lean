import RiemannGaussian.MoebiusFiniteQuantitativeCancellation
import RiemannGaussian.MoebiusFiniteMellinBound

/-!
# Quantitative finite Möbius cancellation with complex Mellin weights

The exact finite Abel identity carries the quantitative integer-prefix
bound to every complex weight in the open critical strip. Its constant
retains the dependence on the complex weight and on the complete derivative
mass. One common scale threshold works for all weights; the arithmetic
cutoff condition retains the distance of the real part from one.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- The actual finite Mellin cancellation constant retains both Abel contributions and their full weight dependence. -/
def moebiusFiniteMellinCancellationConstant (s : ℂ) : ℝ :=
  moebiusFiniteCancellationConstant * (1 + ‖s‖ / (1 - s.re)) +
    (1 + ‖s‖ * moebiusMellinDerivativeMass s)

/-- The quantitative Mellin cancellation constant is positive throughout the open critical strip. -/
theorem moebiusFiniteMellinCancellationConstant_pos {s : ℂ} (hsone : s.re < 1) :
    0 < moebiusFiniteMellinCancellationConstant s := by
  have hC := moebiusFiniteCancellationConstant_pos
  have hZ := moebiusMellinDerivativeMass_nonneg s
  unfold moebiusFiniteMellinCancellationConstant
  positivity

/-- One common scale threshold carries the proved quantitative ordinary prefix bound through every actual finite complex Abel sum. -/
theorem exists_complexMoebiusFinitePrefix_cubic_remainder :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ h : ℝ, H ≤ h → ∀ M : ℕ,
      ‖complexMoebiusFinitePrefix s M‖ ≤
        (moebiusFiniteCancellationConstant * (1 + ‖s‖ / (1 - s.re))) *
          Real.exp (-h / 2) * (M + 1 : ℝ) ^ (1 - s.re) +
        Real.exp (moebiusFiniteContourCenter h) * (1 + ‖s‖ * moebiusMellinDerivativeMass s) := by
  obtain ⟨H, hH, hprefix⟩ := exists_moebiusFinitePrefix_exponential_remainder
  refine ⟨H, hH, fun s hs hsone h hh M ↦ ?_⟩
  have hC := moebiusFiniteCancellationConstant_pos
  have hb := norm_complexMoebiusFinitePrefix_le_linear_remainder hs hsone
    (show 0 ≤ moebiusFiniteCancellationConstant * Real.exp (-h / 2) by positivity)
    (Real.exp_pos (moebiusFiniteContourCenter h)).le (hprefix h hh) M
  exact hb.trans_eq (by ring)

/-- The explicit arithmetic cutoff absorbs the full cubic-scale remainder into the exponentially saved Mellin power. -/
theorem exp_moebiusFiniteContourCenter_le_saved_power {s : ℂ} (hsone : s.re < 1)
    {h : ℝ} (hh : 22 ≤ h) {X : ℝ} (hX : 0 < X)
    (hsize : Real.exp (2 * moebiusFiniteContourCenter h / (1 - s.re)) ≤ X) :
    Real.exp (moebiusFiniteContourCenter h) ≤ X ^ (1 - s.re) * Real.exp (-h / 2) := by
  have hp : 0 < 1 - s.re := by linarith
  have hlog := (Real.le_log_iff_exp_le hX).mpr hsize
  have hm := mul_le_mul_of_nonneg_right hlog hp.le
  rw [div_mul_cancel₀ _ hp.ne'] at hm
  have hpower : Real.exp (2 * moebiusFiniteContourCenter h) ≤ X ^ (1 - s.re) := by
    rw [Real.rpow_def_of_pos hX]
    exact Real.exp_le_exp.mpr hm
  have ha : h ≤ moebiusFiniteContourCenter h := by
    unfold moebiusFiniteContourCenter
    nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ h - 1 by linarith), sq_nonneg (h - 1)]
  calc
    _ ≤ Real.exp (2 * moebiusFiniteContourCenter h - h / 2) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (2 * moebiusFiniteContourCenter h) * Real.exp (-h / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le

/-- The actual finite complex Möbius prefix has a quantitative exponential gain above its specified cubic logarithmic cutoff, with one threshold for all critical-strip weights. -/
theorem exists_complexMoebiusFinitePrefix_cubic_rate :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ h : ℝ, H ≤ h → ∀ M : ℕ,
      Real.exp (2 * moebiusFiniteContourCenter h / (1 - s.re)) ≤ (M + 1 : ℝ) →
        ‖complexMoebiusFinitePrefix s M‖ ≤ moebiusFiniteMellinCancellationConstant s *
          (M + 1 : ℝ) ^ (1 - s.re) * Real.exp (-h / 2) := by
  obtain ⟨H, hH, hprefix⟩ := exists_complexMoebiusFinitePrefix_cubic_remainder
  refine ⟨H, hH, fun s hs hsone h hh M hsize ↦ ?_⟩
  have hrem := exp_moebiusFiniteContourCenter_le_saved_power hsone (hH.trans hh)
    (show (0 : ℝ) < M + 1 by positivity) hsize
  have hZ := moebiusMellinDerivativeMass_nonneg s
  have hb := mul_le_mul_of_nonneg_right hrem
    (show 0 ≤ 1 + ‖s‖ * moebiusMellinDerivativeMass s by positivity)
  apply (hprefix s hs hsone h hh M).trans
  apply (add_le_add le_rfl hb).trans_eq
  unfold moebiusFiniteMellinCancellationConstant
  ring

end

end RiemannGaussian
