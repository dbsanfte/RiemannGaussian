import RiemannGaussian.MoebiusFiniteMellinBound

/-!
# Finite complex Möbius cancellation on the original arithmetic scale

The finite complex-weighted sum has vanishing ratio to its natural power
scale for each fixed weight in the critical strip. The stronger complex
normalization retains the Mellin phase. The actual eta completion factor
is also transported without changing the cutoff or losing its phase.
The original current still requires its divided eta factors and reflected
mixed interactions; the finite coefficient estimate alone does not bound it.
-/

open Complex Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual finite complex-weighted Möbius prefix is o((M+1)^(1-Re(s))) for each fixed complex weight in the critical strip. -/
theorem complexMoebiusFinitePrefix_norm_ratio_tendsto_zero {s : ℂ}
    (hs : 0 < s.re) (hsone : s.re < 1) :
    Tendsto (fun M : ℕ ↦ ‖complexMoebiusFinitePrefix s M‖ / (M + 1 : ℝ) ^ (1 - s.re))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨C, _, hC⟩ := exists_complexMoebiusFinitePrefix_power_remainder hs hsone
    (by linarith : 0 < eps / 2)
  have hx : Tendsto (fun M : ℕ ↦ (M + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (show 0 < 1 - s.re by linarith)).comp hx
  have hz : Tendsto (fun M : ℕ ↦ C / (M + 1 : ℝ) ^ (1 - s.re)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hz (eps / 2) (by linarith)
  refine ⟨A, fun M hM ↦ ?_⟩
  have hpos : 0 < (M + 1 : ℝ) ^ (1 - s.re) := Real.rpow_pos_of_pos (by positivity) _
  have hb := div_le_div_of_nonneg_right (hC M) hpos.le
  rw [add_div, mul_div_cancel_right₀ _ hpos.ne'] at hb
  have he := hA M hM
  rw [Real.dist_eq, sub_zero] at he ⊢
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le)]
  have hle := le_abs_self (C / (M + 1 : ℝ) ^ (1 - s.re))
  linarith

/-- The full complex power normalization of the actual finite Möbius sum tends to zero, retaining its phase. -/
theorem complexMoebiusFinitePrefix_normalized_tendsto_zero {s : ℂ}
    (hs : 0 < s.re) (hsone : s.re < 1) :
    Tendsto (fun M : ℕ ↦ (M + 1 : ℂ) ^ (s - 1) * complexMoebiusFinitePrefix s M)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  convert complexMoebiusFinitePrefix_norm_ratio_tendsto_zero hs hsone using 1
  funext M
  have hn : ‖(M + 1 : ℂ) ^ (s - 1)‖ = (M + 1 : ℝ) ^ (-(1 - s.re)) := by
    simpa only [neg_sub, Complex.sub_re, Complex.one_re] using norm_moebiusMellinWeight (1 - s) M
  rw [norm_mul, hn, Real.rpow_neg (by positivity), div_eq_mul_inv, mul_comm]

/-- The original eta completion and complex divisor phase both survive the checked finite-prefix cancellation for each actual zero. -/
theorem pairedEtaCompletedMoebiusFinitePrefix_normalized_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun M : ℕ ↦ (M + 1 : ℂ) ^ (rho.1 - 1) *
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) * complexMoebiusFinitePrefix rho.1 M))
      atTop (𝓝 0) := by
  have h := (complexMoebiusFinitePrefix_normalized_tendsto_zero
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho)).const_mul
      (pairedEtaXiCompletionFactor rho.1 * rho.1)
  simp only [mul_zero] at h
  convert h using 1
  funext M
  ring

end

end RiemannGaussian
