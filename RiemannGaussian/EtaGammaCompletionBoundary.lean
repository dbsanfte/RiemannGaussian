import RiemannGaussian.EtaGammaNearSquare

/-!
# The exact boundary cost of completing the Moebius square

The complete, untruncated cofactor is the genuine arithmetic convolution
`zeta * mu^2`. Its gamma sum equals the negative smoothed source. The
actual clipped square tends to the positive source. Their exact
coefficient difference therefore tends to twice the nonzero source on
the existing eighth/fifth schedule. Completing the multiplicative core
does not make this boundary negligible.
-/

open Complex Filter
open RiemannGaussian.EtaGammaSmoothing
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaQuadratic

noncomputable section

/-- The complete untruncated Moebius-square cofactor is the original Moebius coefficient after one zeta convolution. -/
theorem cofactor_moebius : cofactor (μ : ArithmeticFunction ℂ) = μ := by
  rw [cofactor, pow_two, ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

/-- The complete untruncated quadratic, using the literal `zeta * mu^2` coefficient at every positive physical integer. -/
def completeQuadratic (rho : NontrivialZetaZero) (A : ℝ) : ℂ :=
  -(∑' n : ℕ, cofactor (μ : ArithmeticFunction ℂ) (n + 1) * gammaCarrier rho A (n + 1))

private theorem summable_complete_cofactor (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ ↦ cofactor (μ : ArithmeticFunction ℂ) (n + 1) *
      gammaCarrier rho A (n + 1)) := by
  apply (summable_norm_cofactor_gamma rho hA _ _).of_norm
  intro n
  simp only [ArithmeticFunction.intCoe_apply, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- The complete quadratic has the opposite smoothed source, with its infinite series evaluated by the already-proved full Moebius identity. -/
theorem completeQuadratic_eq_neg_source (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) :
    completeQuadratic rho A = -gammaMoebiusSource rho A := by
  unfold completeQuadratic
  simp only [cofactor_moebius, ArithmeticFunction.intCoe_apply]
  have he (n : ℕ) : (μ n : ℂ) * gammaCarrier rho A n = gammaMoebiusTerm rho A n := by
    simp only [gammaCarrier, gammaMoebiusTerm]
    ring
  simp_rw [he]
  rw [(hasSum_gammaMoebiusTerm rho hA).tsum_eq]

/-- The entire coefficient boundary between the actual clipped square and the complete multiplicative square, before taking any norm. -/
def completionBoundary (rho : NontrivialZetaZero) (A : ℝ) (U : ℕ) : ℂ :=
  -(∑' n : ℕ, (cofactor (shortMoebius U) (n + 1) -
    cofactor (μ : ArithmeticFunction ℂ) (n + 1)) * gammaCarrier rho A (n + 1))

/-- The coefficientwise boundary is exactly the difference of the original clipped and complete quadratics; both full sums are convergent. -/
theorem completionBoundary_eq_sub (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) (U : ℕ) :
    completionBoundary rho A U = smoothQuadratic rho A U - completeQuadratic rho A := by
  have hs := (summable_norm_cofactor_gamma rho hA (shortMoebius U) (norm_shortMoebius_le_one U)).of_norm
  unfold completionBoundary smoothQuadratic completeQuadratic
  simp_rw [sub_mul]
  rw [hs.tsum_sub (summable_complete_cofactor rho hA)]
  ring

/-- Completing the cofactor exposes an exact source-directed boundary, rather than an omitted exponential tail. -/
theorem completionBoundary_eq_quadratic_add_source (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (U : ℕ) :
    completionBoundary rho A U = smoothQuadratic rho A U + gammaMoebiusSource rho A := by
  rw [completionBoundary_eq_sub rho hA, completeQuadratic_eq_neg_source rho hA, sub_neg_eq_add]

/-- The complete untruncated square tends to the negative original source on the unchanged eighth/fifth physical scale. -/
theorem completeQuadratic_eighth_tendsto_neg_source (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ completeQuadratic rho ((u : ℝ) ^ 8)) atTop
      (𝓝 (-pairedEtaCompletedMoebiusSource rho)) := by
  apply (source_eighth_tendsto_source rho).neg.congr'
  filter_upwards [eventually_ge_atTop 1] with u hu
  exact (completeQuadratic_eq_neg_source rho (pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 8)).symm

/-- The full finite-rectangle completion boundary tends to twice the original nonzero source, at every actual nontrivial zero. -/
theorem completionBoundary_eighth_tendsto_two_source (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ completionBoundary rho ((u : ℝ) ^ 8) (u ^ 5)) atTop
      (𝓝 (2 * pairedEtaCompletedMoebiusSource rho)) := by
  have h := (smoothQuadratic_eighth_tendsto_source rho).sub
    (completeQuadratic_eighth_tendsto_neg_source rho)
  simp only [sub_neg_eq_add, ← two_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with u hu
  exact (completionBoundary_eq_sub rho (pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 8) (u ^ 5)).symm

/-- The exact completion boundary cannot be discarded as a term tending to zero on the original near-square schedule. -/
theorem completionBoundary_eighth_not_tendsto_zero (rho : NontrivialZetaZero) :
    ¬Tendsto (fun u : ℕ ↦ completionBoundary rho ((u : ℝ) ^ 8) (u ^ 5)) atTop (𝓝 0) := by
  intro hzero
  have he := tendsto_nhds_unique (completionBoundary_eighth_tendsto_two_source rho) hzero
  exact (mul_ne_zero (by norm_num) (pairedEtaCompletedMoebiusSource_ne_zero rho)) he

end

end RiemannGaussian.EtaGammaQuadratic
