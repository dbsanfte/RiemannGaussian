import RiemannGaussian.EtaFiniteCurrentMeasureBounds

/-!
# Exponential envelopes of the literal completed-current kernels

The head and adjacent-moment kernels retain their existing signed formulas.
Their absolute-value estimates keep both completion weights, complementary
horizontal exponents, the cutoff increment, and the bounded centered powers.
These envelopes will control reconstruction error, not replace the signed
arithmetic target.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The positive sum of the two completed exponential weights, before
integration over either current carrier. -/
def pairedEtaCompletedCurrentExponentialEnvelope (rho : NontrivialZetaZero) (v : ℝ) : ℝ :=
  pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 * Real.exp (-(1 - rho.1.re) * v) +
    pairedEtaCompletedLaplaceWeight rho.1 * Real.exp (-rho.1.re * v)

/-- Both terms of the completed exponential envelope are nonnegative. -/
theorem pairedEtaCompletedCurrentExponentialEnvelope_nonneg (rho : NontrivialZetaZero) (v : ℝ) :
    0 ≤ pairedEtaCompletedCurrentExponentialEnvelope rho v := by
  have hp : 0 ≤ pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 := Complex.normSq_nonneg _
  have hq : 0 ≤ pairedEtaCompletedLaplaceWeight rho.1 := Complex.normSq_nonneg _
  unfold pairedEtaCompletedCurrentExponentialEnvelope
  positivity

/-- The signed horizontal bracket is bounded by the retained sum of its
two actual completed exponential components. -/
theorem abs_completedCurrentHorizontalBracket_le (rho : NontrivialZetaZero) (v : ℝ) :
    |pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket rho v| ≤
      pairedEtaCompletedCurrentExponentialEnvelope rho v := by
  have hp : 0 ≤ pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 := Complex.normSq_nonneg _
  have hq : 0 ≤ pairedEtaCompletedLaplaceWeight rho.1 := Complex.normSq_nonneg _
  unfold pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket pairedEtaCompletedCurrentExponentialEnvelope
  have hp' := mul_nonneg hp (Real.exp_pos (-(1 - rho.1.re) * v)).le
  have hq' := mul_nonneg hq (Real.exp_pos (-rho.1.re * v)).le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem norm_completed_head_pair (C s : ℂ) (L v u : ℝ) :
    ‖(C * ((-Complex.exp (-s * (L : ℂ))) * Complex.exp (-s * (v : ℂ)))) *
      starRingEnd ℂ (C * Complex.exp (-s * (u : ℂ)))‖ =
      Complex.normSq C * Real.exp (-s.re * (v + L + u)) := by
  have he : Real.exp (-s.re * (v + L + u)) =
      Real.exp ((-s * (L : ℂ)).re) * Real.exp ((-s * (v : ℂ)).re) * Real.exp ((-s * (u : ℂ)).re) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  rw [he, Complex.normSq_eq_norm_sq]
  simp only [norm_mul, norm_neg, starRingEnd_apply, norm_star, Complex.norm_exp]
  ring

/-- At multiplicity one, the actual head kernel has the completed
exponential envelope at its restored physical first coordinate. -/
theorem abs_topPrefixFiniteEnergyHeadKernel_le (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) (p : ℝ × ℝ) :
    |pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p| ≤
      2 * pairedEtaCompletedCurrentExponentialEnvelope rho
        (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) := by
  have hp : ‖pairedEtaTopPrefixFinitePartnerHeadFeature rho N p.1 *
      starRingEnd ℂ (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
        rho (N + 1) p.2)‖ =
      pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 *
        Real.exp (-(1 - rho.1.re) * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2)) := by
    unfold pairedEtaTopPrefixFinitePartnerHeadFeature
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
    simp only [hm, Nat.sub_self, pow_zero, one_mul]
    simpa only [pairedEtaCompletedLaplaceWeight, NontrivialZetaZero.conjugatePartner_coe,
      Complex.sub_re, Complex.one_re, Complex.conj_re] using norm_completed_head_pair
        (pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1) (NontrivialZetaZero.conjugatePartner rho).1
        (pairedEtaLogTailCutoff (N + 1)) p.1 p.2
  have hq : ‖pairedEtaTopPrefixFiniteConjugateHeadFeature rho N p.1 *
      starRingEnd ℂ (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
        rho (N + 1) p.2)‖ =
      pairedEtaCompletedLaplaceWeight rho.1 *
        Real.exp (-rho.1.re * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2)) := by
    unfold pairedEtaTopPrefixFiniteConjugateHeadFeature
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
    simp only [hm, Nat.sub_self, pow_zero, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      starRingEnd_apply, norm_star]
    simpa only [pairedEtaCompletedLaplaceWeight, norm_mul, norm_neg, starRingEnd_apply, norm_star] using
      norm_completed_head_pair (pairedEtaXiCompletionFactor rho.1 * rho.1) rho.1
        (pairedEtaLogTailCutoff (N + 1)) p.1 p.2
  unfold pairedEtaTopPrefixFiniteEnergyHeadKernel
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact ((Complex.abs_re_le_norm _).trans (norm_sub_le _ _)).trans_eq (by
    rw [hp, hq]
    rfl)

/-- The adjacent centered powers are bounded on the literal physical
window by one explicit logarithmic power depending on the multiplicity. -/
theorem abs_adjacent_current_centered_monomial_le {L t u : ℝ} (m : ℕ)
    (ht : t ∈ Icc 0 L) (hu : u ∈ Icc 0 L) :
    |(t - L) ^ (m - 2) * (u - L) ^ (m - 1)| ≤ (1 + L) ^ (2 * m) := by
  have hL : 0 ≤ L := ht.1.trans ht.2
  have htL : |t - L| ≤ 1 + L := by rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; linarith [ht.1]
  have huL : |u - L| ≤ 1 + L := by rw [abs_of_nonpos (sub_nonpos.mpr hu.2)]; linarith [hu.1]
  rw [abs_mul, abs_pow, abs_pow]
  calc
    _ ≤ (1 + L) ^ (m - 2) * (1 + L) ^ (m - 1) :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) htL _) (pow_le_pow_left₀ (abs_nonneg _) huL _)
        (by positivity) (by positivity)
    _ = (1 + L) ^ (m - 2 + (m - 1)) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)

/-- The actual adjacent kernel retains its one cutoff increment and both
completed exponential terms in a uniform finite-window envelope. -/
theorem abs_topPrefixFiniteEnergyFactoredAdjacentMomentKernel_le (rho : NontrivialZetaZero) (N : ℕ)
    {p : ℝ × ℝ} (hp : p.1 ∈ Icc 0 (pairedEtaLogTailCutoff (N + 2)) ∧
      p.2 ∈ Icc 0 (pairedEtaLogTailCutoff (N + 2))) :
    |pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p| ≤
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) *
          pairedEtaCompletedCurrentExponentialEnvelope rho (p.1 + p.2) := by
  have hc : 0 ≤ 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (pairedEtaLogTailShiftIncrement_pos _).le)
  have hpow := abs_adjacent_current_centered_monomial_le (analyticZetaZeroMultiplicity rho) hp.1 hp.2
  unfold pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul _ (abs_completedCurrentHorizontalBracket_le rho _) (abs_nonneg _)
    (mul_nonneg hc (pow_nonneg (by linarith [pairedEtaLogTailCutoff_nonneg (N + 2)]) _))
  exact (mul_le_of_le_one_right (mul_nonneg hc (abs_nonneg _)) (Real.abs_cos_le_one _)).trans
    (mul_le_mul_of_nonneg_left hpow hc)

end

end RiemannGaussian
