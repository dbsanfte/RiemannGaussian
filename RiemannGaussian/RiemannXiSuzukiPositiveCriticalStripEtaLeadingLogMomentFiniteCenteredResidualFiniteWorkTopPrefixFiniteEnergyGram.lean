import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergy

/-!
# Finite positive-measure Gram form of the top-prefix energy defect

This module turns the signed finite energy numerator at the live frontier into
one literal finite eta Gram integral.  First, every binomially defined centered
finite moment is proved equal to a single integral over the finite positive
logarithmic eta measure.  The two completion-weighted complementary features
are then defined on that common measure.

Their integrals are exactly the two complex finite terms from the preceding
module.  Squaring by a justified product-measure exchange gives an integrable
signed Hermitian kernel whose integral is exactly the finite energy difference
`E_N`.  This is an unconditional representation theorem.  It does not prove
the square-summability of `E_N / S_N`.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every polynomial complex Laplace moment is integrable against the finite
positive eta logarithmic measure. -/
theorem integrable_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
    (k N : ℕ) (s : ℂ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ k * Complex.exp (-s * t))
      (pairedEtaFiniteLogMeasure N) := by
  unfold pairedEtaFiniteLogMeasure
  rw [integrable_finsetSum_measure]
  intro n hn
  change IntegrableOn (fun t : ℝ =>
    (t : ℂ) ^ k * Complex.exp (-s * t))
    (Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2)))
  apply IntegrableOn.mono_set
    ((show Continuous (fun t : ℝ =>
      (t : ℂ) ^ k * Complex.exp (-s * t)) by
        fun_prop).continuousOn.integrableOn_Icc)
  exact Ioc_subset_Icc_self

/-- Every centered polynomial complex Laplace moment is integrable against
the finite positive eta logarithmic measure. -/
theorem integrable_centered_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
    (k N : ℕ) (s : ℂ) (a : ℝ) :
    Integrable (fun t : ℝ =>
      (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t))
      (pairedEtaFiniteLogMeasure N) := by
  unfold pairedEtaFiniteLogMeasure
  rw [integrable_finsetSum_measure]
  intro n hn
  change IntegrableOn (fun t : ℝ =>
    (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t))
    (Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2)))
  apply IntegrableOn.mono_set
    ((show Continuous (fun t : ℝ =>
      (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)) by
        fun_prop).continuousOn.integrableOn_Icc)
  exact Ioc_subset_Icc_self

/-- The binomially defined finite centered prefix is one literal centered
moment of the finite eta logarithmic measure. -/
theorem pairedEtaLogLaplaceMomentCenteredPartialSum_eq_integral_finiteLogMeasure
    (k N : ℕ) (s : ℂ) (a : ℝ) :
    pairedEtaLogLaplaceMomentCenteredPartialSum k s a N =
      ∫ t : ℝ,
        (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
        ∂pairedEtaFiniteLogMeasure N := by
  unfold pairedEtaLogLaplaceMomentCenteredPartialSum
  simp_rw [pairedEtaLogLaplaceMomentPartialSum_eq_integral_finiteLogMeasure]
  calc
    (∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          (∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-s * t)
            ∂pairedEtaFiniteLogMeasure N)) =
        ∑ j ∈ Finset.range (k + 1),
          ∫ t : ℝ,
            (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j)) *
              ((t : ℂ) ^ j * Complex.exp (-s * t))
            ∂pairedEtaFiniteLogMeasure N := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
        ∑ j ∈ Finset.range (k + 1),
          (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j)) *
            ((t : ℂ) ^ j * Complex.exp (-s * t))
          ∂pairedEtaFiniteLogMeasure N := by
      rw [integral_finsetSum]
      intro j hj
      exact
        (integrable_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
          j N s).const_mul
            (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j))
    _ = ∫ t : ℝ,
        (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
        ∂pairedEtaFiniteLogMeasure N := by
      apply integral_congr_ae
      filter_upwards with t
      have hpoly : (((t - a : ℝ) : ℂ) ^ k) =
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
              (t : ℂ) ^ j := by
        rw [show ((t - a : ℝ) : ℂ) = (t : ℂ) + -(a : ℂ) by
          push_cast
          ring, add_pow]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hpoly, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Cutoff specialization of the one-integral finite centered-prefix
identity. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure
    (k N : ℕ) (s : ℂ) :
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k s N =
      ∫ t : ℝ,
        (((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ k) *
          Complex.exp (-s * t)
        ∂pairedEtaFiniteLogMeasure N := by
  simpa only [pairedEtaLogLaplaceMomentCutoffCenteredPartialSum,
    pairedEtaLogTailCutoff] using
    pairedEtaLogLaplaceMomentCenteredPartialSum_eq_integral_finiteLogMeasure
      k N s (Real.log (((2 * N + 1 : ℕ) : ℝ)))

/-- The reflected-partner completed finite Gram feature. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      ((((t - pairedEtaLogTailCutoff (N + 1) : ℝ) : ℂ) ^
          (analyticZetaZeroMultiplicity rho - 1)) *
        Complex.exp
          (-(NontrivialZetaZero.conjugatePartner rho).1 * t))

/-- The parity-adjusted conjugate-original completed finite Gram feature. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ((((t - pairedEtaLogTailCutoff (N + 1) : ℝ) : ℂ) ^
            (analyticZetaZeroMultiplicity rho - 1)) *
          Complex.exp (-rho.1 * t)))

/-- The reflected-partner finite feature is integrable. -/
theorem integrable_topPrefixFinitePartnerFeature
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
        rho N)
      (pairedEtaFiniteLogMeasure (N + 1)) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
  exact
    (integrable_centered_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
      (analyticZetaZeroMultiplicity rho - 1) (N + 1)
      (NontrivialZetaZero.conjugatePartner rho).1
      (pairedEtaLogTailCutoff (N + 1))).const_mul _

/-- The parity-adjusted conjugate-original finite feature is integrable. -/
theorem integrable_topPrefixFiniteConjugateFeature
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
        rho N)
      (pairedEtaFiniteLogMeasure (N + 1)) := by
  have hbase :=
    (integrable_centered_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
      (analyticZetaZeroMultiplicity rho - 1) (N + 1) rho.1
      (pairedEtaLogTailCutoff (N + 1))).const_mul
        (pairedEtaXiCompletionFactor rho.1 * rho.1)
  have hconj : Integrable (fun t : ℝ =>
      starRingEnd ℂ
        ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
          ((((t - pairedEtaLogTailCutoff (N + 1) : ℝ) : ℂ) ^
              (analyticZetaZeroMultiplicity rho - 1)) *
            Complex.exp (-rho.1 * t))))
      (pairedEtaFiniteLogMeasure (N + 1)) := by
    apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hbase).congr
    filter_upwards with t
    exact Complex.conjCLE_apply _
  exact hconj.const_mul ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho)

/-- Integrating the partner feature recovers its completed finite term. -/
theorem integral_topPrefixFinitePartnerFeature_eq_finitePartnerTerm
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho N t
        ∂pairedEtaFiniteLogMeasure (N + 1)) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
  rw [integral_const_mul,
    ← pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure]

/-- Integrating the conjugate feature recovers its completed finite term. -/
theorem integral_topPrefixFiniteConjugateFeature_eq_finiteConjugateTerm
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho N t
        ∂pairedEtaFiniteLogMeasure (N + 1)) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
  rw [integral_const_mul, integral_conj, integral_const_mul,
    ← pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure]

/-- The complex reflected-partner rank-one finite Gram kernel. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
      rho N p.1 *
    starRingEnd ℂ
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
        rho N p.2)

/-- The complex conjugate-original rank-one finite Gram kernel. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
      rho N p.1 *
    starRingEnd ℂ
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
        rho N p.2)

/-- The real signed finite energy kernel on two copies of the common positive
eta prefix measure. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
      rho N p -
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
      rho N p).re

private theorem integrable_star_of_integrable
    {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    Integrable (fun t : ℝ => starRingEnd ℂ (f t)) μ := by
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf).congr
  filter_upwards with t
  exact Complex.conjCLE_apply _

/-- The partner finite Gram kernel is integrable on the product measure. -/
theorem integrable_topPrefixFinitePartnerGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
        rho N)
      ((pairedEtaFiniteLogMeasure (N + 1)).prod
        (pairedEtaFiniteLogMeasure (N + 1))) := by
  exact (integrable_topPrefixFinitePartnerFeature rho N).mul_prod
    (integrable_star_of_integrable
      (integrable_topPrefixFinitePartnerFeature rho N))

/-- The conjugate finite Gram kernel is integrable on the product measure. -/
theorem integrable_topPrefixFiniteConjugateGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
        rho N)
      ((pairedEtaFiniteLogMeasure (N + 1)).prod
        (pairedEtaFiniteLogMeasure (N + 1))) := by
  exact (integrable_topPrefixFiniteConjugateFeature rho N).mul_prod
    (integrable_star_of_integrable
      (integrable_topPrefixFiniteConjugateFeature rho N))

/-- The signed real finite energy Gram kernel is integrable. -/
theorem integrable_topPrefixFiniteEnergyGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
        rho N)
      ((pairedEtaFiniteLogMeasure (N + 1)).prod
        (pairedEtaFiniteLogMeasure (N + 1))) := by
  exact ((integrable_topPrefixFinitePartnerGramKernel rho N).sub
    (integrable_topPrefixFiniteConjugateGramKernel rho N)).re

/-- The partner complex Gram integral is its finite term norm square. -/
theorem integral_topPrefixFinitePartnerGramKernel_eq_normSq
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
          rho N p
        ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
          (pairedEtaFiniteLogMeasure (N + 1)))) =
      (Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho N) : ℂ) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
  rw [integral_prod_mul
      (μ := pairedEtaFiniteLogMeasure (N + 1))
      (ν := pairedEtaFiniteLogMeasure (N + 1))
      (fun t : ℝ =>
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho N t)
      (fun t : ℝ => starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho N t)),
    integral_conj,
    integral_topPrefixFinitePartnerFeature_eq_finitePartnerTerm,
    Complex.mul_conj]

/-- The conjugate complex Gram integral is its finite term norm square. -/
theorem integral_topPrefixFiniteConjugateGramKernel_eq_normSq
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
          rho N p
        ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
          (pairedEtaFiniteLogMeasure (N + 1)))) =
      (Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho N) : ℂ) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
  rw [integral_prod_mul
      (μ := pairedEtaFiniteLogMeasure (N + 1))
      (ν := pairedEtaFiniteLogMeasure (N + 1))
      (fun t : ℝ =>
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho N t)
      (fun t : ℝ => starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho N t)),
    integral_conj,
    integral_topPrefixFiniteConjugateFeature_eq_finiteConjugateTerm,
    Complex.mul_conj]

/-- Exact finite positive-measure Gram representation of the signed energy
numerator at the top-prefix summability frontier. -/
theorem integral_topPrefixFiniteEnergyGramKernel_eq_finiteEnergyDifference
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
          rho N p
        ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
          (pairedEtaFiniteLogMeasure (N + 1)))) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N := by
  calc
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
          rho N p
        ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
          (pairedEtaFiniteLogMeasure (N + 1)))) =
        (∫ p : ℝ × ℝ,
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
              rho N p -
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
              rho N p)
          ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
            (pairedEtaFiniteLogMeasure (N + 1)))).re := by
      exact integral_re
        ((integrable_topPrefixFinitePartnerGramKernel rho N).sub
          (integrable_topPrefixFiniteConjugateGramKernel rho N))
    _ = ((∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerGramKernel
            rho N p
          ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
            (pairedEtaFiniteLogMeasure (N + 1)))) -
        ∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateGramKernel
            rho N p
          ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
            (pairedEtaFiniteLogMeasure (N + 1)))).re := by
      rw [integral_sub
        (integrable_topPrefixFinitePartnerGramKernel rho N)
        (integrable_topPrefixFiniteConjugateGramKernel rho N)]
    _ = Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho N) -
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho N) := by
      rw [integral_topPrefixFinitePartnerGramKernel_eq_normSq,
        integral_topPrefixFiniteConjugateGramKernel_eq_normSq]
      norm_num
    _ =
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho N := by
      symm
      exact topPrefixFiniteEnergyDifference_eq_finiteTermNormSq_sub rho N

/-- The normalized finite energy defect is the signed finite Gram integral
divided by the total finite amplitude. -/
theorem
    topPrefixNormalizedFiniteEnergyDefect_eq_integral_finiteEnergyGramKernel_div_total
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N =
      (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
          rho N p
        ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
          (pairedEtaFiniteLogMeasure (N + 1)))) /
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
          rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
  rw [integral_topPrefixFiniteEnergyGramKernel_eq_finiteEnergyDifference]

end

end RiemannGaussian
