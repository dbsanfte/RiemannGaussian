import RiemannGaussian.EtaEnergyLeadingFlux

/-!
# Literal kernels for the isolated leading eta energy current

The preceding module proves that only one degree-one current remains at the
critical first-moment frontier. This module expands that current completely,
without assuming that zeta zeros are simple.

When the analytic multiplicity is one, the current pairs the newly exposed
eta head interval with the successor finite prefix. When the multiplicity is
at least two, it pairs the immediately lower centered moment with the top
centered moment on the same successor prefix measure, multiplied by the one
cutoff-shift factor. Both branches are represented by genuine integrable real
kernels on products of finite positive measures.

A single multiplicity-selected scalar integral equals the isolated leading
flux at every cutoff. Its critical first absolute moment is therefore
summable exactly on the critical line, and the universal statement is
RH-equivalent. This is an exact symmetry-aware representation of the open
current, not the missing cancellation estimate.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completed reflected-partner centered term immediately below the top energy order. -/
def pairedEtaTopPrefixFinitePartnerLowerArithmeticTerm (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho - 2)
        (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)

/-- The parity-adjusted conjugate-original centered term immediately below the top energy order. -/
def pairedEtaTopPrefixFiniteConjugateLowerArithmeticTerm (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho - 2) rho.1 (N + 1))

/-- The degree-one cutoff shift times the signed Hermitian pairing of the lower and top successor moments. -/
def pairedEtaTopPrefixFiniteEnergyAdjacentMomentFlux (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
      pairedEtaLogTailShiftIncrement (N + 1)) *
    ((pairedEtaTopPrefixFinitePartnerLowerArithmeticTerm rho (N + 1) *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho (N + 1))).re -
      (pairedEtaTopPrefixFiniteConjugateLowerArithmeticTerm rho (N + 1) *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho (N + 1))).re)

/-- At analytic multiplicity at least two, the isolated leading flux is exactly the adjacent-moment flux. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_adjacentMomentFlux_of_two_le_multiplicity (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      pairedEtaTopPrefixFiniteEnergyAdjacentMomentFlux rho N := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticZetaZeroMultiplicity rho = k + 2 := by
    use analyticZetaZeroMultiplicity rho - 2
    omega
  unfold pairedEtaTopPrefixFiniteEnergyLeadingFlux
    pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement
    pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement
    pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading
    pairedEtaTopPrefixFiniteEnergyAdjacentMomentFlux pairedEtaTopPrefixFinitePartnerLowerArithmeticTerm pairedEtaTopPrefixFiniteConjugateLowerArithmeticTerm
  simp [hk, Nat.add_comm]
  ring

/-- The completed negative new-head increment in the reflected-partner component. -/
def pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      (-pairedEtaLogLaplaceMomentCutoffCenteredHead 0
        (NontrivialZetaZero.conjugatePartner rho).1 (N + 1))

/-- The parity-adjusted conjugate-original negative new-head increment. -/
def pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        (-pairedEtaLogLaplaceMomentCutoffCenteredHead 0 rho.1 (N + 1)))

/-- The signed Hermitian flux pairing the two completed new-head increments with their successor top terms. -/
def pairedEtaTopPrefixFiniteEnergyHeadFlux (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 *
    ((pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho (N + 1))).re -
      (pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho (N + 1))).re)

/-- At analytic multiplicity one, the isolated leading flux is exactly the new-head flux. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_headFlux_of_multiplicity_eq_one (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      pairedEtaTopPrefixFiniteEnergyHeadFlux rho N := by
  unfold pairedEtaTopPrefixFiniteEnergyLeadingFlux
    pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement
    pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement
    pairedEtaLogLaplaceMomentCutoffCenteredFiniteWorkLeading
    pairedEtaTopPrefixFiniteEnergyHeadFlux pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement
  simp [hm]

/-- Every isolated leading flux lies in exactly the relevant head or adjacent-moment branch allowed by positive analytic multiplicity. -/
theorem topPrefixFiniteEnergyLeadingFlux_multiplicity_dichotomy (rho : NontrivialZetaZero) (N : ℕ) :
    (analyticZetaZeroMultiplicity rho = 1 ∧
      pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N = pairedEtaTopPrefixFiniteEnergyHeadFlux rho N) ∨
    (2 ≤ analyticZetaZeroMultiplicity rho ∧
      pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N = pairedEtaTopPrefixFiniteEnergyAdjacentMomentFlux rho N) := by
  have hmpos := analyticZetaZeroMultiplicity_positive rho
  have hmone : 1 ≤ analyticZetaZeroMultiplicity rho := by omega
  rcases eq_or_lt_of_le hmone with hm | hm
  · exact Or.inl ⟨hm.symm, topPrefixFiniteEnergyLeadingFlux_eq_headFlux_of_multiplicity_eq_one rho hm.symm N⟩
  · exact Or.inr ⟨hm, topPrefixFiniteEnergyLeadingFlux_eq_adjacentMomentFlux_of_two_le_multiplicity rho hm N⟩

/-- The reflected-partner lower centered-moment feature on the finite positive eta measure. -/
def pairedEtaTopPrefixFinitePartnerLowerFeature
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      ((((t - pairedEtaLogTailCutoff (N + 1) : ℝ) : ℂ) ^
          (analyticZetaZeroMultiplicity rho - 2)) *
        Complex.exp (-(NontrivialZetaZero.conjugatePartner rho).1 * t))

/-- The parity-adjusted conjugate-original lower centered-moment feature on the finite positive eta measure. -/
def pairedEtaTopPrefixFiniteConjugateLowerFeature
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ((((t - pairedEtaLogTailCutoff (N + 1) : ℝ) : ℂ) ^
            (analyticZetaZeroMultiplicity rho - 2)) *
          Complex.exp (-rho.1 * t)))

/-- The reflected-partner lower feature is integrable on its finite eta prefix measure. -/
theorem integrable_topPrefixFinitePartnerLowerFeature
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFinitePartnerLowerFeature rho N)
      (pairedEtaFiniteLogMeasure (N + 1)) := by
  unfold pairedEtaTopPrefixFinitePartnerLowerFeature
  exact
    (integrable_centered_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
      (analyticZetaZeroMultiplicity rho - 2) (N + 1)
      (NontrivialZetaZero.conjugatePartner rho).1
      (pairedEtaLogTailCutoff (N + 1))).const_mul _

/-- The conjugate-original lower feature is integrable on its finite eta prefix measure. -/
theorem integrable_topPrefixFiniteConjugateLowerFeature
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteConjugateLowerFeature rho N)
      (pairedEtaFiniteLogMeasure (N + 1)) := by
  have hbase :=
    (integrable_centered_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
      (analyticZetaZeroMultiplicity rho - 2) (N + 1) rho.1
      (pairedEtaLogTailCutoff (N + 1))).const_mul
        (pairedEtaXiCompletionFactor rho.1 * rho.1)
  have hconj : Integrable (fun t : ℝ =>
      starRingEnd ℂ
        ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
          ((((t - pairedEtaLogTailCutoff (N + 1) : ℝ) : ℂ) ^
              (analyticZetaZeroMultiplicity rho - 2)) *
            Complex.exp (-rho.1 * t))))
      (pairedEtaFiniteLogMeasure (N + 1)) := by
    apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hbase).congr
    filter_upwards with t
    exact Complex.conjCLE_apply _
  exact hconj.const_mul ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho)

/-- Integrating the reflected-partner lower feature recovers its completed lower arithmetic term. -/
theorem integral_topPrefixFinitePartnerLowerFeature_eq_lowerTerm (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ, pairedEtaTopPrefixFinitePartnerLowerFeature rho N t
      ∂pairedEtaFiniteLogMeasure (N + 1)) =
      pairedEtaTopPrefixFinitePartnerLowerArithmeticTerm rho N := by
  unfold pairedEtaTopPrefixFinitePartnerLowerFeature pairedEtaTopPrefixFinitePartnerLowerArithmeticTerm
  rw [integral_const_mul,
    ← pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure]

/-- Integrating the conjugate-original lower feature recovers its completed lower arithmetic term. -/
theorem integral_topPrefixFiniteConjugateLowerFeature_eq_lowerTerm (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ, pairedEtaTopPrefixFiniteConjugateLowerFeature rho N t
      ∂pairedEtaFiniteLogMeasure (N + 1)) =
      pairedEtaTopPrefixFiniteConjugateLowerArithmeticTerm rho N := by
  unfold pairedEtaTopPrefixFiniteConjugateLowerFeature pairedEtaTopPrefixFiniteConjugateLowerArithmeticTerm
  rw [integral_const_mul, integral_conj, integral_const_mul,
    ← pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure]

private theorem integrable_star_of_integrable_leadingFluxKernel {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) :
    Integrable (fun t : ℝ => starRingEnd ℂ (f t)) μ := by
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf).congr
  filter_upwards with t
  exact Complex.conjCLE_apply _

/-- The real product kernel for the degree-one adjacent lower--top moment current. -/
def pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel
    (rho : NontrivialZetaZero) (N : ℕ) (z : ℝ × ℝ) : ℝ :=
  2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
      pairedEtaLogTailShiftIncrement (N + 1)) *
    ((pairedEtaTopPrefixFinitePartnerLowerFeature rho (N + 1) z.1 *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
            rho (N + 1) z.2) -
      pairedEtaTopPrefixFiniteConjugateLowerFeature rho (N + 1) z.1 *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
            rho (N + 1) z.2)).re)

/-- The adjacent-moment current kernel is integrable on two copies of the successor finite eta measure. -/
theorem integrable_topPrefixFiniteEnergyAdjacentMomentKernel (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel rho N)
      ((pairedEtaFiniteLogMeasure (N + 2)).prod
        (pairedEtaFiniteLogMeasure (N + 2))) := by
  have hp := (integrable_topPrefixFinitePartnerLowerFeature rho (N + 1)).mul_prod
    (integrable_star_of_integrable_leadingFluxKernel (integrable_topPrefixFinitePartnerFeature rho (N + 1)))
  have hq := (integrable_topPrefixFiniteConjugateLowerFeature rho (N + 1)).mul_prod
    (integrable_star_of_integrable_leadingFluxKernel (integrable_topPrefixFiniteConjugateFeature rho (N + 1)))
  exact (hp.sub hq).re.const_mul _

/-- The adjacent-moment product-kernel integral is exactly the adjacent-moment flux. -/
theorem integral_topPrefixFiniteEnergyAdjacentMomentKernel_eq_adjacentMomentFlux (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ z : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel rho N z
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
        (pairedEtaFiniteLogMeasure (N + 2)))) =
      pairedEtaTopPrefixFiniteEnergyAdjacentMomentFlux rho N := by
  let μ := pairedEtaFiniteLogMeasure (N + 2)
  let pf := pairedEtaTopPrefixFinitePartnerLowerFeature rho (N + 1)
  let pg :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
      rho (N + 1)
  let qf := pairedEtaTopPrefixFiniteConjugateLowerFeature rho (N + 1)
  let qg :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
      rho (N + 1)
  have hpf : Integrable pf μ := integrable_topPrefixFinitePartnerLowerFeature rho (N + 1)
  have hpg : Integrable pg μ := integrable_topPrefixFinitePartnerFeature rho (N + 1)
  have hqf : Integrable qf μ := integrable_topPrefixFiniteConjugateLowerFeature rho (N + 1)
  have hqg : Integrable qg μ := integrable_topPrefixFiniteConjugateFeature rho (N + 1)
  have hcomplex : Integrable (fun z : ℝ × ℝ =>
      pf z.1 * starRingEnd ℂ (pg z.2) -
        qf z.1 * starRingEnd ℂ (qg z.2)) (μ.prod μ) :=
    (hpf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hpg)).sub
      (hqf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hqg))
  have hpProd :
      (∫ z : ℝ × ℝ, pf z.1 * starRingEnd ℂ (pg z.2) ∂μ.prod μ) =
        (∫ t : ℝ, pf t ∂μ) * starRingEnd ℂ (∫ t : ℝ, pg t ∂μ) := by
    rw [integral_prod_mul (μ := μ) (ν := μ) pf
      (fun t : ℝ => starRingEnd ℂ (pg t)), integral_conj]
  have hqProd :
      (∫ z : ℝ × ℝ, qf z.1 * starRingEnd ℂ (qg z.2) ∂μ.prod μ) =
        (∫ t : ℝ, qf t ∂μ) * starRingEnd ℂ (∫ t : ℝ, qg t ∂μ) := by
    rw [integral_prod_mul (μ := μ) (ν := μ) qf
      (fun t : ℝ => starRingEnd ℂ (qg t)), integral_conj]
  unfold pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel
  rw [integral_const_mul]
  congr 1
  calc
    (∫ z : ℝ × ℝ,
        (pf z.1 * starRingEnd ℂ (pg z.2) -
          qf z.1 * starRingEnd ℂ (qg z.2)).re ∂μ.prod μ) =
        (∫ z : ℝ × ℝ,
          (pf z.1 * starRingEnd ℂ (pg z.2) -
            qf z.1 * starRingEnd ℂ (qg z.2)) ∂μ.prod μ).re :=
      integral_re hcomplex
    _ = ((∫ z : ℝ × ℝ, pf z.1 * starRingEnd ℂ (pg z.2) ∂μ.prod μ) -
          ∫ z : ℝ × ℝ, qf z.1 * starRingEnd ℂ (qg z.2) ∂μ.prod μ).re := by
      rw [integral_sub
        (hpf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hpg))
        (hqf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hqg))]
    _ = ((∫ t : ℝ, pf t ∂μ) * starRingEnd ℂ (∫ t : ℝ, pg t ∂μ) -
          (∫ t : ℝ, qf t ∂μ) * starRingEnd ℂ (∫ t : ℝ, qg t ∂μ)).re := by
      rw [hpProd, hqProd]
    _ = ((pairedEtaTopPrefixFinitePartnerLowerArithmeticTerm rho (N + 1) *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1))) -
        (pairedEtaTopPrefixFiniteConjugateLowerArithmeticTerm rho (N + 1) *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1)))).re := by
      rw [integral_topPrefixFinitePartnerLowerFeature_eq_lowerTerm, integral_topPrefixFiniteConjugateLowerFeature_eq_lowerTerm,
        integral_topPrefixFinitePartnerFeature_eq_finitePartnerTerm,
        integral_topPrefixFiniteConjugateFeature_eq_finiteConjugateTerm]

/-- The completed reflected-partner negative-head feature on the translated new support interval. -/
def pairedEtaTopPrefixFinitePartnerHeadFeature
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      ((-Complex.exp
          (-(NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogTailCutoff (N + 1) : ℂ))) *
        Complex.exp (-(NontrivialZetaZero.conjugatePartner rho).1 * u))

/-- The parity-adjusted conjugate-original negative-head feature on the translated new support interval. -/
def pairedEtaTopPrefixFiniteConjugateHeadFeature
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ((-Complex.exp
            (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ))) *
          Complex.exp (-rho.1 * u)))

/-- The reflected-partner negative-head feature is integrable on the translated head measure. -/
theorem integrable_topPrefixFinitePartnerHeadFeature
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFinitePartnerHeadFeature rho N)
      (pairedEtaShiftedLogHeadMeasure (N + 1)) := by
  have hbase :=
    integrable_pairedEtaShiftedLogHeadLaplaceMoment_integrand 0
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)) (N + 1)
  have hscaled :=
    (hbase.const_mul
      (-Complex.exp
        (-(NontrivialZetaZero.conjugatePartner rho).1 *
          (pairedEtaLogTailCutoff (N + 1) : ℂ)))).const_mul
      (pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
        (NontrivialZetaZero.conjugatePartner rho).1)
  apply hscaled.congr
  filter_upwards with u
  unfold pairedEtaTopPrefixFinitePartnerHeadFeature
  simp only [pow_zero, one_mul]

/-- The conjugate-original negative-head feature is integrable on the translated head measure. -/
theorem integrable_topPrefixFiniteConjugateHeadFeature
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteConjugateHeadFeature rho N)
      (pairedEtaShiftedLogHeadMeasure (N + 1)) := by
  have hbase :=
    integrable_pairedEtaShiftedLogHeadLaplaceMoment_integrand 0
      (NontrivialZetaZero.zero_lt_re rho) (N + 1)
  have hscaled :=
    (hbase.const_mul
      (-Complex.exp
        (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ)))).const_mul
      (pairedEtaXiCompletionFactor rho.1 * rho.1)
  have hconj : Integrable (fun u : ℝ =>
      starRingEnd ℂ
        ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
          ((-Complex.exp
              (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ))) *
            Complex.exp (-rho.1 * u))))
      (pairedEtaShiftedLogHeadMeasure (N + 1)) := by
    apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hscaled).congr
    filter_upwards with u
    simp only [pow_zero, one_mul]
    exact Complex.conjCLE_apply _
  apply (hconj.const_mul
    ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho)).congr
  filter_upwards with u
  unfold pairedEtaTopPrefixFiniteConjugateHeadFeature
  ring

/-- Integrating the reflected-partner head feature recovers the completed head increment. -/
theorem integral_topPrefixFinitePartnerHeadFeature_eq_headIncrement
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ u : ℝ, pairedEtaTopPrefixFinitePartnerHeadFeature rho N u
      ∂pairedEtaShiftedLogHeadMeasure (N + 1)) =
      pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement rho N := by
  unfold pairedEtaTopPrefixFinitePartnerHeadFeature pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement
    pairedEtaLogLaplaceMomentCutoffCenteredHead
    pairedEtaShiftedLogHeadLaplaceMoment
  rw [integral_const_mul]
  have hconst :
      (∫ u : ℝ,
        (-Complex.exp
          (-(NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogTailCutoff (N + 1) : ℂ))) *
          Complex.exp (-(NontrivialZetaZero.conjugatePartner rho).1 * u)
        ∂pairedEtaShiftedLogHeadMeasure (N + 1)) =
      -Complex.exp
          (-(NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
        ∫ u : ℝ, Complex.exp
          (-(NontrivialZetaZero.conjugatePartner rho).1 * u)
          ∂pairedEtaShiftedLogHeadMeasure (N + 1) := by
    rw [integral_const_mul]
  rw [hconst]
  simp only [pow_zero, one_mul]
  rw [neg_mul]

/-- Integrating the conjugate-original head feature recovers the completed head increment. -/
theorem integral_topPrefixFiniteConjugateHeadFeature_eq_headIncrement
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ u : ℝ, pairedEtaTopPrefixFiniteConjugateHeadFeature rho N u
      ∂pairedEtaShiftedLogHeadMeasure (N + 1)) =
      pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement rho N := by
  unfold pairedEtaTopPrefixFiniteConjugateHeadFeature pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement
    pairedEtaLogLaplaceMomentCutoffCenteredHead
    pairedEtaShiftedLogHeadLaplaceMoment
  rw [integral_const_mul, integral_conj, integral_const_mul]
  have hconst :
      (∫ u : ℝ,
        (-Complex.exp
          (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ))) *
          Complex.exp (-rho.1 * u)
        ∂pairedEtaShiftedLogHeadMeasure (N + 1)) =
      -Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
        ∫ u : ℝ, Complex.exp (-rho.1 * u)
          ∂pairedEtaShiftedLogHeadMeasure (N + 1) := by
    rw [integral_const_mul]
  rw [hconst]
  simp only [pow_zero, one_mul]
  rw [neg_mul]

/-- The real product kernel coupling the translated new head with the successor finite eta feature. -/
def pairedEtaTopPrefixFiniteEnergyHeadKernel
    (rho : NontrivialZetaZero) (N : ℕ) (z : ℝ × ℝ) : ℝ :=
  2 *
    ((pairedEtaTopPrefixFinitePartnerHeadFeature rho N z.1 *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
            rho (N + 1) z.2) -
      pairedEtaTopPrefixFiniteConjugateHeadFeature rho N z.1 *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
            rho (N + 1) z.2)).re)

/-- The head-current kernel is integrable on the head measure times the successor prefix measure. -/
theorem integrable_topPrefixFiniteEnergyHeadKernel (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N)
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod
        (pairedEtaFiniteLogMeasure (N + 2))) := by
  rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  have hpHead : Integrable (pairedEtaTopPrefixFinitePartnerHeadFeature rho N)
      (volume.restrict (Ioc 0 (pairedEtaShiftedLogHeadWidth (N + 1)))) := by
    simpa only [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] using
      integrable_topPrefixFinitePartnerHeadFeature rho N
  have hqHead : Integrable (pairedEtaTopPrefixFiniteConjugateHeadFeature rho N)
      (volume.restrict (Ioc 0 (pairedEtaShiftedLogHeadWidth (N + 1)))) := by
    simpa only [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] using
      integrable_topPrefixFiniteConjugateHeadFeature rho N
  have hp := hpHead.mul_prod
    (integrable_star_of_integrable_leadingFluxKernel (integrable_topPrefixFinitePartnerFeature rho (N + 1)))
  have hq := hqHead.mul_prod
    (integrable_star_of_integrable_leadingFluxKernel (integrable_topPrefixFiniteConjugateFeature rho (N + 1)))
  exact (hp.sub hq).re.const_mul 2

/-- The head-current product-kernel integral is exactly the head flux. -/
theorem integral_topPrefixFiniteEnergyHeadKernel_eq_headFlux (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ z : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod
        (pairedEtaFiniteLogMeasure (N + 2)))) =
      pairedEtaTopPrefixFiniteEnergyHeadFlux rho N := by
  rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  let μ := volume.restrict (Ioc 0 (pairedEtaShiftedLogHeadWidth (N + 1)))
  let ν := pairedEtaFiniteLogMeasure (N + 2)
  let pf := pairedEtaTopPrefixFinitePartnerHeadFeature rho N
  let pg :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
      rho (N + 1)
  let qf := pairedEtaTopPrefixFiniteConjugateHeadFeature rho N
  let qg :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
      rho (N + 1)
  have hpf : Integrable pf μ := by
    simpa only [pf, μ, pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] using
      integrable_topPrefixFinitePartnerHeadFeature rho N
  have hpg : Integrable pg ν := integrable_topPrefixFinitePartnerFeature rho (N + 1)
  have hqf : Integrable qf μ := by
    simpa only [qf, μ, pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] using
      integrable_topPrefixFiniteConjugateHeadFeature rho N
  have hqg : Integrable qg ν := integrable_topPrefixFiniteConjugateFeature rho (N + 1)
  have hcomplex : Integrable (fun z : ℝ × ℝ =>
      pf z.1 * starRingEnd ℂ (pg z.2) -
        qf z.1 * starRingEnd ℂ (qg z.2)) (μ.prod ν) :=
    (hpf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hpg)).sub
      (hqf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hqg))
  have hpProd :
      (∫ z : ℝ × ℝ, pf z.1 * starRingEnd ℂ (pg z.2) ∂μ.prod ν) =
        (∫ u : ℝ, pf u ∂μ) * starRingEnd ℂ (∫ t : ℝ, pg t ∂ν) := by
    rw [integral_prod_mul (μ := μ) (ν := ν) pf
      (fun t : ℝ => starRingEnd ℂ (pg t)), integral_conj]
  have hqProd :
      (∫ z : ℝ × ℝ, qf z.1 * starRingEnd ℂ (qg z.2) ∂μ.prod ν) =
        (∫ u : ℝ, qf u ∂μ) * starRingEnd ℂ (∫ t : ℝ, qg t ∂ν) := by
    rw [integral_prod_mul (μ := μ) (ν := ν) qf
      (fun t : ℝ => starRingEnd ℂ (qg t)), integral_conj]
  have hpfInt : (∫ u : ℝ, pf u ∂μ) = pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement rho N := by
    have h := integral_topPrefixFinitePartnerHeadFeature_eq_headIncrement rho N
    rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] at h
    simpa only [pf, μ] using h
  have hqfInt : (∫ u : ℝ, qf u ∂μ) = pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement rho N := by
    have h := integral_topPrefixFiniteConjugateHeadFeature_eq_headIncrement rho N
    rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] at h
    simpa only [qf, μ] using h
  have hpgInt : (∫ t : ℝ, pg t ∂ν) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
        rho (N + 1) := by
    simpa only [pg, ν] using
      integral_topPrefixFinitePartnerFeature_eq_finitePartnerTerm rho (N + 1)
  have hqgInt : (∫ t : ℝ, qg t ∂ν) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
        rho (N + 1) := by
    simpa only [qg, ν] using
      integral_topPrefixFiniteConjugateFeature_eq_finiteConjugateTerm rho (N + 1)
  unfold pairedEtaTopPrefixFiniteEnergyHeadKernel
  rw [integral_const_mul]
  congr 1
  calc
    (∫ z : ℝ × ℝ,
        (pf z.1 * starRingEnd ℂ (pg z.2) -
          qf z.1 * starRingEnd ℂ (qg z.2)).re ∂μ.prod ν) =
        (∫ z : ℝ × ℝ,
          (pf z.1 * starRingEnd ℂ (pg z.2) -
            qf z.1 * starRingEnd ℂ (qg z.2)) ∂μ.prod ν).re :=
      integral_re hcomplex
    _ = ((∫ z : ℝ × ℝ, pf z.1 * starRingEnd ℂ (pg z.2) ∂μ.prod ν) -
          ∫ z : ℝ × ℝ, qf z.1 * starRingEnd ℂ (qg z.2) ∂μ.prod ν).re := by
      rw [integral_sub
        (hpf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hpg))
        (hqf.mul_prod (integrable_star_of_integrable_leadingFluxKernel hqg))]
    _ = ((∫ u : ℝ, pf u ∂μ) * starRingEnd ℂ (∫ t : ℝ, pg t ∂ν) -
          (∫ u : ℝ, qf u ∂μ) * starRingEnd ℂ (∫ t : ℝ, qg t ∂ν)).re := by
      rw [hpProd, hqProd]
    _ = ((pairedEtaTopPrefixFinitePartnerHeadArithmeticIncrement rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1))) -
        (pairedEtaTopPrefixFiniteConjugateHeadArithmeticIncrement rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1)))).re := by
      rw [hpfInt, hqfInt, hpgInt, hqgInt]

/-- At multiplicity one, the isolated leading flux is the literal head-current kernel integral. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      ∫ z : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z
        ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod
          (pairedEtaFiniteLogMeasure (N + 2))) := by
  rw [topPrefixFiniteEnergyLeadingFlux_eq_headFlux_of_multiplicity_eq_one rho hm N, integral_topPrefixFiniteEnergyHeadKernel_eq_headFlux]

/-- At multiplicity at least two, the isolated leading flux is the literal adjacent-moment kernel integral. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_integral_adjacentMomentKernel_of_two_le_multiplicity (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      ∫ z : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel rho N z
        ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
          (pairedEtaFiniteLogMeasure (N + 2))) := by
  rw [topPrefixFiniteEnergyLeadingFlux_eq_adjacentMomentFlux_of_two_le_multiplicity rho hm N, integral_topPrefixFiniteEnergyAdjacentMomentKernel_eq_adjacentMomentFlux]

/-- The exhaustive leading-current kernel integral, selecting the head branch at multiplicity one and the adjacent-moment branch otherwise. -/
def pairedEtaTopPrefixFiniteEnergyLeadingKernelIntegral (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ z : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod
        (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ z : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel rho N z
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
        (pairedEtaFiniteLogMeasure (N + 2)))

/-- The multiplicity-selected kernel integral equals the isolated leading flux at every zero and cutoff. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_leadingKernelIntegral (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      pairedEtaTopPrefixFiniteEnergyLeadingKernelIntegral rho N := by
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaTopPrefixFiniteEnergyLeadingKernelIntegral, if_pos hm]
    exact topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one rho hm N
  · rw [pairedEtaTopPrefixFiniteEnergyLeadingKernelIntegral, if_neg hm]
    apply topPrefixFiniteEnergyLeadingFlux_eq_integral_adjacentMomentKernel_of_two_le_multiplicity rho
    have hmpos := analyticZetaZeroMultiplicity_positive rho
    omega

/-- The critical first absolute moment of the literal selected leading-current kernel integrals is finite exactly on the critical line. -/
theorem summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingKernelIntegral_iff_re_eq_half (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingKernelIntegral rho N|) ↔
      rho.1.re = 1 / 2 := by
  simpa only [← topPrefixFiniteEnergyLeadingFlux_eq_leadingKernelIntegral] using
    summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyLeadingFlux_iff_re_eq_half
      rho

/-- Universal critical first-moment summability of the literal multiplicity-selected leading-current kernel integrals. -/
def AllPairedEtaTopPrefixFiniteEnergyLeadingKernelIntegralFirstMomentSummable : Prop :=
  ∀ rho : NontrivialZetaZero,
    Summable (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingKernelIntegral rho N|)

/-- RH is equivalent to universal critical first-moment summability of the literal selected leading-current kernel integrals. -/
theorem riemannHypothesis_iff_all_topPrefixFiniteEnergyLeadingKernelIntegral_firstMoment_summable :
    RiemannHypothesis ↔ AllPairedEtaTopPrefixFiniteEnergyLeadingKernelIntegralFirstMomentSummable := by
  rw [riemannHypothesis_iff_all_topPrefixFiniteEnergyLeadingFlux_firstMoment_summable]
  constructor
  · intro h rho
    simpa only [← topPrefixFiniteEnergyLeadingFlux_eq_leadingKernelIntegral] using h rho
  · intro h rho
    simpa only [topPrefixFiniteEnergyLeadingFlux_eq_leadingKernelIntegral] using h rho

end

end RiemannGaussian
