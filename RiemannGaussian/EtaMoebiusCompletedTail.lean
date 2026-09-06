import RiemannGaussian.EtaMoebiusFinitePrefix

/-!
# An exact multiplicative constraint on the actual completed eta zero tails

The finite Möbius identity is transported to the original completed eta
moments. At every actual nontrivial zero their zeroth prefixes are the
negative genuine tails. The resulting signed complex aggregate equals
one nonzero completion-weighted dyadic source at every cutoff at least
two. All odd endpoint corrections and divided cutoffs remain explicit.

This is a linear arithmetic constraint across different prefixes. It
does not bound the original quadratic current's weighted absolute moment.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The zeroth actual completed moment is exactly the completion factor
times the original finite paired eta polynomial. -/
theorem pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaFiniteCompletedMoment rho N 0 = pairedEtaXiCompletionFactor rho.1 * pairedEtaCorePartialSum N rho.1 := by
  unfold pairedEtaFiniteCompletedMoment
  rw [pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure]
  simp only [pow_zero, one_mul]
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition, pairedEtaFiniteLaplacePartition_eq_integral_logMeasure]
  ring

/-- Below the actual multiplicity, every completed finite prefix is
the negative completed genuine tail at that same cutoff. -/
theorem pairedEtaFiniteCompletedMoment_eq_neg_tail (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaFiniteCompletedMoment rho N k = -pairedEtaCompletedMomentTail rho N k := by
  have h := pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity rho hk N
  unfold pairedEtaFiniteCompletedMoment pairedEtaCompletedMomentTail
  rw [h]
  ring

/-- The original completion factor multiplies the retained odd last
Dirichlet term at each divided integer endpoint. -/
def pairedEtaCompletedOddEndpoint (rho : NontrivialZetaZero) (M : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 * (if Odd M then (M : ℂ) ^ (-rho.1) else 0)

/-- The nonzero source left by finite Möbius inversion, with the
original xi completion retained. -/
def pairedEtaCompletedMoebiusSource (rho : NontrivialZetaZero) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 * (1 - 2 * (2 : ℂ) ^ (-rho.1))

/-- The source cannot vanish at an actual nontrivial zero: both the
completion and dyadic factors are nonzero throughout the open strip. -/
theorem pairedEtaCompletedMoebiusSource_ne_zero (rho : NontrivialZetaZero) :
    pairedEtaCompletedMoebiusSource rho ≠ 0 :=
  mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho))
    (pairedEtaFactor_ne_zero_of_re_lt_one (NontrivialZetaZero.re_lt_one rho))

/-- Finite Möbius inversion constrains the actual completed prefixes
jointly, retaining every odd endpoint term and every complex divisor weight. -/
theorem sum_moebius_mul_pairedEtaFiniteCompletedMoment_add_endpoint (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
      (pairedEtaFiniteCompletedMoment rho ((M / d) / 2) 0 + pairedEtaCompletedOddEndpoint rho (M / d))) =
        pairedEtaCompletedMoebiusSource rho := by
  have h := congrArg (fun z : ℂ ↦ pairedEtaXiCompletionFactor rho.1 * z)
    (sum_moebius_mul_pairedEtaCorePartialSum_add_endpoint rho.1 hM)
  rw [Finset.mul_sum] at h
  calc
    _ = ∑ d ∈ Finset.Icc 1 M, pairedEtaXiCompletionFactor rho.1 *
        ((μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
          (pairedEtaCorePartialSum ((M / d) / 2) rho.1 +
            if Odd (M / d) then ((M / d : ℕ) : ℂ) ^ (-rho.1) else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix]
      unfold pairedEtaCompletedOddEndpoint
      ring
    _ = _ := h

/-- The signed Möbius-weighted aggregate of the genuine completed eta
zero tails, including their exact unpaired endpoint corrections. -/
def pairedEtaCompletedMoebiusTailAggregate (rho : NontrivialZetaZero) (M : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
    (-pairedEtaCompletedMomentTail rho ((M / d) / 2) 0 + pairedEtaCompletedOddEndpoint rho (M / d))

/-- At every actual zero and every integer cutoff at least two, the
original completed tails satisfy this exact nonzero finite arithmetic
constraint. No infinite sum rearrangement or Möbius cancellation estimate
is assumed. -/
theorem pairedEtaCompletedMoebiusTailAggregate_eq_source (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) :
    pairedEtaCompletedMoebiusTailAggregate rho M = pairedEtaCompletedMoebiusSource rho := by
  have h := sum_moebius_mul_pairedEtaFiniteCompletedMoment_add_endpoint rho hM
  simpa only [pairedEtaCompletedMoebiusTailAggregate,
    pairedEtaFiniteCompletedMoment_eq_neg_tail rho (analyticZetaZeroMultiplicity_positive rho)] using h

/-- The full signed tail aggregate is nonzero at every eligible cutoff. -/
theorem pairedEtaCompletedMoebiusTailAggregate_ne_zero (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) : pairedEtaCompletedMoebiusTailAggregate rho M ≠ 0 := by
  rw [pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM]
  exact pairedEtaCompletedMoebiusSource_ne_zero rho

/-- Downstream of its exact complex identity, the entire Möbius tail
aggregate has a cutoff-independent norm. This is a bound for the signed
linear aggregate, not the original current's first absolute moment. -/
theorem norm_pairedEtaCompletedMoebiusTailAggregate (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) :
    ‖pairedEtaCompletedMoebiusTailAggregate rho M‖ = ‖pairedEtaCompletedMoebiusSource rho‖ := by
  rw [pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM]

end

end RiemannGaussian
