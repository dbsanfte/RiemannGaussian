import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteLower
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteGaussianLaplaceGram

/-!
# Finite completed residual for the leading eta moment

The finite lower certificates retain the norm of a complex eta moment prefix.
This module retains the full complex phase and the completed functional-
equation coupling.

First, each finite order-`k` prefix is identified with `(-1)^k` times the
`k`th derivative of the actual finite positive eta Laplace partition.  Thus
the approximation is a derivative of the genuine finite arithmetic model,
not an auxiliary truncation.

At a nontrivial zero, the completed leading prefixes at `rho` and
`1 - conj rho` need not satisfy the exact infinite symmetry.  Their complex
difference is defined as the finite completed partner residual.  Lean proves
that its norm is bounded by the sum of the two explicit support-tail
envelopes, with all completion factors present, and hence tends to zero.

This exposes a phase-sensitive finite arithmetic rigidity target.  The decay
is forced at every actual zero, including a hypothetical off-critical one;
excluding such off-line decay remains open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

open ProbabilityTheory

/-- A finite complex moment prefix is literally the corresponding moment of
the finite positive logarithmic eta measure. -/
theorem pairedEtaLogLaplaceMomentPartialSum_eq_integral_finiteLogMeasure
    (k N : ℕ) (s : ℂ) :
    pairedEtaLogLaplaceMomentPartialSum k s N =
      ∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-s * t)
        ∂pairedEtaFiniteLogMeasure N := by
  unfold pairedEtaLogLaplaceMomentPartialSum
    pairedEtaFiniteLogMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro n hn
    unfold pairedEtaLogLaplaceMomentInterval
    rw [← intervalIntegral.integral_of_le
      (pairedEtaFiniteLogInterval_pos n).le]
  · intro n hn
    change IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ k * Complex.exp (-s * t))
      (Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2)))
    apply IntegrableOn.mono_set
      ((show Continuous (fun t : ℝ ↦
        (t : ℂ) ^ k * Complex.exp (-s * t)) by
          fun_prop).continuousOn.integrableOn_Icc)
    exact Ioc_subset_Icc_self

/-- Every real parameter belongs to the exponential-integrability domain of
negative logarithmic time for a finite eta measure. -/
theorem univ_subset_pairedEtaFinite_negId_integrableExpSet (N : ℕ) :
    (Set.univ : Set ℝ) ⊆
      integrableExpSet (fun t : ℝ ↦ -t) (pairedEtaFiniteLogMeasure N) := by
  intro sigma hsigma
  change Integrable (fun t : ℝ ↦ Real.exp (sigma * -t))
    (pairedEtaFiniteLogMeasure N)
  have h := integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N sigma
  apply h.congr
  filter_upwards with t
  congr 1
  ring

/-- Every complex parameter is an interior exponential-integrability point
for a finite eta measure. -/
theorem pairedEtaFinite_re_mem_interior_negId_integrableExpSet
    (N : ℕ) (s : ℂ) :
    s.re ∈ interior
      (integrableExpSet (fun t : ℝ ↦ -t)
        (pairedEtaFiniteLogMeasure N)) := by
  exact (interior_maximal
    (univ_subset_pairedEtaFinite_negId_integrableExpSet N)
    isOpen_univ) trivial

/-- The finite eta Laplace partition is Mathlib's complex moment-generating
function for negative logarithmic time. -/
theorem pairedEtaFiniteLaplacePartition_eq_complexMGF
    (N : ℕ) (s : ℂ) :
    pairedEtaFiniteLaplacePartition N s =
      complexMGF (fun t : ℝ ↦ -t) (pairedEtaFiniteLogMeasure N) s := by
  rw [pairedEtaFiniteLaplacePartition_eq_integral_logMeasure]
  unfold complexMGF
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  push_cast
  ring_nf

/-- Global function equality between the finite partition and its complex
moment-generating-function realization. -/
theorem pairedEtaFiniteLaplacePartition_eq_complexMGF_fun (N : ℕ) :
    pairedEtaFiniteLaplacePartition N =
      complexMGF (fun t : ℝ ↦ -t) (pairedEtaFiniteLogMeasure N) := by
  funext s
  exact pairedEtaFiniteLaplacePartition_eq_complexMGF N s

/-- Every finite complex moment prefix is the corresponding signed iterated
derivative of the genuine finite eta Laplace partition. -/
theorem iteratedDeriv_pairedEtaFiniteLaplacePartition_eq_logMomentPartialSum
    (k N : ℕ) (s : ℂ) :
    iteratedDeriv k (pairedEtaFiniteLaplacePartition N) s =
      (-1 : ℂ) ^ k * pairedEtaLogLaplaceMomentPartialSum k s N := by
  rw [pairedEtaFiniteLaplacePartition_eq_complexMGF_fun,
    iteratedDeriv_complexMGF
      (pairedEtaFinite_re_mem_interior_negId_integrableExpSet N s) k,
    pairedEtaLogLaplaceMomentPartialSum_eq_integral_finiteLogMeasure]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hpow : (((-t : ℝ) : ℂ) ^ k) =
      (-1 : ℂ) ^ k * (t : ℂ) ^ k := by
    push_cast
    rw [show -(t : ℂ) = (-1 : ℂ) * t by ring_nf, mul_pow]
  rw [hpow]
  simp only [mul_assoc]
  congr 1
  push_cast
  ring_nf

/-- Solving the signed derivative identity expresses each finite moment
prefix directly through the corresponding finite-partition derivative. -/
theorem pairedEtaLogLaplaceMomentPartialSum_eq_iteratedDeriv
    (k N : ℕ) (s : ℂ) :
    pairedEtaLogLaplaceMomentPartialSum k s N =
      (-1 : ℂ) ^ k *
        iteratedDeriv k (pairedEtaFiniteLaplacePartition N) s := by
  rw [iteratedDeriv_pairedEtaFiniteLaplacePartition_eq_logMomentPartialSum]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hsign, one_mul]

/-- The failure of the two finite leading moment prefixes to obey the exact
completed infinite partner symmetry.  This is a fully finite arithmetic
quantity, since each prefix is a derivative of the finite eta partition. -/
def pairedEtaCompletedLeadingLogFinitePartnerResidual
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1 *
      pairedEtaLogLaplaceMomentPartialSum
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 N -
    (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
      starRingEnd ℂ
        (pairedEtaXiCompletionFactor rho.1 * rho.1 *
          pairedEtaLogLaplaceMomentPartialSum
            (analyticZetaZeroMultiplicity rho) rho.1 N)

/-- The explicit sum of the two completion-weighted moment-tail envelopes
controlling the finite partner residual. -/
def pairedEtaCompletedLeadingLogFinitePartnerResidualUpper
    (rho : NontrivialZetaZero) (theta : ℝ) (N : ℕ) : ℝ :=
  pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaLogLaplaceMomentTailUpper
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1.re theta N +
    pairedEtaCompletionSpectralWeight rho *
      pairedEtaLogLaplaceMomentTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re theta N

/-- Exact cancellation of the full completed leading moments rewrites the
finite residual entirely as the two finite-prefix approximation errors. -/
theorem pairedEtaCompletedLeadingLogFinitePartnerResidual_eq_errors
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogFinitePartnerResidual rho N =
      pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (pairedEtaLogLaplaceMomentPartialSum
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1) -
        (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 * rho.1 *
              (pairedEtaLogLaplaceMomentPartialSum
                  (analyticZetaZeroMultiplicity rho) rho.1 N -
                pairedEtaLogLaplaceMoment
                  (analyticZetaZeroMultiplicity rho) rho.1)) := by
  unfold pairedEtaCompletedLeadingLogFinitePartnerResidual
  simp only [mul_sub, map_sub]
  rw [pairedEtaLeadingLogLaplaceMoment_conjugatePartner rho]
  ring

/-- The finite complex completed partner residual is bounded explicitly by
the two arithmetic support tails. -/
theorem norm_pairedEtaCompletedLeadingLogFinitePartnerResidual_le
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogFinitePartnerResidual rho N‖ ≤
      pairedEtaCompletedLeadingLogFinitePartnerResidualUpper
        rho theta N := by
  rw [pairedEtaCompletedLeadingLogFinitePartnerResidual_eq_errors]
  calc
    ‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogLaplaceMomentPartialSum
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1 N -
              pairedEtaLogLaplaceMoment
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1) -
          (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
            starRingEnd ℂ
              (pairedEtaXiCompletionFactor rho.1 * rho.1 *
                (pairedEtaLogLaplaceMomentPartialSum
                    (analyticZetaZeroMultiplicity rho) rho.1 N -
                  pairedEtaLogLaplaceMoment
                    (analyticZetaZeroMultiplicity rho) rho.1))‖ ≤
        ‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogLaplaceMomentPartialSum
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1 N -
              pairedEtaLogLaplaceMoment
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1)‖ +
          ‖(-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
            starRingEnd ℂ
              (pairedEtaXiCompletionFactor rho.1 * rho.1 *
                (pairedEtaLogLaplaceMomentPartialSum
                    (analyticZetaZeroMultiplicity rho) rho.1 N -
                  pairedEtaLogLaplaceMoment
                    (analyticZetaZeroMultiplicity rho) rho.1))‖ :=
      norm_sub_le _ _
    _ = pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          ‖pairedEtaLogLaplaceMomentPartialSum
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1‖ +
        pairedEtaCompletionSpectralWeight rho *
          ‖pairedEtaLogLaplaceMomentPartialSum
              (analyticZetaZeroMultiplicity rho) rho.1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho) rho.1‖ := by
      simp only [pairedEtaCompletionSpectralWeight, norm_mul, norm_pow,
        norm_neg, norm_one, one_pow, one_mul, norm_conj]
    _ ≤ pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaLogLaplaceMomentTailUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1.re theta N +
        pairedEtaCompletionSpectralWeight rho *
          pairedEtaLogLaplaceMomentTailUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re theta N := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.zero_lt_re
              (NontrivialZetaZero.conjugatePartner rho))
            htheta hthetaOne N)
          (pairedEtaCompletionSpectralWeight_pos
            (NontrivialZetaZero.conjugatePartner rho)).le
      · exact mul_le_mul_of_nonneg_left
          (norm_pairedEtaLogLaplaceMomentPartialSum_sub_le_tailUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.zero_lt_re rho) htheta hthetaOne N)
          (pairedEtaCompletionSpectralWeight_pos rho).le
    _ = pairedEtaCompletedLeadingLogFinitePartnerResidualUpper
        rho theta N := rfl

/-- The residual upper envelope is strictly positive for every admissible
split. -/
theorem pairedEtaCompletedLeadingLogFinitePartnerResidualUpper_pos
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (N : ℕ) :
    0 < pairedEtaCompletedLeadingLogFinitePartnerResidualUpper
      rho theta N := by
  unfold pairedEtaCompletedLeadingLogFinitePartnerResidualUpper
  have hpartnerTail := pairedEtaLogLaplaceMomentTailUpper_pos
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re
      (NontrivialZetaZero.conjugatePartner rho)) htheta N
  have hrhoTail := pairedEtaLogLaplaceMomentTailUpper_pos
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) htheta N
  exact add_pos
    (mul_pos (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho)) hpartnerTail)
    (mul_pos (pairedEtaCompletionSpectralWeight_pos rho) hrhoTail)

/-- The explicit completion-weighted two-tail envelope tends to zero. -/
theorem tendsto_pairedEtaCompletedLeadingLogFinitePartnerResidualUpper_zero
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogFinitePartnerResidualUpper
        rho theta N) atTop (nhds 0) := by
  have hpartnerTail := tendsto_pairedEtaLogLaplaceMomentTailUpper_zero
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re
      (NontrivialZetaZero.conjugatePartner rho))
    htheta hthetaOne
  have hrhoTail := tendsto_pairedEtaLogLaplaceMomentTailUpper_zero
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) htheta hthetaOne
  have hpartnerWeight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho)) atTop
      (nhds (pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho))) :=
    tendsto_const_nhds
  have hrhoWeight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight rho) atTop
      (nhds (pairedEtaCompletionSpectralWeight rho)) :=
    tendsto_const_nhds
  simpa only [pairedEtaCompletedLeadingLogFinitePartnerResidualUpper,
    mul_zero, add_zero] using
    (hpartnerWeight.mul hpartnerTail).add (hrhoWeight.mul hrhoTail)

/-- The full complex finite completed partner residual tends to zero with the
explicit two-tail envelope.  This retains phase, parity, and conjugation. -/
theorem tendsto_pairedEtaCompletedLeadingLogFinitePartnerResidual_zero
    (rho : NontrivialZetaZero) {theta : ℝ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogFinitePartnerResidual rho N)
      atTop (nhds 0) := by
  exact squeeze_zero_norm
    (fun N ↦ norm_pairedEtaCompletedLeadingLogFinitePartnerResidual_le
      rho htheta hthetaOne N)
    (tendsto_pairedEtaCompletedLeadingLogFinitePartnerResidualUpper_zero
      rho htheta hthetaOne)

end

end RiemannGaussian
