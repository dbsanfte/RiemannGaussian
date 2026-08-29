import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletedSymmetry
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Explicit leading logarithmic-time moments for completed paired eta

The fixed positive paired-eta logarithmic measure has finite moments of every
order after every positive exponential tilt. This module places its entire
positive half-plane inside Mathlib's complex moment-generating-function
domain and obtains the exact formula

`L⁽ⁿ⁾(s) = (-1)ⁿ ∫ tⁿ exp(-s t) dμ(t)`

for the genuine infinite eta Laplace partition `L`.

At a nontrivial zeta zero, division by the nonzero spectral parameter
preserves the full analytic multiplicity. Consequently every lower moment
vanishes in the required Leibniz calculation, and the first nonzero paired
eta derivative is exactly the spectral parameter times its leading moment.
The completed functional equation then becomes an explicit complementary
identity between these arithmetic moments at arbitrary zero multiplicity.

This removes the remaining derivative abstraction from the completed local
coupling. The identity is still compatible with off-critical zeros; the open
RH input is an independent arithmetic inequality for the two complementary
moments.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

open ProbabilityTheory

/-- The `n`th unsigned logarithmic-time moment of the paired-eta Laplace
kernel. -/
def pairedEtaLogLaplaceMoment (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) ^ n * Complex.exp (-s * t) ∂pairedEtaLogMeasure

/-- Every positive real parameter belongs to the exponential-integrability
domain of negative logarithmic time. -/
theorem Ioi_zero_subset_pairedEta_negId_integrableExpSet :
    Ioi 0 ⊆ integrableExpSet (fun t : ℝ ↦ -t) pairedEtaLogMeasure := by
  intro sigma hsigma
  change Integrable (fun t : ℝ ↦ Real.exp (sigma * -t))
    pairedEtaLogMeasure
  have h := integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  apply h.congr
  filter_upwards with t
  simp only [zero_mul, Real.cos_zero, mul_one]
  congr 1
  ring_nf

/-- A positive real part is an interior point of the exponential-integrability
domain, as required for holomorphic differentiation under the integral. -/
theorem pairedEta_re_mem_interior_negId_integrableExpSet
    {s : ℂ} (hs : 0 < s.re) :
    s.re ∈ interior
      (integrableExpSet (fun t : ℝ ↦ -t) pairedEtaLogMeasure) := by
  exact (interior_maximal
    Ioi_zero_subset_pairedEta_negId_integrableExpSet isOpen_Ioi) hs

/-- The existing infinite eta Laplace partition is exactly Mathlib's complex
moment-generating function for negative logarithmic time. -/
theorem pairedEtaLaplacePartition_eq_complexMGF
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaLaplacePartition s =
      complexMGF (fun t : ℝ ↦ -t) pairedEtaLogMeasure s := by
  rw [← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hs]
  unfold complexMGF
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  push_cast
  ring_nf

/-- The eta Laplace partition and the complex moment-generating function agree
on a neighborhood of every positive-half-plane point. -/
theorem pairedEtaLaplacePartition_eventuallyEq_complexMGF
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaLaplacePartition =ᶠ[nhds s]
      complexMGF (fun t : ℝ ↦ -t) pairedEtaLogMeasure := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.eventually_mem hs] with w hw
  exact pairedEtaLaplacePartition_eq_complexMGF hw

/-- Every unsigned logarithmic-time moment is genuinely integrable after a
positive complex exponential tilt. -/
theorem integrable_pairedEtaLogLaplaceMoment
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦
      (t : ℂ) ^ n * Complex.exp (-s * t)) pairedEtaLogMeasure := by
  have h := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := fun t : ℝ ↦ -t) (n := n)
    (pairedEta_re_mem_interior_negId_integrableExpSet hs)
  have hscaled := h.const_mul ((-1 : ℂ) ^ n)
  apply hscaled.congr
  filter_upwards with t
  have hpow : (((-t : ℝ) : ℂ) ^ n) =
      (-1 : ℂ) ^ n * (t : ℂ) ^ n := by
    push_cast
    rw [show -(t : ℂ) = (-1 : ℂ) * t by ring_nf, mul_pow]
  rw [hpow]
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℂ) ^ n *
          ((-1 : ℂ) ^ n * (t : ℂ) ^ n *
            Complex.exp (s * ((-t : ℝ) : ℂ))) =
        ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          ((t : ℂ) ^ n * Complex.exp (s * ((-t : ℝ) : ℂ))) := by
      ring_nf
    _ = (t : ℂ) ^ n * Complex.exp (-s * t) := by
      rw [hsign, one_mul]
      congr 1
      push_cast
      ring_nf

/-- Every iterated derivative of the infinite eta Laplace partition is its
explicit signed logarithmic-time moment. -/
theorem iteratedDeriv_pairedEtaLaplacePartition_eq_logMoment
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv n pairedEtaLaplacePartition s =
      (-1 : ℂ) ^ n * pairedEtaLogLaplaceMoment n s := by
  rw [(pairedEtaLaplacePartition_eventuallyEq_complexMGF hs).iteratedDeriv_eq n,
    iteratedDeriv_complexMGF
      (pairedEta_re_mem_interior_negId_integrableExpSet hs) n]
  unfold pairedEtaLogLaplaceMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hpow : (((-t : ℝ) : ℂ) ^ n) =
      (-1 : ℂ) ^ n * (t : ℂ) ^ n := by
    push_cast
    rw [show -(t : ℂ) = (-1 : ℂ) * t by ring_nf, mul_pow]
  rw [hpow]
  simp only [mul_assoc]
  congr 1
  push_cast
  ring_nf

/-- The infinite eta Laplace partition is analytic throughout the open
positive half-plane. -/
theorem analyticAt_pairedEtaLaplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ pairedEtaLaplacePartition s := by
  exact (analyticAt_complexMGF
    (pairedEta_re_mem_interior_negId_integrableExpSet hs)).congr
      (pairedEtaLaplacePartition_eventuallyEq_complexMGF hs).symm

/-- Locally in the positive half-plane, paired eta is the identity function
times its positive-measure Laplace partition. -/
theorem pairedEtaCore_eventuallyEq_id_mul_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore =ᶠ[nhds s] id * pairedEtaLaplacePartition := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.eventually_mem hs] with w hw
  simpa using pairedEtaCore_eq_mul_laplacePartition hw

/-- Dividing paired eta by its nonzero spectral parameter preserves the
exact analytic order at every nontrivial zero. -/
theorem analyticOrderAt_pairedEtaLaplacePartition_eq_multiplicity
    (rho : NontrivialZetaZero) :
    analyticOrderAt pairedEtaLaplacePartition rho.1 =
      (analyticZetaZeroMultiplicity rho : ℕ∞) := by
  have hrho : rho.1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [NontrivialZetaZero.zero_lt_re rho]
  have hidOrder : analyticOrderAt (id : ℂ → ℂ) rho.1 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hrho)
  have hpartition : AnalyticAt ℂ pairedEtaLaplacePartition rho.1 :=
    analyticAt_pairedEtaLaplacePartition
      (NontrivialZetaZero.zero_lt_re rho)
  have hproduct := analyticOrderAt_mul analyticAt_id hpartition
  have hlocal := analyticOrderAt_congr
    (pairedEtaCore_eventuallyEq_id_mul_laplacePartition
      (NontrivialZetaZero.zero_lt_re rho))
  calc
    analyticOrderAt pairedEtaLaplacePartition rho.1 =
        0 + analyticOrderAt pairedEtaLaplacePartition rho.1 := by simp
    _ = analyticOrderAt ((id : ℂ → ℂ) * pairedEtaLaplacePartition)
          rho.1 := by rw [hproduct, hidOrder]
    _ = analyticOrderAt pairedEtaCore rho.1 := hlocal.symm
    _ = (analyticZetaZeroMultiplicity rho : ℕ∞) :=
      analyticOrderAt_pairedEtaCore_eq_multiplicity rho

/-- Every Laplace-partition derivative below the exact zeta-zero
multiplicity vanishes. -/
theorem iteratedDeriv_pairedEtaLaplacePartition_eq_zero_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    iteratedDeriv k pairedEtaLaplacePartition rho.1 = 0 := by
  have hanalytic : AnalyticAt ℂ pairedEtaLaplacePartition rho.1 :=
    analyticAt_pairedEtaLaplacePartition
      (NontrivialZetaZero.zero_lt_re rho)
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanalytic).mp
    (analyticOrderAt_pairedEtaLaplacePartition_eq_multiplicity rho)).1 k hk

/-- The first nonzero paired-eta derivative is the spectral parameter times
the exact logarithmic-time moment of the same order. -/
theorem iteratedDeriv_pairedEtaCore_multiplicity_eq_logMoment
    (rho : NontrivialZetaZero) :
    iteratedDeriv (analyticZetaZeroMultiplicity rho) pairedEtaCore rho.1 =
      rho.1 * (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho) rho.1 := by
  classical
  let m := analyticZetaZeroMultiplicity rho
  have hmpos : 0 < m := analyticZetaZeroMultiplicity_positive rho
  have hid : ContDiffAt ℂ (m : ℕ∞) (id : ℂ → ℂ) rho.1 :=
    analyticAt_id.contDiffAt
  have hpartition : ContDiffAt ℂ (m : ℕ∞)
      pairedEtaLaplacePartition rho.1 :=
    (analyticAt_pairedEtaLaplacePartition
      (NontrivialZetaZero.zero_lt_re rho)).contDiffAt
  rw [(pairedEtaCore_eventuallyEq_id_mul_laplacePartition
    (NontrivialZetaZero.zero_lt_re rho)).iteratedDeriv_eq m]
  rw [iteratedDeriv_mul hid hpartition, Finset.sum_eq_single 0]
  · simp [m, iteratedDeriv_pairedEtaLaplacePartition_eq_logMoment,
      NontrivialZetaZero.zero_lt_re, mul_assoc]
  · intro i hi hi0
    have hirange : i < m + 1 := Finset.mem_range.mp hi
    have hsub : m - i < m := by omega
    rw [iteratedDeriv_pairedEtaLaplacePartition_eq_zero_of_lt_multiplicity
      rho hsub]
    simp
  · simp

/-- The leading logarithmic-time moment at a nontrivial zero cannot vanish. -/
theorem pairedEtaLogLaplaceMoment_multiplicity_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho) rho.1 ≠ 0 := by
  intro hzero
  apply iteratedDeriv_pairedEtaCore_multiplicity_ne_zero rho
  rw [iteratedDeriv_pairedEtaCore_multiplicity_eq_logMoment rho, hzero,
    mul_zero]

/-- The completion-coupled local symmetry is an explicit relation between
the first nonzero logarithmic-time moments at complementary zeros. -/
theorem pairedEtaLeadingLogLaplaceMoment_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
        (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 =
      (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho)
              rho.1) := by
  let m := analyticZetaZeroMultiplicity rho
  have hpartner :=
    iteratedDeriv_pairedEtaCore_multiplicity_eq_logMoment
      (NontrivialZetaZero.conjugatePartner rho)
  have hrho := iteratedDeriv_pairedEtaCore_multiplicity_eq_logMoment rho
  have hsym := pairedEtaLeadingDerivative_conjugatePartner rho
  simp only [analyticZetaZeroMultiplicity_conjugatePartner] at hpartner
  rw [hpartner, hrho] at hsym
  change _ = (-1 : ℂ) ^ m * starRingEnd ℂ _
  change _ = _ at hsym
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hsym' :
      (-1 : ℂ) ^ m *
          (pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            pairedEtaLogLaplaceMoment m
              (NontrivialZetaZero.conjugatePartner rho).1) =
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            pairedEtaLogLaplaceMoment m rho.1) := by
    calc
      (-1 : ℂ) ^ m *
            (pairedEtaXiCompletionFactor
              (NontrivialZetaZero.conjugatePartner rho).1 *
              (NontrivialZetaZero.conjugatePartner rho).1 *
              pairedEtaLogLaplaceMoment m
                (NontrivialZetaZero.conjugatePartner rho).1) =
          pairedEtaXiCompletionFactor
              (NontrivialZetaZero.conjugatePartner rho).1 *
            ((NontrivialZetaZero.conjugatePartner rho).1 *
              (-1 : ℂ) ^ m *
              pairedEtaLogLaplaceMoment m
                (NontrivialZetaZero.conjugatePartner rho).1) := by ring_nf
      _ = (-1 : ℂ) ^ m *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 *
              (rho.1 * (-1 : ℂ) ^ m *
                pairedEtaLogLaplaceMoment m rho.1)) := hsym
      _ = starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            pairedEtaLogLaplaceMoment m rho.1) := by
        simp only [map_mul, map_pow, map_neg, map_one]
        calc
          (-1 : ℂ) ^ m *
                (starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1) *
                  (starRingEnd ℂ rho.1 * (-1 : ℂ) ^ m *
                    starRingEnd ℂ (pairedEtaLogLaplaceMoment m rho.1))) =
              ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) *
                (starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1) *
                  starRingEnd ℂ rho.1 *
                  starRingEnd ℂ (pairedEtaLogLaplaceMoment m rho.1)) := by ring_nf
          _ = _ := by rw [hsign, one_mul]
  calc
    pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1 *
          pairedEtaLogLaplaceMoment m
            (NontrivialZetaZero.conjugatePartner rho).1 =
        (-1 : ℂ) ^ m *
          ((-1 : ℂ) ^ m *
            (pairedEtaXiCompletionFactor
              (NontrivialZetaZero.conjugatePartner rho).1 *
              (NontrivialZetaZero.conjugatePartner rho).1 *
              pairedEtaLogLaplaceMoment m
                (NontrivialZetaZero.conjugatePartner rho).1)) := by
      rw [← mul_assoc, hsign, one_mul]
    _ = (-1 : ℂ) ^ m *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            pairedEtaLogLaplaceMoment m rho.1) := by rw [hsym']

/-- The completion- and spectral-parameter-weighted magnitudes of the
leading logarithmic-time moments agree at complementary zeros. -/
theorem norm_pairedEtaLeadingLogLaplaceMoment_conjugatePartner
    (rho : NontrivialZetaZero) :
    ‖pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1‖ *
        ‖(NontrivialZetaZero.conjugatePartner rho).1‖ *
        ‖pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1‖ =
      ‖pairedEtaXiCompletionFactor rho.1‖ * ‖rho.1‖ *
        ‖pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho)
          rho.1‖ := by
  have hnorm := congrArg norm
    (pairedEtaLeadingLogLaplaceMoment_conjugatePartner rho)
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_conj] using hnorm

end

end RiemannGaussian
