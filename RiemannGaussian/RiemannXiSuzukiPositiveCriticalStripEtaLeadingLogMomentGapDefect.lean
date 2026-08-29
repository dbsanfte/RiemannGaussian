import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMoments
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapArithmetic
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# The first paired-eta arithmetic gap moment defect

The positive logarithmic half-line is the disjoint union of the paired-eta
support and its omitted arithmetic gaps. This module differentiates that
measure decomposition to every order and computes the complete half-line
moment exactly:

`integral_0^∞ t^n exp(-s t) dt = n! / s^(n+1)` for `Re(s) > 0`.

At a nontrivial zeta zero of genuine multiplicity `m`, the support moments
vanish for all `k < m`. Hence the gap moment equals the elementary full
half-line moment at exactly those orders up through `m`, and differs for the
first time at `m`. The completed partner symmetry is then rewritten as an
exact relation between these first nonzero gap-moment defects at `rho` and
`1-conj(rho)`.

This identifies a concrete arithmetic quantity on explicit gap intervals
whose independent comparison could force horizontal rigidity. The checked
identities do not supply that comparison and do not imply RH.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

open ProbabilityTheory

/-- The `n`th logarithmic-time moment on the omitted paired-eta gaps. -/
def pairedEtaLogGapMoment (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) ^ n * Complex.exp (-s * t) ∂pairedEtaLogGapMeasure

/-- The `n`th logarithmic-time moment on the complete positive half-line. -/
def positiveHalfLineLogLaplaceMoment (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) ^ n * Complex.exp (-s * t)
    ∂volume.restrict (Ioi 0)

/-- The positive real half-line lies in the full exponential-integrability
domain for negative time. -/
theorem Ioi_zero_subset_full_negId_integrableExpSet :
    Ioi 0 ⊆ integrableExpSet (fun t : ℝ ↦ -t)
      (volume.restrict (Ioi 0)) := by
  intro sigma hsigma
  change Integrable (fun t : ℝ ↦ Real.exp (sigma * -t))
    (volume.restrict (Ioi 0))
  have hcomplex :=
    integrableOn_cexp_neg_sigma_add_I_mul_Ioi_zero hsigma 0
  have hnorm := hcomplex.norm
  apply hnorm.congr
  filter_upwards with t
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re]

/-- A positive real part is interior to the full half-line exponential
domain. -/
theorem full_re_mem_interior_negId_integrableExpSet
    {s : ℂ} (hs : 0 < s.re) :
    s.re ∈ interior (integrableExpSet (fun t : ℝ ↦ -t)
      (volume.restrict (Ioi 0))) := by
  exact (interior_maximal Ioi_zero_subset_full_negId_integrableExpSet
    isOpen_Ioi) hs

/-- The full positive-half-line complex MGF is the reciprocal function in
the positive half-plane. -/
theorem full_negId_complexMGF_eq_inv
    {s : ℂ} (hs : 0 < s.re) :
    complexMGF (fun t : ℝ ↦ -t) (volume.restrict (Ioi 0)) s = s⁻¹ := by
  calc
    complexMGF (fun t : ℝ ↦ -t) (volume.restrict (Ioi 0)) s =
        ∫ t : ℝ in Ioi 0, Complex.exp (-s * t) := by
      unfold complexMGF
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      push_cast
      ring_nf
    _ = s⁻¹ := by
      simpa only [Complex.re_add_im] using
        (integral_cexp_neg_sigma_add_I_mul_Ioi_zero hs s.im)

/-- Locally in the positive half-plane, the full complex MGF is the
reciprocal function. -/
theorem full_negId_complexMGF_eventuallyEq_inv
    {s : ℂ} (hs : 0 < s.re) :
    complexMGF (fun t : ℝ ↦ -t) (volume.restrict (Ioi 0)) =ᶠ[nhds s]
      fun w : ℂ ↦ w⁻¹ := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.eventually_mem hs] with w hw
  exact full_negId_complexMGF_eq_inv hw

/-- All full positive-half-line logarithmic moments are integrable after a
positive complex tilt. -/
theorem integrable_positiveHalfLineLogLaplaceMoment
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ n * Complex.exp (-s * t))
      (volume.restrict (Ioi 0)) := by
  have h := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := fun t : ℝ ↦ -t) (n := n)
    (full_re_mem_interior_negId_integrableExpSet hs)
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

/-- The iterated derivative of reciprocal has its exact factorial form away
from the origin. -/
theorem iteratedDeriv_inv_eq_factorial
    (n : ℕ) {s : ℂ} (hs0 : s ≠ 0) :
    iteratedDeriv n (fun w : ℂ ↦ w⁻¹) s =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) *
        (s ^ (n + 1))⁻¹ := by
  let U : Set ℂ := {0}ᶜ
  have hUopen : IsOpen U := isOpen_compl_singleton
  have hsU : s ∈ U := by simpa [U]
  have h := iteratedDerivWithin_one_div (s := U) n hUopen hsU
  rw [iteratedDerivWithin_of_isOpen hUopen hsU] at h
  simpa only [one_div, show (-1 - (n : ℤ)) = Int.negSucc n by omega,
    zpow_negSucc] using h

/-- The complete positive-half-line moment has the elementary factorial
value `n! / s^(n+1)`. -/
theorem positiveHalfLineLogLaplaceMoment_eq_factorial
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    positiveHalfLineLogLaplaceMoment n s =
      (n.factorial : ℂ) * (s ^ (n + 1))⁻¹ := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  have hmgf := iteratedDeriv_complexMGF
    (full_re_mem_interior_negId_integrableExpSet hs) n
  have hinv := iteratedDeriv_inv_eq_factorial n hs0
  have hlocal := (full_negId_complexMGF_eventuallyEq_inv hs).iteratedDeriv_eq n
  rw [hmgf, hinv] at hlocal
  unfold positiveHalfLineLogLaplaceMoment
  have hmom :
      (∫ t : ℝ in Ioi 0,
          ((-t : ℝ) : ℂ) ^ n * Complex.exp (s * ((-t : ℝ) : ℂ))) =
        (-1 : ℂ) ^ n *
          ∫ t : ℝ in Ioi 0,
            (t : ℂ) ^ n * Complex.exp (-s * t) := by
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
  rw [hmom] at hlocal
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0))
    (by simpa only [mul_assoc] using hlocal)

/-- Gap moments inherit integrability from the complete positive half-line. -/
theorem integrable_pairedEtaLogGapMoment
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ n * Complex.exp (-s * t))
      pairedEtaLogGapMeasure := by
  exact Integrable.mono_measure
    (integrable_positiveHalfLineLogLaplaceMoment n hs)
    pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero

/-- Every full positive-half-line moment splits exactly into its eta-support
and omitted-gap moments. -/
theorem positiveHalfLineLogLaplaceMoment_eq_support_add_gap
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    positiveHalfLineLogLaplaceMoment n s =
      pairedEtaLogLaplaceMoment n s + pairedEtaLogGapMoment n s := by
  have hsupport := integrable_pairedEtaLogLaplaceMoment n hs
  have hgap := integrable_pairedEtaLogGapMoment n hs
  unfold positiveHalfLineLogLaplaceMoment pairedEtaLogLaplaceMoment
    pairedEtaLogGapMoment
  rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure,
    integral_add_measure hsupport hgap]

/-- The eta-support moment plus its gap moment is the elementary full
half-line factorial moment. -/
theorem pairedEtaLogLaplaceMoment_add_gap_eq_factorial
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    pairedEtaLogLaplaceMoment n s + pairedEtaLogGapMoment n s =
      (n.factorial : ℂ) * (s ^ (n + 1))⁻¹ := by
  rw [← positiveHalfLineLogLaplaceMoment_eq_support_add_gap n hs,
    positiveHalfLineLogLaplaceMoment_eq_factorial n hs]

/-- Equivalently, the support moment is the exact defect of the arithmetic
gap moment from the elementary full-half-line value. -/
theorem pairedEtaLogLaplaceMoment_eq_factorial_sub_gap
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    pairedEtaLogLaplaceMoment n s =
      (n.factorial : ℂ) * (s ^ (n + 1))⁻¹ -
        pairedEtaLogGapMoment n s := by
  have h := pairedEtaLogLaplaceMoment_add_gap_eq_factorial n hs
  exact eq_sub_of_add_eq h

/-- At a zero, every support moment below the exact multiplicity vanishes. -/
theorem pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    pairedEtaLogLaplaceMoment k rho.1 = 0 := by
  have hderiv :=
    iteratedDeriv_pairedEtaLaplacePartition_eq_zero_of_lt_multiplicity
      rho hk
  rw [iteratedDeriv_pairedEtaLaplacePartition_eq_logMoment k
    (NontrivialZetaZero.zero_lt_re rho)] at hderiv
  exact (mul_eq_zero.mp hderiv).resolve_left
    (pow_ne_zero k (by norm_num))

/-- At a zero of multiplicity `m`, the arithmetic gap moments agree with the
full half-line moments at every order strictly below `m`. -/
theorem pairedEtaLogGapMoment_eq_factorial_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    pairedEtaLogGapMoment k rho.1 =
      (k.factorial : ℂ) * (rho.1 ^ (k + 1))⁻¹ := by
  have hsplit := pairedEtaLogLaplaceMoment_add_gap_eq_factorial k
    (NontrivialZetaZero.zero_lt_re rho)
  rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho hk,
    zero_add] at hsplit
  exact hsplit

/-- The first arithmetic gap moment that can differ from the full half-line
moment is exactly the genuine zeta-zero multiplicity, and it does differ. -/
theorem pairedEtaLogGapMoment_multiplicity_ne_factorial
    (rho : NontrivialZetaZero) :
    pairedEtaLogGapMoment (analyticZetaZeroMultiplicity rho) rho.1 ≠
      ((analyticZetaZeroMultiplicity rho).factorial : ℂ) *
        (rho.1 ^ (analyticZetaZeroMultiplicity rho + 1))⁻¹ := by
  intro hgap
  have hsplit := pairedEtaLogLaplaceMoment_add_gap_eq_factorial
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)
  rw [hgap] at hsplit
  have hsupport :
      pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho) rho.1 = 0 := by
    exact add_eq_right.mp hsplit
  exact pairedEtaLogLaplaceMoment_multiplicity_ne_zero rho hsupport

/-- Up through the genuine multiplicity, equality of a gap moment with the
full half-line moment holds exactly below the first nonzero order. -/
theorem pairedEtaLogGapMoment_eq_factorial_iff_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k ≤ analyticZetaZeroMultiplicity rho) :
    pairedEtaLogGapMoment k rho.1 =
        (k.factorial : ℂ) * (rho.1 ^ (k + 1))⁻¹ ↔
      k < analyticZetaZeroMultiplicity rho := by
  constructor
  · intro heq
    by_contra hnlt
    have hkm : k = analyticZetaZeroMultiplicity rho := by omega
    subst k
    exact pairedEtaLogGapMoment_multiplicity_ne_factorial rho heq
  · exact pairedEtaLogGapMoment_eq_factorial_of_lt_multiplicity rho

/-- The completed partner identity is an exact relation between the first
nonzero deviations of the explicit arithmetic gap moments from their
elementary full-half-line values. -/
theorem pairedEtaLeadingLogGapMomentDefect_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
        (NontrivialZetaZero.conjugatePartner rho).1 *
        (((analyticZetaZeroMultiplicity rho).factorial : ℂ) *
            ((NontrivialZetaZero.conjugatePartner rho).1 ^
              (analyticZetaZeroMultiplicity rho + 1))⁻¹ -
          pairedEtaLogGapMoment (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1) =
      (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            (((analyticZetaZeroMultiplicity rho).factorial : ℂ) *
                (rho.1 ^ (analyticZetaZeroMultiplicity rho + 1))⁻¹ -
              pairedEtaLogGapMoment (analyticZetaZeroMultiplicity rho)
                rho.1)) := by
  rw [← pairedEtaLogLaplaceMoment_eq_factorial_sub_gap
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)),
    ← pairedEtaLogLaplaceMoment_eq_factorial_sub_gap
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)]
  exact pairedEtaLeadingLogLaplaceMoment_conjugatePartner rho

end

end RiemannGaussian
