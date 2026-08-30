import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredShiftedHierarchy
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapEulerAsymptotic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Sharp normalized asymptotics of centered eta tails

The exact Euler second-difference estimate shows that the ordinary paired-eta
core tail is one half of its odd endpoint power, up to an error one endpoint
power smaller.  Here that estimate is promoted from a pointwise zeroth-order
statement to all centered logarithmic moments.

After multiplication by the complex odd endpoint power, the support-tail
Laplace partition converges locally uniformly on `Re s > 0` to `1 / (2*s)`.
Every member of the sequence is holomorphic there.  The locally uniform
derivative theorem therefore transports the limit through every iterated
derivative.  Identifying those derivatives with the shifted positive-measure
moments gives the sharp limit

`(2N+1)^s * T_k(N,s) -> k! / (2*s^(k+1))`,

where `T_k(N,s)` is the literal cutoff-centered eta tail.  In particular the
leading constant is nonzero throughout the positive half-plane.  This is the
asymptotic input needed to distinguish the two complementary rates inside the
completed centered residual; it is not by itself a zero-location theorem.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

open ProbabilityTheory

/-- The eta core tail normalized by the complex power of its first omitted
odd endpoint. -/
def pairedEtaCoreNormalizedTail (N : ℕ) (s : ℂ) : ℂ :=
  ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ s *
    (pairedEtaCore s - pairedEtaCorePartialSum N s)

/-- The normalized support tail and normalized gap error add to one exactly. -/
theorem pairedEtaCoreNormalizedTail_eq_one_add_gapNormalizedFiniteError
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCoreNormalizedTail N s =
      1 + pairedEtaGapNormalizedFiniteError N s := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hcancel : (x : ℂ) ^ s * (x : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hxne, add_neg_cancel, Complex.cpow_zero]
  have hfinite := pairedEtaCorePartialSum_add_gapCorePartialSum N s
  have hcomplete := pairedEtaGapCore_eq_one_sub_pairedEtaCore hs
  unfold pairedEtaCoreNormalizedTail pairedEtaGapNormalizedFiniteError
  change (x : ℂ) ^ s *
      (pairedEtaCore s - pairedEtaCorePartialSum N s) =
    1 + (x : ℂ) ^ s *
      (pairedEtaGapCorePartialSum N s - pairedEtaGapCore s)
  rw [hcomplete]
  have hendpoint :
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) = (x : ℂ) ^ (-s) := by
    rfl
  nth_rewrite 1 [← hcancel]
  rw [hendpoint] at hfinite
  have hfinite' : pairedEtaCorePartialSum N s +
      pairedEtaGapCorePartialSum N s + (x : ℂ) ^ (-s) = 1 := by
    rw [hfinite]
    ring
  have hpartial : pairedEtaCorePartialSum N s =
      1 - pairedEtaGapCorePartialSum N s - (x : ℂ) ^ (-s) := by
    rw [← hfinite']
    ring
  rw [hpartial]
  ring

/-- Uniform pointwise error bound for the normalized eta support tail. -/
theorem norm_pairedEtaCoreNormalizedTail_sub_half_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaCoreNormalizedTail N s - 1 / 2‖ ≤
      ‖s‖ * ‖s + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  rw [pairedEtaCoreNormalizedTail_eq_one_add_gapNormalizedFiniteError hs]
  have hgap := norm_pairedEtaGapNormalizedFiniteError_add_half_le hs N
  convert hgap using 1
  ring_nf

/-- The normalized eta support tails converge locally uniformly to `1/2` on
the complete positive half-plane. -/
theorem tendstoLocallyUniformlyOn_pairedEtaCoreNormalizedTail_half :
    TendstoLocallyUniformlyOn pairedEtaCoreNormalizedTail
      (fun _ : ℂ => 1 / 2) atTop {s : ℂ | 0 < s.re} := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (Complex.isOpen_re_gt 0)).mpr ?_
  intro K hKU hK
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hinv : Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) atTop (nhds 0) := by
    simpa using
      (tendsto_pairedEtaOddEndpoint_rpow_zero
        (s := (1 : ℂ)) (by norm_num))
  have hscaled : Tendsto (fun N : ℕ =>
      (R * (R + 1)) * (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul (R * (R + 1)) hinv
  filter_upwards [(tendsto_order.1 hscaled).2 epsilon hepsilon] with N hN
  intro s hsK
  have hspos : 0 < s.re := hKU hsK
  have hsR : ‖s‖ ≤ R := hR s hsK
  have hsone : ‖s + 1‖ ≤ R + 1 := by
    calc
      ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ R + 1 := by simpa using add_le_add_right hsR 1
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖pairedEtaCoreNormalizedTail N s - (fun _ : ℂ => 1 / 2) s‖ ≤
        ‖s‖ * ‖s + 1‖ *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) :=
      norm_pairedEtaCoreNormalizedTail_sub_half_le hspos N
    _ ≤ (R * (R + 1)) *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
      have hcoeff : ‖s‖ * ‖s + 1‖ ≤ R * (R + 1) :=
        mul_le_mul hsR hsone (norm_nonneg _) hRpos.le
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by positivity) _)
    _ < epsilon := hN

/-- A constant-in-index family converges locally uniformly to the same
function. -/
private theorem tendstoLocallyUniformlyOn_constIndex
    {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {φ : Filter ι} {S : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ι => g) g φ S := by
  intro u hu x hx
  exact ⟨S, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

/-- The normalized core tail divided by the spectral parameter. -/
def pairedEtaCoreNormalizedLaplaceTail (N : ℕ) (s : ℂ) : ℂ :=
  pairedEtaCoreNormalizedTail N s / s

/-- The normalized support-tail Laplace partitions converge locally uniformly
to the half-density transform `1/(2*s)`. -/
theorem tendstoLocallyUniformlyOn_pairedEtaCoreNormalizedLaplaceTail :
    TendstoLocallyUniformlyOn pairedEtaCoreNormalizedLaplaceTail
      (fun s : ℂ => (1 / 2) / s) atTop {s : ℂ | 0 < s.re} := by
  have hid : TendstoLocallyUniformlyOn
      (fun _ : ℕ => id) id atTop {s : ℂ | 0 < s.re} :=
    tendstoLocallyUniformlyOn_constIndex id
  have hdiv :=
    tendstoLocallyUniformlyOn_pairedEtaCoreNormalizedTail_half.div₀ hid
      (by fun_prop) continuousOn_id (by
        intro s hs hzero
        change s = 0 at hzero
        rw [hzero] at hs
        norm_num at hs)
  change TendstoLocallyUniformlyOn
    (fun N s => pairedEtaCoreNormalizedTail N s / s)
    (fun s : ℂ => (1 / 2) / s) atTop {s : ℂ | 0 < s.re}
  exact hdiv

/-- The normalized core-tail Laplace partition is exactly the zeroth moment
of the translated eta tail measure. -/
theorem pairedEtaCoreNormalizedLaplaceTail_eq_shiftedLogTailLaplaceMoment_zero
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCoreNormalizedLaplaceTail N s =
      pairedEtaShiftedLogTailLaplaceMoment 0 s N := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hcutoff : pairedEtaLogTailCutoff N = Real.log x := by
    rfl
  have hpow :
      Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) =
        (x : ℂ) ^ (-s) := by
    rw [hcutoff]
    rw [Complex.cpow_def_of_ne_zero hxne,
      ← Complex.ofReal_log hx.le]
    congr 1
    ring
  have hcancel : (x : ℂ) ^ s * (x : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hxne, add_neg_cancel, Complex.cpow_zero]
  have hcore := pairedEtaCore_sub_partialSum_eq_mul_tailIntegral hs N
  have hfactor :=
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted 0 s N
  have hfactor' :
      (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N) =
        Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
          pairedEtaShiftedLogTailLaplaceMoment 0 s N := by
    simpa only [pairedEtaLogLaplaceMomentCutoffCenteredTail,
      pow_zero, one_mul] using hfactor
  unfold pairedEtaCoreNormalizedLaplaceTail pairedEtaCoreNormalizedTail
  change (x : ℂ) ^ s *
      (pairedEtaCore s - pairedEtaCorePartialSum N s) / s = _
  rw [hcore]
  have hdivcancel : (x : ℂ) ^ s *
      (s * ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N) / s =
        (x : ℂ) ^ s *
          (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N) := by
    field_simp [hsne]
  rw [hdivcancel]
  rw [hfactor', hpow]
  rw [← mul_assoc, hcancel, one_mul]

/-- Consequently the zeroth shifted eta moments have the same locally uniform
half-density limit. -/
theorem tendstoLocallyUniformlyOn_pairedEtaShiftedLogTailLaplaceMoment_zero :
    TendstoLocallyUniformlyOn
      (fun N s => pairedEtaShiftedLogTailLaplaceMoment 0 s N)
      (fun s : ℂ => (1 / 2) / s) atTop {s : ℂ | 0 < s.re} := by
  apply tendstoLocallyUniformlyOn_pairedEtaCoreNormalizedLaplaceTail.congr
  intro N s hs
  exact pairedEtaCoreNormalizedLaplaceTail_eq_shiftedLogTailLaplaceMoment_zero
    hs N

/-- Every positive real parameter belongs to the exponential-integrability
domain of negative shifted logarithmic time. -/
theorem Ioi_zero_subset_pairedEtaShiftedLogTail_negId_integrableExpSet
    (N : ℕ) :
    Ioi 0 ⊆ integrableExpSet (fun u : ℝ => -u)
      (pairedEtaShiftedLogTailMeasure N) := by
  intro sigma hsigma
  change Integrable (fun u : ℝ => Real.exp (sigma * -u))
    (pairedEtaShiftedLogTailMeasure N)
  have h := integrable_pairedEtaShiftedLogTailLaplaceMoment_integrand
    0 (s := (sigma : ℂ)) (by simpa using hsigma) N
  have hnorm := h.norm
  apply hnorm.congr
  filter_upwards with u
  simp only [pow_zero, one_mul, Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re]

/-- Every positive-real-part parameter is an interior exponential-
integrability point for the shifted eta tail. -/
theorem pairedEtaShiftedLogTail_re_mem_interior_negId_integrableExpSet
    (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    s.re ∈ interior
      (integrableExpSet (fun u : ℝ => -u)
        (pairedEtaShiftedLogTailMeasure N)) := by
  exact (interior_maximal
    (Ioi_zero_subset_pairedEtaShiftedLogTail_negId_integrableExpSet N)
    isOpen_Ioi) hs

/-- The zeroth shifted tail moment is the complex moment-generating function
of negative shifted logarithmic time. -/
theorem pairedEtaShiftedLogTailLaplaceMoment_zero_eq_complexMGF
    (N : ℕ) (s : ℂ) :
    pairedEtaShiftedLogTailLaplaceMoment 0 s N =
      complexMGF (fun u : ℝ => -u)
        (pairedEtaShiftedLogTailMeasure N) s := by
  unfold pairedEtaShiftedLogTailLaplaceMoment complexMGF
  apply integral_congr_ae
  filter_upwards with u
  simp only [pow_zero, one_mul]
  congr 1
  push_cast
  ring

/-- The shifted zeroth moment and its complex-MGF realization agree on a
neighborhood of every positive-half-plane point. -/
theorem pairedEtaShiftedLogTailLaplaceMoment_zero_eventuallyEq_complexMGF
    (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (fun w => pairedEtaShiftedLogTailLaplaceMoment 0 w N) =ᶠ[nhds s]
      complexMGF (fun u : ℝ => -u)
        (pairedEtaShiftedLogTailMeasure N) := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.eventually_mem hs] with w hw
  exact pairedEtaShiftedLogTailLaplaceMoment_zero_eq_complexMGF N w

/-- Every iterated spectral derivative of the shifted tail partition is its
corresponding signed centered moment. -/
theorem iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero_eq_moment
    (k N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv k
        (fun w => pairedEtaShiftedLogTailLaplaceMoment 0 w N) s =
      (-1 : ℂ) ^ k * pairedEtaShiftedLogTailLaplaceMoment k s N := by
  rw [(pairedEtaShiftedLogTailLaplaceMoment_zero_eventuallyEq_complexMGF
      N hs).iteratedDeriv_eq k,
    iteratedDeriv_complexMGF
      (pairedEtaShiftedLogTail_re_mem_interior_negId_integrableExpSet N hs) k]
  unfold pairedEtaShiftedLogTailLaplaceMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  have hpow : (((-u : ℝ) : ℂ) ^ k) =
      (-1 : ℂ) ^ k * (u : ℂ) ^ k := by
    push_cast
    rw [show -(u : ℂ) = (-1 : ℂ) * u by ring_nf, mul_pow]
  rw [hpow]
  simp only [mul_assoc]
  congr 1
  push_cast
  ring_nf

/-- For each cutoff, the shifted zeroth tail moment is analytic throughout
the open positive half-plane. -/
theorem analyticOnNhd_pairedEtaShiftedLogTailLaplaceMoment_zero (N : ℕ) :
    AnalyticOnNhd ℂ
      (fun s => pairedEtaShiftedLogTailLaplaceMoment 0 s N)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (analyticAt_complexMGF
    (pairedEtaShiftedLogTail_re_mem_interior_negId_integrableExpSet N hs)).congr
      (pairedEtaShiftedLogTailLaplaceMoment_zero_eventuallyEq_complexMGF
        N hs).symm

/-- Local uniform convergence of the shifted partitions propagates through
every iterated derivative. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero
    (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N s => iteratedDeriv k
        (fun w => pairedEtaShiftedLogTailLaplaceMoment 0 w N) s)
      (iteratedDeriv k (fun s : ℂ => (1 / 2) / s))
      atTop {s : ℂ | 0 < s.re} := by
  induction k with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        tendstoLocallyUniformlyOn_pairedEtaShiftedLogTailLaplaceMoment_zero
  | succ k ih =>
      have hderiv := ih.deriv
        (Eventually.of_forall fun N => by
          rw [iteratedDeriv_eq_iterate]
          exact (((analyticOnNhd_pairedEtaShiftedLogTailLaplaceMoment_zero N).iterated_deriv k).differentiableOn))
        (Complex.isOpen_re_gt 0)
      change TendstoLocallyUniformlyOn
        (fun N s => deriv
          (iteratedDeriv k
            (fun w => pairedEtaShiftedLogTailLaplaceMoment 0 w N)) s)
        (deriv (iteratedDeriv k (fun s : ℂ => (1 / 2) / s)))
        atTop {s : ℂ | 0 < s.re} at hderiv
      simpa only [← iteratedDeriv_succ] using hderiv

/-- The iterated derivatives of the limiting half-density transform have the
expected inverse-power closed form. -/
theorem iteratedDeriv_half_div_id
    (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun w : ℂ => (1 / 2) / w) s =
      (-1 : ℂ) ^ k *
        (((k.factorial : ℕ) : ℂ) * s ^ (-1 - (k : ℤ)) / 2) := by
  change iteratedDeriv k (fun w : ℂ => (1 / 2 : ℂ) * w⁻¹) s = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    iter_deriv_inv]
  ring

/-- Every shifted centered eta moment has the universal half-density
asymptotic, expressed using an integer inverse power. -/
theorem tendsto_pairedEtaShiftedLogTailLaplaceMoment
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => pairedEtaShiftedLogTailLaplaceMoment k s N)
      atTop
      (nhds (((k.factorial : ℕ) : ℂ) *
        s ^ (-1 - (k : ℤ)) / 2)) := by
  have hderiv :=
    (tendstoLocallyUniformlyOn_iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero
      k).tendsto_at hs
  have hderiv' : Tendsto (fun N : ℕ =>
      (-1 : ℂ) ^ k * pairedEtaShiftedLogTailLaplaceMoment k s N)
      atTop
      (nhds ((-1 : ℂ) ^ k *
        (((k.factorial : ℕ) : ℂ) * s ^ (-1 - (k : ℤ)) / 2))) := by
    convert hderiv using 1
    · funext N
      exact (iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero_eq_moment
        k N hs).symm
    · exact congrArg nhds (iteratedDeriv_half_div_id k s).symm
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hscaled := Filter.Tendsto.const_mul ((-1 : ℂ) ^ k) hderiv'
  simpa only [← mul_assoc, hsign, one_mul] using hscaled

/-- Complex odd-endpoint normalization cancels the cutoff decay exactly,
leaving the corresponding shifted centered moment. -/
theorem pairedEtaOddEndpoint_cpow_mul_cutoffCenteredTail_eq_shiftedMoment
    (k : ℕ) (s : ℂ) (N : ℕ) :
    ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ s *
        pairedEtaLogLaplaceMomentCutoffCenteredTail k s N =
      pairedEtaShiftedLogTailLaplaceMoment k s N := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hcutoff : pairedEtaLogTailCutoff N = Real.log x := by
    rfl
  have hpow :
      Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) =
        (x : ℂ) ^ (-s) := by
    rw [hcutoff, Complex.cpow_def_of_ne_zero hxne,
      ← Complex.ofReal_log hx.le]
    congr 1
    ring
  have hcancel : (x : ℂ) ^ s * (x : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add s (-s) hxne, add_neg_cancel, Complex.cpow_zero]
  rw [pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted,
    hpow]
  change (x : ℂ) ^ s *
      ((x : ℂ) ^ (-s) * pairedEtaShiftedLogTailLaplaceMoment k s N) = _
  rw [← mul_assoc, hcancel, one_mul]

/-- Negative integer powers appearing in the derivative computation are the
ordinary inverse powers expected from the Gamma moment. -/
theorem pairedEtaCenteredTailAsymptoticValue_eq
    (k : ℕ) (s : ℂ) :
    ((k.factorial : ℕ) : ℂ) * s ^ (-1 - (k : ℤ)) / 2 =
      ((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2 := by
  congr 2
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]

/-- Sharp complex asymptotic for every literal cutoff-centered eta tail. -/
theorem tendsto_oddEndpoint_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ s *
        pairedEtaLogLaplaceMomentCutoffCenteredTail k s N)
      atTop
      (nhds (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)) := by
  have h := tendsto_pairedEtaShiftedLogTailLaplaceMoment k hs
  rw [pairedEtaCenteredTailAsymptoticValue_eq k s] at h
  convert h using 1
  funext N
  exact pairedEtaOddEndpoint_cpow_mul_cutoffCenteredTail_eq_shiftedMoment
    k s N

/-- Taking norms in the sharp complex asymptotic gives the exact horizontal
decay rate of every cutoff-centered eta tail. -/
theorem
    tendsto_oddEndpoint_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ s.re) *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredTail k s N‖)
      atTop
      (nhds ‖((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2‖) := by
  have h :=
    (tendsto_oddEndpoint_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
      k hs).norm
  convert h using 1
  funext N
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-- The sharp centered-tail limiting constant is strictly positive throughout
the positive half-plane. -/
theorem pairedEtaCenteredTailAsymptoticValue_norm_pos
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 < ‖((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2‖ := by
  apply norm_pos_iff.mpr
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  exact div_ne_zero
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
      (inv_ne_zero (pow_ne_zero (k + 1) hsne)))
    (by norm_num)

end

end RiemannGaussian
