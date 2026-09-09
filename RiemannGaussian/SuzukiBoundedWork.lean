/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiTransportRH

/-!
# A finite floor for cumulative Suzuki work is sufficient

The exact all-prefix positivity criterion is stronger than the quantitative
estimate needed for zero exclusion. A uniform lower bound of any finite
size for the unchanged cumulative signed prime work suffices, even if it
holds only beyond an arbitrary finite initial prefix.

To prove this, add a constant to the literal logarithmic-average signal.
Landau continuation applies to the resulting positive measure. The added
constant contributes exactly `C / z` on the safe Laplace half-plane; removing
that term leaves a holomorphic continuation of the original arithmetic
response. It cannot change any right-half-zero multiplicity residue.

A lower bound on canonical gaps gives the required signal lower bound by
shifting only the frozen base value in the original transport model. The
summable actual nonlinear costs transfer a work floor to a gap floor.
Conversely, every actual zero right of the critical line forces the signed
work below each prescribed finite floor at arbitrarily large cutoffs.

The independent arithmetic floor is not established here. This module
strengthens the source consequence of a hypothetical zero and removes
unnecessary exact-positivity and finite-head requirements from the target.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology ENNReal

/-- Positive-part measure of a constant shift of the actual arithmetic signal. -/
def suzukiShiftedLaplaceMeasure (C : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (suzukiChebyshevLogAverageLaplaceSignal t + C))

private theorem shiftedDensity_measurable (C : ℝ) :
    AEMeasurable (fun t => ENNReal.ofReal (suzukiChebyshevLogAverageLaplaceSignal t + C))
      (volume.restrict (Ioi 0)) :=
  (aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.add_const C).ennreal_ofReal

private theorem ae_nonneg_time_shifted (C : ℝ) :
    ∀ᵐ t ∂suzukiShiftedLaplaceMeasure C, 0 ≤ t := by
  rw [suzukiShiftedLaplaceMeasure, ae_withDensity_iff' (shiftedDensity_measurable C)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => le_of_lt ht

private theorem shifted_mgf_integrable_safe (C : ℝ)
    (hb : ∀ t : ℝ, 0 < t → -C ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    {x : ℝ} (hx : x < -1 / 2) :
    x ∈ integrableExpSet id (suzukiShiftedLaplaceMeasure C) := by
  change Integrable (fun t : ℝ => Real.exp (x * t)) _
  rw [suzukiShiftedLaplaceMeasure,
    integrable_withDensity_iff_integrable_smul₀' (shiftedDensity_measurable C)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hi := (integrableOn_suzukiChebyshevLogAverageLaplaceKernel
    (lambda := -x) (by linarith)).add
      ((integrableOn_exp_mul_Ioi (by linarith : x < 0) 0).const_mul C)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (by linarith [hb t ht])]
  dsimp [suzukiChebyshevLogAverageLaplaceKernel]
  ring_nf

private theorem shifted_complexMGF_safe (C : ℝ)
    (hb : ∀ t : ℝ, 0 < t → -C ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    complexMGF id (suzukiShiftedLaplaceMeasure C) (-z) =
      suzukiChebyshevLogAverageComplexLaplaceTransform z + (C : ℂ) / z := by
  have hsig : IntegrableOn
      (fun t : ℝ => (suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
        Complex.exp (-z * (t : ℂ))) (Ioi (0 : ℝ)) := by
    have h := integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz
    unfold suzukiChebyshevLogAverageComplexLaplaceIntegrand at h
    exact (integrable_indicator_iff measurableSet_Ioi).mp h
  have hexp := integrableOn_exp_mul_complex_Ioi
    (a := -z) (by simp only [neg_re]; linarith) 0
  rw [complexMGF, suzukiShiftedLaplaceMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ (shiftedDensity_measurable C)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [id_eq]
  have heq : (fun t : ℝ =>
      (ENNReal.ofReal (suzukiChebyshevLogAverageLaplaceSignal t + C)).toReal •
        Complex.exp (-z * (t : ℂ))) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (suzukiChebyshevLogAverageLaplaceSignal t : ℂ) * Complex.exp (-z * (t : ℂ)) +
        (C : ℂ) * Complex.exp (-z * (t : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ENNReal.toReal_ofReal (by linarith [hb t ht]), Complex.real_smul]
    push_cast
    ring_nf
  rw [integral_congr_ae heq, integral_add hsig (hexp.const_mul (C : ℂ)), integral_const_mul,
    integral_exp_mul_complex_Ioi (by simp only [neg_re]; linarith) 0]
  unfold suzukiChebyshevLogAverageComplexLaplaceTransform suzukiChebyshevLogAverageComplexLaplaceIntegrand
  rw [integral_indicator measurableSet_Ioi]
  simp [div_eq_mul_inv]

/-- A constant lower bound for the unchanged arithmetic signal suffices for RH.
The added constant has an explicitly removed Laplace response and cannot alter
any nonzero shifted-zero residue. -/
theorem riemannHypothesis_of_suzuki_signal_bounded_below
    (C : ℝ) (hb : ∀ t : ℝ, 0 < t → -C ≤ suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis := by
  have hF : AnalyticOnNhd ℝ (fun x : ℝ =>
      (suzukiChebyshevLogAverageLaplaceCompletedContinuation (-x : ℂ)).re - C / x)
      (Iio 0) :=
    analyticOnNhd_suzukiCompletedResponse_neg_real.sub
      (analyticOnNhd_const.div analyticOnNhd_id (fun _ hx => ne_of_lt hx))
  have hD : Iio (0 : ℝ) ⊆ interior (integrableExpSet id (suzukiShiftedLaplaceMeasure C)) := by
    apply Iio_subset_interior_integrableExpSet_of_analytic_mgf
      measurable_id.aemeasurable (ae_nonneg_time_shifted C)
      (a := -1 / 2) (fun _ hx => shifted_mgf_integrable_safe C hb hx) hF
    intro x hx
    change x < -1 / 2 at hx
    have hz : 1 / 2 < (-x : ℂ).re := by simp only [neg_re, ofReal_re]; linarith
    have heq := shifted_complexMGF_safe C hb hz
    rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation hz] at heq
    have hre := congrArg Complex.re heq
    simpa [complexMGF_ofReal, div_neg, div_ofReal_re, sub_eq_add_neg] using hre.symm
  let H : ℂ → ℂ := fun z => complexMGF id (suzukiShiftedLaplaceMeasure C) (-z) - (C : ℂ) / z
  have hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    have hi : (-z).re ∈ interior (integrableExpSet id (suzukiShiftedLaplaceMeasure C)) :=
      hD (by simp only [mem_Iio, neg_re]; linarith)
    exact ((analyticAt_complexMGF hi).comp analyticAt_id.neg).sub
      (analyticAt_const.div analyticAt_id (by intro he; subst z; norm_num at hz))
  apply riemannHypothesis_of_suzukiLaplace_extension H hH
  intro z hz
  dsimp [H]
  rw [shifted_complexMGF_safe C hb hz]
  ring_nf


/-- A common lower bound on the actual canonical gaps transports to the whole
literal Suzuki tail. The initial reset cell is handled by its proved base value. -/
theorem suzukiPsi_lower_bound_of_canonical_gap_lower_bound
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ count : ℕ, -C ≤ suzukiFirstTailCanonicalGap count)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    -C ≤ riemannXiSuzukiPsiNonnegative t := by
  let b := suzukiPointwiseFrozenBaseValue (Real.log 2) 1
  let v := suzukiPointwiseFrozenBaseSlope (Real.log 2) 1
  have hv : v ≤ 0 := suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive
  have hfuture : Real.log 2 ≤ suzukiPrimeLocation 1 :=
    suzukiPrimeEventCut_logTwo_one.2 0
  have hall := (suzukiResetModel_nonnegativeOn_tail_iff_transportGaps
    (b + C) v (Real.log 2) le_rfl hv 1 hfuture).mpr (by
      intro cutoff
      cases cutoff with
      | zero =>
        simp only [curvatureTransportGap, screwPrefixMoment, Finset.range_zero,
          Finset.sum_empty, add_zero, suzukiResetTransportMassPoint_zero,
          transportCurvatureMoment_self, sub_zero]
        have hb : 0 < b := suzukiPointwiseFrozenBaseValue_logTwo_one_pos
        linarith
      | succ n =>
        have h := hg n
        unfold suzukiFirstTailCanonicalGap curvatureTransportGap at h
        change 0 ≤ (b + C) + _ - _
        dsimp [b, v] at *
        linarith)
  have hnonneg := hall t ht
  have heq := suzukiFullModel_eq_resetModel_on_tail
    suzukiPrimeEventCut_logTwo_one
    (suzukiPointwiseTailNormalization (Real.log_pos (by norm_num : (1 : ℝ) < 2)) 1) t ht
  have ht0 : 0 ≤ t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans ht
  rw [riemannXiSuzukiPsiNonnegative_eq_screwHingeModel ht0, heq]
  unfold screwHingeModel zeroSlopeCurvatureBackground at hnonneg ⊢
  dsimp [b, v] at hnonneg
  linarith

/-- A common lower bound on canonical gaps, of any finite size, suffices for RH. -/
theorem riemannHypothesis_of_suzukiCanonicalGap_bounded_below
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ count : ℕ, -C ≤ suzukiFirstTailCanonicalGap count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_bounded_below C
  intro t ht
  rw [suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime ht.le]
  by_cases htail : Real.log 2 ≤ t
  · have h := suzukiPsi_lower_bound_of_canonical_gap_lower_bound hC hg htail
    unfold riemannXiSuzukiPsiNonnegative at h
    linarith [suzukiPointwiseArchimedean_lt_four_mul_exp_half ht.le]
  · rw [suzukiPointwisePrimeContribution_eq_zero_of_lt_log_two ht.le (lt_of_not_ge htail)]
    have hp : 0 < 4 * Real.exp (t / 2) := mul_pos (by norm_num) (Real.exp_pos _)
    linarith

/-- An arbitrary uniform lower bound on cumulative signed prime work suffices
for RH: the complete nonlinear cost is already summable unconditionally. -/
theorem riemannHypothesis_of_suzuki_signed_work_bounded_below
    (B : ℝ)
    (hwork : ∀ count : ℕ, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) :
    RiemannHypothesis := by
  let C := |suzukiFirstTailCanonicalGap 0| + |B| +
    ∑' n : ℕ, suzukiFirstTailTransportCellCost n
  have hcost : 0 ≤ ∑' n : ℕ, suzukiFirstTailTransportCellCost n :=
    tsum_nonneg (fun n => (suzukiFirstTailTransportCellCost_bounds n).1)
  apply riemannHypothesis_of_suzukiCanonicalGap_bounded_below
    (C := C) (by dsimp [C]; positivity)
  intro count
  have heq := suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost 0 count
  have hb := suzukiFirstTailTransportCellCost_block_le_tail 0 count
  simp only [Nat.zero_add] at heq hb
  rw [heq]
  dsimp [C]
  linarith [hwork count, neg_abs_le (suzukiFirstTailCanonicalGap 0), le_abs_self B]

/-- A right-half zero forces the cumulative signed work below every prescribed
finite floor. This is stronger than one finite-prefix failure. -/
theorem suzuki_signed_work_unbounded_below_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (B : ℝ) :
    ∃ count : ℕ, (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) < -B := by
  by_contra hnot
  push Not at hnot
  have hRH := riemannHypothesis_of_suzuki_signed_work_bounded_below B hnot
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith


/-- A finite initial prefix can be absorbed into the arbitrary constant floor;
only an eventual bound on the original signed work is needed. -/
theorem riemannHypothesis_of_suzuki_signed_work_eventually_bounded_below
    (B : ℝ)
    (hwork : ∀ᶠ count : ℕ in atTop, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) :
    RiemannHypothesis := by
  obtain ⟨start, hstart⟩ := eventually_atTop.mp hwork
  let E : ℝ := ∑ j ∈ Finset.range start,
    |∑ n ∈ Finset.range j, suzukiFirstTailTransportLinearWork n|
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply riemannHypothesis_of_suzuki_signed_work_bounded_below (|B| + E)
  intro count
  by_cases hc : start ≤ count
  · linarith [hstart count hc, le_abs_self B]
  · have he : |∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n| ≤ E :=
      Finset.single_le_sum
        (f := fun j : ℕ => |∑ n ∈ Finset.range j, suzukiFirstTailTransportLinearWork n|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (lt_of_not_ge hc))
    linarith [neg_abs_le (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n),
      abs_nonneg B]

/-- Under a right-half zero every finite work floor fails at arbitrarily large
cutoffs. Finite initial checks and the summable cost cannot prevent this escape. -/
theorem suzuki_signed_work_frequently_below_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (B : ℝ) :
    ∃ᶠ count : ℕ in atTop,
      (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) < -B := by
  by_contra hnot
  have he : ∀ᶠ count : ℕ in atTop, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n := by
    simpa only [not_frequently, not_lt] using hnot
  have hRH := riemannHypothesis_of_suzuki_signed_work_eventually_bounded_below B he
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith

end
end RiemannGaussian
