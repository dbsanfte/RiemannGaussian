/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiProperPrimePowerWork
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentGapBound

/-!
# Absorbing logarithmic losses in the Suzuki work criterion

A logarithmic cutoff allowance becomes an affine time allowance at the
actual active event cell. Its positive compensator has a genuinely convergent
Laplace integral for every positive damping. Subtracting that analytic
response after the positive-Laplace argument preserves every hypothetical
right-half-zero residue.

The arithmetic lower bound on ordinary-prime work remains an open premise.
This module repairs the allowance interface; it does not prove that bound.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology ENNReal

private def timeDensity (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (f t))

private theorem timeDensity_nonneg_time (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0))) :
    ∀ᵐ t ∂timeDensity f, 0 ≤ t := by
  rw [timeDensity, ae_withDensity_iff' hf.ennreal_ofReal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => ht.le

private theorem timeDensity_integrable_exp (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) (x : ℝ)
    (hi : IntegrableOn (fun t : ℝ => f t * Real.exp (x * t)) (Ioi 0)) :
    x ∈ integrableExpSet id (timeDensity f) := by
  change Integrable (fun t : ℝ => Real.exp (x * t)) _
  rw [timeDensity, integrable_withDensity_iff_integrable_smul₀' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hpos t ht), smul_eq_mul]

private theorem timeDensity_complexMGF (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) (z : ℂ) :
    complexMGF id (timeDensity f) z =
      ∫ t in Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (z * (t : ℂ)) := by
  rw [complexMGF, timeDensity,
    integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hpos t ht), Complex.real_smul]
  rfl

private theorem integrable_complex_weight (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) (z : ℂ)
    (hi : IntegrableOn (fun t : ℝ => f t * Real.exp (z.re * t)) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => (f t : ℂ) * Complex.exp (z * (t : ℂ))) (Ioi 0) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [norm_real, Complex.norm_exp, abs_of_nonneg (hpos t ht)]

private theorem affine_weight_integrable (C D : ℝ) {x : ℝ} (hx : x < 0) :
    IntegrableOn (fun t : ℝ => (C + D * t) * Real.exp (x * t)) (Ioi 0) := by
  have hc := (integrableOn_exp_mul_Ioi hx 0).const_mul C
  have ht : IntegrableOn (fun t : ℝ => t * Real.exp (x * t)) (Ioi 0) := by
    simpa only [pow_one, neg_neg] using
      (integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 1 (sigma := -x) (by linarith))
  apply (hc.add (ht.const_mul D)).congr
  filter_upwards [] with t
  dsimp only [Pi.add_apply]
  ring

/-- Either orientation of an affine one-sided bound forces RH. Multiplying
the genuine signal by a nonzero real constant preserves its zero poles;
the affine compensator is removed from the analytic extension. -/
theorem riemannHypothesis_of_suzuki_signal_scaled_affine_lower_bound
    {a C D : ℝ} (ha : a ≠ 0) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t : ℝ, 0 < t → -(C + D * t) ≤ a * suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis := by
  let f : ℝ → ℝ := fun t => C + D * t
  let g : ℝ → ℝ := fun t => a * suzukiChebyshevLogAverageLaplaceSignal t + f t
  have hf : AEMeasurable f (volume.restrict (Ioi 0)) := by dsimp [f]; fun_prop
  have hg : AEMeasurable g (volume.restrict (Ioi 0)) :=
    (aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.const_mul a).add hf
  have hfpos : ∀ t : ℝ, 0 < t → 0 ≤ f t := by intro t ht; dsimp [f]; positivity
  have hgpos : ∀ t : ℝ, 0 < t → 0 ≤ g t := by intro t ht; dsimp [g, f]; linarith [hb t ht]
  have hfi : ∀ x : ℝ, x < 0 → x ∈ integrableExpSet id (timeDensity f) := by
    intro x hx
    exact timeDensity_integrable_exp f hf hfpos x (affine_weight_integrable C D hx)
  have hfd : Iio (0 : ℝ) ⊆ interior (integrableExpSet id (timeDensity f)) :=
    isOpen_Iio.subset_interior_iff.mpr hfi
  have hgi : ∀ x : ℝ, x < -1 / 2 → x ∈ integrableExpSet id (timeDensity g) := by
    intro x hx
    apply timeDensity_integrable_exp g hg hgpos x
    have hi := (integrableOn_suzukiChebyshevLogAverageLaplaceKernel
      (lambda := -x) (by linarith)).const_mul a |>.add
        (affine_weight_integrable C D (by linarith : x < 0))
    apply hi.congr
    filter_upwards [] with t
    dsimp [g, f, suzukiChebyshevLogAverageLaplaceKernel]
    ring_nf
  have heq : ∀ z : ℂ, 1 / 2 < z.re →
      complexMGF id (timeDensity g) (-z) =
        (a : ℂ) * suzukiChebyshevLogAverageComplexLaplaceTransform z +
          complexMGF id (timeDensity f) (-z) := by
    intro z hz
    have hsig : IntegrableOn
        (fun t : ℝ => (suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
          Complex.exp (-z * (t : ℂ))) (Ioi (0 : ℝ)) := by
      have h := integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz
      unfold suzukiChebyshevLogAverageComplexLaplaceIntegrand at h
      exact (integrable_indicator_iff measurableSet_Ioi).mp h
    have hfint := integrable_complex_weight f hf hfpos (-z)
      (affine_weight_integrable C D (by simp only [neg_re]; linarith : (-z).re < 0))
    rw [timeDensity_complexMGF g hg hgpos, timeDensity_complexMGF f hf hfpos]
    have hfun : (fun t : ℝ => (g t : ℂ) * Complex.exp (-z * (t : ℂ))) =
        fun t => (a : ℂ) * ((suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
          Complex.exp (-z * (t : ℂ))) +
          (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
      ext t
      dsimp [g]
      push_cast
      ring
    rw [hfun, integral_add (hsig.const_mul (a : ℂ)) hfint, integral_const_mul]
    unfold suzukiChebyshevLogAverageComplexLaplaceTransform
      suzukiChebyshevLogAverageComplexLaplaceIntegrand
    rw [integral_indicator measurableSet_Ioi]
  have hF : AnalyticOnNhd ℝ (fun x : ℝ =>
      a * (suzukiChebyshevLogAverageLaplaceCompletedContinuation (-x : ℂ)).re +
        mgf id (timeDensity f) x) (Iio 0) :=
    fun x hx => (analyticAt_const.mul
      (analyticOnNhd_suzukiCompletedResponse_neg_real x hx)).add (analyticAt_mgf (hfd hx))
  have hgd : Iio (0 : ℝ) ⊆ interior (integrableExpSet id (timeDensity g)) := by
    apply Iio_subset_interior_integrableExpSet_of_analytic_mgf
      measurable_id.aemeasurable (timeDensity_nonneg_time g hg)
      (a := -1 / 2) hgi hF
    intro x hx
    change x < -1 / 2 at hx
    have hz : 1 / 2 < (-x : ℂ).re := by simp only [neg_re, ofReal_re]; linarith
    have h := heq (-x) hz
    rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation hz] at h
    have hr := congrArg Complex.re h
    simpa [complexMGF_ofReal] using hr.symm
  let H : ℂ → ℂ := fun z => (a : ℂ)⁻¹ * (complexMGF id (timeDensity g) (-z) -
    complexMGF id (timeDensity f) (-z))
  have hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re} := by
    intro z hz
    have hx : (-z).re ∈ Iio (0 : ℝ) := by change -z.re < 0; exact neg_neg_of_pos hz
    exact analyticAt_const.mul
      (((analyticAt_complexMGF (hgd hx)).comp analyticAt_id.neg).sub
        ((analyticAt_complexMGF (hfd hx)).comp analyticAt_id.neg))
  apply riemannHypothesis_of_suzukiLaplace_extension H hH
  intro z hz
  dsimp [H]
  rw [heq z hz]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  field_simp
  ring

/-- An affine time loss is harmless to the analytic RH implication. The
compensator's Laplace transform genuinely converges throughout `Re z > 0`
and is subtracted before applying the zero-residue contradiction. -/
theorem riemannHypothesis_of_suzuki_signal_affine_lower_bound
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t : ℝ, 0 < t → -(C + D * t) ≤ suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_scaled_affine_lower_bound
    (a := 1) (by norm_num) hC hD
  simpa using hb

private abbrev firstTailGap (cutoff : ℕ) : ℝ :=
  curvatureTransportGap
    (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
    (Real.log 2) suzukiSmoothCurvature
    (suzukiResetLocation (Real.log 2) 1)
    (suzukiResetWeight (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
    (suzukiResetTransportMassPoint (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
      (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
    cutoff

private theorem firstTailGap_le_frozen (cutoff : ℕ) {t : ℝ} (ht : Real.log 2 ≤ t) :
    firstTailGap cutoff ≤ frozenScrewHingeModel
      (zeroSlopeCurvatureBackground (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature)
      (suzukiResetLocation (Real.log 2) 1)
      (suzukiResetWeight (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1) cutoff t := by
  have hc : ContinuousOn suzukiSmoothCurvature (Ici (Real.log 2)) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro s hs
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hs)
  have hp : ∀ s : ℝ, Real.log 2 ≤ s → 0 ≤ suzukiSmoothCurvature s :=
    fun _ hs => (suzukiSmoothCurvature_pos_of_log_two_le hs).le
  have hm := suzukiResetTransportMassPoint_mass_eq (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) le_rfl
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 cutoff
  have hmin := frozenScrewHingeModel_minimized_at_massPoint
    (baseMargin := suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
    (location := suzukiResetLocation (Real.log 2) 1) hc hp
    (base_le_suzukiResetTransportMassPoint (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) le_rfl
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 cutoff) hm t ht
  rw [frozenScrewHingeModel_zeroSlopeCurvature_eq, hm] at hmin
  unfold firstTailGap curvatureTransportGap
  linarith

/-- The active event prefix converts a logarithmic cutoff floor into the
same affine time floor. No bound for inactive future prefixes is used. -/
theorem suzukiPsi_lower_bound_of_canonical_gap_log_lower_bound
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ count : ℕ, -(C + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiFirstTailCanonicalGap count)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    -(C + D * t) ≤ riemannXiSuzukiPsiNonnegative t := by
  have ht0 : 0 ≤ t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans ht
  obtain ⟨cutoff, hcut⟩ := suzukiResetEventCutsCover (suzukiPrimeEventCut_logTwo_one.2 0) t
  have heq := suzukiFullModel_eq_resetModel_on_tail suzukiPrimeEventCut_logTwo_one
    (suzukiPointwiseTailNormalization (Real.log_pos (by norm_num : (1 : ℝ) < 2)) 1) t ht
  rw [riemannXiSuzukiPsiNonnegative_eq_screwHingeModel ht0, heq,
    screwHingeModel_eq_frozen_of_eventCut
      (summable_suzukiResetNegativeHinge (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1 t) hcut]
  apply le_trans _ (firstTailGap_le_frozen cutoff ht)
  cases cutoff with
  | zero =>
    have hbase := suzukiPointwiseFrozenBaseValue_logTwo_one_pos
    simp only [firstTailGap, curvatureTransportGap, screwPrefixMoment,
      Finset.range_zero, Finset.sum_empty, add_zero, suzukiResetTransportMassPoint_zero,
      transportCurvatureMoment_self, sub_zero]
    have hp : 0 ≤ C + D * t := by positivity
    linarith
  | succ count =>
    have hlog : Real.log ((count + 2 : ℕ) : ℝ) ≤ t := by
      cases count with
      | zero => simpa using ht
      | succ n =>
        have h := hcut.1 (n + 1) (by omega)
        simpa only [suzukiResetLocation_succ, suzukiPrimeLocation, Nat.add_assoc,
          Nat.reduceAdd] using h
    have h := mul_le_mul_of_nonneg_left hlog hD
    change -(C + D * t) ≤ suzukiFirstTailCanonicalGap count
    linarith [hg count]

/-- A logarithmic lower loss on all canonical gaps suffices for RH. Its
linear time compensation is genuinely integrable at every positive damping. -/
theorem riemannHypothesis_of_suzukiCanonicalGap_log_lower_bound
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ count : ℕ, -(C + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiFirstTailCanonicalGap count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_affine_lower_bound hC hD
  intro t ht
  rw [suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime ht.le]
  by_cases htail : Real.log 2 ≤ t
  · have h := suzukiPsi_lower_bound_of_canonical_gap_log_lower_bound hC hD hg htail
    unfold riemannXiSuzukiPsiNonnegative at h
    linarith [suzukiPointwiseArchimedean_lt_four_mul_exp_half ht.le]
  · rw [suzukiPointwisePrimeContribution_eq_zero_of_lt_log_two ht.le (lt_of_not_ge htail)]
    have hp : 0 ≤ C + D * t := by positivity
    have he : 0 < 4 * Real.exp (t / 2) := by positivity
    linarith

/-- The actual summable transport costs preserve a logarithmic work floor.
The logarithmic allowance is absorbed by the proved affine-time argument. -/
theorem riemannHypothesis_of_suzuki_signed_work_log_lower_bound
    (B : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ count : ℕ, -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      ∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j) :
    RiemannHypothesis := by
  let C := |suzukiFirstTailCanonicalGap 0| + |B| +
    ∑' j : ℕ, suzukiFirstTailTransportCellCost j
  have hc : 0 ≤ ∑' j : ℕ, suzukiFirstTailTransportCellCost j :=
    tsum_nonneg (fun j => (suzukiFirstTailTransportCellCost_bounds j).1)
  apply riemannHypothesis_of_suzukiCanonicalGap_log_lower_bound
    (C := C) (by dsimp [C]; positivity) hD
  intro count
  have heq := suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost 0 count
  have hcost := suzukiFirstTailTransportCellCost_block_le_tail 0 count
  simp only [Nat.zero_add] at heq hcost
  rw [heq]
  dsimp [C]
  linarith [hw count, neg_abs_le (suzukiFirstTailCanonicalGap 0), le_abs_self B]

/-- A finite initial prefix is absorbed into the constant part of an eventual
logarithmic lower allowance on the original cumulative signed work. -/
theorem riemannHypothesis_of_suzuki_signed_work_eventually_log_lower_bound
    (B : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ᶠ count : ℕ in atTop, -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      ∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j) :
    RiemannHypothesis := by
  obtain ⟨start, hs⟩ := eventually_atTop.mp hw
  let E : ℝ := ∑ n ∈ Finset.range start,
    |∑ j ∈ Finset.range n, suzukiFirstTailTransportLinearWork j|
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply riemannHypothesis_of_suzuki_signed_work_log_lower_bound (|B| + E) hD
  intro count
  by_cases hc : start ≤ count
  · linarith [hs count hc, le_abs_self B]
  · have hb : |∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j| ≤ E :=
      Finset.single_le_sum
        (f := fun n : ℕ => |∑ j ∈ Finset.range n, suzukiFirstTailTransportLinearWork j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (lt_of_not_ge hc))
    have hl : 0 ≤ D * Real.log ((count + 2 : ℕ) : ℝ) :=
      mul_nonneg hD (Real.log_nonneg (by norm_cast; omega))
    linarith [neg_abs_le (∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j),
      abs_nonneg B]

/-- The independent proper-prime-power bound is fully absorbed: an eventual
logarithmic floor for ordinary-prime events suffices for RH. Their full old
prefix masses and original canonical centers are retained. This arithmetic
floor is still an open hypothesis. -/
theorem riemannHypothesis_of_suzuki_ordinaryPrime_work_eventually_log_lower_bound
    (B : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ᶠ count : ℕ in atTop, -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiOrdinaryPrimeWork count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signed_work_eventually_log_lower_bound
    (B + 90) (D := D + 45) (by linarith)
  filter_upwards [hw] with count hc
  have h := suzuki_signed_work_lower_of_ordinary_lower hc
  convert h using 1
  ring

/-- In particular, a finite floor on ordinary-prime work alone suffices. No
unproved summability of proper-prime-power work is used in this implication. -/
theorem riemannHypothesis_of_suzuki_ordinaryPrime_work_eventually_bounded_below
    (B : ℝ)
    (hw : ∀ᶠ count : ℕ in atTop, -B ≤ suzukiOrdinaryPrimeWork count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_ordinaryPrime_work_eventually_log_lower_bound
    B (D := 0) (by norm_num)
  simpa only [zero_mul, add_zero] using hw

/-- The finite mass-log target can also be restricted to ordinary-prime new
atoms, while preserving all preceding prime powers inside its mass logarithm.
Only the already proved positive Lerch correction is discarded in this bound. -/
theorem riemannHypothesis_of_suzuki_ordinaryPrime_massLog_eventually_log_lower_bound
    (B : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ᶠ count : ℕ in atTop, -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      ∑ j ∈ Finset.range count, if (j + 3).Prime then suzukiFirstTailMassLogWork j else 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_ordinaryPrime_work_eventually_log_lower_bound B hD
  filter_upwards [hw] with count hc
  apply hc.trans
  unfold suzukiOrdinaryPrimeWork
  apply Finset.sum_le_sum
  intro j hj
  by_cases hp : (j + 3).Prime
  · simp only [if_pos hp]
    linarith [suzukiFirstTailTransportLinearWork_eq_massLog_add_error j,
      (suzukiFirstTailMassLogWorkError_bounds j).1]
  · simp only [if_neg hp, le_refl]

/-- A hypothetical right-half zero forces ordinary-prime work below every
prescribed logarithmic floor at arbitrarily late cutoffs. The proof includes
the whole proper-prime-power allowance through the repaired analytic chain. -/
theorem suzuki_ordinaryPrime_work_frequently_below_log_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (B : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ᶠ count : ℕ in atTop, suzukiOrdinaryPrimeWork count <
      -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) := by
  by_contra hnot
  have hw : ∀ᶠ count : ℕ in atTop, -(B + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiOrdinaryPrimeWork count := by simpa only [not_frequently, not_lt] using hnot
  have hRH := riemannHypothesis_of_suzuki_ordinaryPrime_work_eventually_log_lower_bound B hD hw
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith

end
end RiemannGaussian
