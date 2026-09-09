/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiProperPrimePowerWork
import RiemannGaussian.SuzukiLaplaceCompensator
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
  apply riemannHypothesis_of_suzuki_signal_scaled_compensated_lower_bound
    ha (fun t => C + D * t) (by fun_prop) _ (fun _ hx => affine_weight_integrable C D hx) hb
  intro t ht
  positivity

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

/-- The active event prefix transports any nonnegative increasing time
allowance from all canonical gaps to the literal Suzuki function. Only the
active prefix is used, retaining its exact physical cutoff. -/
theorem suzukiPsi_lower_bound_of_canonical_gap_monotone_lower_bound
    (f : ℝ → ℝ) (hf : MonotoneOn f (Ici (Real.log 2)))
    (hfpos : ∀ t : ℝ, Real.log 2 ≤ t → 0 ≤ f t)
    (hg : ∀ count : ℕ, -f (Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiFirstTailCanonicalGap count)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    -f t ≤ riemannXiSuzukiPsiNonnegative t := by
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
    have hp := hfpos t ht
    linarith
  | succ count =>
    have hlog : Real.log ((count + 2 : ℕ) : ℝ) ≤ t := by
      cases count with
      | zero => simpa using ht
      | succ n =>
        have h := hcut.1 (n + 1) (by omega)
        simpa only [suzukiResetLocation_succ, suzukiPrimeLocation, Nat.add_assoc,
          Nat.reduceAdd] using h
    have hbase : Real.log 2 ≤ Real.log ((count + 2 : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_cast; omega)
    have h := hf hbase ht hlog
    change -f t ≤ suzukiFirstTailCanonicalGap count
    linarith [hg count]

/-- The active event prefix converts a logarithmic cutoff floor into the
same affine time floor. No bound for inactive future prefixes is used. -/
theorem suzukiPsi_lower_bound_of_canonical_gap_log_lower_bound
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ count : ℕ, -(C + D * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      suzukiFirstTailCanonicalGap count)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    -(C + D * t) ≤ riemannXiSuzukiPsiNonnegative t := by
  apply suzukiPsi_lower_bound_of_canonical_gap_monotone_lower_bound
    (fun s => C + D * s) _ _ hg ht
  · intro x _ y _ hxy
    dsimp only
    linarith [mul_le_mul_of_nonneg_left hxy hD]
  · intro s hs
    have hs0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hs
    positivity

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
