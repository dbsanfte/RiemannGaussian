/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointRadialFloor
import RiemannGaussian.ZetaRieszPrimeCountMass

/-!
# Paying a larger prime-count part of the existing joint core

The restricted radius permits a count threshold 512 times smaller than
the original one, on the same moment schedule. The estimates cover the
whole integer response, not just a frequency window. No new carrier is
defined, and the retained low counts still require a signed joint floor.
-/

namespace RiemannGaussian.ZetaRieszJointCountFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeCountMass ZetaRieszJointAllocation
open ZetaRieszBalancedCompanion ZetaRieszWideOwnerAudit ZetaRieszParityPacket
open ZetaRieszAnnulusJoint

/-- Exact reduction in the existing count threshold, with no change to
the moment order or any integer mask. -/
theorem reduced_count_factor (j : ℕ) (hj : 9 ≤ j) :
    512*dyadicPrimeCount (j-9) = dyadicPrimeCount j := by
  unfold dyadicPrimeCount
  rw [show j+3 = (j-9+3)+9 by omega,pow_add]
  norm_num
  ring

/-- The smaller threshold still buys a fixed geometric saving, checked
using rational logarithm bounds rather than a floating rate. -/
theorem reduced_count_power_saving (j : ℕ) (hj : 64 ≤ j) :
    (7001/7000 : ℝ)^dyadicMomentOrder j ≤
      (dyadicPrimeCount (j-9) : ℝ)^dyadicPrimeCount (j-9) := by
  have hj9 : 9 ≤ j := by omega
  have hN : dyadicMomentOrder j = 4096*(j+4)*dyadicPrimeCount (j-9) := by
    rw [dyadicMomentOrder,← reduced_count_factor j hj9]
    ring
  have hb : (7001/7000 : ℝ)^(4096*(j+4)) ≤ (dyadicPrimeCount (j-9) : ℝ) := by
    have hl : Real.log (7001/7000 : ℝ) ≤ 1/7000 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7001/7000)
      linarith
    have h2 : (693/1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hjR : (64 : ℝ) ≤ j := by exact_mod_cast hj
    have hleft := mul_le_mul_of_nonneg_left hl
      (show 0 ≤ 4096*((j : ℝ)+4) by positivity)
    have hright := mul_le_mul_of_nonneg_left h2
      (show 0 ≤ (j : ℝ)-6 by linarith)
    have hr : 4096*((j : ℝ)+4)*Real.log (7001/7000 : ℝ) ≤
        ((j : ℝ)-6)*Real.log 2 := by linarith
    have he : ((j-9+3 : ℕ) : ℝ) = (j : ℝ)-6 := by
      rw [Nat.cast_add,Nat.cast_sub hj9]
      norm_num
      ring
    calc
      _ = Real.exp ((4096*((j : ℝ)+4))*Real.log (7001/7000 : ℝ)) := by
        rw [show 4096*((j : ℝ)+4) = ((4096*(j+4) : ℕ) : ℝ) by push_cast; ring,
          Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ Real.exp (((j : ℝ)-6)*Real.log 2) := Real.exp_le_exp.mpr hr
      _ = _ := by
        rw [← he,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        simp only [dyadicPrimeCount,Nat.cast_pow,Nat.cast_ofNat]
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ (7001/7000 : ℝ)^(4096*(j+4)))
    hb (dyadicPrimeCount (j-9))
  simpa only [← pow_mul,← hN] using h

/-- The source, count saving and subexponential Euler slack leave a
strict rational rate below one on the restricted radius interval. -/
theorem count_rate_bound :
    (radiusCeiling/(131071/262144 : ℝ))*(100001/100000)/(7001/7000) ≤
      (49999/50000 : ℝ) := by norm_num [radiusCeiling]

/-- The actual residual allocation is a contraction of the original
coefficient. This does not remove it from the surviving signed sum. -/
theorem norm_residual_le (A : Finset ℕ) (L : ℝ) (N n : ℕ) :
    ‖residualCoefficient A L N n‖ ≤ ‖SquarefreeVaughanLogSource.coefficient L n‖ := by
  have hs := boundedShare_bounds A N n
  rw [residualCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ 1-boundedShare A N n by linarith)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- A count-generating estimate for the literal residual sum. It keeps
the full complex phase, arbitrary physical selection and old allocation;
all frequencies are covered by this bound. -/
theorem norm_residual_sum_le_count (A D : Finset ℕ) (N : ℕ) (y : ℝ)
    {L u q r : ℝ} (hL : 0 < L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hq : 0 < q) (hqhalf : q < 1/2) (hr : 1 ≤ r)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand N)
    {K : ℕ} (hK : ∀ n ∈ D, K ≤ n.primeFactors.card) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (32*radiusCeiling*Real.log 2)*((N : ℝ)*(radiusCeiling/q)^N)*
        Real.exp (2*r*countMass (3/2-q))/r^K := by
  have hs : ‖∑ n ∈ D,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (32*(N : ℝ)*Real.log 2*q⁻¹^N)*
        ∑ n ∈ D, (2 : ℝ)^n.primeFactors.card*Real.exp (-(3/2-q)*Real.log n) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hc := (norm_residual_le A L N n).trans
      ((SquarefreeVaughanLogSource.norm_coefficient_le hL n).trans
        ((ZetaRieszSmoothHead.logMajorant_le_prime_count (hD n hn)).trans
          (mul_le_mul_of_nonneg_right (ZetaRieszSmoothHead.log_le_of_mem_band (hband hn))
            (by positivity))))
    have hk := norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n hq
    rw [norm_mul]
    apply (mul_le_mul hc hk (norm_nonneg _) (by positivity)).trans_eq
    rw [show (3/2+Complex.I*(y : ℂ)).re = (3/2 : ℝ) by norm_num]
    unfold zetaPrimeExpWeight
    ring
  have hm := many_prime_mass_le D hD hK (by linarith : 1 < 3/2-q) hr
  have hU0 : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  calc
    _ ≤ radiusCeiling^(N+1)*((32*(N : ℝ)*Real.log 2*q⁻¹^N)*
        ∑ n ∈ D, (2 : ℝ)^n.primeFactors.card*Real.exp (-(3/2-q)*Real.log n)) := by
      exact mul_le_mul (pow_le_pow_left₀ hu hU (N+1)) hs (norm_nonneg _)
        (by unfold radiusCeiling; positivity)
    _ ≤ radiusCeiling^(N+1)*((32*(N : ℝ)*Real.log 2*q⁻¹^N)*
        (Real.exp (2*r*countMass (3/2-q))/r^K)) := by
      gcongr
    _ = _ := by rw [pow_succ,div_pow]; ring

/-- Uniform eventual geometric control of every selected high-count
residual sum at the smaller threshold. The Euler mass is paid here, not
left as a new hypothesis. No zero hypothesis or prime-count completion
is used. The eventual order threshold is not numerically evaluated. -/
theorem eventually_norm_residual_many_le :
    ∀ᶠ j : ℕ in atTop, ∀ (A D : Finset ℕ) (L y u : ℝ),
      0 < L → 0 ≤ u → u ≤ radiusCeiling →
      D ⊆ zetaPrimeLogBand (dyadicMomentOrder j) →
      (∀ n ∈ D, dyadicPrimeCount (j-9) ≤ n.primeFactors.card) →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n ∈ D,
        residualCoefficient A L (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
        (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
          (49999/50000 : ℝ)^dyadicMomentOrder j := by
  have hEuler := eventually_exp_count_le_geometric
    (2*countMass (3/2-(131071/262144 : ℝ)))
    (by norm_num : (1 : ℝ) < 100001/100000)
  filter_upwards [eventually_ge_atTop 64,hEuler] with j hj hEj
  intro A D L y u hL hu hU hband hK
  let S := D.filter Squarefree
  have hS : ∀ n ∈ S, Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hSB : S ⊆ zetaPrimeLogBand (dyadicMomentOrder j) :=
    (Finset.filter_subset _ _).trans hband
  have hSK : ∀ n ∈ S, dyadicPrimeCount (j-9) ≤ n.primeFactors.card :=
    fun n hn => hK n (Finset.mem_filter.mp hn).1
  have heq : (∑ n ∈ D, residualCoefficient A L (dyadicMomentOrder j) n*
      zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n) =
      ∑ n ∈ S, residualCoefficient A L (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hns : ¬Squarefree n := fun hs => hnot (Finset.mem_filter.mpr ⟨hn,hs⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hns]
  rw [heq]
  have hK1 : (1 : ℝ) ≤ dyadicPrimeCount (j-9) := by
    exact_mod_cast (show 1 ≤ dyadicPrimeCount (j-9) by
      have h := four_le_dyadicPrimeCount (j-9); omega)
  have hKm : (dyadicPrimeCount (j-9) : ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (show dyadicPrimeCount (j-9) ≤ dyadicPrimeCount j by
      simp only [dyadicPrimeCount]
      exact pow_le_pow_right₀ (by norm_num) (by omega))
  have hE : Real.exp (2*(dyadicPrimeCount (j-9) : ℝ)*
      countMass (3/2-(131071/262144 : ℝ))) ≤
      (100001/100000 : ℝ)^dyadicMomentOrder j := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hEj
    nlinarith [mul_le_mul_of_nonneg_right hKm
      (countMass_nonneg (3/2-(131071/262144 : ℝ)))]
  have hb := norm_residual_sum_le_count A S (dyadicMomentOrder j) y hL hu hU
    (by norm_num : (0 : ℝ) < 131071/262144)
    (by norm_num : (131071/262144 : ℝ) < 1/2) hK1 hS hSB hSK
  have hU0 : 0 ≤ radiusCeiling := by norm_num [radiusCeiling]
  apply hb.trans
  calc
    _ ≤ (32*radiusCeiling*Real.log 2)*
        ((dyadicMomentOrder j : ℝ)*(radiusCeiling/(131071/262144))^dyadicMomentOrder j)*
        Real.exp (2*(dyadicPrimeCount (j-9) : ℝ)*countMass (3/2-(131071/262144 : ℝ))) /
          (7001/7000 : ℝ)^dyadicMomentOrder j :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (reduced_count_power_saving j hj)
    _ ≤ (32*radiusCeiling*Real.log 2)*
        ((dyadicMomentOrder j : ℝ)*(radiusCeiling/(131071/262144))^dyadicMomentOrder j)*
        (100001/100000 : ℝ)^dyadicMomentOrder j /
          (7001/7000 : ℝ)^dyadicMomentOrder j := by gcongr
    _ = (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
        ((radiusCeiling/(131071/262144))*(100001/100000)/(7001/7000))^dyadicMomentOrder j := by
      simp only [div_pow,mul_pow]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) count_rate_bound _

private theorem core_subset_original (u : ℝ) (N K : ℕ) :
    coreBand u N K ⊆ zetaPrimeLogBand N := by
  intro n hn
  have hnarrow := (Finset.mem_filter.mp hn).1
  have hnon := (Finset.mem_filter.mp hnarrow).1
  have hret := (Finset.mem_sdiff.mp hnon).1
  have horig := (Finset.mem_sdiff.mp hret).1
  have hfew := (Finset.mem_filter.mp horig).1
  have hcentral := (Finset.mem_filter.mp hfew).1
  exact centralUnpairedBand_subset_original u N hcentral

/-- The entire newly removed part of the actual core is independently
small, including its allocation factor and all complex phases. -/
theorem eventually_norm_high_core_le :
    ∀ᶠ j : ℕ in atTop, ∀ u y : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*
        ∑ n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
            (fun n => dyadicPrimeCount (j-9) ≤ n.primeFactors.card),
          residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖ ≤
        (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
          (49999/50000 : ℝ)^dyadicMomentOrder j := by
  filter_upwards [eventually_norm_residual_many_le] with j hj
  intro u y hu hU
  exact hj _ _ _ y u (SquarefreeVaughanLogSource.length_pos u _) hu hU
    ((Finset.filter_subset _ _).trans (core_subset_original _ _ _))
    (fun _ hn => (Finset.mem_filter.mp hn).2)

/-- Changing only the count endpoint of the existing core is exactly
intersection with that endpoint. All original support tests survive. -/
theorem coreBand_count_filter (u : ℝ) (N K K' : ℕ) (hK : K' ≤ K) :
    coreBand u N K' = (coreBand u N K).filter (fun n => n.primeFactors.card < K') := by
  ext n
  simp only [coreBand,ZetaRieszTypeII.narrowBand,LogarithmicDeviation.deviationBand,
    ZetaRieszDominantAllocation.nondominantBand,ZetaRieszMaskSupport.retainedBand,
    ZetaRieszDominantAllocation.dominantSector,ZetaRieszJointAllocation.cancellingSector,
    ZetaRieszCompanionMask.originalMask,ZetaRieszHarmonicWindow.fewBand,
    Finset.mem_filter,Finset.mem_sdiff]
  by_cases hc : n.primeFactors.card < K'
  · simp only [hc,lt_of_lt_of_le hc hK,and_true]
  · simp only [hc,and_false,false_and,not_false_eq_true]

/-- The difference between the two existing core responses is exactly
the high-count sum already bounded, with no additional boundary term. -/
theorem coreResponse_sub_count (u y : ℝ) (N K K' : ℕ) (hK : K' ≤ K) :
    coreResponse u y N K-coreResponse u y N K' =
      ∑ n ∈ (coreBand u N K).filter (fun n => K' ≤ n.primeFactors.card),
        residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  unfold coreResponse
  rw [coreBand_count_filter u N K K' hK]
  have he := Finset.sum_filter_add_sum_filter_not (coreBand u N K)
    (fun n => n.primeFactors.card < K') (fun n =>
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  simp only [not_lt] at he
  linear_combination -he

/-- The smaller count endpoint is paid independently, on the original
cofinal schedule. The complex difference is controlled before observing
its real part, uniformly over all heights and restricted radii. -/
theorem eventually_norm_core_count_change_le :
    ∀ᶠ j : ℕ in atTop, ∀ u y : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*
        (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
          coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount (j-9)))‖ ≤
        (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
          (49999/50000 : ℝ)^dyadicMomentOrder j := by
  filter_upwards [eventually_norm_high_core_le] with j hj
  intro u y hu hU
  rw [coreResponse_sub_count _ _ _ _ _ (show dyadicPrimeCount (j-9) ≤ dyadicPrimeCount j by
    unfold dyadicPrimeCount
    exact pow_le_pow_right₀ (by norm_num) (by omega))]
  exact hj u y hu hU

/-- A direct signed inequality for the WHOLE retained core. Only the
paid high-count labels have been removed. The complete signed low-count
sum, including the central allocation transition, remains together. -/
theorem eventually_re_core_ge_smaller_count :
    ∀ᶠ j : ℕ in atTop, ∀ u y : ℝ, 0 ≤ u → u ≤ radiusCeiling →
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).re-
          (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
            (49999/50000 : ℝ)^dyadicMomentOrder j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_norm_core_count_change_le] with j hj
  intro u y hu hU
  have h := hj u y hu hU
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    ((u : ℂ)^(dyadicMomentOrder j+1)*
      (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount (j-9)))))).1
  rw [mul_sub] at h
  rw [mul_sub,Complex.sub_re] at hr
  linarith

/-- The explicit allowance tends to zero; no separate component floor
or exposed-zero hypothesis is used to pay the count reduction. -/
theorem tendsto_count_allowance :
    Tendsto (fun j => (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
      (49999/50000 : ℝ)^dyadicMomentOrder j) atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 49999/50000)
    (by norm_num : (49999/50000 : ℝ) < 1)).comp tendsto_dyadicMomentOrder
  have ht := h.const_mul (32*radiusCeiling*Real.log 2)
  simpa only [Function.comp_def,mul_assoc,mul_zero] using ht

/-- The new deletion error vanishes even for moving heights and radii.
This transfers any future joint signed floor without inserting one as a
premise of the arithmetic estimate. -/
theorem tendsto_core_count_change (u y : ℕ → ℝ)
    (hu : ∀ j, 0 ≤ u j) (hU : ∀ j, u j ≤ radiusCeiling) :
    Tendsto (fun j => (u j : ℂ)^(dyadicMomentOrder j+1)*
      (coreResponse (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount j)-
        coreResponse (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount (j-9))))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ tendsto_count_allowance
  filter_upwards [eventually_norm_core_count_change_le] with j hj
  exact hj (u j) (y j) (hu j) (hU j)

/-- The user's original JOINT target is source-equivalent to the same
core with the smaller count endpoint, through independently paid errors.
Neither the packet nor its complementary carrier is estimated separately. -/
theorem tendsto_joint_sub_smaller_count {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)+
        ZetaRieszLeastBoundary.rest u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount (j-9))))
      atTop (𝓝 0) := by
  have h := ((ZetaRieszJointFloor.tendsto_nondominant_sub_core hu hU y).sub
    (ZetaRieszJointFloor.tendsto_nondominant_sub_joint hu hU y)).add
      (tendsto_core_count_change (fun _ => u) (fun _ => y) (fun _ => hu) (fun _ => hU))
  simp only [sub_zero,zero_add] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- On the newly retained count range, every divisor made of primes at
most N squared spends at most N/2048 of logarithm. No small prime or its
phase is deleted by this support theorem. -/
theorem reduced_smooth_divisor_log_le (j : ℕ) (hj : 64 ≤ j) {a n : ℕ}
    (hn : Squarefree n) (had : a ∣ n)
    (hc : n.primeFactors.card < dyadicPrimeCount (j-9))
    (ha : ∀ p ∈ a.primeFactors, p ≤ (dyadicMomentOrder j)^2) :
    Real.log a ≤ (dyadicMomentOrder j : ℝ)/2048 := by
  have has := hn.squarefree_of_dvd had
  have hsub : a.primeFactors ⊆ n.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans had,hn.ne_zero⟩
  have hcard : (a.primeFactors.card : ℝ) ≤ dyadicPrimeCount (j-9) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Nat.le_of_lt hc)
  have hb : Real.log a ≤ (a.primeFactors.card : ℝ)*(2*Real.log (dyadicMomentOrder j)) := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum has]
    calc
      _ ≤ ∑ _p ∈ a.primeFactors, 2*Real.log (dyadicMomentOrder j) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
          (by exact_mod_cast ha p hp : (p : ℝ) ≤ ((dyadicMomentOrder j)^2 : ℕ))
        simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using h
      _ = _ := by simp
  have hlog := ZetaRieszMaskSupport.log_dyadicMoment_le j (by omega)
  have hprod := mul_le_mul hcard
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : (0 : ℝ) ≤ 2*Real.log (dyadicMomentOrder j))
    (Nat.cast_nonneg (dyadicPrimeCount (j-9)))
  have hN : (dyadicMomentOrder j : ℝ) =
      4096*((j : ℝ)+4)*(dyadicPrimeCount (j-9) : ℝ) := by
    rw [dyadicMomentOrder,← reduced_count_factor j (by omega)]
    push_cast
    ring
  rw [hN]
  nlinarith

end
end RiemannGaussian.ZetaRieszJointCountFloor
