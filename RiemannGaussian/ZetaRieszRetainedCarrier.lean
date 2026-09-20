/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMaskSupport

/-!
# The remaining signed carrier has no separate off-mask correction

The complete high-count and balanced off-mask errors have been paid, and the remaining mask comparison is exact eventually. The live carrier is the original signed Riesz coefficient times a fraction between zero and one, on its original lower-count support minus the proved cancellation sector. The source and reserve survive; the joint floor remains open.
-/

namespace RiemannGaussian.ZetaRieszMaskSupport

noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszGeneralCofactorTilt ZetaRieszCofactorTiltRate
open ZetaRieszCompanionMask ZetaRieszWeightedCount

/-- The original lower-count arithmetic support with only the proved allocation-cancellation sector removed. -/
def retainedBand (u : ℝ) (N K : ℕ) : Finset ℕ := originalMask u N K \ cancellingSector u N K

/-- The original signed Riesz coefficient times its nonnegative unassigned fraction on the retained original support. -/
def retainedResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ retainedBand u N K,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n * zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The retained original support lies in the residual after both independently paid mask corrections. -/
theorem retainedBand_subset (u : ℝ) (N K : ℕ) :
    retainedBand u N K ⊆ residualMaskBand u N K := by
  intro n hn
  obtain ⟨hnS,hnC⟩ := Finset.mem_sdiff.mp hn
  have hnW : n ∈ literalWindow N := (mem_literalWindow N n).mpr (Finset.mem_filter.mp hnS).2
  have hcount : n.primeFactors.card<K := (Finset.mem_filter.mp (Finset.mem_filter.mp hnS).1).2.2
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hnW,hnC⟩,hcount⟩,?_⟩
  intro hm
  exact (Finset.mem_filter.mp hm).2.1 hnS

/-- Every remaining off-mask coefficient vanishes exactly once the proved size conditions hold; no signed correction is omitted. -/
theorem residualMask_eq_retained (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ)))
    (hLlo : (5/4:ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (y : ℝ) :
    residualMaskResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j) =
      retainedResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  have hz : ∀ n ∈ residualMaskBand u N K, n ∉ retainedBand u N K →
      finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n=0 := by
    intro n hn hnot
    suffices h : finiteCoefficient u N K n=0 by rw [h,zero_mul]
    by_contra hc
    have hnS := residual_nonzero_mem_original j hj hu huh hLlo hn hc
    have hnC : n ∉ cancellingSector u N K :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).1).2
    exact hnot (Finset.mem_sdiff.mpr ⟨hnS,hnC⟩)
  have he := Finset.sum_subset (retainedBand_subset u N K) hz
  change (∑ n ∈ residualMaskBand u N K, _)=_
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  have hnS := (Finset.mem_sdiff.mp hn).1
  have hc : finiteCoefficient u N K n = residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n := by
    rw [finiteCoefficient_eq_mask_sub_assigned,if_pos hnS]
    unfold residualCoefficient assignedCoefficient
    push_cast
    ring
  rw [hc]

/-- The literal damped physical length eventually exceeds five quarters of the moment order throughout the reserve range. -/
theorem eventually_length_lower {u : ℝ} (hu : 0<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) :
    ∀ᶠ N : ℕ in atTop, (5/4:ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
  have hr : 1 ≤ Real.exp (5/8:ℝ) := Real.one_le_exp (by norm_num)
  have hur : u*Real.exp (5/8:ℝ)<1 := by
    have h := mul_le_mul_of_nonneg_right huh (Real.exp_pos (5/8:ℝ)).le
    rw [← Real.exp_add] at h
    exact h.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have h := ZetaRieszExtremePrimeCount.eventually_length_ge_tilt hu hr hur
  norm_num only [Real.log_exp] at h
  convert h using 1

/-- The source-normalized retained carrier with only nonnegative unassigned multipliers on its original support. -/
def retainedRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u:ℂ)^(dyadicMomentOrder j+1) * retainedResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- All completion, allocation-sector, high-count and mask corrections vanish
together for arbitrary moving heights. This is an independent arithmetic
estimate for the difference, with no zero or signed-floor hypothesis. -/
theorem tendsto_arithmetic_sub_retained_moving (y : ℕ → ℝ) {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => ZetaRieszJointCofactor.arithmeticRemainder u (y j) j -
      retainedRemainder u (y j) j) atTop (𝓝 0) := by
  have hu0 : 0 ≤ u := by linarith
  have houter : Tendsto (fun j => ZetaRieszJointCofactor.arithmeticRemainder u (y j) j -
      finiteRemainder u (y j) j) atTop (𝓝 0) := by
    obtain ⟨r,C,hr0,hr1,_hC,hb⟩ := exists_finiteResponse_error
    have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      tendsto_dyadicMomentOrder).mul_const C
    simp only [Function.comp_def, zero_mul] at ht
    apply squeeze_zero_norm (fun j => ?_) ht
    have h := hb (dyadicMomentOrder j) (dyadicPrimeCount j) (y j) u hu0 huh
    dsimp only [ZetaRieszJointCofactor.arithmeticRemainder, finiteRemainder]
    simpa only [mul_sub] using h
  have hsector : Tendsto (fun j => finiteRemainder u (y j) j -
      remainingRemainder u (y j) j) atTop (𝓝 0) := by
    have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one
      sectorRate_bounds.1 sectorRate_bounds.2).comp tendsto_dyadicMomentOrder).mul_const
        ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))
    simp only [Function.comp_def, zero_mul] at ht
    apply squeeze_zero_norm' (a := fun j => sectorRate^(dyadicMomentOrder j) *
      ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) ?_ ht
    filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 320)] with j hj
    dsimp only [finiteRemainder, remainingRemainder]
    rw [← mul_sub, finite_sub_remaining]
    exact actual_sector_geometric (dyadicMomentOrder j) (dyadicPrimeCount j) hj (y j) hu0 huh
  have hcount : Tendsto (fun j => remainingRemainder u (y j) j -
      lowCountRemainder u (y j) j) atTop (𝓝 0) := by
    have hU : Real.exp (-(11/16:ℝ)) < 17/32 := radius_ceiling.trans_lt (by norm_num)
    have ht := tendsto_remaining_sub_lowCount (fun _ => u) y (fun _ => hu0)
      (fun _ => huh) (Real.exp_pos _) hU
    simpa only [remainingRemainder, lowCountRemainder, mul_sub] using ht
  have hmask : Tendsto (fun j => lowCountRemainder u (y j) j -
      residualMaskRemainder u (y j) j) atTop (𝓝 0) := by
    have hr : 0 < sectorRate := by unfold sectorRate; positivity
    have ht := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
      1 hr sectorRate_bounds.2).comp tendsto_dyadicMomentOrder).mul_const
        ((4/3:ℝ)*((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
    simp only [Function.comp_def, pow_one, zero_mul] at ht
    apply squeeze_zero_norm (a := fun j => ((dyadicMomentOrder j:ℝ)+1)*
      sectorRate^(dyadicMomentOrder j) *
        ((4/3:ℝ)*((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) ?_ ht
    intro j
    dsimp only [lowCountRemainder, residualMaskRemainder]
    rw [← mul_sub]
    exact (balancedOffMask_bound (dyadicMomentOrder j) (dyadicPrimeCount j)
      (y j) hu0 huh).trans_eq (by ring)
  have htotal := ((houter.add hsector).add hcount).add hmask
  simp only [add_zero] at htotal
  apply htotal.congr'
  filter_upwards [eventually_ge_atTop 32,
    tendsto_dyadicMomentOrder.eventually (eventually_length_lower (by linarith) huh)] with j hj hL
  have he : residualMaskRemainder u (y j) j = retainedRemainder u (y j) j := by
    dsimp only [residualMaskRemainder, retainedRemainder]
    rw [residualMask_eq_retained j hj hu huh hL]
  rw [he]
  ring

/-- One starting order controls the entire real height axis for every
positive error tolerance. The retained sum itself is not bounded here. -/
theorem eventually_all_heights_arithmetic_error {u ε : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (hε : 0<ε) :
    ∀ᶠ j in atTop, ∀ y : ℝ,
      ‖ZetaRieszJointCofactor.arithmeticRemainder u y j - retainedRemainder u y j‖ < ε := by
  by_contra h
  have hf : ∃ᶠ j in atTop, ∃ y : ℝ,
      ε ≤ ‖ZetaRieszJointCofactor.arithmeticRemainder u y j - retainedRemainder u y j‖ := by
    simpa only [not_forall, not_lt] using (not_eventually.mp h)
  let y (j : ℕ) : ℝ := if hj : ∃ t : ℝ,
      ε ≤ ‖ZetaRieszJointCofactor.arithmeticRemainder u t j - retainedRemainder u t j‖
    then Classical.choose hj else 0
  have hbad : ∃ᶠ j in atTop,
      ε ≤ ‖ZetaRieszJointCofactor.arithmeticRemainder u (y j) j - retainedRemainder u (y j) j‖ := by
    apply hf.mono
    intro j hj
    simpa only [y, dif_pos hj] using Classical.choose_spec hj
  have ht := (tendsto_arithmetic_sub_retained_moving y hu huh).norm
  simp only [norm_zero] at ht
  have hsmall : ∀ᶠ j in atTop,
      ‖ZetaRieszJointCofactor.arithmeticRemainder u (y j) j - retainedRemainder u (y j) j‖ < ε := by
    exact ht.eventually (eventually_lt_nhds hε)
  obtain ⟨j,hj,hj'⟩ := (hbad.and_eventually hsmall).exists
  exact (not_lt_of_ge hj) hj'

/-- The complete original mask correction is discharged and the exact source plus positive reserve survives; the joint arithmetic floor remains open. -/
theorem tendsto_retained_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im:ℂ))-tau.1‖)
    (huh : 3/2-rho.1.re < Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => retainedRemainder (3/2-rho.1.re) rho.1.im j +
      ((3/2-rho.1.re:ℝ):ℂ)^(dyadicMomentOrder j+1) *
        ZetaRieszWingReserve.reserve (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho:ℂ) + (analyticZetaZeroMultiplicity rho:ℂ)^2 *
        (RieszHarmonicCostBounds.paidHarmonicCost (3/2-rho.1.re):ℂ))) := by
  have hu : 1/2 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he := tendsto_arithmetic_sub_retained_moving (fun _ => rho.1.im) hu huh.le
  have hs := (ZetaRieszJointCofactor.tendsto_arithmeticRemainder_add_reserve
    rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall (fun _ => by ring))


end
end RiemannGaussian.ZetaRieszMaskSupport
