/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWeightedCount
import RiemannGaussian.ZetaRieszBalancedCompanion

/-!
# Paying the balanced off-mask companion correction

After the whole high-count correction is removed, the complete balanced off-mask correction also vanishes independently. The exact original coefficients, source and positive reserve remain. The joint real floor is open.
-/

namespace RiemannGaussian.ZetaRieszCompanionMask
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency

open ZetaRieszBalancedCompanion
open ZetaRieszWeightedCount

/-- The exact original lower-count arithmetic mask inside the reserve logarithmic window. -/
def originalMask (u : ℝ) (N K : ℕ) : Finset ℕ :=
  LogarithmicDeviation.deviationBand (ZetaRieszHarmonicWindow.fewBand u N K) (7/4) (9/4) N

/-- The lower-count companion correction outside the original mask whose eligible selected primes are balanced. -/
def balancedOffMask (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (lowCountBand u N K).filter (fun n => n ∉ originalMask u N K ∧
    ∀ p ∈ n.primeFactors, p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N →
      eligibleCofactor p (n/p) → Real.log p ≤ Real.log n/2)

/-- The surviving lower-count support after only the independently bounded balanced off-mask correction is removed. -/
def residualMaskBand (u : ℝ) (N K : ℕ) : Finset ℕ := lowCountBand u N K \ balancedOffMask u N K

/-- The original signed finite coefficients on the surviving support after balanced mask correction. -/
def residualMaskResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ residualMaskBand u N K, finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The discarded mask correction is exactly minus the complete assigned coefficient on its literal balanced support. -/
theorem lowCount_sub_mask (u y : ℝ) (N K : ℕ) :
    lowCountResponse u y N K - residualMaskResponse u y N K =
      -(∑ n ∈ balancedOffMask u N K,
        assignedCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  have hsub : balancedOffMask u N K ⊆ lowCountBand u N K := Finset.filter_subset _ _
  have hs := Finset.sum_sdiff
    (f := fun n => finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) hsub
  have he : (∑ n ∈ balancedOffMask u N K,
      finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      -(∑ n ∈ balancedOffMask u N K,
        assignedCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).2.1
    change n ∉ LogarithmicDeviation.deviationBand (ZetaRieszHarmonicWindow.fewBand u N K) (7/4) (9/4) N at hnS
    simp only [finiteCoefficient, finiteWeight, if_neg hnS, zero_sub,
      assignedCoefficient, Complex.ofReal_neg, neg_mul]
  dsimp only [lowCountResponse, residualMaskResponse, residualMaskBand]
  linear_combination -hs + he

/-- The entire balanced off-mask correction has a height-uniform source-scale geometric allowance. -/
theorem balancedOffMask_bound (N K : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    ‖(u:ℂ)^(N+1) * (lowCountResponse u y N K - residualMaskResponse u y N K)‖ ≤
      (4*((N:ℝ)+1)/3) * (sectorRate^N *
        ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  rw [lowCount_sub_mask, mul_neg, norm_neg]
  exact balanced_companion_bound _ _ (SquarefreeVaughanLogSource.length_pos u N) N
    (fun n hn => (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1)
    (fun n hn => (Finset.mem_filter.mp hn).2.2) y hu huU

/-- The source-normalized residual after the high-count and balanced off-mask corrections have been paid. -/
def residualMaskRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u:ℂ)^(dyadicMomentOrder j+1) * residualMaskResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- Removing the balanced off-mask correction loses only an independently vanishing error on the original dyadic schedule. -/
theorem tendsto_lowCount_sub_mask (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => lowCountRemainder u y j - residualMaskRemainder u y j) atTop (𝓝 0) := by
  have hr : 0 < sectorRate := by unfold sectorRate; positivity
  have ht := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hr sectorRate_bounds.2).comp
    tendsto_dyadicMomentOrder).mul_const ((4/3:ℝ)*((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
  simp only [Function.comp_def, pow_one, zero_mul] at ht
  apply squeeze_zero_norm (a := fun j : ℕ => ((dyadicMomentOrder j:ℝ)+1)*sectorRate^(dyadicMomentOrder j) *
    ((4/3:ℝ)*((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) ?_ ht
  intro j
  dsimp only [lowCountRemainder, residualMaskRemainder]
  rw [← mul_sub]
  exact (balancedOffMask_bound (dyadicMomentOrder j) (dyadicPrimeCount j) y hu huU).trans_eq (by ring)

/-- The unchanged exposed-zero source and positive reserve survive both proved mask corrections; the joint floor remains open. -/
theorem tendsto_mask_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im:ℂ))-tau.1‖)
    (huh : 3/2-rho.1.re < Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => residualMaskRemainder (3/2-rho.1.re) rho.1.im j +
      ((3/2-rho.1.re:ℝ):ℂ)^(dyadicMomentOrder j+1) *
        ZetaRieszWingReserve.reserve (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho:ℂ) + (analyticZetaZeroMultiplicity rho:ℂ)^2 *
        (RieszHarmonicCostBounds.paidHarmonicCost (3/2-rho.1.re):ℂ))) := by
  have hu : 0 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he := tendsto_lowCount_sub_mask rho.1.im hu huh.le
  have hs := (tendsto_lowCount_add_reserve rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall (fun _ => by ring))


end
end RiemannGaussian.ZetaRieszCompanionMask
