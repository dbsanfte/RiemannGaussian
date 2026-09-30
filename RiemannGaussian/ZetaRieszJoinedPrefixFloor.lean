/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSaturatedCoreFloor
import RiemannGaussian.ZetaRieszSevenPrimeReflection
import RiemannGaussian.ZetaRieszSevenCountTail

/-!
# Cutoff cancellation in the compensated physical floor

The prefix and saturation savings are spent only on the unpaid remainder
of `eventually_core_full_floor`. All radial payments, exact signed low-count
observations, and the unspent 1/64 of the four-prime supply remain. This
strengthens the previous seven-prime floor on the same labels and phases.
The remaining signed budget is not bounded by 79/1000.
-/

namespace RiemannGaussian.ZetaRieszJoinedPrefixFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszReflectedPrimeBounds ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszLeastOrderOverflow
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation
open ZetaRieszFourPrimeHead ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead
open ZetaRieszSevenCountTail ZetaRieszAnnulusJoint

/-- An exact reduction of an existing charge, not an additional population
of favorable atoms. The previous seven-prime saving is already included. -/
def cutoffSaving (L y : ℝ) (n : ℕ) : ℝ :=
  max (ZetaRieszSevenPrimeReflection.floorCost L y n-
    ZetaRieszSaturatedCoreFloor.floorCost L y n) 0

theorem cutoffSaving_nonneg (L y : ℝ) (n : ℕ) : 0 ≤ cutoffSaving L y n :=
  le_max_right _ _

theorem cutoffSaving_le_previous {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    cutoffSaving L y n ≤ ZetaRieszSevenPrimeReflection.floorCost L y n := by
  apply max_le
  · linarith [ZetaRieszSaturatedCoreFloor.floorCost_nonneg hL y n]
  · unfold ZetaRieszSevenPrimeReflection.floorCost
    positivity [ZetaRieszSevenPrimeReflection.lowerAllowance_nonneg hL n,
      ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 1]

/-- A cancelled label returns its entire old adverse charge. Its actual
contribution is zero, so this statement does not double-count supply. -/
theorem cutoffSaving_eq_previous_of_saturation {L : ℝ} (hL : 0 < L)
    (y : ℝ) {n : ℕ}
    (h : ZetaRieszSaturatedCoreFloor.SaturatedActive L n ∨
      ZetaRieszSaturatedCoreFloor.ReflectedPrefixSaturated L n) :
    cutoffSaving L y n = ZetaRieszSevenPrimeReflection.floorCost L y n := by
  rw [cutoffSaving,ZetaRieszSaturatedCoreFloor.floorCost,if_pos h,sub_zero]
  apply max_eq_left
  unfold ZetaRieszSevenPrimeReflection.floorCost
  positivity [ZetaRieszSevenPrimeReflection.lowerAllowance_nonneg hL n,
    ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 1]

/-- Prime-prefix cancellation likewise removes the entire previous charge
on its favorable phase, for every total count covered by the prefix identity. -/
theorem cutoffSaving_eq_previous_of_prefix {L : ℝ} (hL : 0 < L)
    (y : ℝ) {n : ℕ} (h : ZetaRieszSaturatedCoreFloor.TwoOuterPrimePrefix L n)
    (hp : ZetaRieszSaturatedCoreFloor.primePrefixResponse L n ≤ 0)
    (hc : 0 ≤ Real.cos (y*Real.log n)) :
    cutoffSaving L y n = ZetaRieszSevenPrimeReflection.floorCost L y n := by
  rw [cutoffSaving,ZetaRieszSaturatedCoreFloor.floorCost_eq_zero_of_prefix_credit
    hL y h hp hc,sub_zero]
  apply max_eq_left
  unfold ZetaRieszSevenPrimeReflection.floorCost
  positivity [ZetaRieszSevenPrimeReflection.lowerAllowance_nonneg hL n,
    ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 1]

/-- In the unit-prefix layer the new charge is no larger than the exact
short-cutoff charge, even if either saturation test already cancels it. -/
theorem prefix_cost_le_inner {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : ZetaRieszSaturatedCoreFloor.TwoOuterInner L n) :
    ZetaRieszSaturatedCoreFloor.floorCost L y n ≤
      ZetaRieszSaturatedCoreFloor.innerFloorCost L y n := by
  have hp : ZetaRieszSaturatedCoreFloor.TwoOuterPrimePrefix L n :=
    ⟨h.1,h.2.1,h.2.2.1,by
      have := h.2.2.2
      linarith [Real.log_natCast_nonneg (activePart (Real.log n-L) n).minFac]⟩
  unfold ZetaRieszSaturatedCoreFloor.floorCost
  split_ifs
  · unfold ZetaRieszSaturatedCoreFloor.innerFloorCost
    positivity [Real.log_natCast_nonneg n]
  · exact (ZetaRieszSaturatedCoreFloor.primePrefixFloorCost_eq_inner hL y h).le

/-- A numerical improvement against the OPTIMIZED seven-prime charge:
if the remaining cutoff is at most a quarter of the least-prime logarithm,
at least three quarters of that charge is removed, for either phase.
The condition is on the literal logarithms, not limiting shares. -/
theorem cutoffSaving_ge_three_quarters {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : ZetaRieszSaturatedCoreFloor.TwoOuterInner L n)
    (hc : n.primeFactors.card = 7)
    (hg : 4*max 0 (L-Real.log (outerPart (Real.log n-L) n)) ≤ Real.log n.minFac) :
    (3/4 : ℝ)*ZetaRieszSevenPrimeReflection.floorCost L y n ≤ cutoffSaving L y n := by
  have hq : ZetaRieszSaturatedCoreFloor.floorCost L y n ≤
      (1/4 : ℝ)*ZetaRieszSevenPrimeReflection.floorCost L y n := by
    apply (prefix_cost_le_inner hL y h).trans
    have ha := (ZetaRieszSevenPrimeReflection.previous_seven_allowances hL h.1 hc h.2.2.1).2
    have hb : 0 ≤ Real.log n/L*Real.log n.minFac :=
      mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
        (Real.log_natCast_nonneg n.minFac)
    have hgm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg (div_nonneg (Real.log_natCast_nonneg n) hL.le))
      (show 0 ≤ max (Real.cos (y*Real.log n)) 0 from le_max_right _ _)
    unfold ZetaRieszSaturatedCoreFloor.innerFloorCost ZetaRieszSevenPrimeReflection.floorCost
    rw [ZetaRieszSevenPrimeReflection.seven_lowerAllowance_eq hL h.1 hc h.2.2.1,ha]
    nlinarith only [hgm,mul_nonneg hb (le_max_right (-Real.cos (y*Real.log n)) 0)]
  have hs : ZetaRieszSevenPrimeReflection.floorCost L y n-
      ZetaRieszSaturatedCoreFloor.floorCost L y n ≤ cutoffSaving L y n := le_max_left _ _
  linarith

/-- The three-quarter saving is summed with the LITERAL allocation and
factorial weights. It can be spent on any matching subset of the unpaid
remainder; no assertion about the density of that subset is needed. -/
theorem weighted_saving_ge_three_quarters (S T A : Finset ℕ) (N : ℕ)
    {L : ℝ} (hL : 0 < L) (y : ℝ) (hTS : T ⊆ S)
    (hT : ∀ n ∈ T, ZetaRieszSaturatedCoreFloor.TwoOuterInner L n ∧
      n.primeFactors.card = 7 ∧
      4*max 0 (L-Real.log (outerPart (Real.log n-L) n)) ≤ Real.log n.minFac) :
    (3/4 : ℝ)*(∑ n ∈ T, weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n) ≤
      ∑ n ∈ S.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
        weight A N n*cutoffSaving L y n := by
  calc
    _ ≤ ∑ n ∈ T, weight A N n*cutoffSaving L y n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hi,hc,hg⟩ := hT n hn
      have hh := mul_le_mul_of_nonneg_left
        (cutoffSaving_ge_three_quarters hL y hi hc hg) (weight_nonneg A N n)
      nlinarith only [hh]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro n hn
      exact Finset.mem_filter.mpr ⟨hTS hn,by have := (hT n hn).2.1; omega⟩)
      (fun n _ _ => mul_nonneg (weight_nonneg A N n) (cutoffSaving_nonneg L y n))

/-- Both bounds concern the SAME real observation. Their charge reduction
can therefore be added to the old floor without spending another atom. -/
theorem residual_floor_with_saving (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : 5 ≤ n.primeFactors.card)
    (hcut : 2*Real.log n ≤ 3*L) (hq : Real.log n < 4*(Real.log n-L))
    (htwo : 2*Real.log n ≤ 7*(Real.log n-L)) :
    let v := (residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n+
      weight A N n*cutoffSaving L y n ≤ v := by
  dsimp only
  have hold := (ZetaRieszSevenPrimeReflection.residual_retained_bounds
    A hL y N hc hcut hq htwo).1
  have hnew := ZetaRieszSaturatedCoreFloor.residual_retained_floor A hL y N n
  unfold cutoffSaving
  by_cases h : ZetaRieszSaturatedCoreFloor.floorCost L y n ≤
      ZetaRieszSevenPrimeReflection.floorCost L y n
  · rw [max_eq_left (sub_nonneg.mpr h)]
    nlinarith only [hnew]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),mul_zero,add_zero]
    exact hold

/-- The saving is supported only on whichever remainder the caller retains.
All low-count terms remain signed and exact; no old compensated sector is
charged by this theorem. -/
theorem eventually_core_subset_floor {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*((∑ n ∈ S, if 7 ≤ n.primeFactors.card then
        max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re)+
        ∑ n ∈ S.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*cutoffSaving L y n) ≤ ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hcut hN K y S hS
  dsimp only
  rw [Finset.sum_filter,← Finset.sum_add_distrib,← Complex.ofReal_pow,
    Complex.re_ofReal_mul,Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) _)
  apply Finset.sum_le_sum
  intro n hn
  split_ifs with hc
  · exact residual_floor_with_saving _ (SquarefreeVaughanLogSource.length_pos u N) y N
      (by omega) (hcut K n (hS hn)) (core_cutoff_quarter hu.le hN (hS hn))
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu.le hN (hS hn)).le
  · simp only [add_zero,le_refl]

/-- The new cancellation improves the ACTUAL joined physical floor after
all existing radial payments. The nonnegative G is charged only to the
unpaid rest; the old seven-prime credit and unspent 1/64 supply are retained.
No floor constant or zero hypothesis is assumed, and -79/1000 is not claimed. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ θ : ℝ, ∃ err : ℕ → ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      0 < θ ∧ θ ≤ 1/128 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let Gs := radialHeads S N P V L
        let Ts := radialTail S N R
        let Ys := radialSupply N h v
        let B := wholeTail S N R
        let E := S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B)
        let W := ∑ n ∈ E, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*cutoffSaving L y n
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-err j ≤
          ((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j))).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hr,hr1,hC,hbase⟩ :=
    ZetaRieszSevenCountTail.eventually_core_full_floor hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,tendsto_dyadicMomentOrder.eventually
    (eventually_core_subset_floor hu hU)] with j hj hbound
  obtain ⟨v,hvb,hY,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let Ts := radialTail S N R
  let Ys := radialSupply N h v
  let B := wholeTail S N R
  let E := S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B)
  let W := ∑ n ∈ E, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*cutoffSaving L y n
  have hE : E ⊆ coreBand u N (dyadicPrimeCount j) := Finset.sdiff_subset
  have hb := hbound (dyadicPrimeCount j) y E hE
  dsimp only at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ =>
    mul_nonneg (weight_nonneg A N n) (cutoffSaving_nonneg L y n))
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  refine ⟨v,hvb,hY,hG,?_⟩
  change u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-(r^N*C+e j) ≤ ((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j))).re
  change u^(N+1)*(W+G) ≤ u^(N+1)*(∑ n ∈ E, f n).re at hb
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j))).re ≤ e j at hbridge
  nlinarith only [hcore,hb,hbridge]

end
end RiemannGaussian.ZetaRieszJoinedPrefixFloor
