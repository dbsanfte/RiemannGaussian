/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSevenPrimeReflection
import RiemannGaussian.ZetaRieszSevenCountTail
import RiemannGaussian.ZetaRieszJointFloor

/-!
# Second-reflection savings in the whole joint floor and ceiling

The old radial payments and the original signed complementary population
are kept together. The new seven-prime saving is spent only on the unpaid
rest, and is transferred to the same `J+C` used by the multiplicity-aware
endgame. No estimate on an isolated packet is substituted for the joint sum.
-/

namespace RiemannGaussian.ZetaRieszJointReflectionBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszReflectedPrimeBounds ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszLeastOrderOverflow
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation
open ZetaRieszFourPrimeHead ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead
open ZetaRieszSevenCountTail

/-- The exact charge reduction is supported only on the genuine
squarefree seven-prime/two-reflected-large sector. -/
theorem cost_savings_exact {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    ZetaRieszReflectedPrimeBounds.floorCost L y n-ZetaRieszSevenPrimeReflection.floorCost L y n =
      (if Squarefree n ∧ n.primeFactors.card = 7 ∧ (outerPrimes (Real.log n-L) n).card = 2 then
        2*(Real.log n/L*Real.log n.minFac)*max (Real.cos (y*Real.log n)) 0 else 0) ∧
    ZetaRieszReflectedPrimeBounds.ceilingCost L y n-ZetaRieszSevenPrimeReflection.ceilingCost L y n =
      (if Squarefree n ∧ n.primeFactors.card = 7 ∧ (outerPrimes (Real.log n-L) n).card = 2 then
        2*(Real.log n/L*Real.log n.minFac)*max (-Real.cos (y*Real.log n)) 0 else 0) := by
  by_cases hs : Squarefree n
  · by_cases h : n.primeFactors.card = 7 ∧ (outerPrimes (Real.log n-L) n).card = 2
    · have hh : Squarefree n ∧ n.primeFactors.card = 7 ∧
          (outerPrimes (Real.log n-L) n).card = 2 := ⟨hs,h⟩
      simp only [if_pos hh]
      exact ZetaRieszSevenPrimeReflection.seven_cost_savings hL y hs h.1 h.2
    · have hh : ¬ (Squarefree n ∧ n.primeFactors.card = 7 ∧
          (outerPrimes (Real.log n-L) n).card = 2) := fun ha => h ha.2
      simp only [if_neg hh,ZetaRieszSevenPrimeReflection.floorCost,
        ZetaRieszSevenPrimeReflection.ceilingCost,ZetaRieszSevenPrimeReflection.lowerAllowance,
        if_neg h,ZetaRieszReflectedPrimeBounds.floorCost,ZetaRieszReflectedPrimeBounds.ceilingCost,sub_self]
      exact ⟨trivial,trivial⟩
  · have hz (b : ℕ) : ZetaRieszReflectedPrimeBounds.allowance L n b = 0 := by
      simp [ZetaRieszReflectedPrimeBounds.allowance,previousAllowance,activeAllowance,
        ZetaRieszComplementWindow.allowance,ZetaRieszIntersectingWindow.allowance,hs]
    have hb : 0 ≤ Real.log n/L*Real.log n.minFac :=
      mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (Real.log_natCast_nonneg n.minFac)
    have hnew : ZetaRieszSevenPrimeReflection.lowerAllowance L n = 0 := by
      simp only [ZetaRieszSevenPrimeReflection.lowerAllowance,hz,min_eq_left hb]
      split_ifs <;> rfl
    simp only [hs,false_and,if_false,ZetaRieszSevenPrimeReflection.floorCost,
      ZetaRieszSevenPrimeReflection.ceilingCost,ZetaRieszReflectedPrimeBounds.floorCost,
      ZetaRieszReflectedPrimeBounds.ceilingCost,hnew,hz,zero_mul,zero_add,sub_self,and_self]

/-- Summing first gives an exact improvement of the two finite signed
observations, for arbitrary original real atoms. The saving is not applied
to any population already removed by a payment. -/
theorem sum_observation_savings (S A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (y : ℝ) (v : ℕ → ℝ) :
    let E := S.filter (fun n : ℕ => Squarefree n ∧ n.primeFactors.card = 7 ∧
      (outerPrimes (Real.log n-L) n).card = 2)
    (∑ n ∈ S, if 7 ≤ n.primeFactors.card then
      max (v n) 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else v n) =
      (∑ n ∈ S, if 7 ≤ n.primeFactors.card then
        max (v n) 0-weight A N n*ZetaRieszReflectedPrimeBounds.floorCost L y n else v n)+
        2*∑ n ∈ E, weight A N n*(Real.log n/L*Real.log n.minFac)*max (Real.cos (y*Real.log n)) 0 ∧
    (∑ n ∈ S, if 7 ≤ n.primeFactors.card then
      min (v n) 0+weight A N n*ZetaRieszSevenPrimeReflection.ceilingCost L y n else v n) =
      (∑ n ∈ S, if 7 ≤ n.primeFactors.card then
        min (v n) 0+weight A N n*ZetaRieszReflectedPrimeBounds.ceilingCost L y n else v n)-
        2*∑ n ∈ E, weight A N n*(Real.log n/L*Real.log n.minFac)*max (-Real.cos (y*Real.log n)) 0 := by
  dsimp only
  simp only [Finset.sum_filter,Finset.mul_sum]
  constructor
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hh := congrArg (fun x : ℝ => weight A N n*x) (cost_savings_exact hL y n).1
    by_cases h : Squarefree n ∧ n.primeFactors.card = 7 ∧ (outerPrimes (Real.log n-L) n).card = 2
    · have hc : 7 ≤ n.primeFactors.card := by omega
      simp only [if_pos h,if_pos hc] at hh ⊢
      nlinarith only [hh]
    · simp only [if_neg h,mul_zero] at hh ⊢
      split_ifs <;> linarith only [hh]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hh := congrArg (fun x : ℝ => weight A N n*x) (cost_savings_exact hL y n).2
    by_cases h : Squarefree n ∧ n.primeFactors.card = 7 ∧ (outerPrimes (Real.log n-L) n).card = 2
    · have hc : 7 ≤ n.primeFactors.card := by omega
      simp only [if_pos h,if_pos hc] at hh ⊢
      nlinarith only [hh]
    · simp only [if_neg h,mul_zero] at hh ⊢
      split_ifs <;> linarith only [hh]

/-- The same old paid boundary error transports both signs from the
whole core to the exact `J+C`; no zero hypothesis or arithmetic premise
is used to make this error vanish. -/
theorem exists_joint_core_error {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ j,
      let N := dyadicMomentOrder j
      let K := dyadicPrimeCount j
      let J := lowerThresholdPacket u y N K-shortOverflowPacket u y N K+
        ZetaRieszLeastBoundary.rest u y N K
      |((u : ℂ)^(N+1)*coreResponse u y N K).re-((u : ℂ)^(N+1)*J).re| ≤ err j := by
  let err := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (ZetaRieszLeastBoundary.fullPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      (lowerThresholdPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
        shortOverflowPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)))‖
  have ht := (tendsto_full_sub_joint_boundary hu hU (fun _ => y)
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
  rw [norm_zero] at ht
  refine ⟨err,fun j => norm_nonneg _,ht,?_⟩
  intro j
  dsimp only
  have he : (u : ℂ)^(dyadicMomentOrder j+1)*coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      (u : ℂ)^(dyadicMomentOrder j+1)*
        (lowerThresholdPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
          shortOverflowPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)+
          ZetaRieszLeastBoundary.rest u y (dyadicMomentOrder j) (dyadicPrimeCount j)) =
      (u : ℂ)^(dyadicMomentOrder j+1)*
        (ZetaRieszLeastBoundary.fullPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
          (lowerThresholdPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
            shortOverflowPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j))) := by
    rw [ZetaRieszLeastBoundary.core_ledger]
    ring
  rw [← Complex.sub_re,he]
  exact Complex.abs_re_le_norm _

/-- The whole joint floor keeps every old radial payment, charges only
its unpaid rest and improves the earlier signed observation by an exact
nonnegative two-unit seven-prime saving. The independent final constant
-79/1000 is not asserted. -/
theorem eventually_joint_floor {u y : ℝ} (hu : 1/2 < u)
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
          max (f n).re 0-weight A N n*ZetaRieszReflectedPrimeBounds.floorCost L y n else (f n).re
        let G := 2*∑ n ∈ E.filter (fun n : ℕ => Squarefree n ∧ n.primeFactors.card = 7 ∧
          (outerPrimes (Real.log n-L) n).card = 2),
          weight A N n*(Real.log n/L*Real.log n.minFac)*max (Real.cos (y*Real.log n)) 0
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-err j ≤
          ((u : ℂ)^(N+1)*(lowerThresholdPacket u y N (dyadicPrimeCount j)-
            shortOverflowPacket u y N (dyadicPrimeCount j)+
            ZetaRieszLeastBoundary.rest u y N (dyadicPrimeCount j))).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hr,hr1,hC,hbase⟩ :=
    ZetaRieszSevenCountTail.eventually_core_full_floor hu hU hy
  obtain ⟨e,he0,heLim,he⟩ := exists_joint_core_error (by linarith : 0 ≤ u) hU y
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSevenPrimeReflection.eventually_core_subset_bounds hu hU)] with j hj hbound
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
    max (f n).re 0-weight A N n*ZetaRieszReflectedPrimeBounds.floorCost L y n else (f n).re
  let G := 2*∑ n ∈ E.filter (fun n : ℕ => Squarefree n ∧ n.primeFactors.card = 7 ∧
    (outerPrimes (Real.log n-L) n).card = 2),
    weight A N n*(Real.log n/L*Real.log n.minFac)*max (Real.cos (y*Real.log n)) 0
  have hE : E ⊆ coreBand u N (dyadicPrimeCount j) := Finset.sdiff_subset
  have hb := (hbound (dyadicPrimeCount j) y E hE).1
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hb
  rw [(sum_observation_savings E A (SquarefreeVaughanLogSource.length_pos u N) N y
    (fun n => (f n).re)).1] at hb
  have hG : 0 ≤ G := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_nonneg
    intro n _
    exact mul_nonneg (mul_nonneg (weight_nonneg A N n)
      (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n)
        (SquarefreeVaughanLogSource.length_pos u N).le) (Real.log_natCast_nonneg n.minFac))) (le_max_right _ _)
  have hbridge := (abs_le.mp (he j)).2
  refine ⟨v,hvb,hY,hG,?_⟩
  change u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-(r^N*C+e j) ≤ ((u : ℂ)^(N+1)*(lowerThresholdPacket u y N (dyadicPrimeCount j)-
            shortOverflowPacket u y N (dyadicPrimeCount j)+
            ZetaRieszLeastBoundary.rest u y N (dyadicPrimeCount j))).re
  change u^(N+1)*(W+G) ≤ u^(N+1)*(∑ n ∈ E, f n).re at hb
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-((u : ℂ)^(N+1)*(lowerThresholdPacket u y N (dyadicPrimeCount j)-
            shortOverflowPacket u y N (dyadicPrimeCount j)+
            ZetaRieszLeastBoundary.rest u y N (dyadicPrimeCount j))).re ≤ e j at hbridge
  nlinarith only [hcore,hb,hbridge]

/-- The whole joint ceiling keeps every old radial payment, charges only
its unpaid rest and improves the earlier signed observation by an exact
nonnegative two-unit seven-prime saving. The independent final constant
3/2 is not asserted. -/
theorem eventually_joint_ceiling {u y : ℝ} (hu : 1/2 < u)
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
          min (f n).re 0+weight A N n*ZetaRieszReflectedPrimeBounds.ceilingCost L y n else (f n).re
        let G := 2*∑ n ∈ E.filter (fun n : ℕ => Squarefree n ∧ n.primeFactors.card = 7 ∧
          (outerPrimes (Real.log n-L) n).card = 2),
          weight A N n*(Real.log n/L*Real.log n.minFac)*max (-Real.cos (y*Real.log n)) 0
        0 < -(∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          ((u : ℂ)^(N+1)*(lowerThresholdPacket u y N (dyadicPrimeCount j)-
            shortOverflowPacket u y N (dyadicPrimeCount j)+
            ZetaRieszLeastBoundary.rest u y N (dyadicPrimeCount j))).re ≤
          u^(N+1)*(W-G+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
            min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+
            min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)+err j := by
  obtain ⟨η,h,δ,ε,ζ,θ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hr,hr1,hC,hbase⟩ :=
    ZetaRieszSevenCountTail.eventually_core_full_ceiling hu hU hy
  obtain ⟨e,he0,heLim,he⟩ := exists_joint_core_error (by linarith : 0 ≤ u) hU y
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSevenPrimeReflection.eventually_core_subset_bounds hu hU)] with j hj hbound
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
    min (f n).re 0+weight A N n*ZetaRieszReflectedPrimeBounds.ceilingCost L y n else (f n).re
  let G := 2*∑ n ∈ E.filter (fun n : ℕ => Squarefree n ∧ n.primeFactors.card = 7 ∧
    (outerPrimes (Real.log n-L) n).card = 2),
    weight A N n*(Real.log n/L*Real.log n.minFac)*max (-Real.cos (y*Real.log n)) 0
  have hE : E ⊆ coreBand u N (dyadicPrimeCount j) := Finset.sdiff_subset
  have hb := (hbound (dyadicPrimeCount j) y E hE).2
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hb
  rw [(sum_observation_savings E A (SquarefreeVaughanLogSource.length_pos u N) N y
    (fun n => (f n).re)).2] at hb
  have hG : 0 ≤ G := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_nonneg
    intro n _
    exact mul_nonneg (mul_nonneg (weight_nonneg A N n)
      (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n)
        (SquarefreeVaughanLogSource.length_pos u N).le) (Real.log_natCast_nonneg n.minFac))) (le_max_right _ _)
  have hbridge := (abs_le.mp (he j)).1
  refine ⟨v,hvb,hY,hG,?_⟩
  change ((u : ℂ)^(N+1)*(lowerThresholdPacket u y N (dyadicPrimeCount j)-
            shortOverflowPacket u y N (dyadicPrimeCount j)+
            ZetaRieszLeastBoundary.rest u y N (dyadicPrimeCount j))).re ≤ u^(N+1)*(W-G+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
            min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+
            min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)+(r^N*C+e j)
  change u^(N+1)*(∑ n ∈ E, f n).re ≤ u^(N+1)*(W-G) at hb
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤ u^(N+1)*((∑ n ∈ E, f n).re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
            min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+
            min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)+r^N*C at hcore
  change -e j ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-((u : ℂ)^(N+1)*(lowerThresholdPacket u y N (dyadicPrimeCount j)-
            shortOverflowPacket u y N (dyadicPrimeCount j)+
            ZetaRieszLeastBoundary.rest u y N (dyadicPrimeCount j))).re at hbridge
  nlinarith only [hcore,hb,hbridge]

end
end RiemannGaussian.ZetaRieszJointReflectionBounds
