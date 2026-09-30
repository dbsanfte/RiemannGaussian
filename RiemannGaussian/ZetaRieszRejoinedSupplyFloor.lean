/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWholeFixedCountFloor

set_option autoImplicit false

/-!
# A joint whole-carrier floor after rejoining the four-prime supply

All counts 3..55 are summed with their supply labels before the signed
estimate. The surviving main labels have growing prime count. Their floor
must still pay the explicit relative supply debit; no absolute cofinal
numerical floor is asserted.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszRejoinedSupplyFloor
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszSevenCountTail
open ZetaRieszOneSidedArithmetic (weight weight_nonneg)
open ZetaRieszRoughFivePeriodFloor (radialSupply_count)
open ZetaRieszRoughFiveJoinedFloor
open ZetaRieszFiveSignCoverFloor (completeGrid slabGrid biUnion_slabGrid_eq)
open ZetaRieszLowCountRefund (tailCost tailCost_nonneg wholeTail_zero_eq)
open ZetaRieszHighSignCoverFloor (periodUnits)

/-- The old logarithmic tail is disjoint from the entire fixed band. -/
theorem countThreshold_gt_fiftyFive {N : ℕ} (hN : 1000 ≤ N) :
    55 < ZetaRieszLogCountBudget.countThreshold N := by
  have hp := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (N+1)
  by_contra hn
  have hc : Nat.clog 2 (N+1) ≤ 6 := by
    unfold ZetaRieszLogCountBudget.countThreshold at hn
    omega
  have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hc
  norm_num at hpow
  omega

theorem radialTail_subset_whole (S : Finset ℕ) (N R : ℕ) :
    radialTail S N R ⊆ wholeTail S N R := by
  intro n hn
  obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hnS,hs,_,_,hc⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnS,hs,hc⟩

/-- Join the supply to the same full fixed-count set before taking a real
part. This exact identity prevents a second use of its positive credit. -/
theorem rejoined_supply_sum (S Y T B D : Finset ℕ) (f : ℕ → ℂ)
    (hDS : D ⊆ S) (hYD : Y ⊆ D) (hTB : T ⊆ B) (hDB : Disjoint D B) :
    (∑ n ∈ S\(Y ∪ T ∪ B), f n)+(∑ n ∈ Y, f n) =
      (∑ n ∈ S\(D ∪ B), f n)+(∑ n ∈ D, f n) := by
  have hD : D ⊆ S\B := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨hDS hn,fun hb => (Finset.disjoint_left.mp hDB hn hb)⟩
  have hY := Finset.Subset.trans hYD hD
  have h₁ := Finset.sum_sdiff hY (f := f)
  have h₂ := Finset.sum_sdiff hD (f := f)
  have hset₁ : (S\B)\Y = S\(Y ∪ T ∪ B) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨⟨hn,hb⟩,hy⟩
      exact ⟨hn,fun hh => hh.elim (fun hh => hh.elim hy (fun ht => hb (hTB ht))) hb⟩
    · tauto
  have hset₂ : (S\B)\D = S\(D ∪ B) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hset₁] at h₁
  rw [hset₂] at h₂
  exact h₁.trans h₂.symm

private theorem core_count_ge_three {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) : 3 ≤ n.primeFactors.card := by
  have hnar := (Finset.mem_filter.mp hn).1
  have hnon := (Finset.mem_filter.mp hnar).1
  have hret := (Finset.mem_sdiff.mp hnon).1
  have horig := (Finset.mem_sdiff.mp hret).1
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp horig).1).2.1
  omega

/-- Every main remainder label is beyond the entire fixed-count band.
No coefficient or phase approximation is needed for this support fact. -/
theorem remainder_count_ge_fiftySix {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K\
      ((coreBand u N K).filter (fun n : ℕ =>
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪
        wholeTail (coreBand u N K) N 0)) :
    56 ≤ n.primeFactors.card := by
  obtain ⟨hncore,hnot⟩ := Finset.mem_sdiff.mp hn
  have hc3 := core_count_ge_three hncore
  by_contra hc56
  apply hnot
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hncore,hc3,by omega⟩)

/-- Nonzero literal atoms in the remaining main term lie strictly below
the separately charged logarithmic tail. The threshold grows with N;
the fixed-count period theorem is not uniform over this range. -/
theorem remaining_effective_geometry {u : ℝ} {N K n : ℕ}
    (A : Finset ℕ) (L y : ℝ)
    (hn : n ∈ coreBand u N K\
      ((coreBand u N K).filter (fun n : ℕ =>
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪
        wholeTail (coreBand u N K) N 0))
    (hne : residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n ≠ 0) :
    Squarefree n ∧ 56 ≤ n.primeFactors.card ∧
      n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N := by
  have hc := remainder_count_ge_fiftySix hn
  obtain ⟨hncore,hnot⟩ := Finset.mem_sdiff.mp hn
  have hs : Squarefree n := by
    by_contra hs
    apply hne
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs]
  refine ⟨hs,hc,?_⟩
  by_contra hbad
  apply hnot
  apply Finset.mem_union_right
  rw [wholeTail_zero_eq]
  exact Finset.mem_filter.mpr ⟨hncore,hs,le_of_not_gt hbad⟩

set_option maxHeartbeats 1600000 in
/-- Rejoin every fixed count, including the positive supply, BEFORE the
whole-band signed estimate. The only main remainder has count >=56.
The same supply survives solely as an explicit debit, with no duplicated
positive credit. This is not yet the numerical -79/1000 floor. -/
theorem eventually_joined_floor_with_growing_counts {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N 0
        let Ys := radialSupply N h w
        let D := S.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
        let H := S\(D ∪ wholeTail S N 0)
        let W := ∑ n ∈ H, (max (f n).re 0-
          weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n)
        let G := ∑ n ∈ H, weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
          ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Ts, f n).re 0+
            max (∑ n ∈ D, f n).re 0-(tailCost c N+ε)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨h,c,κ,r,C,hh,hhu,hc,hκ,hκeq,hr,hr1,hC,hbase⟩ :=
    ZetaRieszSharpSupplyFloor.eventually_core_floor_with_sharp_tail hu hU hy
  refine ⟨h,c,hh,hhu,hc,?_⟩
  intro ε hε
  obtain ⟨eb,heb0,heb,hband⟩ := ZetaRieszWholeFixedCountFloor.exists_core_band_floor hu hU hy
    (by positivity : 0 < κ*128*ε)
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  have he0 j : 0 ≤ e j := norm_nonneg _
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  let err := fun j => r^(dyadicMomentOrder j)*C+e j+eb j
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim |>.add heb
    simpa only [err,Function.comp_apply,zero_mul,mul_zero,zero_add] using ht
  refine ⟨err,(fun j => by dsimp [err]; positivity [he0 j,heb0 j]),herr,?_⟩
  filter_upwards [hbase,hband,
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hband hYsub hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Ts := radialTail S N 0
  let Ys := radialSupply N h w
  let B := wholeTail S N 0
  let D := S.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
  let H := S\(D ∪ B)
  let W := ∑ n ∈ H, (max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n)
  let G := ∑ n ∈ H, weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
    ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  have hYin : Ys ⊆ D := by
    intro n hn
    have hncore : n ∈ S := by
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hYsub M hM (w M) (hw M hM).1 (hw M hM).2 hn
    have hc4 := radialSupply_count (by omega : 1000 ≤ N) hh hhu w hw hn
    exact Finset.mem_filter.mpr ⟨hncore,by omega,by omega⟩
  have hDB : Disjoint D B := by
    apply Finset.disjoint_left.mpr
    intro n hnD hnB
    have hcount := (Finset.mem_filter.mp hnD).2
    change n ∈ wholeTail S N 0 at hnB
    rw [wholeTail_zero_eq] at hnB
    have htail := (Finset.mem_filter.mp hnB).2.2
    have hbig := countThreshold_gt_fiftyFive (by omega : 1000 ≤ N)
    omega
  have hjoin := congrArg Complex.re (rejoined_supply_sum S Ys Ts B D f
    (Finset.filter_subset _ _) hYin (radialTail_subset_whole S N 0) hDB)
  simp only [Complex.add_re] at hjoin
  have hjoinScaled := congrArg (fun x : ℝ => u^(N+1)*x) hjoin
  have hbudget := period_grids_cost_paid (by omega : 1 ≤ N) hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*periodUnits N y ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hbudgetε := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 128*ε)
  have hbudgetε' : (κ*128*ε)*periodUnits N y ≤ ε*(∑ n ∈ Ys, f n).re := by
    nlinarith only [hbudgetε]
  have hscaled := mul_le_mul_of_nonneg_left hbudgetε'
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change -u^(N+1)*(κ*128*ε)*periodUnits N y-eb j ≤
    ((u : ℂ)^(N+1)*∑ n ∈ D, f n).re at hband
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hband
  have hDfloor : -u^(N+1)*ε*(∑ n ∈ Ys, f n).re-eb j ≤
      u^(N+1)*(∑ n ∈ D, f n).re := by
    nlinarith only [hband,hscaled]
  have hDmax : u^(N+1)*max (∑ n ∈ D, f n).re 0-
      u^(N+1)*ε*(∑ n ∈ Ys, f n).re-eb j ≤ u^(N+1)*(∑ n ∈ D, f n).re := by
    by_cases hp : 0 ≤ (∑ n ∈ D, f n).re
    · rw [max_eq_left hp]
      have hz : 0 ≤ u^(N+1)*ε*(∑ n ∈ Ys, f n).re := by positivity [hY.le]
      linarith only [hz,heb0 j]
    · rw [max_eq_right (le_of_not_ge hp),mul_zero,zero_sub]
      nlinarith only [hDfloor]
  have hhigh (n : ℕ) (hn : n ∈ H) : 7 ≤ n.primeFactors.card := by
    obtain ⟨hnS,hnot⟩ := Finset.mem_sdiff.mp hn
    have hc3 := core_count_ge_three hnS
    by_contra hc7
    apply hnot
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnS,hc3,by omega⟩)
  have hb := hbound (dyadicPrimeCount j) y H Finset.sdiff_subset
  have hfilter : H.filter (fun n : ℕ => 7 ≤ n.primeFactors.card) = H :=
    Finset.filter_eq_self.mpr hhigh
  dsimp only at hb
  rw [hfilter] at hb
  simp only [Finset.sum_congr rfl (fun n hn => if_pos (hhigh n hn))] at hb
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ H, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  change u^(N+1)*((∑ n ∈ S\(Ys ∪ Ts ∪ B), f n).re+
    max (∑ n ∈ Ts, f n).re 0+(1-tailCost c N)*(∑ n ∈ Ys, f n).re)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  change u^(N+1)*(W+G+max (∑ n ∈ Ts, f n).re 0+max (∑ n ∈ D, f n).re 0-
    (tailCost c N+ε)*(∑ n ∈ Ys, f n).re)-(r^N*C+e j+eb j) ≤ _
  nlinarith only [hcore,hjoinScaled,hDmax,hb,hbridge]

end RiemannGaussian.ZetaRieszRejoinedSupplyFloor
