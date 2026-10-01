/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPopulationFloor
import RiemannGaussian.ZetaRieszRejoinedSupplyFloor

set_option autoImplicit false

/-!
# One signed floor after rejoining all fixed counts and their funding supply

The four-prime supply is included in the actual fixed-count sum before
estimating that sum. Both disjoint growing-population payments use the same
supply witness. The resulting debit is explicit and unrounded; its relative
decay is not asserted to be absolute decay at source scale.

The unresolved term retains its whole complex phase and signed real part.
No crossing norm, parity-layer allowance or unproved arithmetic bound enters.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszRejoinedPopulationFloor
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszSevenCountTail
open ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszUnpaidCountTiltFloor ZetaRieszIntermediateScaleCost
open ZetaRieszDenseCountCoverFloor ZetaRieszParityLayerCost
open ZetaRieszRoughFivePeriodFloor (radialSupply_count)
open ZetaRieszRoughFiveJoinedFloor
open ZetaRieszFiveSignCoverFloor (completeGrid slabGrid biUnion_slabGrid_eq)
open ZetaRieszHighSignCoverFloor (periodUnits)
open ZetaRieszLowCountRefund (tailCost tailCost_nonneg tendsto_tailCost wholeTail_zero_eq)

/-- The exact additional debit for both growing-population payments.
It is relative to the SAME original four-prime supply. -/
def growingDebit (κ : ℝ) (N : ℕ) : ℝ :=
  (unpaidCountSupplyPrice N+intermediateSupplyPrice N)/(128*κ)

theorem growingDebit_nonneg {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    0 ≤ growingDebit κ N := by
  have hl : 0 ≤ log ((N : ℝ)+1) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hv : 0 ≤ log (4*((N : ℝ)+1)) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have h2 : 0 < log 2 := log_pos (by norm_num)
  unfold growingDebit unpaidCountSupplyPrice intermediateSupplyPrice
  positivity [gappedHeadCost_pos.le,h2.le]

theorem tendsto_growingDebit (κ : ℝ) :
    Tendsto (growingDebit κ) atTop (𝓝 0) := by
  change Tendsto (fun N => (unpaidCountSupplyPrice N+intermediateSupplyPrice N)/(128*κ)) atTop (𝓝 0)
  simpa only [zero_add,zero_div] using
    (tendsto_unpaidCountSupplyPrice.add tendsto_intermediateSupplyPrice).div_const (128*κ)

/-- Rejoining changes the former fixed positive supply credit into its
actual signed band. The exact remaining debit tends to zero relatively. -/
theorem tendsto_total_relative_debit (c κ : ℝ) :
    Tendsto (fun N => tailCost c N+growingDebit κ N) atTop (𝓝 0) := by
  simpa only [zero_add] using (tendsto_tailCost c).add (tendsto_growingDebit κ)

private theorem dense56_in_rejoined_remainder (u : ℝ) (N K : ℕ) :
    dense56Band u N K ⊆ coreBand u N K\
      ((coreBand u N K).filter (fun n : ℕ =>
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪
        wholeTail (coreBand u N K) N 0) := by
  intro n hn
  obtain ⟨hnD,h56⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnS,hs,_,_,hupper⟩ := Finset.mem_filter.mp hnD
  refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
  intro hbad
  rcases Finset.mem_union.mp hbad with hfixed|htail
  · have hc := (Finset.mem_filter.mp hfixed).2.2
    omega
  · rw [wholeTail_zero_eq] at htail
    have hc := (Finset.mem_filter.mp htail).2.2
    omega

private theorem bin56_in_rejoined_remainder (u : ℝ) (N K : ℕ) :
    bin56Band u N K ⊆ coreBand u N K\
      ((coreBand u N K).filter (fun n : ℕ =>
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪
        wholeTail (coreBand u N K) N 0) := by
  intro n hn
  obtain ⟨hnB,h56⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnS,hs,_,_,hupper⟩ := Finset.mem_filter.mp hnB
  refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
  intro hbad
  rcases Finset.mem_union.mp hbad with hfixed|htail
  · have hc := (Finset.mem_filter.mp hfixed).2.2
    omega
  · rw [wholeTail_zero_eq] at htail
    have hc := (Finset.mem_filter.mp htail).2.2
    omega

private theorem growing_bands_disjoint (u : ℝ) (N K : ℕ) :
    Disjoint (dense56Band u N K) (bin56Band u N K) := by
  apply Finset.disjoint_left.mpr
  intro n hd hb
  have hlo := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.2.2.1.1
  have hhi := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2.2.2.1
  exact (not_lt_of_ge hhi) hlo

set_option maxHeartbeats 1600000 in
/-- The fixed-count band, including the complete four-prime funding
supply, and BOTH growing-population bands are paid JOINTLY. The only
unresolved labels are in the many-bin lower growing band. The unrounded
supply debit stays explicit: it is not a numerical whole-floor theorem. -/
theorem eventually_joined_floor_rejoined_populations {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N K
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N 0
        let Ys := radialSupply N h w
        let D := S.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
        let Ds := dense56Band u N K
        let Bs := bin56Band u N K
        let Paid := (D ∪ Ds) ∪ Bs
        let H := S\(Paid ∪ wholeTail S N 0)
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*((∑ n ∈ H, f n).re+max (∑ n ∈ Paid, f n).re 0+
            max (∑ n ∈ Ts, f n).re 0-
            (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,r₀,C₀,hh,hhu,hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ :=
    ZetaRieszSharpSupplyFloor.eventually_core_floor_with_sharp_tail hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨eb,heb0,heb,hfixed⟩ := ZetaRieszWholeFixedCountFloor.exists_core_band_floor hu hU hy
    (by positivity : 0 < κ*128*ε)
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hdense⟩ := exists_dense56_band_floor hu hU hy
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hbin⟩ := exists_bin56_band_floor hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  let d := fun j => 4*zetaMoebiusLogMajorantMass (1+1/262144)*
    Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)
  have he0 j : 0 ≤ e j := norm_nonneg _
  have hd0 j : 0 ≤ d j := by
    dsimp [d]
    positivity [zetaMoebiusLogMajorantMass_nonneg (1+1/262144)]
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  have hdLim : Tendsto d atTop (𝓝 0) := by
    have ht := (ZetaRieszJointDominantFloor.Refined.tendsto_allowance.const_mul (2 : ℝ)).comp
      tendsto_dyadicMomentOrder
    simp only [mul_zero] at ht
    convert ht using 1
    funext j
    dsimp [d,Function.comp_def]
    ring
  have h₀ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₀1).mul_const C₀).comp
    tendsto_dyadicMomentOrder
  have h₁ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₁ hr₁1).mul_const (2*C₁)).comp
    tendsto_dyadicMomentOrder
  have h₂ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₂ hr₂1).mul_const (2*C₂)).comp
    tendsto_dyadicMomentOrder
  have ho := (tendsto_ownerPaymentError.comp tendsto_dyadicMomentOrder).const_mul (6 : ℝ)
  have ho0 j : 0 ≤ ownerPaymentError (dyadicMomentOrder j) := by
    unfold ownerPaymentError
    positivity [zetaMoebiusLogMajorantMass_nonneg (2049/2048),
      ZetaRieszNonownerAllocation.nonownerRate_bounds.1]
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+eb j+2*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂+
    6*ownerPaymentError (dyadicMomentOrder j)
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (((((h₀.add heLim).add heb).add (hdLim.const_mul (2 : ℝ))).add h₁).add h₂).add ho
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨err,(fun j => by dsimp [err]; positivity [he0 j,hd0 j,heb0 j,ho0 j]),herr,?_⟩
  filter_upwards [hbase,hfixed,hdense,hbin,eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hfixed hdense hbin hYsub hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N K
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Ts := radialTail S N 0
  let Ys := radialSupply N h w
  let B := wholeTail S N 0
  let D := S.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
  let Ds := dense56Band u N K
  let Bs := bin56Band u N K
  let Paid := (D ∪ Ds) ∪ Bs
  let H := S\(Paid ∪ B)
  refine ⟨w,hw,hY,?_⟩
  have hYin : Ys ⊆ D := by
    intro n hn
    have hncore : n ∈ S := by
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hYsub M hM (w M) (hw M hM).1 (hw M hM).2 hn
    have h4 := radialSupply_count (by omega : 1000 ≤ N) hh hhu w hw hn
    exact Finset.mem_filter.mpr ⟨hncore,by omega,by omega⟩
  have hDB : Disjoint D B := by
    apply Finset.disjoint_left.mpr
    intro n hnD hnB
    have hcnt := (Finset.mem_filter.mp hnD).2
    change n ∈ wholeTail S N 0 at hnB
    rw [wholeTail_zero_eq] at hnB
    have htail := (Finset.mem_filter.mp hnB).2.2
    have hbig := ZetaRieszRejoinedSupplyFloor.countThreshold_gt_fiftyFive
      (by omega : 1000 ≤ N)
    omega
  have hjoin := congrArg Complex.re
    (ZetaRieszRejoinedSupplyFloor.rejoined_supply_sum S Ys Ts B D f
      (Finset.filter_subset _ _) hYin
      (ZetaRieszRejoinedSupplyFloor.radialTail_subset_whole S N 0) hDB)
  simp only [Complex.add_re] at hjoin
  have hjoinScaled := congrArg (fun x : ℝ => u^(N+1)*x) hjoin
  have hDsub : Ds ⊆ S\(D ∪ B) := dense56_in_rejoined_remainder u N K
  have hBsub₀ : Bs ⊆ S\(D ∪ B) := bin56_in_rejoined_remainder u N K
  have hBsub : Bs ⊆ (S\(D ∪ B))\Ds := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨hBsub₀ hn,
      fun hd => Finset.disjoint_left.mp (growing_bands_disjoint u N K) hd hn⟩
  have hdeq := congrArg Complex.re (Finset.sum_sdiff hDsub (f := f))
  have hbeq := congrArg Complex.re (Finset.sum_sdiff hBsub (f := f))
  simp only [Complex.add_re] at hdeq hbeq
  have hHset : ((S\(D ∪ B))\Ds)\Bs = H := by
    ext n
    simp only [H,Paid,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hHset] at hbeq
  have hfixedDense : Disjoint D Ds := Finset.disjoint_left.mpr (by
    intro n hnD hnDs
    exact (Finset.mem_sdiff.mp (hDsub hnDs)).2 (Finset.mem_union_left _ hnD))
  have hfixedBin : Disjoint D Bs := Finset.disjoint_left.mpr (by
    intro n hnD hnBs
    exact (Finset.mem_sdiff.mp (hBsub₀ hnBs)).2 (Finset.mem_union_left _ hnD))
  have hpaidEq := congrArg Complex.re
    (Finset.sum_union ((Finset.disjoint_union_left.mpr
      ⟨hfixedBin,growing_bands_disjoint u N K⟩)) (f := f))
  rw [Finset.sum_union hfixedDense] at hpaidEq
  simp only [Complex.add_re] at hpaidEq
  change (∑ n ∈ Paid,f n).re=(∑ n ∈ D,f n).re+(∑ n ∈ Ds,f n).re+
    (∑ n ∈ Bs,f n).re at hpaidEq
  have hfullEq : (∑ n ∈ S\(D ∪ B),f n).re+(∑ n ∈ D,f n).re=
      (∑ n ∈ H,f n).re+(∑ n ∈ Paid,f n).re := by
    linarith only [hdeq,hbeq,hpaidEq]
  have hbudget := period_grids_cost_paid (by omega : 1 ≤ N) hc hy hhu hκeq
    w f (radialIndices N) (slabGrid N (Real.pi/y) y)
    (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*periodUnits N y ≤ (1/128 : ℝ)*(∑ n ∈ Ys,f n).re at hbudget
  have hfixed' := hfixed
  change -u^(N+1)*(κ*128*ε)*periodUnits N y-eb j ≤
    ((u : ℂ)^(N+1)*∑ n ∈ D,f n).re at hfixed'
  have hdense' := hdense
  change -u^(N+1)*unpaidCountSupplyPrice N*periodUnits N y-d j-2*r₁^N*C₁-
    3*ownerPaymentError N ≤ ((u : ℂ)^(N+1)*∑ n ∈ Ds,f n).re at hdense'
  have hbin' := hbin
  change -u^(N+1)*intermediateSupplyPrice N*periodUnits N y-d j-2*r₂^N*C₂-
    3*ownerPaymentError N ≤ ((u : ℂ)^(N+1)*∑ n ∈ Bs,f n).re at hbin'
  rw [←Complex.ofReal_pow,Complex.re_ofReal_mul] at hfixed' hdense' hbin'
  have hrateEq : growingDebit κ N*(128*κ)=
      unpaidCountSupplyPrice N+intermediateSupplyPrice N := by
    unfold growingDebit
    exact div_mul_cancel₀ _ (by positivity)
  have hfund := mul_le_mul_of_nonneg_left hbudget
    (by positivity [growingDebit_nonneg hκ N] : 0 ≤ 128*(ε+growingDebit κ N))
  have hfund' : (κ*128*ε+unpaidCountSupplyPrice N+intermediateSupplyPrice N)*
      periodUnits N y ≤ (ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re := by
    calc
      _ = (128*(ε+growingDebit κ N))*(κ*periodUnits N y) := by
        calc
          _ = (κ*128*ε+(unpaidCountSupplyPrice N+intermediateSupplyPrice N))*periodUnits N y := by ring
          _ = (κ*128*ε+growingDebit κ N*(128*κ))*periodUnits N y := by rw [hrateEq]
          _ = _ := by ring
      _ ≤ (128*(ε+growingDebit κ N))*((1/128 : ℝ)*(∑ n ∈ Ys,f n).re) := hfund
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hfund'
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaidEqScaled := congrArg (fun x : ℝ => u^(N+1)*x) hpaidEq
  have hpaidFloor : -u^(N+1)*(ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re-
      (eb j+2*d j+2*r₁^N*C₁+2*r₂^N*C₂+6*ownerPaymentError N) ≤
      u^(N+1)*(∑ n ∈ Paid,f n).re := by
    nlinarith only [hscaled,hfixed',hdense',hbin',hpaidEqScaled]
  have hcost0 : 0 ≤ u^(N+1)*(ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re+
      (eb j+2*d j+2*r₁^N*C₁+2*r₂^N*C₂+6*ownerPaymentError N) := by
    positivity [hY.le,heb0 j,hd0 j,ho0 j,growingDebit_nonneg hκ N]
  have hpaidMax : u^(N+1)*max (∑ n ∈ Paid,f n).re 0-
      u^(N+1)*(ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re-
      (eb j+2*d j+2*r₁^N*C₁+2*r₂^N*C₂+6*ownerPaymentError N) ≤
      u^(N+1)*(∑ n ∈ Paid,f n).re := by
    by_cases hp : 0 ≤ (∑ n ∈ Paid,f n).re
    · rw [max_eq_left hp]
      linarith only [hcost0]
    · rw [max_eq_right (le_of_not_ge hp),mul_zero,zero_sub]
      nlinarith only [hpaidFloor]
  have hfullScaled := congrArg (fun x : ℝ => u^(N+1)*x) hfullEq
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N K-ZetaRieszGammaJoint.joinedPhysical u y N K))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [←mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N K).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re ≤ e j at hbridge
  change u^(N+1)*((∑ n ∈ S\(Ys ∪ Ts ∪ B),f n).re+max (∑ n ∈ Ts,f n).re 0+
    (1-tailCost c N)*(∑ n ∈ Ys,f n).re)-r₀^N*C₀ ≤
    ((u : ℂ)^(N+1)*coreResponse u y N K).re at hcore
  change u^(N+1)*((∑ n ∈ H,f n).re+max (∑ n ∈ Paid,f n).re 0+
    max (∑ n ∈ Ts,f n).re 0-(tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-
      (r₀^N*C₀+e j+eb j+2*d j+2*r₁^N*C₁+2*r₂^N*C₂+6*ownerPaymentError N) ≤ _
  nlinarith only [hcore,hjoinScaled,hfullScaled,hpaidMax,hbridge]

/-- All fixed counts, including the funding population, have been rejoined.
The actual remaining nonzero labels are exclusively the many-bin lower
growing population; no low-order or prime-density approximation is used. -/
theorem remaining_effective_geometry {u : ℝ} {N K n : ℕ} (A : Finset ℕ) (L y : ℝ)
    (hn : n ∈ coreBand u N K\
      ((((coreBand u N K).filter (fun n : ℕ =>
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
        bin56Band u N K) ∪ wholeTail (coreBand u N K) N 0))
    (hne : residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n ≠ 0) :
    Squarefree n ∧ 56 ≤ n.primeFactors.card ∧
      (n.primeFactors.card : ℝ) < 5*log ((N : ℝ)+1)+2 ∧
      ⌊log ((N : ℝ)+1)/16⌋₊ < (cofactorBins N (n/ZetaRieszPrimeEndpoint.largestPrime n)).card := by
  obtain ⟨hnS,hnot⟩ := Finset.mem_sdiff.mp hn
  have hnotD : n ∉ (coreBand u N K).filter (fun n : ℕ =>
      3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) :=
    fun h => hnot (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hnotTail : n ∉ wholeTail (coreBand u N K) N 0 :=
    fun h => hnot (Finset.mem_union_right _ h)
  have hold := ZetaRieszRejoinedSupplyFloor.remaining_effective_geometry A L y
    (Finset.mem_sdiff.mpr ⟨hnS,fun h => (Finset.mem_union.mp h).elim hnotD hnotTail⟩) hne
  obtain ⟨hs,h56,hupper⟩ := hold
  have hnotDense : n ∉ dense56Band u N K := fun h =>
    hnot (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hlo : (n.primeFactors.card : ℝ) < 5*log ((N : ℝ)+1)+2 := by
    by_contra h
    exact hnotDense (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hnS,hs,by omega,le_of_not_gt h,hupper⟩,h56⟩)
  refine ⟨hs,h56,hlo,?_⟩
  by_contra hb
  apply hnot
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hnS,hs,by omega,⟨hlo,le_of_not_gt hb⟩,hupper⟩,h56⟩))

end RiemannGaussian.ZetaRieszRejoinedPopulationFloor
