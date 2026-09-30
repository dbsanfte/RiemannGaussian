/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowCountRefund

set_option autoImplicit false

/-!
# Keeping the quantitative charges in the joined arithmetic floor

The logarithmic count tail has its actual O(N^-4) relative charge.
Complete signed prime periods can use any fixed positive budget on the SAME
supply. No fixed 3/128 debit is intrinsic, but neither relative estimate is
source-normalized decay and the numerical -79/1000 floor remains open.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSharpSupplyFloor
open ZetaRieszTransitionFiveFloor ZetaRieszStaggeredFloor
open ZetaRieszRoughFivePeriodFloor (spent radialSupply_count)
open ZetaRieszRoughFiveJoinedFloor
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic (weight weight_nonneg)
open ZetaRieszMultiPeriodSix
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead ZetaRieszSevenCountTail
open ZetaRieszFixedCountPeriod (response)
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszFiveSignCoverFloor (completeGrid slabGrid biUnion_slabGrid_eq
  exists_completeGrid_period exists_outer_subset_bound)

open ZetaRieszThreeSignCoverFloor (tripleRestSpent tripleRestSpent_eq
  nontriple_rest_filter_eq)
open ZetaRieszHighSignCoverFloor (high_rest_filter_eq exists_unpaid_band_floor)
open ZetaRieszFourSmallFloor (PaidFour exists_unpaid_four_away_supply_floor)

open ZetaRieszLowCountRefund (tail_floor tailCost tailCost_nonneg tendsto_tailCost
  radial_tail_sharp_cost tripleRestSpent_zero)

set_option maxHeartbeats 1200000 in
/-- All low-count heads stay in the signed sum. The tail keeps its actual
O(N^-4) charge relative to the SAME supply, with the original radial
boundary payment retained. -/
theorem eventually_core_floor_with_sharp_tail {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ r C : ℝ, 0 < h ∧ h ≤ 1/20 ∧
      0 < c ∧ 0 < κ ∧ κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let R : ℕ := 0
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let B := wholeTail S N R
        0 < (∑ n ∈ Ys, f n).re ∧
          (∀ M ∈ radialIndices N,
            c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
              (∑ n ∈ supply M h (w M), f n).re) ∧
          u^(N+1)*((∑ n ∈ S\(Ys ∪ Ts ∪ B), f n).re+
            max (∑ n ∈ Ts, f n).re 0+(1-tailCost c N)*(∑ n ∈ Ys, f n).re)-r^N*C ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨h,c,κ,r₀,C₀,hh,hhu,hc,hκ,hκeq,_,_,_,hbase⟩ :=
    ZetaRieszLowCountRefund.eventually_core_floor_with_heads_rejoined hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := ZetaRieszSevenCountTail.exists_missed_tail_bound
  refine ⟨h,c,κ,r,C,hh,hhu,hc,hκ,hκeq,hr,hr1,hC,?_⟩
  filter_upwards [hbase,eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hsub hN
  obtain ⟨w,hwb,hY,hscale,_⟩ := hj
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let R : ℕ := 0
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let B := wholeTail S N R
  have hTpay := radial_tail_sharp_cost S A (by omega : 1 ≤ N) hhu
    (SquarefreeVaughanLogSource.length_pos _ _) hc w hwb hscale
  have hTsub : Ts ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hTcount : ∀ n ∈ Ts, 7 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N)
      (Finset.mem_filter.mp hn).2.2.2.2
  have hYcount : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => radialSupply_count (by omega) hh hhu w hwb hn
  have hYsub : Ys ⊆ S := by
    intro n hn
    obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
    exact hsub M hM (w M) (hwb M hM).1 (hwb M hM).2 hn
  have hYT : Disjoint Ys Ts := Finset.disjoint_left.mpr
    (fun n hnY hnT => by have := hYcount n hnY; have := hTcount n hnT; omega)
  have hfloor := tail_floor f (Finset.union_subset hYsub hTsub) hYT hTpay
  have hcore := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  let D := B\Ts
  have hDsub : D ⊆ S\(Ys ∪ Ts) := by
    intro n hn
    obtain ⟨hnB,hnT⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnS,_,hc⟩ := Finset.mem_filter.mp hnB
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hm
    rcases Finset.mem_union.mp hm with hnY | hnT'
    · have ht := ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N) hc
      have hyc := hYcount n hnY
      omega
    · exact hnT hnT'
  have hnorm := hmissed N R S A y u hN (by linarith) hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ r^N*C at hnorm
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hreal
  have hsum := congrArg Complex.re (Finset.sum_sdiff hDsub (f := f))
  have hsets : (S\(Ys ∪ Ts))\D = S\(Ys ∪ Ts ∪ B) := by
    ext n
    simp only [D,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hsets,Complex.add_re] at hsum
  have hscaled := congrArg (fun x : ℝ => u^(N+1)*x) hsum
  refine ⟨w,hwb,hY,hscale,?_⟩
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  nlinarith only [hcore,hreal,hscaled]

private theorem paid_parts (E : Finset ℕ) (f : ℕ → ℂ) (N : ℕ) (L : ℝ) :
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 5), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 6), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55), f n)+
    (∑ n ∈ (E.filter (fun n : ℕ => n.primeFactors.card = 4)).filter
      (fun n => PaidFour N L n), f n) =
    ∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
      n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
      (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
      (n.primeFactors.card = 4 ∧ PaidFour N L n)), f n := by
  rw [Finset.filter_filter]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h3 : n.primeFactors.card = 3
  · simp [h3]
  by_cases h5 : n.primeFactors.card = 5
  · simp [h5]
  by_cases h6 : n.primeFactors.card = 6
  · simp [h6]
  by_cases h4 : n.primeFactors.card = 4
  · simp [h4]
  simp only [h3,h5,h6,h4,if_false,false_or,false_and,or_false,zero_add,add_zero]

set_option maxHeartbeats 1600000 in
/-- All earlier heads and fixed-count signed payments retain arbitrarily
close to the FULL original supply, with its precise O(N^-4) tail cost.
The supply width and lower constant are independent of the requested
period budget. This is not an absolute bound for the unpaid remainder. -/
theorem eventually_joined_floor_with_arbitrary_debit {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let η : ℝ := 0
        let Q : ℕ := 0
        let P : ℕ := 0
        let V : ℕ := 0
        let R : ℕ := 0
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let E := S\tripleRestSpent S N Q P V R η h L w
        let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n))
        let Eo := E\Epaid
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Ts, f n).re 0+
            max (∑ n ∈ Epaid, f n).re 0+(1-tailCost c N-ε)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨h,c,κ,r₀,C₀,hh,hhu,hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ :=
    eventually_core_floor_with_sharp_tail hu hU hy
  refine ⟨h,c,hh,hhu,hc,?_⟩
  intro ε hε
  let η : ℝ := 0
  have hηu : η ≤ 1/1000 := by norm_num [η]
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩  :=
    ZetaRieszFiveSignCoverFloor.exists_unpaid_five_floor hu hU hy (by positivity : 0 < κ*128*ε/5)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hsix⟩ := ZetaRieszSixSignCoverFloor.exists_unpaid_six_floor hu hU hy (by positivity : 0 < κ*128*ε/5)
  obtain ⟨r₃,C₃,hr₃,hr₃1,hC₃,hthree⟩ := ZetaRieszThreeSignCoverFloor.exists_unpaid_three_floor hu hU hy
    (by positivity : 0 < κ*128*ε/5)
  obtain ⟨err₄,herr₄0,herr₄,hhigh⟩ := exists_unpaid_band_floor hu hU hy
    (by positivity : 0 < κ*128*ε/5)
  obtain ⟨r₅,C₅,hr₅,hr₅1,hC₅,hfour⟩ := exists_unpaid_four_away_supply_floor hu hU hy
    (by positivity : 0 < κ*128*ε/5)
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  let d := fun j => 4*zetaMoebiusLogMajorantMass (1+1/262144)*
    Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have hd0 (j : ℕ) : 0 ≤ d j := by
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
  have h₃ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₃ hr₃1).mul_const (2*C₃)).comp
    tendsto_dyadicMomentOrder
  have h₅ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₅ hr₅1).mul_const (2*C₅)).comp
    tendsto_dyadicMomentOrder
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+5*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂+2*r₃^(dyadicMomentOrder j)*C₃+err₄ j+2*r₅^(dyadicMomentOrder j)*C₅
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (((((h₀.add heLim).add (hdLim.const_mul (5 : ℝ))).add h₁).add h₂).add h₃).add herr₄ |>.add h₅
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨err,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j,herr₄0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hsix,hthree,hhigh,hfour,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
      with j hj hfive hsix hthree hhigh hfour hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q : ℕ := 0
  let P : ℕ := 0
  let V : ℕ := 0
  let R : ℕ := 0
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let E := S\tripleRestSpent S N Q P V R η h L w
  let E3 := E.filter (fun n : ℕ => n.primeFactors.card = 3)
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let E6 := E.filter (fun n : ℕ => n.primeFactors.card = 6)
  let E4p := (E.filter (fun n : ℕ => n.primeFactors.card = 4)).filter
    (fun n => PaidFour N L n)
  let Ehi := E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
  let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n))
  let Eo := E\Epaid
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  have hQlog : Real.log Q ≤ (N : ℝ)/128 := by simp only [Q,Nat.cast_zero,Real.log_zero]; positivity
  have ht := hthree Q P V R η h w hh hhu hηu hQlog hw
  have hp := hfive Q P V R η h w hh hhu hw
  have hq := hsix Q P V R η h w hh hhu hw
  have h5eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (5 : ℕ) ≠ 3)
  have h6eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (6 : ℕ) ≠ 3)
  have hbandFloor := hhigh Q P V R η h w hh hhu hw
  have hheq := high_rest_filter_eq S N Q P V R η h L w
  have hfourFloor := hfour Q P V R η h w hh hhu hw
  have h4eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (4 : ℕ) ≠ 3)
  dsimp only at hfourFloor
  rw [←h4eq] at hfourFloor
  dsimp only at hp hq ht hbandFloor
  rw [←h5eq] at hp
  rw [←h6eq] at hq
  rw [←hheq] at hbandFloor
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*(κ*128*ε/5)*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  change -u^(N+1)*(κ*128*ε/5)*units-d j-2*r₂^N*C₂ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E6, f n).re at hq
  change -u^(N+1)*(κ*128*ε/5)*units-d j-2*r₃^N*C₃ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E3, f n).re at ht
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hp hq ht
  change -u^(N+1)*(κ*128*ε/5)*units-err₄ j ≤
    ((u : ℂ)^(N+1)*∑ n ∈ Ehi, f n).re at hbandFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hbandFloor
  rw [show 8*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(dyadicMomentOrder j : ℝ)/1000000) = 2*d j by dsimp [d]; ring]
    at hfourFloor
  change -u^(N+1)*(κ*128*ε/5)*units-2*d j-2*r₅^N*C₅ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E4p, f n).re at hfourFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hfourFloor
  have hbudget := period_grids_cost_paid (by omega : 1 ≤ N) hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hbudgetε := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 128*ε)
  have hbudgetε' : (κ*128*ε)*units ≤ ε*(∑ n ∈ Ys, f n).re := by
    nlinarith only [hbudgetε]
  have hscaled := mul_le_mul_of_nonneg_left hbudgetε'
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*ε*(∑ n ∈ Ys, f n).re-5*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j-2*r₅^N*C₅ ≤
      u^(N+1)*((∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
        (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re) := by
    nlinarith only [hscaled,hp,hq,ht,hbandFloor,hfourFloor]
  have hpaidEq := congrArg Complex.re (paid_parts E f N L)
  simp only [Complex.add_re] at hpaidEq
  change (∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
    (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re = (∑ n ∈ Epaid, f n).re at hpaidEq
  rw [hpaidEq] at hpaid
  have hcost : 0 ≤ u^(N+1)*ε*(∑ n ∈ Ys, f n).re+5*d j+
      2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅ := by
    positivity [hY.le,hd0 j,herr₄0 j]
  have hpaidMax : u^(N+1)*max (∑ n ∈ Epaid, f n).re 0-
      u^(N+1)*ε*(∑ n ∈ Ys, f n).re-5*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j-2*r₅^N*C₅ ≤
      u^(N+1)*(∑ n ∈ Epaid, f n).re := by
    by_cases hp : 0 ≤ (∑ n ∈ Epaid, f n).re
    · rw [max_eq_left hp]
      linarith only [hcost]
    · rw [max_eq_right (le_of_not_ge hp),mul_zero,zero_sub]
      linarith only [hpaid]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
      n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n)) E)
      (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ Epaid, f n).re = (∑ n ∈ E, f n).re at hs
  let credits := max (∑ n ∈ Ts, f n).re 0
  let B := wholeTail S N R
  have hSpent := tripleRestSpent_zero (R := R) (L := L) S η
    (by omega : 1000 ≤ N) hh hhu w hw
  change tripleRestSpent S N Q P V R η h L w = Ys ∪ Ts ∪ B at hSpent
  change u^(N+1)*((∑ n ∈ S\(Ys ∪ Ts ∪ B), f n).re+
    max (∑ n ∈ Ts, f n).re 0+(1-tailCost c N)*(∑ n ∈ Ys, f n).re)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  rw [←hSpent] at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(1-tailCost c N)*(∑ n ∈ Ys, f n).re)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := hcore
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(W+G+credits+max (∑ n ∈ Epaid, f n).re 0+(1-tailCost c N-ε)*(∑ n ∈ Ys, f n).re)-
      (r₀^N*C₀+e j+5*d j+2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaidMax,hbridge,hscaledLedger]
  exact hfinal

/-- Rejoining the same supply leaves precisely the sharp, unrounded
debit. It is not licensed to count this supply a second time. -/
theorem joint_supply_debit (E Y : Finset ℕ) (f : ℕ → ℂ) (c ε : ℝ) (N : ℕ)
    (hd : Disjoint E Y) :
    (∑ n ∈ E, f n).re+(1-tailCost c N-ε)*(∑ n ∈ Y, f n).re =
      (∑ n ∈ E ∪ Y, f n).re-(tailCost c N+ε)*(∑ n ∈ Y, f n).re := by
  rw [Finset.sum_union hd,Complex.add_re]
  ring

/-- No fixed positive relative debit is forced: allocate half of any
requested margin to periods and eventually less than half to the tail.
This does NOT bound that debit after multiplying by the growing supply. -/
theorem eventually_relative_debit_lt (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, tailCost c N+δ/2 < δ := by
  filter_upwards [(tendsto_tailCost c).eventually_lt_const (by linarith : 0 < δ/2)]
    with N hN
  linarith only [hN]

end RiemannGaussian.ZetaRieszSharpSupplyFloor
