/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import CheckRieszCentralCapacityTransfer
import RiemannGaussian.ZetaRieszSixCofactorPeriod
import CheckRieszFullPositiveFive
import Mathlib.Tactic.Linter

/-!
# Concrete whole comparisons with joint six-prime cancellation

The broad, variable-coefficient six-prime period is paid once, disjoint from every earlier
population. All finite cover premises are discharged by cached assemblies;
the exact signed rest and every favorable coupled observation are retained.
-/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget
open RieszCentralCapacityTransfer
namespace RieszSixCofactorJoint

/-- Both literal prime periods are paid in the whole floor, with all numerical cover premises discharged and the remaining carrier kept signed. -/
theorem eventually_combined_floor    {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
      let Q := ZetaRieszTriplePeriod.population v y
      let Z := ZetaRieszSixCofactorPeriod.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z ∪ D), f n).re+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ Z, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        ((1/16)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨baseErr,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  let err := fun j => baseErr j+ZetaRieszTriplePeriod.allocationBound
    (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
  refine ⟨m,err,hm,fun j => add_nonneg (he0 j)
    (ZetaRieszTriplePeriod.allocationBound_nonneg _),?_,?_⟩
  · simpa only [err,Function.comp_def,mul_zero,add_zero] using heLim.add
      ((ZetaRieszTriplePeriod.tendsto_allocationBound.comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder))
  have htriple := ZetaRieszJointTriplePayment.eventually_signed_population_bound hu hU hm hy hhu hε
  have hsix := ZetaRieszSixCofactorPeriod.eventually_signed_population_bound hu hU hm hy hhu hε
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hcutoff := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveInterior.eventually_saddle_cutoff_ratio hu.le hU)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_full_five_period_floor_with_radial RieszPositiveFiveInterior.Assembly.part0000_tree
      RieszFullPositiveFiveTransfer.checked_cover RieszFullPositiveFiveTransfer.checked_total hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hcutoff,hboundary,howner,htriple,hsix,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ))] with j hpay hJ hcutoff hboundary howner htriple hsix hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
  let Q := ZetaRieszTriplePeriod.population v y
  let Z := ZetaRieszSixCofactorPeriod.population v y
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy,Real.pi_lt_four]
  have hnewbin : ∀ i ∈ Finset.range (8*m),
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at hcell
    have htl : 2*(N : ℝ)-1 ≤ T i := by linarith only [hcell.1,hv,hpi]
    have htu : T i+h ≤ 2*(N : ℝ)+1 := by linarith only [hcell.2,hvu,hpi]
    have ht0 : 0 < T i := by linarith only [hcell.1,hlo,hNR]
    have hh0 : 0 < T i+h := by linarith only [ht0,hh]
    have hlow := (hcutoff (T i+h) (by linarith only [htl,hh]) htu).1
    have hhigh := (hcutoff (T i) htl (by linarith only [htu,hh])).2
    exact ⟨(le_div_iff₀ hh0).mp hlow,(div_le_iff₀ ht0).mp hhigh⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins hnewbin
  have hHbase : H ⊆ S\(P ∪ I ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ I) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ I ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1600*V₀*h at hcostH
  have hNRlarge : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv100 : 100 ≤ v := by linarith only [hNRlarge,hv]
  obtain ⟨hQcore,Vq,hVq,hVqBase,hcostQ⟩ := htriple v hpeak hlo hhi
  change |u^(N+1)*(∑ n ∈ Q, f n).re| ≤
    u^(N+1)*((m : ℝ)/6250*Vq*h)+ZetaRieszTriplePeriod.allocationBound N at hcostQ
  have hQP : Disjoint Q P := by
    apply Finset.disjoint_left.mpr
    intro n hn hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with h3 | h45
    · exact (Finset.disjoint_left.mp (ZetaRieszTriplePeriod.disjoint_balanced S (T i) h hv100 hy)) hn h3
    rcases Finset.mem_union.mp h45 with h4 | h5
    · exact (Finset.disjoint_left.mp (ZetaRieszJointTriplePayment.disjoint_adverse hv100 hy
        (clippedSupport S) L (T i) h y (δ*N))) hn h4
    obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
    exact Finset.disjoint_left.mp (ZetaRieszJointTriplePayment.disjoint_supply hv100 hy
      (T i) h y (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)) hn hw
  have hQI : Disjoint Q I := ZetaRieszJointTriplePayment.disjoint_interior hv100 hy _ _ _ _ _ _
  have hQH : Disjoint Q H := ZetaRieszJointTriplePayment.disjoint_head hv100 hy _ _ _ _ _
  have hQD : Disjoint Q D := ZetaRieszJointTriplePayment.disjoint_owner hv100 hy _ _
  have hQE : Q ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hQcore hn,?_⟩
    intro he
    rcases Finset.mem_union.mp he with hpi | hh
    · rcases Finset.mem_union.mp hpi with hp | hi
      · exact Finset.disjoint_left.mp hQP hn hp
      · exact Finset.disjoint_left.mp hQI hn hi
    · exact Finset.disjoint_left.mp hQH hn hh
  obtain ⟨hZcore,Vz,hVz,hVzBase,hcostZ⟩ := hsix v hpeak hv (by linarith [hvu]) hlo hhi
  change |u^(N+1)*(∑ n ∈ Z, f n).re| ≤
    u^(N+1)*((m : ℝ)/100000*Vz*h) at hcostZ
  have hZP : Disjoint Z P := by
    apply Finset.disjoint_left.mpr
    intro n hn hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with h3 | h45
    · exact (Finset.disjoint_left.mp (ZetaRieszSixCofactorPeriod.disjoint_balanced hv100 hy S (T i) h)) hn h3
    rcases Finset.mem_union.mp h45 with h4 | h5
    · exact (Finset.disjoint_left.mp (ZetaRieszSixCofactorPeriod.disjoint_adverse hv100 hy
        (clippedSupport S) L (T i) h y (δ*N))) hn h4
    obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
    exact Finset.disjoint_left.mp (ZetaRieszSixCofactorPeriod.disjoint_supply hv100 hy
      (T i) h y (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)) hn hw
  have hZI : Disjoint Z I := ZetaRieszSixCofactorPeriod.disjoint_interior hv100 hy _ _ _ _ _ _
  have hZH : Disjoint Z H := ZetaRieszSixCofactorPeriod.disjoint_head hv100 hy _ _ _ _ _
  have hZD : Disjoint Z D := ZetaRieszSixCofactorPeriod.disjoint_owner hv100 hy _ _
  have hZEold : Z ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hZcore hn,?_⟩
    intro he
    rcases Finset.mem_union.mp he with hpi | hh
    · rcases Finset.mem_union.mp hpi with hp | hi
      · exact Finset.disjoint_left.mp hZP hn hp
      · exact Finset.disjoint_left.mp hZI hn hi
    · exact Finset.disjoint_left.mp hZH hn hh
  have hZQ : Disjoint Z Q := ZetaRieszSixCofactorPeriod.disjoint_triple hv100 hy
  have hZE : Z ⊆ S\(P ∪ I ∪ H ∪ Q) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hZEold hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro he
    rcases Finset.mem_union.mp he with he | hq
    · exact hnnot he
    · exact Finset.disjoint_left.mp hZQ hn hq
  have hwhole := ZetaRieszJointOwnerPayment.floor_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := (∑ n ∈ I, max 0 (f n).re)+(m : ℝ)/1200*V₀*h) (by nlinarith only [hpaid])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszSaddleCredit.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    (by omega) hm hv (by linarith only [hvu])
  have hhalf : (1/32)*(Real.exp (-v/2)*v^N/N.factorial)/1000+Vq/6250+Vz/100000 ≤
      (1/4800 : ℝ)*V₀ := by
    linarith only [hVr,hV₀,hVqBase,hVzBase]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ I) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hDold : D ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hDpre : D ⊆ S\(P ∪ I ∪ H ∪ Q) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDold hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro he
    rcases Finset.mem_union.mp he with he | hq
    · exact hnnot he
    · exact Finset.disjoint_left.mp hQD hq hn
  have hD : D ⊆ S\(P ∪ I ∪ H ∪ Q ∪ Z) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDpre hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro he
    rcases Finset.mem_union.mp he with he | hz
    · exact hnnot he
    · exact Finset.disjoint_left.mp hZD hz hn
  have hcostD := howner (S\(P ∪ I)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hpaidQ := ZetaRieszJointTriplePayment.scaled_floor_after_signed_payment f hQE hcostQ
    (g := u^(N+1)*((∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+(m : ℝ)/4800*V₀*h))
    (whole := u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re)
    (by nlinarith only [hscaled])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hpaidQ
  have hpaidZ := ZetaRieszJointTriplePayment.scaled_floor_after_signed_payment f hZE hcostZ
    (g := u^(N+1)*((∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+
      max (∑ n ∈ Q, f n).re 0+(m : ℝ)/4800*V₀*h-(m : ℝ)/6250*Vq*h)-
        ZetaRieszTriplePeriod.allocationBound N)
    (whole := u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re)
    (by nlinarith only [hpaidQ])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hpaidZ
  have hbody : u^(N+1)*(∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z), f n).re+
      (u^(N+1)*((∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ Z, f n).re 0)+
        (1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-
          ZetaRieszTriplePeriod.allocationBound N) ≤
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    nlinarith only [hc,hrs,hpaidZ]
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z ∪ D), f n).re+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ Z, f n).re 0+max (∑ n ∈ D, f n).re 0)+
    ((1/16)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-(baseErr j+ZetaRieszTriplePeriod.allocationBound N) ≤ _
  nlinarith only [hbound,(abs_le.mp herr).2]

#print axioms eventually_combined_floor

/-- The same disjoint six-prime period is paid in the whole ceiling, with all numerical cover premises discharged and the remaining carrier kept signed. -/
theorem eventually_combined_ceiling    {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
      let Q := ZetaRieszTriplePeriod.population v y
      let Z := ZetaRieszSixCofactorPeriod.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z ∪ D), f n).re+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ Z, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          ((1/16)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨baseErr,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  let err := fun j => baseErr j+ZetaRieszTriplePeriod.allocationBound
    (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
  refine ⟨m,err,hm,fun j => add_nonneg (he0 j)
    (ZetaRieszTriplePeriod.allocationBound_nonneg _),?_,?_⟩
  · simpa only [err,Function.comp_def,mul_zero,add_zero] using heLim.add
      ((ZetaRieszTriplePeriod.tendsto_allocationBound.comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder))
  have htriple := ZetaRieszJointTriplePayment.eventually_signed_population_bound hu hU hm hy hhu hε
  have hsix := ZetaRieszSixCofactorPeriod.eventually_signed_population_bound hu hU hm hy hhu hε
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hcutoff := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveInterior.eventually_saddle_cutoff_ratio hu.le hU)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_full_five_period_ceiling_with_radial RieszPositiveFiveInterior.Assembly.part0000_tree
      RieszFullPositiveFiveTransfer.checked_cover RieszFullPositiveFiveTransfer.checked_total hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hcutoff,hboundary,howner,htriple,hsix,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ))] with j hpay hJ hcutoff hboundary howner htriple hsix hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
  let Q := ZetaRieszTriplePeriod.population v y
  let Z := ZetaRieszSixCofactorPeriod.population v y
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy,Real.pi_lt_four]
  have hnewbin : ∀ i ∈ Finset.range (8*m),
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at hcell
    have htl : 2*(N : ℝ)-1 ≤ T i := by linarith only [hcell.1,hv,hpi]
    have htu : T i+h ≤ 2*(N : ℝ)+1 := by linarith only [hcell.2,hvu,hpi]
    have ht0 : 0 < T i := by linarith only [hcell.1,hlo,hNR]
    have hh0 : 0 < T i+h := by linarith only [ht0,hh]
    have hlow := (hcutoff (T i+h) (by linarith only [htl,hh]) htu).1
    have hhigh := (hcutoff (T i) htl (by linarith only [htu,hh])).2
    exact ⟨(le_div_iff₀ hh0).mp hlow,(div_le_iff₀ ht0).mp hhigh⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins hnewbin
  have hHbase : H ⊆ S\(P ∪ I ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ I) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ I ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1600*V₀*h at hcostH
  have hNRlarge : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv100 : 100 ≤ v := by linarith only [hNRlarge,hv]
  obtain ⟨hQcore,Vq,hVq,hVqBase,hcostQ⟩ := htriple v hpeak hlo hhi
  change |u^(N+1)*(∑ n ∈ Q, f n).re| ≤
    u^(N+1)*((m : ℝ)/6250*Vq*h)+ZetaRieszTriplePeriod.allocationBound N at hcostQ
  have hQP : Disjoint Q P := by
    apply Finset.disjoint_left.mpr
    intro n hn hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with h3 | h45
    · exact (Finset.disjoint_left.mp (ZetaRieszTriplePeriod.disjoint_balanced S (T i) h hv100 hy)) hn h3
    rcases Finset.mem_union.mp h45 with h4 | h5
    · exact (Finset.disjoint_left.mp (ZetaRieszJointTriplePayment.disjoint_adverse hv100 hy
        (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N))) hn h4
    by_cases hs : 0 ≤ Real.cos (y*T i)-|y| * h
    · rw [if_pos hs] at h5
      obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
      exact Finset.disjoint_left.mp (ZetaRieszJointTriplePayment.disjoint_supply hv100 hy
        (T i) h (Real.pi/T i) (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)) hn hw
    · simp only [if_neg hs,Finset.notMem_empty] at h5
  have hQI : Disjoint Q I := ZetaRieszJointTriplePayment.disjoint_interior hv100 hy _ _ _ _ _ _
  have hQH : Disjoint Q H := ZetaRieszJointTriplePayment.disjoint_head hv100 hy _ _ _ _ _
  have hQD : Disjoint Q D := ZetaRieszJointTriplePayment.disjoint_owner hv100 hy _ _
  have hQE : Q ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hQcore hn,?_⟩
    intro he
    rcases Finset.mem_union.mp he with hpi | hh
    · rcases Finset.mem_union.mp hpi with hp | hi
      · exact Finset.disjoint_left.mp hQP hn hp
      · exact Finset.disjoint_left.mp hQI hn hi
    · exact Finset.disjoint_left.mp hQH hn hh
  obtain ⟨hZcore,Vz,hVz,hVzBase,hcostZ⟩ := hsix v hpeak hv (by linarith [hvu]) hlo hhi
  change |u^(N+1)*(∑ n ∈ Z, f n).re| ≤
    u^(N+1)*((m : ℝ)/100000*Vz*h) at hcostZ
  have hZP : Disjoint Z P := by
    apply Finset.disjoint_left.mpr
    intro n hn hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with h3 | h45
    · exact (Finset.disjoint_left.mp (ZetaRieszSixCofactorPeriod.disjoint_balanced hv100 hy S (T i) h)) hn h3
    rcases Finset.mem_union.mp h45 with h4 | h5
    · exact (Finset.disjoint_left.mp (ZetaRieszSixCofactorPeriod.disjoint_adverse hv100 hy
        (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N))) hn h4
    by_cases hs : 0 ≤ Real.cos (y*T i)-|y| * h
    · rw [if_pos hs] at h5
      obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
      exact Finset.disjoint_left.mp (ZetaRieszSixCofactorPeriod.disjoint_supply hv100 hy
        (T i) h (Real.pi/T i) (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)) hn hw
    · simp only [if_neg hs,Finset.notMem_empty] at h5
  have hZI : Disjoint Z I := ZetaRieszSixCofactorPeriod.disjoint_interior hv100 hy _ _ _ _ _ _
  have hZH : Disjoint Z H := ZetaRieszSixCofactorPeriod.disjoint_head hv100 hy _ _ _ _ _
  have hZD : Disjoint Z D := ZetaRieszSixCofactorPeriod.disjoint_owner hv100 hy _ _
  have hZEold : Z ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hZcore hn,?_⟩
    intro he
    rcases Finset.mem_union.mp he with hpi | hh
    · rcases Finset.mem_union.mp hpi with hp | hi
      · exact Finset.disjoint_left.mp hZP hn hp
      · exact Finset.disjoint_left.mp hZI hn hi
    · exact Finset.disjoint_left.mp hZH hn hh
  have hZQ : Disjoint Z Q := ZetaRieszSixCofactorPeriod.disjoint_triple hv100 hy
  have hZE : Z ⊆ S\(P ∪ I ∪ H ∪ Q) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hZEold hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro he
    rcases Finset.mem_union.mp he with he | hq
    · exact hnnot he
    · exact Finset.disjoint_left.mp hZQ hn hq
  have hwhole := ZetaRieszJointOwnerPayment.ceiling_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := (m : ℝ)/1200*V₀*h-(∑ n ∈ I, min (f n).re 0)) (by nlinarith only [hpaid])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszSaddleCredit.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    (by omega) hm hv (by linarith only [hvu])
  have hhalf : (1/32)*(Real.exp (-v/2)*v^N/N.factorial)/1000+Vq/6250+Vz/100000 ≤
      (1/4800 : ℝ)*V₀ := by
    linarith only [hVr,hV₀,hVqBase,hVzBase]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ I) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hDold : D ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hDpre : D ⊆ S\(P ∪ I ∪ H ∪ Q) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDold hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro he
    rcases Finset.mem_union.mp he with he | hq
    · exact hnnot he
    · exact Finset.disjoint_left.mp hQD hq hn
  have hD : D ⊆ S\(P ∪ I ∪ H ∪ Q ∪ Z) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDpre hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro he
    rcases Finset.mem_union.mp he with he | hz
    · exact hnnot he
    · exact Finset.disjoint_left.mp hZD hz hn
  have hcostD := howner (S\(P ∪ I)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hpaidQ := ZetaRieszJointTriplePayment.scaled_ceiling_after_signed_payment f hQE hcostQ
    (g := u^(N+1)*((m : ℝ)/4800*V₀*h-((∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0)))
    (whole := u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re)
    (by nlinarith only [hscaled])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hpaidQ
  have hpaidZ := ZetaRieszJointTriplePayment.scaled_ceiling_after_signed_payment f hZE hcostZ
    (g := u^(N+1)*((m : ℝ)/4800*V₀*h-(m : ℝ)/6250*Vq*h-
      ((∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0))-
        ZetaRieszTriplePeriod.allocationBound N)
    (whole := u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re)
    (by nlinarith only [hpaidQ])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hpaidZ
  have hbody : u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re ≤
      u^(N+1)*(∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z), f n).re-
      ((1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-
        u^(N+1)*((∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ Z, f n).re 0)-
          ZetaRieszTriplePeriod.allocationBound N) := by
    nlinarith only [hc,hrs,hpaidZ]
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z ∪ D), f n).re+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ Z, f n).re 0+min (∑ n ∈ D, f n).re 0)-
    ((1/16)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+(baseErr j+ZetaRieszTriplePeriod.allocationBound N)
  nlinarith only [hbound,(abs_le.mp herr).1]

#print axioms eventually_combined_ceiling

end RieszSixCofactorJoint

#lint+ in RieszSixCofactorJoint
