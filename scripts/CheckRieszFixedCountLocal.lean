/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import CheckRieszCentralCapacityTransfer
import RiemannGaussian.ZetaRieszFixedCountBand
import CheckRieszFullPositiveFive
import Mathlib.Tactic.Linter

/-!
# Local whole-sum payments for six through fifty-five prime factors

The old six-prime period and forty-nine new prime-count sectors are paid
together, disjoint from every earlier population. All finite cover premises are discharged by cached assemblies;
the exact signed rest and every favorable coupled observation are retained.
-/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget
open RieszCentralCapacityTransfer
namespace RieszFixedCountLocal

/-- The certified signed floor gain is uniform across the square-root saddle band, and belongs only to the literal paid population. -/
theorem eventually_period_floor    {u b δ : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
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
      let Z := ZetaRieszFixedCountBand.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      let E := S ∩ (P ∪ I ∪ H ∪ Q ∪ Z)
      u^(N+1)*((∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ Z, f n).re 0)+
        (1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-ZetaRieszTriplePeriod.allocationBound N ≤ u^(N+1)*(∑ n ∈ E, f n).re := by
  have htriple := ZetaRieszJointTriplePayment.eventually_signed_population_bound hu hU hm hy hhu hε
  have hsix := ZetaRieszFixedCountBand.eventually_population_bound hu hU hm hy hhu hε
  have hcutoff := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSaddleBand.eventually_cutoff_ratio hu.le hU)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  filter_upwards [eventually_full_five_period_floor_with_radial RieszPositiveFiveInterior.Assembly.part0000_tree
      RieszFullPositiveFiveTransfer.checked_cover RieszFullPositiveFiveTransfer.checked_total hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hcutoff,hboundary,htriple,hsix,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszSaddleBand.eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/1000))]
    with j hpay hcutoff hboundary htriple hsix hN hsmallN v
  dsimp only
  intro hpeak hv hvu
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
  let Z := ZetaRieszFixedCountBand.population v y
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy,Real.pi_lt_four]
  have hNRlarge : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo : (39/20 : ℝ)*N ≤ v-Real.pi/|y| := by linarith only [hv,hpi,hNRlarge]
  have hhi : v+Real.pi/|y| ≤ (203/100 : ℝ)*N := by
    change Real.sqrt (N : ℝ)+1 ≤ (1/1000 : ℝ)*N at hsmallN
    linarith only [hvu,hpi,hsmallN,hNRlarge]
  have hh : 0 < h := by dsimp only [h]; positivity
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at ht
    have hb := hcutoff (T i) (by linarith only [ht.1,hv,hpi])
      (by linarith only [ht.2,hvu,hpi,hh])
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high]
    constructor <;> linarith [hb.1,hb.2]
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  have hnewbin : ∀ i ∈ Finset.range (8*m),
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at hcell
    have htl : 2*(N : ℝ)-1 ≤ T i := by linarith only [hcell.1,hv,hpi]
    have htu : T i+h ≤ 2*(N : ℝ)+Real.sqrt N+1 := by linarith only [hcell.2,hvu,hpi]
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
    u^(N+1)*((m : ℝ)/90000*Vz*h) at hcostZ
  have hZP : Disjoint Z P := by
    apply Finset.disjoint_left.mpr
    intro n hn hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with h3 | h45
    · exact (Finset.disjoint_left.mp (ZetaRieszFixedCountBand.disjoint_balanced hv100 hy S (T i) h)) hn h3
    rcases Finset.mem_union.mp h45 with h4 | h5
    · exact (Finset.disjoint_left.mp (ZetaRieszFixedCountBand.disjoint_adverse hv100 hy
        (clippedSupport S) L (T i) h y (δ*N))) hn h4
    obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
    exact Finset.disjoint_left.mp (ZetaRieszFixedCountBand.disjoint_supply hv100 hy
      (T i) h y (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)) hn hw
  have hZI : Disjoint Z I := ZetaRieszFixedCountBand.disjoint_interior hv100 hy _ _ _ _ _ _
  have hZH : Disjoint Z H := ZetaRieszFixedCountBand.disjoint_head hv100 hy _ _ _ _ _
  have hZEold : Z ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hZcore hn,?_⟩
    intro he
    rcases Finset.mem_union.mp he with hpi | hh
    · rcases Finset.mem_union.mp hpi with hp | hi
      · exact Finset.disjoint_left.mp hZP hn hp
      · exact Finset.disjoint_left.mp hZI hn hi
    · exact Finset.disjoint_left.mp hZH hn hh
  have hZQ : Disjoint Z Q := ZetaRieszFixedCountBand.disjoint_triple hv100 hy
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
  have hc := ZetaRieszSaddleBand.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    (by omega) hm hv (by linarith only [hvu])
  have hhalf : (1/32)*(Real.exp (-v/2)*v^N/N.factorial)/1000+Vq/6250+Vz/90000 ≤
      (1/4800 : ℝ)*V₀ := by
    linarith only [hVr,hV₀,hVqBase,hVzBase]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
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
  have hsplit : (∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z), f n)+(∑ n ∈ S ∩ (P ∪ I ∪ H ∪ Q ∪ Z), f n) =
      ZetaRieszParityPacket.coreResponse u y N K := by
    change _ = ∑ n ∈ S, f n
    simpa only [add_comm] using Finset.sum_inter_add_sum_sdiff S (P ∪ I ∪ H ∪ Q ∪ Z) f
  have hr := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hr
  nlinarith only [hbody, congrArg (fun x : ℝ => u^(N+1)*x) hr]

#print axioms eventually_period_floor

set_option maxHeartbeats 400000 in
/-- The certified signed ceiling gain is uniform across the square-root saddle band, and belongs only to the literal paid population. -/
theorem eventually_period_ceiling    {u b δ : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
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
      let Z := ZetaRieszFixedCountBand.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      Real.cos (y*v) = -1 → 2*(N : ℝ) ≤ v → v ≤ 2*N+Real.sqrt N →
      let E := S ∩ (P ∪ I ∪ H ∪ Q ∪ Z)
      u^(N+1)*(∑ n ∈ E, f n).re ≤ u^(N+1)*((∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ Z, f n).re 0)-
        (1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N+ZetaRieszTriplePeriod.allocationBound N := by
  have htriple := ZetaRieszJointTriplePayment.eventually_signed_population_bound hu hU hm hy hhu hε
  have hsix := ZetaRieszFixedCountBand.eventually_population_bound hu hU hm hy hhu hε
  have hcutoff := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSaddleBand.eventually_cutoff_ratio hu.le hU)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  filter_upwards [eventually_full_five_period_ceiling_with_radial RieszPositiveFiveInterior.Assembly.part0000_tree
      RieszFullPositiveFiveTransfer.checked_cover RieszFullPositiveFiveTransfer.checked_total hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hcutoff,hboundary,htriple,hsix,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszSaddleBand.eventually_sqrt_add_one_le_mul (by norm_num : (0 : ℝ) < 1/1000))]
    with j hpay hcutoff hboundary htriple hsix hN hsmallN v
  dsimp only
  intro hpeak hv hvu
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
  let Z := ZetaRieszFixedCountBand.population v y
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy,Real.pi_lt_four]
  have hNRlarge : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo : (39/20 : ℝ)*N ≤ v-Real.pi/|y| := by linarith only [hv,hpi,hNRlarge]
  have hhi : v+Real.pi/|y| ≤ (203/100 : ℝ)*N := by
    change Real.sqrt (N : ℝ)+1 ≤ (1/1000 : ℝ)*N at hsmallN
    linarith only [hvu,hpi,hsmallN,hNRlarge]
  have hh : 0 < h := by dsimp only [h]; positivity
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at ht
    have hb := hcutoff (T i) (by linarith only [ht.1,hv,hpi])
      (by linarith only [ht.2,hvu,hpi,hh])
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high]
    constructor <;> linarith [hb.1,hb.2]
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  have hnewbin : ∀ i ∈ Finset.range (8*m),
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at hcell
    have htl : 2*(N : ℝ)-1 ≤ T i := by linarith only [hcell.1,hv,hpi]
    have htu : T i+h ≤ 2*(N : ℝ)+Real.sqrt N+1 := by linarith only [hcell.2,hvu,hpi]
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
    u^(N+1)*((m : ℝ)/90000*Vz*h) at hcostZ
  have hZP : Disjoint Z P := by
    apply Finset.disjoint_left.mpr
    intro n hn hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with h3 | h45
    · exact (Finset.disjoint_left.mp (ZetaRieszFixedCountBand.disjoint_balanced hv100 hy S (T i) h)) hn h3
    rcases Finset.mem_union.mp h45 with h4 | h5
    · exact (Finset.disjoint_left.mp (ZetaRieszFixedCountBand.disjoint_adverse hv100 hy
        (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N))) hn h4
    by_cases hs : 0 ≤ Real.cos (y*T i)-|y| * h
    · rw [if_pos hs] at h5
      obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
      exact Finset.disjoint_left.mp (ZetaRieszFixedCountBand.disjoint_supply hv100 hy
        (T i) h (Real.pi/T i) (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)) hn hw
    · simp only [if_neg hs,Finset.notMem_empty] at h5
  have hZI : Disjoint Z I := ZetaRieszFixedCountBand.disjoint_interior hv100 hy _ _ _ _ _ _
  have hZH : Disjoint Z H := ZetaRieszFixedCountBand.disjoint_head hv100 hy _ _ _ _ _
  have hZEold : Z ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hZcore hn,?_⟩
    intro he
    rcases Finset.mem_union.mp he with hpi | hh
    · rcases Finset.mem_union.mp hpi with hp | hi
      · exact Finset.disjoint_left.mp hZP hn hp
      · exact Finset.disjoint_left.mp hZI hn hi
    · exact Finset.disjoint_left.mp hZH hn hh
  have hZQ : Disjoint Z Q := ZetaRieszFixedCountBand.disjoint_triple hv100 hy
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
  have hc := ZetaRieszSaddleBand.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    (by omega) hm hv (by linarith only [hvu])
  have hhalf : (1/32)*(Real.exp (-v/2)*v^N/N.factorial)/1000+Vq/6250+Vz/90000 ≤
      (1/4800 : ℝ)*V₀ := by
    linarith only [hVr,hV₀,hVqBase,hVzBase]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
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
  have hsplit : (∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ Z), f n)+(∑ n ∈ S ∩ (P ∪ I ∪ H ∪ Q ∪ Z), f n) =
      ZetaRieszParityPacket.coreResponse u y N K := by
    change _ = ∑ n ∈ S, f n
    simpa only [add_comm] using Finset.sum_inter_add_sum_sdiff S (P ∪ I ∪ H ∪ Q ∪ Z) f
  have hr := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hr
  nlinarith only [hbody, congrArg (fun x : ℝ => u^(N+1)*x) hr]

#print axioms eventually_period_ceiling

end RieszFixedCountLocal

#lint+ in RieszFixedCountLocal
