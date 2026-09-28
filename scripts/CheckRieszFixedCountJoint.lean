/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import CheckRieszFixedCountLocal
import RiemannGaussian.ZetaRieszSaddlePacking
import RiemannGaussian.ZetaRieszSixPrimeSecondReflection
import Mathlib.Tactic.Linter

/-! # Whole signed comparisons paying forty-nine additional prime counts
Each complete period contributes its own certified signed gain. All labels,
allocation weights and favorable period observations are literal. -/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget
open ZetaRieszMultiPeriodSix (center)
namespace RieszFixedCountJoint

/-- The exact paid period and its favorable signed observation; `upper`
selects the ceiling's original populations, not a new arithmetic model. -/
def localData (upper : Bool) (u b δ y v : ℝ) (N K M m : ℕ) : Finset ℕ × ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := if upper then (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅))) else (Finset.range (8*m)).biUnion (fun i =>
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
  (S ∩ (P ∪ I ∪ H ∪ Q ∪ Z), if upper then
    (∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+
      min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ Z, f n).re 0
    else (∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+
      max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ Z, f n).re 0)

/-- Paid labels always retain the exact original core. -/
theorem localData_subset (upper : Bool) (u b δ y v : ℝ) (N K M m : ℕ) :
    (localData upper u b δ y v N K M m).1 ⊆ ZetaRieszParityPacket.coreBand u N K :=
  Finset.inter_subset_left

private theorem supply_log {t h y : ℝ} {lo H : Fin 4 → ℝ} {n : ℕ}
    (hn : n ∈ ZetaRieszJointPrimeCells.supplyCell t h y lo H) :
    t < Real.log n ∧ Real.log n ≤ t+h := by
  unfold ZetaRieszJointPrimeCells.supplyCell at hn
  split at hn
  · obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    have hq0 : (∏ i, q i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ =>
      (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (Fintype.mem_piFinset.mp hq i)).1.ne_zero)
    have hp' := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hq0) (by exact_mod_cast hp'.1.ne_zero)]
    constructor <;> linarith [hp'.2.1,hp'.2.2]
  · simp only [Finset.notMem_empty] at hn

/-- Every paid label belongs to its own half-open full phase period. -/
theorem localData_log {upper : Bool} {u b δ y v : ℝ} {N K M m n : ℕ}
    (hm : 0 < m) (hy : 54 ≤ |y|) (hv : 100 ≤ v)
    (hn : n ∈ (localData upper u b δ y v N K M m).1) :
    v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| := by
  have hy0 : 0 < |y| := by linarith
  dsimp only [localData] at hn
  have hp := (Finset.mem_inter.mp hn).2
  rcases Finset.mem_union.mp hp with hpiHQ | hz
  swap
  · have hb := ZetaRieszFixedCountBand.population_data hv hy hz
    exact ⟨hb.2.2.1,hb.2.2.2.1⟩
  rcases Finset.mem_union.mp hpiHQ with hpiH | hq
  swap
  · have hb := ZetaRieszTriplePeriod.population_data hv hy hq
    exact ⟨hb.2.2.1,hb.2.2.2.1⟩
  rcases Finset.mem_union.mp hpiH with hpi | hh
  swap
  · have hb := (ZetaRieszPositiveFiveBoundary.mem_periodPopulation hm hy0 _ _ _ n).mp hh
    exact ⟨hb.2.2.2.1,hb.2.2.2.2.1⟩
  rcases Finset.mem_union.mp hpi with hp | hi
  swap
  · obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hi
    have hb := (Finset.mem_filter.mp hn).2.2.2
    have hc := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hc.1.trans_lt hb.1,hb.2.1.trans hc.2⟩
  have hcell (i : ℕ) (hi : i ∈ Finset.range (8*m))
      (hn : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| < Real.log n ∧
        Real.log n ≤ v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|+Real.pi/(4*m*|y|)) :
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| := by
    have hc := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hc.1.trans_lt hn.1,hn.2.trans hc.2⟩
  cases upper <;> simp only [Bool.false_eq_true,↓reduceIte] at hp
  all_goals
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hp
    apply hcell i hi
    rcases Finset.mem_union.mp hn with h3 | h45
    · have hb := (Finset.mem_filter.mp h3).2.2.2
      exact ⟨hb.1,hb.2.1⟩
    rcases Finset.mem_union.mp h45 with h4 | h5
    · have hb := (Finset.mem_filter.mp h4).2.2.2.2
      exact ⟨hb.1,hb.2.1⟩
  · obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
    exact supply_log hw
  · split at h5
    · obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h5
      exact supply_log hw
    · simp only [Finset.notMem_empty] at h5


set_option maxHeartbeats 600000 in
/-- The literal whole floor accumulates signed credit across a square-root
saddle band. Prime-completion errors are summed, the owner band and global
companion error are paid once, and every favorable observation stays signed. -/
theorem eventually_combined_floor {u b δ : ℝ} {M : ℕ}
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
      let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
      let data := fun i => localData false u b δ y (center v y i) N K M m
      let E := B.biUnion (fun i => (data i).1)
      let D := ZetaRieszJointOwnerPayment.population (S\E) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ 2*(N : ℝ) ≤ v ∧ v ≤ 2*N+1/2 ∧
      u^(N+1)*((∑ n ∈ S\(E ∪ D), f n).re+(∑ i ∈ B, (data i).2)+max (∑ n ∈ D, f n).re 0)+
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,_,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  have hu0 : 0 ≤ u := by linarith
  have hy0 : 0 < |y| := by linarith
  obtain ⟨baseErr,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error hu0 hU y
  let err := fun j => baseErr j+((ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)+1)*
    ZetaRieszTriplePeriod.allocationBound (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
  refine ⟨m,err,hm,fun j => add_nonneg (he0 j)
    (mul_nonneg (by positivity) (ZetaRieszTriplePeriod.allocationBound_nonneg _)),?_,?_⟩
  · simpa only [err,Function.comp_def,add_zero] using heLim.add
      (ZetaRieszSaddlePacking.tendsto_polynomial_allocation.comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  have hlocal := RieszFixedCountLocal.eventually_period_floor hu hU y hy hm hhu hε hδ hδu hb hsmall hcover
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit (abs_pos.mp hy0) (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [hlocal,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSaddlePacking.eventually_count_le y),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
    with j hj howner hcount hN
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  obtain ⟨v,hv,hvu,hphase⟩ := ZetaRieszCapacityPhaseBudget.exists_negative_peak hy (2*(N : ℝ))
  let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
  let data := fun i => localData false u b δ y (center v y i) N K M m
  let E := B.biUnion (fun i => (data i).1)
  let D := ZetaRieszJointOwnerPayment.population (S\E) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hv100 : 100 ≤ v := by
    have hnR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hv,hnR]
  have hdisj : ∀ i ∈ B, ∀ k ∈ B, i ≠ k → Disjoint (data i).1 (data k).1 := by
    have hsup (i n : ℕ) (hn : n ∈ (data i).1) :
        center v y i-Real.pi/|y| < Real.log n ∧ Real.log n ≤ center v y i+Real.pi/|y| := by
      apply localData_log hm hy (le_trans hv100 ?_) hn
      dsimp only [center]
      exact le_add_of_nonneg_right (by positivity)
    intro i _ k _ hik
    exact ZetaRieszSaddlePacking.disjoint_of_log_support hy0 (fun i => (data i).1) hsup hik
  have hpay : ∀ i ∈ B, u^(N+1)*(data i).2+(1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-
        ZetaRieszTriplePeriod.allocationBound N ≤ u^(N+1)*(∑ n ∈ (data i).1, f n).re := by
    intro i hi
    have hc := ZetaRieszSaddlePacking.center_bounds (by omega : 1 ≤ N) hv hvu hi
    have hp := hj (center v y i)
      (by rw [ZetaRieszMultiPeriodSix.center_phase (abs_pos.mp hy0),hphase]) hc.1 hc.2
    simpa only [data,localData,Bool.false_eq_true,↓reduceIte] using hp
  have hwhole := ZetaRieszSaddlePacking.floor_union S B (fun i => (data i).1) f
    (fun i => (data i).2) (fun i _ => localData_subset false u b δ y (center v y i) N K M m) hdisj hpay
  have hD : D ⊆ S\E := ZetaRieszJointOwnerPayment.population_subset _ _
  have hcostD := howner (S\E) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(∑ n ∈ S\E, f n).re+(u^(N+1)*(∑ i ∈ B, (data i).2)+(B.card : ℝ)*((1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-ZetaRieszTriplePeriod.allocationBound N)) ≤ u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    change _ ≤ u^(N+1)*(∑ n ∈ S, f n).re
    nlinarith only [hwhole]
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f (pow_nonneg hu0 (N+1)) hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  have hcost : (B.card : ℝ)*ZetaRieszTriplePeriod.allocationBound N ≤
      ((N : ℝ)+1)*ZetaRieszTriplePeriod.allocationBound N := by
    apply mul_le_mul_of_nonneg_right _ (ZetaRieszTriplePeriod.allocationBound_nonneg N)
    simpa only [B,Finset.card_range] using hcount
  refine ⟨v,hphase,hv,hvu,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(E ∪ D), f n).re+(∑ i ∈ B, (data i).2)+max (∑ n ∈ D, f n).re 0)+
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-(baseErr j+((N : ℝ)+1)*ZetaRieszTriplePeriod.allocationBound N) ≤ _
  nlinarith only [hbound,hcost,(abs_le.mp herr).2]

#print axioms eventually_combined_floor

set_option maxHeartbeats 600000 in
/-- The literal whole ceiling accumulates signed credit across a square-root
saddle band. Prime-completion errors are summed, the owner band and global
companion error are paid once, and every favorable observation stays signed. -/
theorem eventually_combined_ceiling {u b δ : ℝ} {M : ℕ}
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
      let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
      let data := fun i => localData true u b δ y (center v y i) N K M m
      let E := B.biUnion (fun i => (data i).1)
      let D := ZetaRieszJointOwnerPayment.population (S\E) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ 2*(N : ℝ) ≤ v ∧ v ≤ 2*N+1/2 ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(E ∪ D), f n).re+(∑ i ∈ B, (data i).2)+min (∑ n ∈ D, f n).re 0)-
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,hm,_,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  have hu0 : 0 ≤ u := by linarith
  have hy0 : 0 < |y| := by linarith
  obtain ⟨baseErr,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error hu0 hU y
  let err := fun j => baseErr j+((ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)+1)*
    ZetaRieszTriplePeriod.allocationBound (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
  refine ⟨m,err,hm,fun j => add_nonneg (he0 j)
    (mul_nonneg (by positivity) (ZetaRieszTriplePeriod.allocationBound_nonneg _)),?_,?_⟩
  · simpa only [err,Function.comp_def,add_zero] using heLim.add
      (ZetaRieszSaddlePacking.tendsto_polynomial_allocation.comp
        ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  have hlocal := RieszFixedCountLocal.eventually_period_ceiling hu hU y hy hm hhu hε hδ hδu hb hsmall hcover
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit (abs_pos.mp hy0) (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [hlocal,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSaddlePacking.eventually_count_le y),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
    with j hj howner hcount hN
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  obtain ⟨v,hv,hvu,hphase⟩ := ZetaRieszCapacityPhaseBudget.exists_negative_peak hy (2*(N : ℝ))
  let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
  let data := fun i => localData true u b δ y (center v y i) N K M m
  let E := B.biUnion (fun i => (data i).1)
  let D := ZetaRieszJointOwnerPayment.population (S\E) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hv100 : 100 ≤ v := by
    have hnR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hv,hnR]
  have hdisj : ∀ i ∈ B, ∀ k ∈ B, i ≠ k → Disjoint (data i).1 (data k).1 := by
    have hsup (i n : ℕ) (hn : n ∈ (data i).1) :
        center v y i-Real.pi/|y| < Real.log n ∧ Real.log n ≤ center v y i+Real.pi/|y| := by
      apply localData_log hm hy (le_trans hv100 ?_) hn
      dsimp only [center]
      exact le_add_of_nonneg_right (by positivity)
    intro i _ k _ hik
    exact ZetaRieszSaddlePacking.disjoint_of_log_support hy0 (fun i => (data i).1) hsup hik
  have hpay : ∀ i ∈ B, u^(N+1)*(∑ n ∈ (data i).1, f n).re ≤ u^(N+1)*(data i).2-(1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N+ZetaRieszTriplePeriod.allocationBound N := by
    intro i hi
    have hc := ZetaRieszSaddlePacking.center_bounds (by omega : 1 ≤ N) hv hvu hi
    have hp := hj (center v y i)
      (by rw [ZetaRieszMultiPeriodSix.center_phase (abs_pos.mp hy0),hphase]) hc.1 hc.2
    simpa only [data,localData,Bool.false_eq_true,↓reduceIte] using hp
  have hwhole := ZetaRieszSaddlePacking.ceiling_union S B (fun i => (data i).1) f
    (fun i => (data i).2) (fun i _ => localData_subset true u b δ y (center v y i) N K M m) hdisj hpay
  have hD : D ⊆ S\E := ZetaRieszJointOwnerPayment.population_subset _ _
  have hcostD := howner (S\E) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re ≤ u^(N+1)*(∑ n ∈ S\E, f n).re-((B.card : ℝ)*((1/16)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-ZetaRieszTriplePeriod.allocationBound N)-u^(N+1)*(∑ i ∈ B, (data i).2)) := by
    change u^(N+1)*(∑ n ∈ S, f n).re ≤ _
    nlinarith only [hwhole]
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f (pow_nonneg hu0 (N+1)) hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  have hcost : (B.card : ℝ)*ZetaRieszTriplePeriod.allocationBound N ≤
      ((N : ℝ)+1)*ZetaRieszTriplePeriod.allocationBound N := by
    apply mul_le_mul_of_nonneg_right _ (ZetaRieszTriplePeriod.allocationBound_nonneg N)
    simpa only [B,Finset.card_range] using hcount
  refine ⟨v,hphase,hv,hvu,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤
        u^(N+1)*((∑ n ∈ S\(E ∪ D), f n).re+(∑ i ∈ B, (data i).2)+min (∑ n ∈ D, f n).re 0)-
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+(baseErr j+((N : ℝ)+1)*ZetaRieszTriplePeriod.allocationBound N)
  nlinarith only [hbound,hcost,(abs_le.mp herr).1]

#print axioms eventually_combined_ceiling

end RieszFixedCountJoint

#lint+ in RieszFixedCountJoint
