/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointCapacityFloor
import RiemannGaussian.ZetaRieszCapacityPhaseBudget
import RiemannGaussian.ZetaRieszOppositePhase
import RiemannGaussian.ZetaRieszJointCapacityCeiling
import RiemannGaussian.ZetaRieszBalancedTripleBudget
import RieszFourCapacityBin0.Assembly
import RieszFiveCapacityBin0.Assembly

/-!
# Optional checked first-bin JOINT literal capacity floor

Import only the separately checked cached assemblies. Keep this outside
ordinary CI and do not rerun their exhaustive verification. The numerical
debit and credit enter one actual finite-prime inequality, retaining the
single complement of their disjoint union and their distinct phase factors.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

namespace RieszJointCapacityTransfer

/-- The two checked first-bin constants bound actual adverse four-prime
and favorable five-prime populations in ONE signed arithmetic ledger. -/
theorem eventually_first_bin_core_floor {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      (∑ n ∈ S\(Q ∪ D), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        ((8529739/62500000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h))-
        ((133421/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hgeom : ∀ x ∈ ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box,
      x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ) := by
    intro x hx
    have h0 := (hx 0 (Set.mem_univ _)).2
    have h1 := (hx 1 (Set.mem_univ _)).2
    norm_num [RieszFiveCapacityBin0.Assembly.part0000_box] at h0 h1
    constructor <;> linarith
  filter_upwards [ZetaRieszJointCapacityFloor.eventually_joint_core_capacity_floor
    RieszFiveCapacityBin0.Assembly.part0000_box RieszFourCapacityBin0.Assembly.low
    (hi := RieszFiveCapacityBin0.Assembly.high) hu hU hh hhu hδ hδu hb hsmall hcover
    (by norm_num [RieszFourCapacityBin0.Assembly.low]) hgeom] with j hJ t y
  dsimp only
  intro htlo hthi hlo hhi
  have hf := hJ t y htlo hthi hlo hhi
  have hbox : ZetaRieszFourAngularDomain.outerBox RieszFourCapacityBin0.Assembly.low =
      RieszFourCapacityBin0.Assembly.part0000_box := by
    funext i
    fin_cases i <;> norm_num [ZetaRieszFourAngularDomain.outerBox,
      RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.part0000_box]
  have hupp := RieszFourCapacityBin0.Assembly.whole_debit_upper ⟨hlo,hhi⟩
  rw [← hbox] at hupp
  have hlower := RieszFiveCapacityBin0.Assembly.whole_supply_lower
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hupp hlower
  have hcredit : (8529739/62500000 : ℝ) ≤ (996/1000 : ℝ)*
      (∫ x in ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box,
        ZetaRieszFiveCapacityCover.density RieszFiveCapacityBin0.Assembly.low
          RieszFiveCapacityBin0.Assembly.high (1/100) x)-1/50000 := by linarith
  have hdebit : (1003/1000 : ℝ)*
      ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox
          RieszFourCapacityBin0.Assembly.low),
        ZetaRieszFourCapacityCover.density
          (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/t) x)+
          1/1000000000+1/78000000)+1/100000 ≤ 133421/1000000 := by linarith
  have ht : 0 ≤ t := (show 0 ≤ (39/20 : ℝ)*
    ZetaRieszPrimeCountFrequency.dyadicMomentOrder j by positivity).trans htlo
  have hF : 0 ≤ (Real.exp (-(t+h)/2)*t^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*
        max 0 (-Real.cos (y*t)-|y| * h)*h := by positivity
  have hE : 0 ≤ (Real.exp (-t/2)*(t+h)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*
        (max 0 (-Real.cos (y*t))+|y| * h)*h := by positivity
  have hf' := mul_le_mul_of_nonneg_right hcredit hF
  have he' := mul_le_mul_of_nonneg_right hdebit hE
  dsimp only [RieszFourCapacityBin0.Assembly.low,RieszFiveCapacityBin0.Assembly.low] at hf hf' he' ⊢
  linarith only [hf,hf',he']

/-- The checked angular constants can be spent simultaneously over any
disjoint finite family of original log intervals, retaining one signed rest. -/
theorem eventually_first_bin_family_floor {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b)))
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
          L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (8529739/62500000 : ℝ)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (-Real.cos (y*T i)-|y| * h)*h)-
          (133421/1000000 : ℝ)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (-Real.cos (y*T i))+|y| * h)*h))) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_first_bin_core_floor hu hU hh hhu hδ hδu hb hsmall hcover]
    with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine ZetaRieszJointCapacityFloor.family_floor_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · exact ZetaRieszJointCapacityFloor.joint_populations_disjoint I _ T hsep
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

/-- A whole literal phase-period population has strictly positive credit
after paying its complete selected adverse four-prime class. Every label
outside the disjoint union stays in the actual signed core complement. -/
theorem eventually_first_bin_period_payment {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (m : ℝ)/1000*V₀*h ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_first_bin_family_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hpay⟩ := ZetaRieszCapacityPhaseBudget.original_finite_period_budget
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

/-- No geometric or phase-population premise remains: a complete paid
period exists at every sufficiently large original dyadic order. The mesh
is fixed at each fixed height. This is a strict actual component payment,
not a bound on the whole signed complementary carrier. -/
theorem eventually_exists_first_bin_payment {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re <
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_period_payment hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom] with j hpay hJ
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hfloor⟩ := hpay v hpeak hlo hhi hbins
  have hp : 0 < (m : ℝ)/1000*V₀*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨v,hpeak,hlo,hhi,by linarith only [hfloor,hp]⟩

/-- The checked debit also controls the entire positive-coefficient
four-prime population from above at the original height. Calibration and
its relative error are discharged; the complement is kept signed. -/
theorem eventually_first_bin_four_ceiling {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (133555/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (Real.cos (y*t))+|y| * h)*h) := by
  filter_upwards [ZetaRieszOppositePhase.eventually_four_core_ceiling hu hU hh hhu hδ hδu,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlo hhi
  have hf := hJ t y RieszFourCapacityBin0.Assembly.low htlo hthi
    (by norm_num [RieszFourCapacityBin0.Assembly.low]) hlo
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let D := (1003/1000 : ℝ)*
    ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox
        RieszFourCapacityBin0.Assembly.low),
      ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000
  have hbox : ZetaRieszFourAngularDomain.outerBox RieszFourCapacityBin0.Assembly.low =
      RieszFourCapacityBin0.Assembly.part0000_box := by
    funext i
    fin_cases i <;> norm_num [ZetaRieszFourAngularDomain.outerBox,
      RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.part0000_box]
  have hupp := RieszFourCapacityBin0.Assembly.whole_debit_upper ⟨hlo,hhi⟩
  rw [← hbox] at hupp
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hupp
  have hD : D ≤ 133421/1000000 := by dsimp only [D,L,N]; linarith only [hupp]
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hcal := ZetaRieszOppositePhase.calibration_cost_le ht hh.le hhu
  have hc0 : 0 ≤ (10000/9999 : ℝ)*(1+|Real.pi/t| * h) := by positivity
  have hpaid : (10000/9999 : ℝ)*(1+|Real.pi/t| * h)*D ≤ 133555/1000000 := by
    have h₁ := mul_le_mul_of_nonneg_left hD hc0
    have h₂ := mul_le_mul_of_nonneg_right hcal (by norm_num : (0 : ℝ) ≤ 133421/1000000)
    linarith only [h₁,h₂]
  have hV : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (Real.cos (y*t))+|y| * h)*h := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpaid hV
  dsimp only [D,L,N] at hscaled
  linarith only [hf,hscaled]

/-- The same checked angular populations give a joint UPPER inequality
at the original positive phase, after all calibration costs and with a
single disjoint spending ledger. -/
theorem eventually_first_bin_joint_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      0 ≤ Real.cos (y*t)-|y| * h →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(Q ∪ D), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (133555/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h)-
        (6823/50000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          (Real.cos (y*t)-|y| * h)*h) := by
  have hgeom : ∀ x ∈ ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box,
      x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ) := by
    intro x hx
    have h0 := (hx 0 (Set.mem_univ _)).2
    have h1 := (hx 1 (Set.mem_univ _)).2
    norm_num [RieszFiveCapacityBin0.Assembly.part0000_box] at h0 h1
    constructor <;> linarith
  filter_upwards [eventually_first_bin_four_ceiling hu hU hh hhu hδ hδu,
    ZetaRieszJointCapacityCeiling.eventually_five_core_ceiling
      RieszFiveCapacityBin0.Assembly.part0000_box
      (lo := RieszFiveCapacityBin0.Assembly.low) (hi := RieszFiveCapacityBin0.Assembly.high)
      hu hU hh hhu hb hsmall hcover (by norm_num [RieszFiveCapacityBin0.Assembly.low]) hgeom,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hfour hfive hN t y
  dsimp only
  intro htlo hthi hlo hhi hphase
  have hf := hfive t y htlo hthi hlo hhi hphase
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hcal := ZetaRieszOppositePhase.calibration_phase ht hh.le hhu
  have hI := RieszFiveCapacityBin0.Assembly.whole_supply_lower
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hI
  have hbase : (8529739/62500000 : ℝ) ≤ (996/1000 : ℝ)*
      (∫ x in ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box,
        ZetaRieszFiveCapacityCover.density RieszFiveCapacityBin0.Assembly.low
          RieszFiveCapacityBin0.Assembly.high (1/100) x)-1/50000 := by linarith only [hI]
  have hc0 : 0 ≤ 1-|Real.pi/t| * h := by linarith [hcal.2]
  have hc := mul_le_mul_of_nonneg_left hbase hc0
  have hnum : (6823/50000 : ℝ) ≤ (1-|Real.pi/t| * h)*(8529739/62500000) := by
    linarith only [hcal.2]
  have hF : 0 ≤ (Real.exp (-(t+h)/2)*t^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*(Real.cos (y*t)-|y| * h)*h := by
    have ht0 : 0 ≤ t := by linarith
    positivity
  have hpaid := mul_le_mul_of_nonneg_right (hnum.trans hc) hF
  have hf' := hfour t y htlo hthi hlo hhi
  refine ZetaRieszJointCapacityCeiling.joint_ceiling_of_disjoint _
    (by intro n hn; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
    (ZetaRieszJointCapacityFloor.adverse_interior_disjoint _ (by linarith : 0 < t)) hf' ?_
  dsimp only [RieszFourCapacityBin0.Assembly.low,RieszFiveCapacityBin0.Assembly.low] at hf hpaid ⊢
  unfold ZetaRieszParityPacket.coreResponse at hf
  linarith only [hf,hpaid]

/-- At an actual positive cosine peak, the selected five-prime credit
pays the complete selected four-prime upper debit with explicit surplus
h*V_N(t)/1000. This is an actual signed UPPER payment, not a whole ceiling. -/
theorem eventually_first_bin_positive_peak_payment {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let D := (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
            (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      Real.cos (y*t) = 1 → |y| * h ≤ 1/10000 →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(Q ∪ D), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (1/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial)*h := by
  filter_upwards [eventually_first_bin_joint_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlo hhi hpeak hε
  have ht : 0 < t := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hf := hJ t y htlo hthi hlo hhi (by rw [hpeak]; linarith only [hε])
  rw [hpeak] at hf
  simp only [max_eq_right zero_le_one] at hf
  have hn0 : (0 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by positivity
  have hbudget := ZetaRieszCapacityPhaseBudget.positive_peak_capacity_budget
    (N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ht
    (by nlinarith only [htlo,hn0])
    hh.le hhu (mul_nonneg (abs_nonneg y) hh.le) hε
  linarith only [hf,hbudget]

/-- Every sufficiently late original dyadic order contains an actual
opposite-phase payment in the first certified bin. All phase, cutoff and
radial hypotheses of the component upper comparison are discharged. -/
theorem eventually_exists_first_bin_upper_payment {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/100000 ∧ |y| * h ≤ 1/10000 ∧
      ∀ᶠ j : ℕ in atTop, ∃ t : ℝ,
        let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
        let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := ZetaRieszParityPacket.coreBand u N K
        let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
        let D := (ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b).biUnion
            (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
              (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
        Real.cos (y*t) = 1 ∧ (39/20 : ℝ)*N ≤ t ∧ t+h ≤ (203/100 : ℝ)*N ∧
        (ZetaRieszParityPacket.coreResponse u y N K).re <
        (∑ n ∈ S\(Q ∪ D), ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨Real.pi/(4*m*|y|),hh,hhu,hε,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_positive_peak_payment hu hU hh hhu hδ hδu hb hsmall hcover,
    hgeom,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hN
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let t := v-Real.pi/|y|
  have hy0 : 0 < |y| := by linarith
  have htcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm
    (i := 0) (by omega) v hy0
  have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m 0/|y| = t := by
    simp [ZetaRieszCapacityPhaseBudget.periodAngle,t,sub_eq_add_neg,neg_div]
  rw [ht'] at htcell
  have hthi := htcell.2.trans hhi
  have hbnd : (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/t ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/t ≤
        RieszFourCapacityBin0.Assembly.high := by
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin t (le_refl _) (by linarith only [htcell.2,hh])
  have hp := ZetaRieszCapacityPhaseBudget.cos_left_edge hy0 hpeak
  have hf := hpay t y hlo hthi hbnd.1 hbnd.2 hp hε
  have ht0 : 0 < t := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [hlo,hn]
  have hV : 0 < (1/1000 : ℝ)*
      (Real.exp (-t/2)*t^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨t,hp,hlo,hthi,by linarith only [hf,hV]⟩

/-- On every phase cell the four-prime debit is retained. Five-prime
credit is spent only when its ORIGINAL phase is favorable; all unspent
labels remain in the signed complement. This includes cosine boundaries. -/
theorem eventually_first_bin_all_phase_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := if 0 ≤ Real.cos (y*t)-|y| * h then
        I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
          (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)) else ∅
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(Q ∪ D), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (133555/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h)-
        (6823/50000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          max 0 (Real.cos (y*t)-|y| * h)*h) := by
  filter_upwards [eventually_first_bin_joint_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    eventually_first_bin_four_ceiling hu hU hh hhu hδ hδu] with j hJ hfour t y
  dsimp only
  intro htlo hthi hlo hhi
  by_cases hp : 0 ≤ Real.cos (y*t)-|y| * h
  · simpa only [if_pos hp,max_eq_right hp] using hJ t y htlo hthi hlo hhi hp
  · simpa only [if_neg hp,Finset.union_empty,max_eq_left (le_of_not_ge hp),
      mul_zero,zero_mul,sub_zero] using hfour t y htlo hthi hlo hhi

/-- All-phase upper payments over disjoint literal windows are added
with one signed complement. The calibration height varies with the
window, while the arithmetic sum is always evaluated at the original y. -/
theorem eventually_first_bin_family_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b))
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅)
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
          L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (133555/1000000 : ℝ)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (Real.cos (y*T i))+|y| * h)*h)-
          (6823/50000 : ℝ)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (Real.cos (y*T i)-|y| * h)*h))) := by
  filter_upwards [eventually_first_bin_all_phase_ceiling hu hU hh hhu hδ hδu hb hsmall hcover]
    with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine ZetaRieszJointCapacityCeiling.family_ceiling_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hlog (a : ℕ) (ha : n ∈
        adversePopulation (clippedSupport (ZetaRieszParityPacket.coreBand u
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)))
          (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
          (T a) h (Real.pi/T a) (δ*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ∪
          (if 0 ≤ Real.cos (y*T a)-|y| * h then
            (ZetaRieszFiveAngularBoundary.interiorFamily M RieszFiveCapacityBin0.Assembly.low
              RieszFiveCapacityBin0.Assembly.high (h/T a) b).biUnion
                (fun v => ZetaRieszJointPrimeCells.supplyCell (T a) h (Real.pi/T a)
                  (fun k => T a*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T a*b))
            else ∅)) : T a < Real.log n ∧ Real.log n ≤ T a+h := by
      by_cases hp : 0 ≤ Real.cos (y*T a)-|y| * h
      · simp only [if_pos hp] at ha
        exact ZetaRieszJointCapacityFloor.joint_population_log_bounds _ ha
      · simp only [if_neg hp,Finset.union_empty] at ha
        obtain ⟨_,_,_,_,ht,hth,_,_⟩ := Finset.mem_filter.mp ha
        exact ⟨ht,hth⟩
    have hl := hlog i hn
    have hl' := hlog k hn'
    rcases lt_or_gt_of_ne hik with hik | hki
    · linarith [hsep i hi k hk hik]
    · linarith [hsep k hk i hi hki]
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

/-- The selected five-prime population pays the complete calibrated
four-prime debit on a full original phase period, with a negative margin.
The original core and its single unestimated signed complement are kept. -/
theorem eventually_first_bin_upper_period_payment {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅)
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧ (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
          (m : ℝ)/2000*V₀*h := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_first_bin_family_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hpay⟩ := ZetaRieszCapacityPhaseBudget.original_finite_upper_period_budget
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

/-- A complete upper-paid phase period exists on EVERY sufficiently late
original dyadic order. No zero, simplicity, angular integral premise,
or assumption on the signed complementary carrier is used. -/
theorem eventually_exists_first_bin_upper_period {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅)
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      (ZetaRieszParityPacket.coreResponse u y N K).re <
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_upper_period_payment hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom] with j hpay hJ
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hceiling⟩ := hpay v hpeak hlo hhi hbins
  have hp : 0 < (m : ℝ)/2000*V₀*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨v,hpeak,hlo,hhi,by linarith only [hceiling,hp]⟩

/-- One five-prime supply now pays BOTH the previous four-prime debit
and the full explicit balanced triple band in the same literal window.
The three prime counts are disjoint, and their single complement stays signed. -/
theorem eventually_first_bin_three_four_five_floor {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBalancedTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        ((8529739/62500000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h))-
        ((133521/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have htriple := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszBalancedTripleBudget.eventually_signed_bounds hh hhu)
  filter_upwards [eventually_first_bin_core_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    htriple,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ htri hN t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBalancedTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
  let I := ZetaRieszFiveAngularBoundary.interiorFamily M
    RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
  let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
    (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := by linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith
  have hNt : (N : ℝ) ≤ t := by linarith only [htlo,hn]
  have hLlo := (le_div_iff₀ ht0).mp hlo
  norm_num only [RieszFourCapacityBin0.Assembly.low,Rat.cast_div,Rat.cast_ofNat] at hLlo
  have hmid : t+h ≤ 2*L := by dsimp only [L,N]; linarith only [hLlo,ht,hhu]
  have hT := htri S A t L y hNt (SquarefreeVaughanLogSource.length_pos u N) hmid
  have h45 := hJ t y htlo hthi hlo hhi
  have hdis : Disjoint B (Q ∪ D) := ZetaRieszBalancedTripleBudget.disjoint_from_four_five S ht0
  have hsub : B ⊆ S\(Q ∪ D) := Finset.subset_sdiff.mpr ⟨Finset.filter_subset _ _,hdis⟩
  have hsplit := congrArg Complex.re (Finset.sum_sdiff (f := f) hsub)
  have hid : (S\(Q ∪ D))\B = S\(B ∪ (Q ∪ D)) := by ext n; simp; tauto
  rw [hid] at hsplit
  simp only [Complex.add_re] at hsplit
  unfold ZetaRieszParityPacket.coreResponse at h45 ⊢
  dsimp only [N,K,L,A,S,B,Q,I,D,f,ZetaRieszBalancedTripleBudget.population] at hsplit hT ⊢
  nlinarith only [hsplit,h45,hT.1]

/-- One five-prime supply now pays BOTH the previous four-prime debit
and the full explicit balanced triple band in the same literal window.
The three prime counts are disjoint, and their single complement stays signed. -/
theorem eventually_first_bin_three_four_five_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBalancedTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      0 ≤ Real.cos (y*t)-|y| * h →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (133655/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h)-
        (6823/50000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          (Real.cos (y*t)-|y| * h)*h) := by
  have htriple := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszBalancedTripleBudget.eventually_signed_bounds hh hhu)
  filter_upwards [eventually_first_bin_joint_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    htriple,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ htri hN t y
  dsimp only
  intro htlo hthi hlo hhi hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBalancedTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
  let I := ZetaRieszFiveAngularBoundary.interiorFamily M
    RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
  let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
    (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := by linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith
  have hNt : (N : ℝ) ≤ t := by linarith only [htlo,hn]
  have hLlo := (le_div_iff₀ ht0).mp hlo
  norm_num only [RieszFourCapacityBin0.Assembly.low,Rat.cast_div,Rat.cast_ofNat] at hLlo
  have hmid : t+h ≤ 2*L := by dsimp only [L,N]; linarith only [hLlo,ht,hhu]
  have hT := htri S A t L y hNt (SquarefreeVaughanLogSource.length_pos u N) hmid
  have h45 := hJ t y htlo hthi hlo hhi hphase
  have hdis : Disjoint B (Q ∪ D) := ZetaRieszBalancedTripleBudget.disjoint_from_four_five S ht0
  have hsub : B ⊆ S\(Q ∪ D) := Finset.subset_sdiff.mpr ⟨Finset.filter_subset _ _,hdis⟩
  have hsplit := congrArg Complex.re (Finset.sum_sdiff (f := f) hsub)
  have hid : (S\(Q ∪ D))\B = S\(B ∪ (Q ∪ D)) := by ext n; simp; tauto
  rw [hid] at hsplit
  simp only [Complex.add_re] at hsplit
  unfold ZetaRieszParityPacket.coreResponse at h45 ⊢
  dsimp only [N,K,L,A,S,B,Q,I,D,f,ZetaRieszBalancedTripleBudget.population] at hsplit hT ⊢
  nlinarith only [hsplit,h45,hT.2]

/-- At a positive phase peak, ONE five-prime population pays both the
whole selected four-prime upper debit and the explicit balanced triple band. -/
theorem eventually_first_bin_positive_peak_three_four_five {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBalancedTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let D := (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
            (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      Real.cos (y*t) = 1 → |y| * h ≤ 1/10000 →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (1/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial)*h := by
  filter_upwards [eventually_first_bin_three_four_five_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlo hhi hpeak hε
  have ht : 0 < t := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hf := hJ t y htlo hthi hlo hhi (by rw [hpeak]; linarith only [hε])
  rw [hpeak] at hf
  simp only [max_eq_right zero_le_one] at hf
  have hn0 : (0 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by positivity
  have hbudget := ZetaRieszCapacityPhaseBudget.positive_peak_with_triples
    (N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ht
    (by nlinarith only [htlo,hn0])
    hh.le hhu (mul_nonneg (abs_nonneg y) hh.le) hε
  linarith only [hf,hbudget]

/-- The same joint spending at a negative phase peak proves a strict
lower payment for the explicit triple band and selected four-prime debit. -/
theorem eventually_first_bin_negative_peak_three_four_five {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBalancedTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      let D := (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
            (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      Real.cos (y*t) = -1 → |y| * h ≤ 1/10000 →
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (1/1000 : ℝ)*(Real.exp (-t/2)*t^N/N.factorial)*h ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_first_bin_three_four_five_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlo hhi hpeak hε
  have ht : 0 < t := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hf := hJ t y htlo hthi hlo hhi
  rw [hpeak] at hf
  have he : 0 ≤ 1-|y| * h := by linarith only [hε]
  simp only [neg_neg,max_eq_right zero_le_one,max_eq_right he] at hf
  have hn0 : (0 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by positivity
  have hbudget := ZetaRieszCapacityPhaseBudget.negative_peak_with_triples
    (N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ht
    (by nlinarith only [htlo,hn0])
    hh.le hhu (mul_nonneg (abs_nonneg y) hh.le) hε
  linarith only [hf,hbudget]

/-- The upper three/four/five payment occurs in an actual window on
every sufficiently large original dyadic order, independently of any zero. -/
theorem eventually_exists_first_bin_three_four_five_upper {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/100000 ∧ |y| * h ≤ 1/10000 ∧
      ∀ᶠ j : ℕ in atTop, ∃ t : ℝ,
        let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
        let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := ZetaRieszParityPacket.coreBand u N K
        let B := ZetaRieszBalancedTripleBudget.population S t h
        let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
        let D := (ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b).biUnion
            (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
              (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
        Real.cos (y*t) = 1 ∧ (39/20 : ℝ)*N ≤ t ∧ t+h ≤ (203/100 : ℝ)*N ∧
        (ZetaRieszParityPacket.coreResponse u y N K).re <
        (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨Real.pi/(4*m*|y|),hh,hhu,hε,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_positive_peak_three_four_five hu hU hh hhu hδ hδu hb hsmall hcover,
    hgeom,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hN
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let t := v-Real.pi/|y|
  have hy0 : 0 < |y| := by linarith
  have htcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm
    (i := 0) (by omega) v hy0
  have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m 0/|y| = t := by
    simp [ZetaRieszCapacityPhaseBudget.periodAngle,t,sub_eq_add_neg,neg_div]
  rw [ht'] at htcell
  have hthi := htcell.2.trans hhi
  have hbnd : (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/t ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/t ≤
        RieszFourCapacityBin0.Assembly.high := by
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin t (le_refl _) (by linarith only [htcell.2,hh])
  have hp := ZetaRieszCapacityPhaseBudget.cos_left_edge hy0 hpeak
  have hf := hpay t y hlo hthi hbnd.1 hbnd.2 hp hε
  have ht0 : 0 < t := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [hlo,hn]
  have hV : 0 < (1/1000 : ℝ)*
      (Real.exp (-t/2)*t^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨t,hp,hlo,hthi,by linarith only [hf,hV]⟩

/-- The lower three/four/five payment also occurs in an actual window
on every sufficiently large original dyadic order, with one signed rest. -/
theorem eventually_exists_first_bin_three_four_five_lower {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/100000 ∧ |y| * h ≤ 1/10000 ∧
      ∀ᶠ j : ℕ in atTop, ∃ t : ℝ,
        let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
        let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := ZetaRieszParityPacket.coreBand u N K
        let B := ZetaRieszBalancedTripleBudget.population S t h
        let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
        let D := (ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b).biUnion
            (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
              (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
        Real.cos (y*t) = -1 ∧ (39/20 : ℝ)*N ≤ t ∧ t+h ≤ (203/100 : ℝ)*N ∧
        (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re <
          (ZetaRieszParityPacket.coreResponse u y N K).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨Real.pi/(4*m*|y|),hh,hhu,hε,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_negative_peak_three_four_five hu hU hh hhu hδ hδu hb hsmall hcover,
    hgeom,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hN
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmid : ZetaRieszCapacityPhaseBudget.periodAngle m (4*m) = 0 := by
    unfold ZetaRieszCapacityPhaseBudget.periodAngle
    push_cast
    field_simp [hmR.ne']
    ring
  have htcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm
    (i := 4*m) (by omega) v hy0
  rw [hmid,zero_div,add_zero] at htcell
  have htlo := hlo.trans htcell.1
  have hthi := htcell.2.trans hhi
  have hbnd : (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/v ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/v ≤
        RieszFourCapacityBin0.Assembly.high := by
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin v htcell.1 (by linarith only [htcell.2,hh])
  have hf := hpay v y htlo hthi hbnd.1 hbnd.2 hpeak hε
  have ht0 : 0 < v := by
    have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hV : 0 < (1/1000 : ℝ)*
      (Real.exp (-v/2)*v^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*(Real.pi/(4*m*|y|)) := by
    positivity
  exact ⟨v,hpeak,htlo,hthi,by linarith only [hf,hV]⟩

/-- Every phase cell retains the full balanced-triple and calibrated four-prime debit.
Five-prime credit is spent once, only when its original phase is favorable. -/
theorem eventually_first_bin_three_four_five_all_phase_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBalancedTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := if 0 ≤ Real.cos (y*t)-|y| * h then
        I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
          (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)) else ∅
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (133655/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h)-
        (6823/50000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          max 0 (Real.cos (y*t)-|y| * h)*h) := by
  have htriple := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszBalancedTripleBudget.eventually_signed_bounds hh hhu)
  filter_upwards [eventually_first_bin_all_phase_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    htriple,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ htri hN t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBalancedTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
  let I := ZetaRieszFiveAngularBoundary.interiorFamily M
    RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
  let D := if 0 ≤ Real.cos (y*t)-|y| * h then
    I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
      (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)) else ∅
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := by linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith
  have hNt : (N : ℝ) ≤ t := by linarith only [htlo,hn]
  have hLlo := (le_div_iff₀ ht0).mp hlo
  norm_num only [RieszFourCapacityBin0.Assembly.low,Rat.cast_div,Rat.cast_ofNat] at hLlo
  have hmid : t+h ≤ 2*L := by dsimp only [L,N]; linarith only [hLlo,ht,hhu]
  have hT := htri S A t L y hNt (SquarefreeVaughanLogSource.length_pos u N) hmid
  have h45 := hJ t y htlo hthi hlo hhi
  have hdis0 : Disjoint B (Q ∪ I.biUnion (fun v =>
      ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))) :=
    ZetaRieszBalancedTripleBudget.disjoint_from_four_five S ht0
  have hdis : Disjoint B (Q ∪ D) := hdis0.mono_right (by
    dsimp only [D]
    split_ifs <;> simp)
  have hsub : B ⊆ S\(Q ∪ D) := Finset.subset_sdiff.mpr ⟨Finset.filter_subset _ _,hdis⟩
  have hsplit := congrArg Complex.re (Finset.sum_sdiff (f := f) hsub)
  have hid : (S\(Q ∪ D))\B = S\(B ∪ (Q ∪ D)) := by ext n; simp; tauto
  rw [hid] at hsplit
  simp only [Complex.add_re] at hsplit
  unfold ZetaRieszParityPacket.coreResponse at h45 ⊢
  dsimp only [N,K,L,A,S,B,Q,I,D,f,ZetaRieszBalancedTripleBudget.population] at hsplit hT ⊢
  nlinarith only [hsplit,h45,hT.2]

/-- All three selected prime-count classes are spent jointly over disjoint log windows. -/
theorem eventually_first_bin_three_four_five_family_floor {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let P := fun i => ZetaRieszBalancedTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b))))
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
          L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (8529739/62500000 : ℝ)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (-Real.cos (y*T i)-|y| * h)*h)-
          (133521/1000000 : ℝ)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (-Real.cos (y*T i))+|y| * h)*h))) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_first_bin_three_four_five_floor hu hU hh hhu hδ hδu hb hsmall hcover]
    with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine ZetaRieszJointCapacityFloor.family_floor_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · simpa only [if_true] using
      ZetaRieszBalancedTripleBudget.joint_populations_disjoint I _ T (fun _ => y)
        (fun _ => True) hsep
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

/-- All-phase three/four/five upper payments have one disjoint signed complement. -/
theorem eventually_first_bin_three_four_five_family_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBalancedTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
          L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (133655/1000000 : ℝ)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (Real.cos (y*T i))+|y| * h)*h)-
          (6823/50000 : ℝ)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (Real.cos (y*T i)-|y| * h)*h))) := by
  filter_upwards [eventually_first_bin_three_four_five_all_phase_ceiling hu hU hh hhu hδ hδu hb hsmall hcover]
    with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine ZetaRieszJointCapacityCeiling.family_ceiling_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · exact ZetaRieszBalancedTripleBudget.joint_populations_disjoint I _ T
      (fun i => Real.pi/T i) (fun i => 0 ≤ Real.cos (y*T i)-|y| * h) hsep
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

/-- A complete original phase period pays the explicit balanced triples and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_first_bin_three_four_five_period_payment {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBalancedTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (m : ℝ)/2000*V₀*h ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_first_bin_three_four_five_family_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hpay⟩ := ZetaRieszCapacityPhaseBudget.original_finite_period_budget_with_triples
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

/-- A complete original phase period pays the explicit balanced triples and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_first_bin_three_four_five_upper_period_payment {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBalancedTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin0.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧ (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
          (m : ℝ)/2000*V₀*h := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_first_bin_three_four_five_family_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hpay⟩ := ZetaRieszCapacityPhaseBudget.original_finite_upper_period_budget_with_triples
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

/-- A complete original phase period pays the explicit balanced triples and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_exists_first_bin_three_four_five_period {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBalancedTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re <
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_three_four_five_period_payment hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom] with j hpay hJ
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hfloor⟩ := hpay v hpeak hlo hhi hbins
  have hp : 0 < (m : ℝ)/2000*V₀*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨v,hpeak,hlo,hhi,by linarith only [hfloor,hp]⟩

/-- A complete original phase period pays the explicit balanced triples and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_exists_first_bin_three_four_five_upper_period {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBalancedTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      (ZetaRieszParityPacket.coreResponse u y N K).re <
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_first_bin_period hu.le hU)
  filter_upwards [eventually_first_bin_three_four_five_upper_period_payment hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom] with j hpay hJ
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin0.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin0.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin0.Assembly.low,RieszFourCapacityBin0.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hceiling⟩ := hpay v hpeak hlo hhi hbins
  have hp : 0 < (m : ℝ)/2000*V₀*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨v,hpeak,hlo,hhi,by linarith only [hceiling,hp]⟩

#print axioms eventually_first_bin_three_four_five_all_phase_ceiling
#print axioms eventually_first_bin_three_four_five_family_floor
#print axioms eventually_first_bin_three_four_five_family_ceiling
#print axioms eventually_first_bin_three_four_five_period_payment
#print axioms eventually_first_bin_three_four_five_upper_period_payment
#print axioms eventually_exists_first_bin_three_four_five_period
#print axioms eventually_exists_first_bin_three_four_five_upper_period

#print axioms eventually_exists_first_bin_three_four_five_lower
#print axioms eventually_first_bin_positive_peak_three_four_five
#print axioms eventually_first_bin_negative_peak_three_four_five
#print axioms eventually_exists_first_bin_three_four_five_upper
#print axioms eventually_first_bin_three_four_five_floor
#print axioms eventually_first_bin_three_four_five_ceiling
#print axioms eventually_exists_first_bin_upper_period
#print axioms eventually_first_bin_all_phase_ceiling
#print axioms eventually_first_bin_family_ceiling
#print axioms eventually_first_bin_upper_period_payment
#print axioms eventually_first_bin_core_floor
#print axioms eventually_first_bin_family_floor
#print axioms eventually_first_bin_period_payment
#print axioms eventually_exists_first_bin_payment
#print axioms eventually_first_bin_four_ceiling
#print axioms eventually_first_bin_joint_ceiling
#print axioms eventually_first_bin_positive_peak_payment
#print axioms eventually_exists_first_bin_upper_payment
end RieszJointCapacityTransfer
