/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveAngularDomain

/-!
# One literal four/five-prime capacity ledger

The complete angular debit and credit enter one signed inequality, with
the complement of their union retained. Count four and count five prove
disjointness before either population is spent. No extra prime estimate,
phase approximation, carrier completion or numerical certificate is assumed.
-/

namespace RiemannGaussian.ZetaRieszJointCapacityFloor
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

/-- Two proved component floors combine with one signed complement when
their spent populations are disjoint. No upper bound on that complement
or smallness of either component is required. -/
theorem joint_floor_of_disjoint {S Q D : Finset ℕ} (f : ℕ → ℂ) {debit credit : ℝ}
    (hQ : Q ⊆ S) (hdis : Disjoint Q D)
    (hfour : (∑ n ∈ S\Q, f n).re-debit ≤ (∑ n ∈ S, f n).re)
    (hfive : (∑ n ∈ S\D, f n).re+credit ≤ (∑ n ∈ S, f n).re) :
    (∑ n ∈ S\(Q ∪ D), f n).re+credit-debit ≤ (∑ n ∈ S, f n).re := by
  have hQ' : Q ⊆ S\D := Finset.subset_sdiff.mpr ⟨hQ,hdis⟩
  have h₁ := congrArg Complex.re (Finset.sum_sdiff (f := f) hQ)
  have h₂ := congrArg Complex.re (Finset.sum_sdiff (f := f) hQ')
  have he : (S\D)\Q = S\(Q ∪ D) := by ext n; simp; tauto
  rw [he] at h₂
  simp only [Complex.add_re] at h₁ h₂
  linarith

/-- Every label in the actual favorable interior family has exactly five
distinct prime factors; the phase guard cannot create additional labels. -/
theorem interior_supply_count {M : ℕ} {lo hi t h b y : ℝ} (ht : 0 < t)
    {v : Fin 4 → Fin M}
    (hv : v ∈ ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b)
    {n : ℕ} (hn : n ∈ ZetaRieszJointPrimeCells.supplyCell t h y
      (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)) :
    n.primeFactors.card = 5 := by
  have hg := (Finset.mem_filter.mp hv).2
  dsimp only at hg
  by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
  · have ho : ∀ i k, i < k →
        t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i+t*b ≤
          t*ZetaRieszFiveInteriorBudget.gridLo 0 b v k := by
      intro i k hik
      nlinarith [hg.2.1 i k hik]
    have hqp : t*ZetaRieszFiveInteriorBudget.gridLo 0 b v 3+t*b ≤
        t-∑ i, (t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i+t*b) := by
      simp_rw [← mul_add,← Finset.mul_sum]
      nlinarith [hg.2.2.2.1]
    have hm : t-(∑ i, t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i)+h ≤ (9/16 : ℝ)*t := by
      rw [← Finset.mul_sum]
      have hs := mul_le_mul_of_nonneg_left hg.2.2.2.2.1 ht.le
      rw [mul_add,mul_div_cancel₀ _ ht.ne'] at hs
      nlinarith
    exact ZetaRieszFivePrimeCells.cell_products_count ho hqp hm
      (by simpa only [ZetaRieszJointPrimeCells.supplyCell,if_pos hp] using hn)
  · simp only [ZetaRieszJointPrimeCells.supplyCell,if_neg hp,Finset.notMem_empty] at hn

/-- The complete selected adverse population is disjoint from the whole
favorable family, including ordering and phase boundaries. -/
theorem adverse_interior_disjoint (S : Finset ℕ) {M : ℕ} {L lo hi t h b y a : ℝ}
    (ht : 0 < t) :
    Disjoint (adversePopulation (clippedSupport S) L t h y a)
      ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b).biUnion
        (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
          (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hc4 := (Finset.mem_filter.mp hn).2.2.1
  obtain ⟨v,hv,hnv⟩ := Finset.mem_biUnion.mp hn'
  have hc5 := interior_supply_count ht hv hnv
  omega

/-- The complete four-prime angular debit and five-prime certificate
integral enter ONE original-core lower bound. All arithmetic masks and
the full phase are retained, and each favorable label is spent only once.
The numerical comparison of the two radial/phase factors is still explicit. -/
theorem eventually_joint_core_capacity_floor (B : ZetaRieszCapacityCover.Box)
    (lo : ℚ) {u h b δ hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (17/25 : ℝ) ≤ lo)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ)) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → (lo : ℝ) ≤ L/t → L/t ≤ hi →
      (∑ n ∈ S\(Q ∪ D), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (((996/1000 : ℝ)*(∫ x in ZetaRieszCapacityCover.region B,
          ZetaRieszFiveCapacityCover.density lo hi (1/100) x)-1/50000)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h))-
        (((1003/1000 : ℝ)*
          ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox lo),
            ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [ZetaRieszFourAngularDomain.eventually_core_capacity_floor hu hU hh hhu hδ hδu,
    ZetaRieszFiveAngularDomain.eventually_core_capacity_floor B (lo := lo) (hi := hi)
      hu hU hh hhu hb hsmall hcover hlo hB,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hfour hfive hj t y
  dsimp only
  intro htlo hthi hlt htl
  have hn : (1 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by exact_mod_cast hj
  have ht : 0 < t := by nlinarith
  exact joint_floor_of_disjoint _
    (by intro n hn; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
    (adverse_interior_disjoint _ ht)
    (hfour t y lo htlo hthi hlo hlt) (hfive t y htlo hthi hlt htl)

/-- Disjoint interval populations can be spent together without duplicating
their common core or its signed complement. Intersecting with the original
support is an exact finite-sum identity, not an additional carrier mask. -/
theorem family_floor_of_pairwise_disjoint {ι : Type*}
    (I : Finset ι) (S : Finset ℕ) (P : ι → Finset ℕ) (f : ℕ → ℂ) (g : ι → ℝ)
    (hdis : Set.PairwiseDisjoint (↑I) P)
    (hfloor : ∀ i ∈ I, (∑ n ∈ S\P i, f n).re+g i ≤ (∑ n ∈ S, f n).re) :
    (∑ n ∈ S\I.biUnion P, f n).re+(∑ i ∈ I, g i) ≤ (∑ n ∈ S, f n).re := by
  let Q := fun i => S ∩ P i
  have hQS (i : ι) : Q i ⊆ S := Finset.inter_subset_left
  have hQdis : Set.PairwiseDisjoint (↑I) Q := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono Finset.inter_subset_right Finset.inter_subset_right
  have hg (i : ι) (hi : i ∈ I) : g i ≤ (∑ n ∈ Q i, f n).re := by
    have he := congrArg Complex.re (Finset.sum_sdiff (f := f) (hQS i))
    simp only [Q,Finset.sdiff_inter_self_left,Complex.add_re] at he
    have hf := hfloor i hi
    linarith
  have hsum := Finset.sum_le_sum hg
  have hU : I.biUnion Q ⊆ S := Finset.biUnion_subset.mpr (fun i _ => hQS i)
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hU)
  have hid : S\I.biUnion Q = S\I.biUnion P := by
    rw [show I.biUnion Q = S ∩ I.biUnion P from (Finset.inter_biUnion S I P).symm,
      Finset.sdiff_inter_self_left]
  rw [hid,Finset.sum_biUnion hQdis,Complex.add_re,Complex.re_sum] at he
  simp only [Complex.re_sum] at hsum he ⊢
  linarith

/-- The moving largest-prime interval retains the exact half-open total
logarithm cell, regardless of the outer share grid or phase guard. -/
theorem supplyCell_log_bounds {t h y : ℝ} {lo H : Fin 4 → ℝ} {n : ℕ}
    (hn : n ∈ ZetaRieszJointPrimeCells.supplyCell t h y lo H) :
    t < Real.log n ∧ Real.log n ≤ t+h := by
  by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
  · simp only [ZetaRieszJointPrimeCells.supplyCell,if_pos hp] at hn
    obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
    have hv0 : (∏ i, v i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ =>
      (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds (Fintype.mem_piFinset.mp hv i)).1.ne_zero)
    exact (ZetaRieszCoupledWindow.product_log_bounds hv0 hp).2
  · simp only [ZetaRieszJointPrimeCells.supplyCell,if_neg hp,Finset.notMem_empty] at hn

/-- Both sides of the joint capacity inequality lie in the same literal
total-log interval; the complete union therefore respects interval disjointness. -/
theorem joint_population_log_bounds (S : Finset ℕ) {M : ℕ} {L lo hi t h b y a : ℝ}
    {n : ℕ} (hn : n ∈ adversePopulation (clippedSupport S) L t h y a ∪
      ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b).biUnion
        (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
          (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)))) :
    t < Real.log n ∧ Real.log n ≤ t+h := by
  rcases Finset.mem_union.mp hn with hn | hn
  · obtain ⟨_,_,_,_,ht,hth,_,_⟩ := Finset.mem_filter.mp hn
    exact ⟨ht,hth⟩
  · obtain ⟨v,_hv,hn⟩ := Finset.mem_biUnion.mp hn
    exact supplyCell_log_bounds hn

/-- Ordered half-open total-log windows disjoin the actual complete
four/five populations, independently of any overlap of their share grids. -/
theorem joint_populations_disjoint (I : Finset ℕ) (S : Finset ℕ) (T : ℕ → ℝ)
    {M : ℕ} {L lo hi h b y a : ℝ}
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i < j → T i+h ≤ T j) :
    Set.PairwiseDisjoint (↑I) (fun i => adversePopulation (clippedSupport S) L (T i) h y a ∪
      ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/T i) b).biUnion
        (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h y
          (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b)))) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := joint_population_log_bounds S hn
  have hb' := joint_population_log_bounds S hn'
  rcases lt_or_gt_of_ne hij with hij | hji
  · linarith [hsep i hi j hj hij]
  · linarith [hsep j hj i hi hji]

/-- The actual capacity credits and debits aggregate over a complete
finite interval family with ONE signed complement and no repeated labels.
No absolute carrier bound or phase deletion enters this inequality. -/
theorem eventually_joint_core_family_floor (B : ZetaRieszCapacityCover.Box)
    (lo : ℚ) {u h b δ hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (17/25 : ℝ) ≤ lo)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ)) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let P := fun i => adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b)))
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (lo : ℝ) ≤ L/T i ∧ L/T i ≤ hi) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (((996/1000 : ℝ)*(∫ x in ZetaRieszCapacityCover.region B,
            ZetaRieszFiveCapacityCover.density lo hi (1/100) x)-1/50000)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (-Real.cos (y*T i)-|y| * h)*h))-
          (((1003/1000 : ℝ)*
            ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox lo),
              ZetaRieszFourCapacityCover.density (L/T i) x)+1/1000000000+1/78000000)+1/100000)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (-Real.cos (y*T i))+|y| * h)*h)))) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_joint_core_capacity_floor B lo hu hU hh hhu hδ hδu
    hb hsmall hcover hlo hB] with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine family_floor_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · exact joint_populations_disjoint I _ T hsep
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

end
end RiemannGaussian.ZetaRieszJointCapacityFloor
