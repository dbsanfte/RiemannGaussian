/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFewBinCoverFloor
import RiemannGaussian.ZetaRieszHighSignCoverFloor

set_option autoImplicit false

/-!
# Join existing fixed-count and new growing-population payments

The existing fixed-count ledger is retained. New growing-population
payments begin at count56, so no original label or supply credit is
spent twice. The target remains a signed whole-floor inequality.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJoinedPopulationFloor
open ZetaRieszFewBinCoverFloor
open ZetaRieszDenseCountCoverFloor ZetaRieszDenseShellCost
open ZetaRieszIntermediateScaleCost ZetaRieszParityLayerCost
open ZetaRieszUnpaidCountTiltFloor ZetaRieszPrimeEndpoint
open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszJointAllocation
open ZetaRieszAllowancePrimeBoxes ZetaRieszClippedOwnerPeriodFloor
open ZetaRieszTinyOwnerPeriodFloor ZetaRieszSignedPeriodFloor
open ZetaRieszStaggeredFloor ZetaRieszBroadOwnerPeriodFloor
open ZetaRieszDenseSmallTopFloor ZetaRieszSmallCofactorCancellation

set_option maxHeartbeats 1000000

/-- New upper growing-count payment, disjoint from the old fixed band. -/
def dense56Band (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (denseBand u N K).filter (fun n => 56≤n.primeFactors.card)

/-- New lower growing-count few-bin payment, disjoint from the old fixed band. -/
def bin56Band (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (binBand u N K).filter (fun n => 56≤n.primeFactors.card)

private theorem grid_center_bounds {N : ℕ} (hN : 1000≤N) {b y : ℝ} (hy : 54≤y)
    {i : ℕ} (hi : i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y) :
    100≤ZetaRieszMultiPeriodSix.center b y i ∧
    (N : ℝ)+2≤ZetaRieszMultiPeriodSix.center b y i ∧
    ZetaRieszMultiPeriodSix.center b y i≤4*((N : ℝ)+1) := by
  have hd := (Finset.mem_filter.mp hi).2
  have hNR : (1000 : ℝ)≤N := by exact_mod_cast hN
  have hp : 0≤Real.pi/y := by positivity
  constructor
  · linarith only [hd.1,hNR,hp]
  constructor <;> linarith only [hd.1,hd.2.1,hNR,hp]

private theorem family_two_cover_ledger (A : ℕ→Finset ℕ) (S P Q : Finset ℕ)
    (L y : ℝ) (N : ℕ) (hP : P⊆S) (hQ : Q⊆S) :
    (∑ n∈S,residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
      (∑ n∈P,signedPart 1 (A n) L y N n)+
      (∑ n∈Q,signedPart (-1) (A n) L y N n)+
      (∑ n∈S\P,signedPart 1 (A n) L y N n)+
      (∑ n∈S\Q,signedPart (-1) (A n) L y N n) := by
  rw [Complex.re_sum]
  simp_rw [← signedPart_add]
  rw [Finset.sum_add_distrib]
  have hp := Finset.sum_sdiff hP (f := fun n => signedPart 1 (A n) L y N n)
  have hq := Finset.sum_sdiff hQ (f := fun n => signedPart (-1) (A n) L y N n)
  linarith only [hp,hq]

private theorem norm_owner_subset_le (A G : Finset ℕ) {N : ℕ} {u y L B : ℝ}
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hL : 0<L)
    (hG : G⊆literalWindow N)
    (hB : ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤B) :
    ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient (A∩{largestPrime n}) L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤B+ownerPaymentError N := by
  have hb := ZetaRieszNonownerAllocation.residual_sub_owner_bound (fun _ => A) G
    (fun _ => 1) hL N hG (by intros; norm_num) y hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  simp only [one_mul,sub_mul,Finset.sum_sub_distrib,mul_sub] at hb
  have ht := norm_sub_le
    ((u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    (((u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
     ((u : ℂ)^(N+1)*∑ n∈G,residualCoefficient (A∩{largestPrime n}) L N n*
       zetaPrimeLogKernel N (3/2+Complex.I*y) n))
  rw [sub_sub_cancel] at ht
  exact ht.trans (add_le_add hB hb)

private theorem family_positive_part_sum (A : ℕ→Finset ℕ) (D : Finset ℕ)
    (L y : ℝ) (N : ℕ) :
    (∑ n∈D,signedPart 1 (A n) L y N n)=
      (∑ n∈D.filter (fun n => 0<(SquarefreeVaughanLogSource.coefficient L n).re),
        residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : 0<(SquarefreeVaughanLogSource.coefficient L n).re
  · rw [if_pos hp,← signedPart_add]
    have hz : signedPart (-1) (A n) L y N n=0 := by
      simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
        -(SquarefreeVaughanLogSource.coefficient L n).re≤0),mul_zero,zero_mul]
    rw [hz,add_zero]
  · rw [if_neg hp]
    simp only [signedPart,one_mul,max_eq_right (le_of_not_gt hp),mul_zero,zero_mul]

private theorem family_negative_part_sum (A : ℕ→Finset ℕ) (D : Finset ℕ)
    (L y : ℝ) (N : ℕ) :
    (∑ n∈D,signedPart (-1) (A n) L y N n)=
      (∑ n∈D.filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re<0),
        residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : (SquarefreeVaughanLogSource.coefficient L n).re<0
  · rw [if_pos hp,← signedPart_add]
    have hz : signedPart 1 (A n) L y N n=0 := by
      simp only [signedPart,one_mul,max_eq_right hp.le,mul_zero,zero_mul]
    rw [hz,zero_add]
  · rw [if_neg hp]
    simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
      -(SquarefreeVaughanLogSource.coefficient L n).re≤0),mul_zero,zero_mul]

/-- Count is preserved from the SAME original seed under owner extension. -/
theorem densePeriod_count_ge_from_seeds {S : Finset ℕ} {u H v y : ℝ} {N K n c : ℕ}
    (hS : ∀ n∈S,n∈coreBand u N K ∧ Squarefree n ∧ c≤n.primeFactors.card)
    (hn : n∈countPeriod S N H v y) : c≤n.primeFactors.card := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hh := Finset.mem_filter.mp ha
  obtain ⟨n₀,hn₀,he⟩ := Finset.mem_image.mp hh.1
  have hd := canonical_owner_data (hS n₀ hn₀).2.1
    (ZetaRieszJointPrimeEnergy.core_count (hS n₀ hn₀).1)
  have hc := owner_fibre_count hh.2.1 hh.2.2.2.2.2.2.2 hp
  rw [hc.2,←he,←hd.2.2.2.1]
  exact (hS n₀ hn₀).2.2

/-- Complete fibres remain in the original selected count56+ band. -/
theorem densePeriod_subset_56Band (j : ℕ) (hj : 32≤j)
    {u H v y : ℝ} (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤y) (hv : 100≤v)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j≤v-Real.pi/y)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*dyadicMomentOrder j) :
    countPeriod (dense56Band u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) H v y⊆dense56Band u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  have hS (m : ℕ) (hm : m∈dense56Band u (dyadicMomentOrder j) (dyadicPrimeCount j)) :
      m∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧ Squarefree m ∧ 56 ≤ m.primeFactors.card :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.1,(Finset.mem_filter.mp hm).2⟩
  have hd := countPeriod_data hy hv hn
  have hcore := countPeriod_subset_core_from_seeds j hj _ hu hU hy hv
    (fun m hm => ⟨(hS m hm).1,(hS m hm).2.1⟩) hL hlo hhi hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hcore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1⟩,densePeriod_count_ge_from_seeds hS hn⟩

theorem densePeriodGrid_subset_56Band (j : ℕ) (hj : 32≤j) {u b y : ℝ}
    (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y)
    (hN : 1000≤dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    densePeriodGrid (dense56Band u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) b y⊆dense56Band u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨k,_hk,hn⟩ := Finset.mem_biUnion.mp hn
  have hd := (Finset.mem_filter.mp hi).2
  exact densePeriod_subset_56Band j hj hu hU hy (grid_center_bounds hN hy hi).1
    hL hd.1 hd.2.1 hn

theorem dense56_label_grid_cover {u : ℝ} {N K n : ℕ}
    (hn : n∈dense56Band u N K) (hN : 4000≤N) {y b : ℝ} (hy : 54≤y)
    (hb : Real.pi/y≤b ∧ b≤2*Real.pi/y)
    (hlo : (244/125 : ℝ)*N<log n) (hhi : log n≤(2029/1000 : ℝ)*N)
    (hshare : log (largestPrime n)≤(601/1000 : ℝ)*log n)
    (hlarge : 20000<log (largestPrime n)) :
    ∃ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
      ∃ j∈denseScaleGrid (dense56Band u N K) N (ZetaRieszMultiPeriodSix.center b y i) y,
        n∈countPeriod (dense56Band u N K) N (10000*(2 : ℝ)^j)
          (ZetaRieszMultiPeriodSix.center b y i) y ∨
        n∈countBoundary (dense56Band u N K) N (10000*(2 : ℝ)^j)
          (ZetaRieszMultiPeriodSix.center b y i) y := by
  obtain ⟨i,hi,hT⟩ := ZetaRieszFiveSignCoverFloor.exists_completeGrid_period hN hy hb hlo hhi
  have hv : 100≤ZetaRieszMultiPeriodSix.center b y i := by
    have hNR : (4000 : ℝ)≤N := by exact_mod_cast hN
    have hπ : Real.pi/y≤1/16 :=
      (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
    linarith only [hT.2,hlo,hNR,hπ]
  obtain ⟨_,hs,hc,hclo,hchi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
  have hh := dense_label_full_cover (dense56Band u N K) hn hs hc hclo hchi hy hv hT hshare hlarge
  refine ⟨i,hi,?_⟩
  rcases hh with ⟨j,hp⟩ | ⟨j,hd⟩
  · have ha : countCofactors (dense56Band u N K) N (10000*(2 : ℝ)^j)
        (ZetaRieszMultiPeriodSix.center b y i) y≠∅ := by
      intro hem
      simp only [countPeriod,hem,Finset.biUnion_empty,Finset.notMem_empty] at hp
    exact ⟨j,mem_denseScaleGrid _ _ hy hv (Or.inl ha),Or.inl hp⟩
  · exact ⟨j,mem_denseScaleGrid _ _ hy hv
      (Or.inr (Finset.ne_empty_of_mem hd)),Or.inr hd⟩

/-- A LITERAL two-grid signed floor for the entire unpaid dense band.
Only the two explicitly displayed unmatched geometric populations remain;
all complete owner periods AND canonical near-owner clips have ONE
vanishing relative price. No rowwise signed hypothesis is assumed.
The owner allocation is unchanged and both arithmetic signs are joined. -/
theorem eventually_dense56_two_grid_floor {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let K := dyadicPrimeCount j
      let S := dense56Band u N K
      let A := fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}
      let L := SquarefreeVaughanLogSource.length u N
      let b := Real.pi/y
      let P := densePeriodGrid S N b y
      let Q := densePeriodGrid S N (b+Real.pi/y) y
      let D := denseBoundaryGrid S N b y
      let F := denseBoundaryGrid S N (b+Real.pi/y) y;
      (∑ n∈S\(P∪D),signedPart 1 (A n) L y N n)+
        (∑ n∈S\(Q∪F),signedPart (-1) (A n) L y N n)-
        unpaidCountSupplyPrice N*
          ((∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
            amplitude N (ZetaRieszMultiPeriodSix.center b y i)/
              ZetaRieszMultiPeriodSix.center b y i)+
           (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y,
            amplitude N (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)/
              ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i))≤
          (∑ n∈S,residualCoefficient (A n) L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hy0 : 0<y := by linarith
  have hpeak : cos (y*(Real.pi/y))=-1 := by
    rw [mul_div_cancel₀ _ hy0.ne',Real.cos_pi]
  have hroom := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [tendsto_dyadicMomentOrder.eventually eventually_dense_grid_floor,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0<u) (by norm_num : (0 : ℝ)≤11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hf hL hN hj
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := dense56Band u N K
  let A := fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}
  let L := SquarefreeVaughanLogSource.length u N
  let b := Real.pi/y
  let P := densePeriodGrid S N b y
  let Q := densePeriodGrid S N (b+Real.pi/y) y
  let D := denseBoundaryGrid S N b y
  let F := denseBoundaryGrid S N (b+Real.pi/y) y
  let I := ZetaRieszFiveSignCoverFloor.completeGrid N b y
  let J := ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y
  norm_num only at hL
  have hp := hf I S (fun _ _ => P) (fun _ _ => S)
    (ZetaRieszMultiPeriodSix.center b y) (fun _ => 1) u y hy
    (fun _ hi => (grid_center_bounds hN hy hi).2.1)
    (fun _ hi => (grid_center_bounds hN hy hi).2.2)
    (by intros; norm_num) hL
    (fun _ hi => (Finset.mem_filter.mp hi).2.2.1)
    (fun i _ => (staggered_peaks hy0 hpeak i).1.1)
    (by intro i _; rw [one_mul,(staggered_peaks hy0 hpeak i).1.2]; norm_num)
  have hq := hf J S (fun _ _ => S) (fun _ _ => Q)
    (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y) (fun _ => -1) u y hy
    (fun _ hi => (grid_center_bounds hN hy hi).2.1)
    (fun _ hi => (grid_center_bounds hN hy hi).2.2)
    (by intros; norm_num) hL
    (fun _ hi => (Finset.mem_filter.mp hi).2.2.1)
    (fun i _ => (staggered_peaks hy0 hpeak i).2.1)
    (by intro i _; rw [(staggered_peaks hy0 hpeak i).2.2]; norm_num)
  simp only [countBoundary_sdiff_seed,Finset.sum_empty,add_zero,
    Finset.sum_add_distrib] at hp hq
  rw [← densePeriodGrid_sum S hN hy,
    ← denseBoundaryGrid_sum S P N hy] at hp
  rw [← densePeriodGrid_sum S hN hy,
    ← denseBoundaryGrid_sum S Q N hy] at hq
  have hP := densePeriodGrid_subset_56Band j hj hu hU hy hN hL (b := b)
  have hQ := densePeriodGrid_subset_56Band j hj hu hU hy hN hL (b := b+Real.pi/y)
  have he := family_two_cover_ledger A S P Q L y N hP hQ
  rw [ZetaRieszOwnerTieFloor.missed_boundary_split S D P
      (denseBoundaryGrid_subset S N b y) (fun n => signedPart 1 (A n) L y N n),
    ZetaRieszOwnerTieFloor.missed_boundary_split S F Q
      (denseBoundaryGrid_subset S N (b+Real.pi/y) y)
      (fun n => signedPart (-1) (A n) L y N n)] at he
  dsimp only
  change _≤(∑ n∈S,residualCoefficient (A n) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  change -unpaidCountSupplyPrice N*(∑ i∈I,
    amplitude N (ZetaRieszMultiPeriodSix.center b y i)/ZetaRieszMultiPeriodSix.center b y i)≤
      (∑ n∈P,signedPart 1 (A n) L y N n)+(∑ n∈D\P,signedPart 1 (A n) L y N n) at hp
  change -unpaidCountSupplyPrice N*(∑ i∈J,
    amplitude N (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)/
      ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)≤
      (∑ n∈Q,signedPart (-1) (A n) L y N n)+
      (∑ n∈F\Q,signedPart (-1) (A n) L y N n) at hq
  linarith only [he,hp,hq]

/-- Every unmatched label has an EXPLICIT geometric cause: a paid radial
edge, a large-owner share, or a small-owner head. There is no anonymous
intermediate-count, bin, parity, roughness or clipped-phase remainder. -/
theorem dense56_grid_unmatched_geometry {u : ℝ} {N K n : ℕ}
    (hN : 4000≤N) {b y : ℝ} (hy : 54≤y)
    (hb : Real.pi/y≤b ∧ b≤2*Real.pi/y)
    (hn : n∈dense56Band u N K\
      (densePeriodGrid (dense56Band u N K) N b y∪
       denseBoundaryGrid (dense56Band u N K) N b y)) :
    ¬((244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N) ∨
      (601/1000 : ℝ)*log n<log (largestPrime n) ∨
      log (largestPrime n)≤20000 := by
  obtain ⟨hn,hnot⟩ := Finset.mem_sdiff.mp hn
  by_contra h
  push Not at h
  obtain ⟨i,hi,k,hk,hp|hd⟩ := dense56_label_grid_cover hn hN hy hb h.1.1 h.1.2 h.2.1 h.2.2
  · exact hnot (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_biUnion.mpr ⟨k,hk,hp⟩⟩)))
  · exact hnot (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_biUnion.mpr ⟨k,hk,hd⟩⟩)))

/-- ANY literal signed subset of an unmatched dense-grid population has
only the already certified radial/large-owner source errors. This pays the
exterior masks, not the retained resonant sum or its absolute allowance. -/
theorem exists_dense56_unmatched_bound {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∃ r C : ℝ,0≤r ∧ r<1 ∧ 0≤C ∧
      ∀ᶠ j : ℕ in atTop,∀ (b : ℝ) (G : Finset ℕ),
        (Real.pi/y≤b ∧ b≤2*Real.pi/y) →
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let S := dense56Band u N K
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N;
        G⊆S\(densePeriodGrid S N b y∪denseBoundaryGrid S N b y) →
        ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
          2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,houter⟩ := ZetaRieszFiveSignCoverFloor.exists_outer_subset_bound
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually eventually_dense_owner_large,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hlarge hN hj
  intro b G hb
  dsimp only
  intro hG
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := dense56Band u N K
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let dom := fun n : ℕ => Squarefree n ∧ 1<n ∧ ¬n.Prime ∧
    ∃ p∈n.primeFactors,p∈A ∧ eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*log n≤log p
  let D := G.filter dom
  let F := (G\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N))
  have he : (∑ n∈G,f n)=(∑ n∈D,f n)+(∑ n∈F,f n) := by
    have hs := Finset.sum_sdiff (Finset.filter_subset dom G) (f := f)
    have hf : (∑ n∈F,f n)=∑ n∈G\D,f n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnotF
      obtain ⟨hnG,hnotD⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hnS,_⟩ := Finset.mem_sdiff.mp (hG hnG)
      have hnCore := (Finset.mem_filter.mp (Finset.mem_filter.mp hnS).1).1
      have hnotdom : ¬dom n := fun hd => hnotD (Finset.mem_filter.mpr ⟨hnG,hd⟩)
      have hgeo : (244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N := by
        by_contra hg
        exact hnotF (Finset.mem_filter.mpr ⟨hn,hg⟩)
      have hgeom := dense56_grid_unmatched_geometry hN hy hb (hG hnG)
      have howner : (601/1000 : ℝ)*log n<log (largestPrime n) :=
        (hgeom.resolve_left (not_not.mpr hgeo)).resolve_right
          (not_le.mpr (hlarge u K n (Finset.mem_filter.mp hnS).1))
      have hz : residualCoefficient A L N n=0 := by
        by_contra hzero
        have hh := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u
          (Finset.mem_filter.mpr ⟨hnCore,hnotdom⟩) hzero
          (largestPrime n) (ZetaRieszOwnedCells.largestPrime_mem_of_two
            (by have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hnS).1).2.2.1; omega))
        exact (not_lt_of_ge howner.le) hh
      simp only [f,hz,zero_mul]
    rw [← hf] at hs
    change (∑ n∈F,f n)+(∑ n∈D,f n)=∑ n∈G,f n at hs
    exact hs.symm.trans (add_comm _ _)
  have hLhi : L≤(139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (by omega : 2≤N)
    have hl : 2*log 2≤(139/100 : ℝ) := by linarith [log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))
  have hd := ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A D N (by omega) y
    (by linarith : 0≤u) hU (SquarefreeVaughanLogSource.length_pos u N) hLhi (by
      intro n hn
      obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hn
      refine ⟨hs,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
      have hlogcut : log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ)=L := by
        simp only [L,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
      change log p≤L
      rw [← hlogcut]
      exact (log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  have hf := houter N A F y u (by linarith : 0≤u) hU (by
    intro n hn; exact (Finset.mem_filter.mp hn).2)
  change ‖(u : ℂ)^(N+1)*∑ n∈G,f n‖≤_
  rw [he,mul_add]
  exact (norm_add_le _ _).trans (add_le_add hd hf)

/-- The ENTIRE original unpaid dense band now has an independent signed
floor, with one relative supply price and source-geometric errors. Both
literal phase grids, all counts and all original masks are covered; no
unmatched signed population or completion correction is a hypothesis. -/
theorem exists_dense56_band_floor {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∃ r C : ℝ,0≤r ∧ r<1 ∧ 0≤C ∧
      ∀ᶠ j : ℕ in atTop,
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let S := dense56Band u N K
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let b := Real.pi/y;
        -u^(N+1)*unpaidCountSupplyPrice N*
          ((∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
            exp (-ZetaRieszMultiPeriodSix.center b y i/2)*
              (ZetaRieszMultiPeriodSix.center b y i)^N/N.factorial)+
           (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y,
            exp (-ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i/2)*
              (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)^N/N.factorial))-
          4*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)-
          2*r^N*C-3*ownerPaymentError N≤
            ((u : ℂ)^(N+1)*∑ n∈S,residualCoefficient A L N n*
              zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r,C,hr,hr1,hC,hunmatched⟩ := exists_dense56_unmatched_bound hu hU hy
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [eventually_dense56_two_grid_floor hu hU hy,hunmatched,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
      with j hfloor hbound hN
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := dense56Band u N K
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let Ao := fun n => A∩{largestPrime n}
  let b := Real.pi/y
  let U := S\(densePeriodGrid S N b y∪denseBoundaryGrid S N b y)
  let V := S\(densePeriodGrid S N (b+Real.pi/y) y∪denseBoundaryGrid S N (b+Real.pi/y) y)
  let G := U.filter (fun n => 0<(SquarefreeVaughanLogSource.coefficient L n).re)
  let H := V.filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re<0)
  have hy0 : 0<y := by linarith
  have hπ : 0≤Real.pi/y := by positivity
  have hb : Real.pi/y≤b ∧ b≤2*Real.pi/y := by
    refine ⟨le_rfl,?_⟩
    calc
      b ≤ Real.pi/y+Real.pi/y := by dsimp [b]; linarith only [hπ]
      _ = 2*Real.pi/y := by ring
  have hb' : Real.pi/y≤b+Real.pi/y ∧ b+Real.pi/y≤2*Real.pi/y := by
    constructor
    · dsimp [b]; linarith only [hπ]
    · exact le_of_eq (by dsimp [b]; ring)
  have hG := hbound b G hb (Finset.filter_subset _ _)
  have hH := hbound (b+Real.pi/y) H hb' (Finset.filter_subset _ _)
  have hwindow : S⊆literalWindow N :=
    Finset.Subset.trans (Finset.filter_subset _ _) (Finset.Subset.trans (Finset.filter_subset _ _) (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))
  have hGw : G⊆literalWindow N :=
    Finset.Subset.trans (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset) hwindow
  have hHw : H⊆literalWindow N :=
    Finset.Subset.trans (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset) hwindow
  have hGp := norm_owner_subset_le A G (by linarith : 0≤u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hGw hG
  have hHp := norm_owner_subset_le A H (by linarith : 0≤u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hHw hH
  have hp := (abs_le.mp ((Complex.abs_re_le_norm _).trans hGp)).1
  have hq := (abs_le.mp ((Complex.abs_re_le_norm _).trans hHp)).1
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← family_positive_part_sum] at hp
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← family_negative_part_sum] at hq
  have hscaled := mul_le_mul_of_nonneg_left hfloor
    (pow_nonneg (by linarith : 0≤u) (N+1))
  have ho := (ZetaRieszNonownerAllocation.signed_owner_bounds (fun _ => A) S (fun _ => 1)
    (SquarefreeVaughanLogSource.length_pos u N) N hwindow (by intros; norm_num) y
    (by linarith : 0≤u) (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)).1
  simp only [one_mul] at ho
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at ho
  simp only [Complex.re_ofReal_mul] at ho
  have hunit {c : ℝ} (hc : 0<c) : amplitude N c/c=exp (-c/2)*c^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  have hsum (d : ℝ) :
      (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N d y,
        amplitude N (ZetaRieszMultiPeriodSix.center d y i)/ZetaRieszMultiPeriodSix.center d y i)=
      ∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N d y,
        exp (-ZetaRieszMultiPeriodSix.center d y i/2)*(ZetaRieszMultiPeriodSix.center d y i)^N/N.factorial := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hunit (by have hh := (grid_center_bounds hN hy hi).1; linarith)
  dsimp only at hscaled
  rw [hsum b,hsum (b+Real.pi/y)] at hscaled
  dsimp only
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  change _≤u^(N+1)*(∑ n∈S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  change -(2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C+
    ownerPaymentError N)≤u^(N+1)*(∑ n∈U,signedPart 1 (Ao n) L y N n) at hp
  change -(2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C+
    ownerPaymentError N)≤u^(N+1)*(∑ n∈V,signedPart (-1) (Ao n) L y N n) at hq
  change u^(N+1)*(∑ n∈S,residualCoefficient (Ao n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
    ownerPaymentError N≤u^(N+1)*(∑ n∈S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re at ho
  nlinarith only [hp,hq,hscaled,ho]

/-- Count is preserved from the SAME original seed under owner extension. -/
theorem binPeriod_count_ge_from_seeds {S : Finset ℕ} {u H v y : ℝ} {N K n c : ℕ}
    (hS : ∀ n∈S,n∈coreBand u N K ∧ Squarefree n ∧ c≤n.primeFactors.card)
    (hn : n∈binPeriod S N H v y) : c≤n.primeFactors.card := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hh := Finset.mem_filter.mp ha
  obtain ⟨n₀,hn₀,he⟩ := Finset.mem_image.mp hh.1
  have hd := canonical_owner_data (hS n₀ hn₀).2.1
    (ZetaRieszJointPrimeEnergy.core_count (hS n₀ hn₀).1)
  have hc := owner_fibre_count hh.2.1 hh.2.2.2.2.2.2.2 hp
  rw [hc.2,←he,←hd.2.2.2.1]
  exact (hS n₀ hn₀).2.2

/-- Complete fibres remain in the original selected count56+ band. -/
theorem binPeriod_subset_56Band (j : ℕ) (hj : 32≤j)
    {u H v y : ℝ} (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤y) (hv : 100≤v)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*dyadicMomentOrder j≤v-Real.pi/y)
    (hhi : v+Real.pi/y≤(203/100 : ℝ)*dyadicMomentOrder j) :
    binPeriod (bin56Band u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) H v y⊆bin56Band u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  have hS (m : ℕ) (hm : m∈bin56Band u (dyadicMomentOrder j) (dyadicPrimeCount j)) :
      m∈coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧ Squarefree m ∧ 56 ≤ m.primeFactors.card :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.1,(Finset.mem_filter.mp hm).2⟩
  have hd := binPeriod_data hy hv hn
  have hcore := binPeriod_subset_core_from_seeds j hj _ hu hU hy hv
    (fun m hm => ⟨(hS m hm).1,(hS m hm).2.1⟩) hL hlo hhi hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hcore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1⟩,binPeriod_count_ge_from_seeds hS hn⟩

theorem binPeriodGrid_subset_56Band (j : ℕ) (hj : 32≤j) {u b y : ℝ}
    (hu : 1/2<u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y)
    (hN : 1000≤dyadicMomentOrder j)
    (hL : (11/8 : ℝ)*dyadicMomentOrder j≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    binPeriodGrid (bin56Band u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) b y⊆bin56Band u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  intro n hn
  obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨k,_hk,hn⟩ := Finset.mem_biUnion.mp hn
  have hd := (Finset.mem_filter.mp hi).2
  exact binPeriod_subset_56Band j hj hu hU hy (grid_center_bounds hN hy hi).1
    hL hd.1 hd.2.1 hn

theorem bin56_label_grid_cover {u : ℝ} {N K n : ℕ}
    (hn : n∈bin56Band u N K) (hN : 4000≤N) {y b : ℝ} (hy : 54≤y)
    (hb : Real.pi/y≤b ∧ b≤2*Real.pi/y)
    (hlo : (244/125 : ℝ)*N<log n) (hhi : log n≤(2029/1000 : ℝ)*N)
    (hshare : log (largestPrime n)≤(601/1000 : ℝ)*log n)
    (hlarge : 20000<log (largestPrime n)) :
    ∃ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
      ∃ j∈binScaleGrid (bin56Band u N K) N (ZetaRieszMultiPeriodSix.center b y i) y,
        n∈binPeriod (bin56Band u N K) N (10000*(2 : ℝ)^j)
          (ZetaRieszMultiPeriodSix.center b y i) y ∨
        n∈binBoundary (bin56Band u N K) N (10000*(2 : ℝ)^j)
          (ZetaRieszMultiPeriodSix.center b y i) y := by
  obtain ⟨i,hi,hT⟩ := ZetaRieszFiveSignCoverFloor.exists_completeGrid_period hN hy hb hlo hhi
  have hv : 100≤ZetaRieszMultiPeriodSix.center b y i := by
    have hNR : (4000 : ℝ)≤N := by exact_mod_cast hN
    have hπ : Real.pi/y≤1/16 :=
      (div_le_iff₀ (by linarith : 0<y)).mpr (by nlinarith [Real.pi_lt_d4])
    linarith only [hT.2,hlo,hNR,hπ]
  obtain ⟨_,hs,hc,hclo,hchi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
  have hh := bin_label_full_cover (bin56Band u N K) hn hs hc hclo hchi hy hv hT hshare hlarge
  refine ⟨i,hi,?_⟩
  rcases hh with ⟨j,hp⟩ | ⟨j,hd⟩
  · have ha : binCofactors (bin56Band u N K) N (10000*(2 : ℝ)^j)
        (ZetaRieszMultiPeriodSix.center b y i) y≠∅ := by
      intro hem
      simp only [binPeriod,hem,Finset.biUnion_empty,Finset.notMem_empty] at hp
    exact ⟨j,mem_binScaleGrid _ _ hy hv (Or.inl ha),Or.inl hp⟩
  · exact ⟨j,mem_binScaleGrid _ _ hy hv
      (Or.inr (Finset.ne_empty_of_mem hd)),Or.inr hd⟩


/-- A LITERAL two-grid signed floor for the entire unpaid lower-count few-bin band.
Only the two explicitly displayed unmatched geometric populations remain;
all complete owner periods AND canonical near-owner clips have ONE
vanishing relative price. No rowwise signed hypothesis is assumed.
The owner allocation is unchanged and both arithmetic signs are joined. -/
theorem eventually_bin56_two_grid_floor {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let K := dyadicPrimeCount j
      let S := bin56Band u N K
      let A := fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}
      let L := SquarefreeVaughanLogSource.length u N
      let b := Real.pi/y
      let P := binPeriodGrid S N b y
      let Q := binPeriodGrid S N (b+Real.pi/y) y
      let D := binBoundaryGrid S N b y
      let F := binBoundaryGrid S N (b+Real.pi/y) y;
      (∑ n∈S\(P∪D),signedPart 1 (A n) L y N n)+
        (∑ n∈S\(Q∪F),signedPart (-1) (A n) L y N n)-
        intermediateSupplyPrice N*
          ((∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
            amplitude N (ZetaRieszMultiPeriodSix.center b y i)/
              ZetaRieszMultiPeriodSix.center b y i)+
           (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y,
            amplitude N (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)/
              ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i))≤
          (∑ n∈S,residualCoefficient (A n) L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hy0 : 0<y := by linarith
  have hpeak : cos (y*(Real.pi/y))=-1 := by
    rw [mul_div_cancel₀ _ hy0.ne',Real.cos_pi]
  have hroom := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [tendsto_dyadicMomentOrder.eventually eventually_bin_grid_floor,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0<u) (by norm_num : (0 : ℝ)≤11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hf hL hN hj
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := bin56Band u N K
  let A := fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}
  let L := SquarefreeVaughanLogSource.length u N
  let b := Real.pi/y
  let P := binPeriodGrid S N b y
  let Q := binPeriodGrid S N (b+Real.pi/y) y
  let D := binBoundaryGrid S N b y
  let F := binBoundaryGrid S N (b+Real.pi/y) y
  let I := ZetaRieszFiveSignCoverFloor.completeGrid N b y
  let J := ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y
  norm_num only at hL
  have hp := hf I S (fun _ _ => P) (fun _ _ => S)
    (ZetaRieszMultiPeriodSix.center b y) (fun _ => 1) u y hy
    (fun _ hi => (grid_center_bounds hN hy hi).2.1)
    (fun _ hi => (grid_center_bounds hN hy hi).2.2)
    (by intros; norm_num) hL
    (fun _ hi => (Finset.mem_filter.mp hi).2.2.1)
    (fun i _ => (staggered_peaks hy0 hpeak i).1.1)
    (by intro i _; rw [one_mul,(staggered_peaks hy0 hpeak i).1.2]; norm_num)
  have hq := hf J S (fun _ _ => S) (fun _ _ => Q)
    (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y) (fun _ => -1) u y hy
    (fun _ hi => (grid_center_bounds hN hy hi).2.1)
    (fun _ hi => (grid_center_bounds hN hy hi).2.2)
    (by intros; norm_num) hL
    (fun _ hi => (Finset.mem_filter.mp hi).2.2.1)
    (fun i _ => (staggered_peaks hy0 hpeak i).2.1)
    (by intro i _; rw [(staggered_peaks hy0 hpeak i).2.2]; norm_num)
  simp only [binBoundary_sdiff_seed,Finset.sum_empty,add_zero,
    Finset.sum_add_distrib] at hp hq
  rw [← binPeriodGrid_sum S hN hy,
    ← binBoundaryGrid_sum S P N hy] at hp
  rw [← binPeriodGrid_sum S hN hy,
    ← binBoundaryGrid_sum S Q N hy] at hq
  have hP := binPeriodGrid_subset_56Band j hj hu hU hy hN hL (b := b)
  have hQ := binPeriodGrid_subset_56Band j hj hu hU hy hN hL (b := b+Real.pi/y)
  have he := family_two_cover_ledger A S P Q L y N hP hQ
  rw [ZetaRieszOwnerTieFloor.missed_boundary_split S D P
      (binBoundaryGrid_subset S N b y) (fun n => signedPart 1 (A n) L y N n),
    ZetaRieszOwnerTieFloor.missed_boundary_split S F Q
      (binBoundaryGrid_subset S N (b+Real.pi/y) y)
      (fun n => signedPart (-1) (A n) L y N n)] at he
  dsimp only
  change _≤(∑ n∈S,residualCoefficient (A n) L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  change -intermediateSupplyPrice N*(∑ i∈I,
    amplitude N (ZetaRieszMultiPeriodSix.center b y i)/ZetaRieszMultiPeriodSix.center b y i)≤
      (∑ n∈P,signedPart 1 (A n) L y N n)+(∑ n∈D\P,signedPart 1 (A n) L y N n) at hp
  change -intermediateSupplyPrice N*(∑ i∈J,
    amplitude N (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)/
      ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)≤
      (∑ n∈Q,signedPart (-1) (A n) L y N n)+
      (∑ n∈F\Q,signedPart (-1) (A n) L y N n) at hq
  linarith only [he,hp,hq]

/-- Every unmatched label has an EXPLICIT geometric cause: a paid radial
edge, a large-owner share, or a small-owner head. There is no anonymous
intermediate-count, bin, parity, roughness or clipped-phase remainder. -/
theorem bin56_grid_unmatched_geometry {u : ℝ} {N K n : ℕ}
    (hN : 4000≤N) {b y : ℝ} (hy : 54≤y)
    (hb : Real.pi/y≤b ∧ b≤2*Real.pi/y)
    (hn : n∈bin56Band u N K\
      (binPeriodGrid (bin56Band u N K) N b y∪
       binBoundaryGrid (bin56Band u N K) N b y)) :
    ¬((244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N) ∨
      (601/1000 : ℝ)*log n<log (largestPrime n) ∨
      log (largestPrime n)≤20000 := by
  obtain ⟨hn,hnot⟩ := Finset.mem_sdiff.mp hn
  by_contra h
  push Not at h
  obtain ⟨i,hi,k,hk,hp|hd⟩ := bin56_label_grid_cover hn hN hy hb h.1.1 h.1.2 h.2.1 h.2.2
  · exact hnot (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_biUnion.mpr ⟨k,hk,hp⟩⟩)))
  · exact hnot (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨i,hi,Finset.mem_biUnion.mpr ⟨k,hk,hd⟩⟩)))

/-- ANY literal signed subset of an unmatched dense-grid population has
only the already certified radial/large-owner source errors. This pays the
exterior masks, not the retained resonant sum or its absolute allowance. -/
theorem exists_bin56_unmatched_bound {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∃ r C : ℝ,0≤r ∧ r<1 ∧ 0≤C ∧
      ∀ᶠ j : ℕ in atTop,∀ (b : ℝ) (G : Finset ℕ),
        (Real.pi/y≤b ∧ b≤2*Real.pi/y) →
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let S := bin56Band u N K
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N;
        G⊆S\(binPeriodGrid S N b y∪binBoundaryGrid S N b y) →
        ‖(u : ℂ)^(N+1)*∑ n∈G,residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
          2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,houter⟩ := ZetaRieszFiveSignCoverFloor.exists_outer_subset_bound
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually eventually_bin_owner_large,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hlarge hN hj
  intro b G hb
  dsimp only
  intro hG
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := bin56Band u N K
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let dom := fun n : ℕ => Squarefree n ∧ 1<n ∧ ¬n.Prime ∧
    ∃ p∈n.primeFactors,p∈A ∧ eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*log n≤log p
  let D := G.filter dom
  let F := (G\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N))
  have he : (∑ n∈G,f n)=(∑ n∈D,f n)+(∑ n∈F,f n) := by
    have hs := Finset.sum_sdiff (Finset.filter_subset dom G) (f := f)
    have hf : (∑ n∈F,f n)=∑ n∈G\D,f n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnotF
      obtain ⟨hnG,hnotD⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hnS,_⟩ := Finset.mem_sdiff.mp (hG hnG)
      have hnCore := (Finset.mem_filter.mp (Finset.mem_filter.mp hnS).1).1
      have hnotdom : ¬dom n := fun hd => hnotD (Finset.mem_filter.mpr ⟨hnG,hd⟩)
      have hgeo : (244/125 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N := by
        by_contra hg
        exact hnotF (Finset.mem_filter.mpr ⟨hn,hg⟩)
      have hgeom := bin56_grid_unmatched_geometry hN hy hb (hG hnG)
      have howner : (601/1000 : ℝ)*log n<log (largestPrime n) :=
        (hgeom.resolve_left (not_not.mpr hgeo)).resolve_right
          (not_le.mpr (hlarge u K n (Finset.mem_filter.mp hnS).1))
      have hz : residualCoefficient A L N n=0 := by
        by_contra hzero
        have hh := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u
          (Finset.mem_filter.mpr ⟨hnCore,hnotdom⟩) hzero
          (largestPrime n) (ZetaRieszOwnedCells.largestPrime_mem_of_two
            (by have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hnS).1).2.2.1; omega))
        exact (not_lt_of_ge howner.le) hh
      simp only [f,hz,zero_mul]
    rw [← hf] at hs
    change (∑ n∈F,f n)+(∑ n∈D,f n)=∑ n∈G,f n at hs
    exact hs.symm.trans (add_comm _ _)
  have hLhi : L≤(139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (by omega : 2≤N)
    have hl : 2*log 2≤(139/100 : ℝ) := by linarith [log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))
  have hd := ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A D N (by omega) y
    (by linarith : 0≤u) hU (SquarefreeVaughanLogSource.length_pos u N) hLhi (by
      intro n hn
      obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hn
      refine ⟨hs,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
      have hlogcut : log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ)=L := by
        simp only [L,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
      change log p≤L
      rw [← hlogcut]
      exact (log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  have hf := houter N A F y u (by linarith : 0≤u) hU (by
    intro n hn; exact (Finset.mem_filter.mp hn).2)
  change ‖(u : ℂ)^(N+1)*∑ n∈G,f n‖≤_
  rw [he,mul_add]
  exact (norm_add_le _ _).trans (add_le_add hd hf)

/-- The ENTIRE original unpaid few-bin band now has an independent signed
floor, with one relative supply price and source-geometric errors. Both
literal phase grids, all counts and all original masks are covered; no
unmatched signed population or completion correction is a hypothesis. -/
theorem exists_bin56_band_floor {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤y) :
    ∃ r C : ℝ,0≤r ∧ r<1 ∧ 0≤C ∧
      ∀ᶠ j : ℕ in atTop,
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let S := bin56Band u N K
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let b := Real.pi/y;
        -u^(N+1)*intermediateSupplyPrice N*
          ((∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N b y,
            exp (-ZetaRieszMultiPeriodSix.center b y i/2)*
              (ZetaRieszMultiPeriodSix.center b y i)^N/N.factorial)+
           (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N (b+Real.pi/y) y,
            exp (-ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i/2)*
              (ZetaRieszMultiPeriodSix.center (b+Real.pi/y) y i)^N/N.factorial))-
          4*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)-
          2*r^N*C-3*ownerPaymentError N≤
            ((u : ℂ)^(N+1)*∑ n∈S,residualCoefficient A L N n*
              zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r,C,hr,hr1,hC,hunmatched⟩ := exists_bin56_unmatched_bound hu hU hy
  refine ⟨r,C,hr,hr1,hC,?_⟩
  filter_upwards [eventually_bin56_two_grid_floor hu hU hy,hunmatched,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
      with j hfloor hbound hN
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let S := bin56Band u N K
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let Ao := fun n => A∩{largestPrime n}
  let b := Real.pi/y
  let U := S\(binPeriodGrid S N b y∪binBoundaryGrid S N b y)
  let V := S\(binPeriodGrid S N (b+Real.pi/y) y∪binBoundaryGrid S N (b+Real.pi/y) y)
  let G := U.filter (fun n => 0<(SquarefreeVaughanLogSource.coefficient L n).re)
  let H := V.filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re<0)
  have hy0 : 0<y := by linarith
  have hπ : 0≤Real.pi/y := by positivity
  have hb : Real.pi/y≤b ∧ b≤2*Real.pi/y := by
    refine ⟨le_rfl,?_⟩
    calc
      b ≤ Real.pi/y+Real.pi/y := by dsimp [b]; linarith only [hπ]
      _ = 2*Real.pi/y := by ring
  have hb' : Real.pi/y≤b+Real.pi/y ∧ b+Real.pi/y≤2*Real.pi/y := by
    constructor
    · dsimp [b]; linarith only [hπ]
    · exact le_of_eq (by dsimp [b]; ring)
  have hG := hbound b G hb (Finset.filter_subset _ _)
  have hH := hbound (b+Real.pi/y) H hb' (Finset.filter_subset _ _)
  have hwindow : S⊆literalWindow N :=
    Finset.Subset.trans (Finset.filter_subset _ _) (Finset.Subset.trans (Finset.filter_subset _ _) (ZetaRieszNonownerAllocation.coreBand_subset_literalWindow u N K))
  have hGw : G⊆literalWindow N :=
    Finset.Subset.trans (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset) hwindow
  have hHw : H⊆literalWindow N :=
    Finset.Subset.trans (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset) hwindow
  have hGp := norm_owner_subset_le A G (by linarith : 0≤u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hGw hG
  have hHp := norm_owner_subset_le A H (by linarith : 0≤u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hHw hH
  have hp := (abs_le.mp ((Complex.abs_re_le_norm _).trans hGp)).1
  have hq := (abs_le.mp ((Complex.abs_re_le_norm _).trans hHp)).1
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← family_positive_part_sum] at hp
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← family_negative_part_sum] at hq
  have hscaled := mul_le_mul_of_nonneg_left hfloor
    (pow_nonneg (by linarith : 0≤u) (N+1))
  have ho := (ZetaRieszNonownerAllocation.signed_owner_bounds (fun _ => A) S (fun _ => 1)
    (SquarefreeVaughanLogSource.length_pos u N) N hwindow (by intros; norm_num) y
    (by linarith : 0≤u) (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)).1
  simp only [one_mul] at ho
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at ho
  simp only [Complex.re_ofReal_mul] at ho
  have hunit {c : ℝ} (hc : 0<c) : amplitude N c/c=exp (-c/2)*c^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  have hsum (d : ℝ) :
      (∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N d y,
        amplitude N (ZetaRieszMultiPeriodSix.center d y i)/ZetaRieszMultiPeriodSix.center d y i)=
      ∑ i∈ZetaRieszFiveSignCoverFloor.completeGrid N d y,
        exp (-ZetaRieszMultiPeriodSix.center d y i/2)*(ZetaRieszMultiPeriodSix.center d y i)^N/N.factorial := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hunit (by have hh := (grid_center_bounds hN hy hi).1; linarith)
  dsimp only at hscaled
  rw [hsum b,hsum (b+Real.pi/y)] at hscaled
  dsimp only
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  change _≤u^(N+1)*(∑ n∈S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  change -(2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C+
    ownerPaymentError N)≤u^(N+1)*(∑ n∈U,signedPart 1 (Ao n) L y N n) at hp
  change -(2*zetaMoebiusLogMajorantMass (1+1/262144)*exp (-(N : ℝ)/1000000)+r^N*C+
    ownerPaymentError N)≤u^(N+1)*(∑ n∈V,signedPart (-1) (Ao n) L y N n) at hq
  change u^(N+1)*(∑ n∈S,residualCoefficient (Ao n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
    ownerPaymentError N≤u^(N+1)*(∑ n∈S,residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re at ho
  nlinarith only [hp,hq,hscaled,ho]

open ZetaRieszFiveSignCoverFloor ZetaRieszRoughFiveJoinedFloor
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead ZetaRieszSevenCountTail
open ZetaRieszRoughFivePeriodFloor ZetaRieszMultiPeriodSix
open ZetaRieszOneSidedArithmetic

open ZetaRieszHighSignCoverFloor

private theorem paid_parts (E : Finset ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 5), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 6), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55), f n) =
    ∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
      n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
      (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)), f n := by
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h3 : n.primeFactors.card = 3
  · simp [h3]
  by_cases h5 : n.primeFactors.card = 5
  · simp [h5]
  by_cases h6 : n.primeFactors.card = 6
  · simp [h6]
  simp only [h3,h5,h6,if_false,false_or,zero_add]

open ZetaRieszThreeSignCoverFloor (tripleRestSpent nontriple_rest_filter_eq
  tripleRestSpent_eq eventually_core_full_floor_with_triples_rejoined)

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h

set_option maxHeartbeats 1600000 in
/-- Join all existing fixed-count payments with BOTH original growing
population payments, with no overlap. The SAME literal supply retains
257/512 after all three debits; every existing favorable fixed-band
and head credit survives. The numerical whole floor remains open. -/
theorem eventually_joined_floor_combined_populations {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ : ℝ, ∃ err : ℕ → ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      0 < θ ∧ θ ≤ 1/128 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
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
        let Ys := radialSupply N h w
        let E := S\tripleRestSpent S N Q P V R η h L w
        let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55))
        let Ds := dense56Band u N (dyadicPrimeCount j)
        let Bs := bin56Band u N (dyadicPrimeCount j)
        let Eo := ((E\Epaid)\Ds)\Bs
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
            max (∑ n ∈ Epaid, f n).re 0+(257/512 : ℝ)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r₀,C₀,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ := eventually_core_full_floor_with_triples_rejoined hu hU hy
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩  :=
    ZetaRieszFiveSignCoverFloor.exists_unpaid_five_floor hu hU hy (by positivity : 0 < κ/4)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hsix⟩ := ZetaRieszSixSignCoverFloor.exists_unpaid_six_floor hu hU hy (by positivity : 0 < κ/4)
  obtain ⟨r₃,C₃,hr₃,hr₃1,hC₃,hthree⟩ := ZetaRieszThreeSignCoverFloor.exists_unpaid_three_floor hu hU hy
    (by positivity : 0 < κ/4)
  obtain ⟨err₄,herr₄0,herr₄,hhigh⟩ := exists_unpaid_band_floor hu hU hy
    (by positivity : 0 < κ/4)
  obtain ⟨r₅,C₅,hr₅,hr₅1,hC₅,hdense⟩ := exists_dense56_band_floor hu hU hy
  obtain ⟨r₆,C₆,hr₆,hr₆1,hC₆,hbin⟩ := exists_bin56_band_floor hu hU hy
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
  have h₆ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₆ hr₆1).mul_const (2*C₆)).comp
    tendsto_dyadicMomentOrder
  have h₇ := (tendsto_ownerPaymentError.comp tendsto_dyadicMomentOrder).const_mul (6 : ℝ)
  have ho0 (j : ℕ) : 0≤ownerPaymentError (dyadicMomentOrder j) := by
    unfold ownerPaymentError
    positivity [zetaMoebiusLogMajorantMass_nonneg (2049/2048),
      ZetaRieszNonownerAllocation.nonownerRate_bounds.1]
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+5*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂+2*r₃^(dyadicMomentOrder j)*C₃+err₄ j+
    2*r₅^(dyadicMomentOrder j)*C₅+2*r₆^(dyadicMomentOrder j)*C₆+6*ownerPaymentError (dyadicMomentOrder j)
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := ((((((((h₀.add heLim).add (hdLim.const_mul (5 : ℝ))).add h₁).add h₂).add h₃).add herr₄).add h₅).add h₆).add h₇
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j,herr₄0 j,ho0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hsix,hthree,hhigh,hdense,hbin,
    tendsto_dyadicMomentOrder.eventually (eventually_count_cost_paid_by_same_supply hc hy),
    tendsto_dyadicMomentOrder.eventually (eventually_bin_cost_paid_by_same_supply hc hy),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
      with j hj hfive hsix hthree hhigh hdense hbin hdensecost hbincost hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
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
  let Ys := radialSupply N h w
  let E := S\tripleRestSpent S N Q P V R η h L w
  let E3 := E.filter (fun n : ℕ => n.primeFactors.card = 3)
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let E6 := E.filter (fun n : ℕ => n.primeFactors.card = 6)
  let Ehi := E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
  let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55))
  let Ds := dense56Band u N (dyadicPrimeCount j)
  let Bs := bin56Band u N (dyadicPrimeCount j)
  let Eo := ((E\Epaid)\Ds)\Bs
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  have hQlog : Real.log Q ≤ (N : ℝ)/128 :=
    (log_floor_exp_le (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))).trans
      (by have hd := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N); nlinarith)
  have ht := hthree Q P V R η h w hh hhu hηu hQlog hw
  have hp := hfive Q P V R η h w hh hhu hw
  have hq := hsix Q P V R η h w hh hhu hw
  have h5eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (5 : ℕ) ≠ 3)
  have h6eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (6 : ℕ) ≠ 3)
  have hbandFloor := hhigh Q P V R η h w hh hhu hw
  have hheq := high_rest_filter_eq S N Q P V R η h L w
  dsimp only at hp hq ht hbandFloor
  rw [←h5eq] at hp
  rw [←h6eq] at hq
  rw [←hheq] at hbandFloor
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*(κ/4)*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  change -u^(N+1)*(κ/4)*units-d j-2*r₂^N*C₂ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E6, f n).re at hq
  change -u^(N+1)*(κ/4)*units-d j-2*r₃^N*C₃ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E3, f n).re at ht
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hp hq ht
  change -u^(N+1)*(κ/4)*units-err₄ j ≤
    ((u : ℂ)^(N+1)*∑ n ∈ Ehi, f n).re at hbandFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hbandFloor
  have hbudget := period_grids_cost_paid (by omega : 1 ≤ N) hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-3*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j ≤
      u^(N+1)*((∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
        (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re) := by
    nlinarith only [hscaled,hp,hq,ht,hbandFloor]
  have hpaidEq := congrArg Complex.re (paid_parts E f)
  simp only [Complex.add_re] at hpaidEq
  change (∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
    (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re = (∑ n ∈ Epaid, f n).re at hpaidEq
  rw [hpaidEq] at hpaid
  have hcost : 0 ≤ u^(N+1)*(∑ n ∈ Ys, f n).re/128+3*d j+
      2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j := by
    positivity [hY.le,hd0 j,herr₄0 j]
  have hpaidMax : u^(N+1)*max (∑ n ∈ Epaid, f n).re 0-
      u^(N+1)*(∑ n ∈ Ys, f n).re/128-3*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j ≤
      u^(N+1)*(∑ n ∈ Epaid, f n).re := by
    by_cases hp : 0 ≤ (∑ n ∈ Epaid, f n).re
    · rw [max_eq_left hp]
      linarith only [hcost]
    · rw [max_eq_right (le_of_not_ge hp),mul_zero,zero_sub]
      linarith only [hpaid]
  have hDpaid := hdense
  change -u^(N+1)*unpaidCountSupplyPrice N*units-d j-2*r₅^N*C₅-3*ownerPaymentError N≤
    ((u : ℂ)^(N+1)*∑ n∈Ds,f n).re at hDpaid
  have hDbudget := hdensecost h (Real.pi/y) w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hhu hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hDbudget
  change unpaidCountSupplyPrice N*units≤(1/256 : ℝ)*(∑ n∈Ys,f n).re at hDbudget
  have hDscaled := mul_le_mul_of_nonneg_left hDbudget
    (pow_nonneg (by linarith : 0≤u) (N+1))
  have hDpaid' : -u^(N+1)*(∑ n∈Ys,f n).re/256-d j-2*r₅^N*C₅-3*ownerPaymentError N≤
      ((u : ℂ)^(N+1)*∑ n∈Ds,f n).re := by
    linarith only [hDscaled,hDpaid]
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hDpaid'
  have hBpaid := hbin
  change -u^(N+1)*intermediateSupplyPrice N*units-d j-2*r₆^N*C₆-3*ownerPaymentError N≤
    ((u : ℂ)^(N+1)*∑ n∈Bs,f n).re at hBpaid
  have hBbudget := hbincost h (Real.pi/y) w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hhu hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hBbudget
  change intermediateSupplyPrice N*units≤(1/512 : ℝ)*(∑ n∈Ys,f n).re at hBbudget
  have hBscaled := mul_le_mul_of_nonneg_left hBbudget
    (pow_nonneg (by linarith : 0≤u) (N+1))
  have hBpaid' : -u^(N+1)*(∑ n∈Ys,f n).re/512-d j-2*r₆^N*C₆-3*ownerPaymentError N≤
      ((u : ℂ)^(N+1)*∑ n∈Bs,f n).re := by
    linarith only [hBscaled,hBpaid]
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hBpaid'
  have hNewSub (T : Finset ℕ)
      (hT : T⊆S) (hcard : ∀ n∈T,56≤n.primeFactors.card)
      (hupper : ∀ n∈T,n.primeFactors.card<ZetaRieszLogCountBudget.countThreshold N) :
      T⊆E\Epaid := by
    have hsub := middle_population_subset_unpaid S T
      (N := N) (Q := Q) (P := P) (V := V) (R := R) (h := h) (L := L)
      (by omega : 1000≤N) η hh hhu w hw hT
      (by intro n hn; exact ⟨by have := hcard n hn; omega,hupper n hn⟩)
    intro n hn
    have hold := Finset.mem_sdiff.mp (hsub hn)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
      ⟨hold.1,fun hrest => hold.2 (Finset.mem_sdiff.mp hrest).1⟩,?_⟩
    intro hp
    have hc := (Finset.mem_filter.mp hp).2
    have hh := hcard n hn
    omega
  have hDsub : Ds⊆E\Epaid := hNewSub Ds
    (Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.2.2)
  have hBsub₀ : Bs⊆E\Epaid := hNewSub Bs
    (Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.2.2)
  have hBsub : Bs⊆(E\Epaid)\Ds := by
    intro n hn
    refine Finset.mem_sdiff.mpr ⟨hBsub₀ hn,?_⟩
    intro hd
    have hlo := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.2.1.1
    have hhi := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2.2.2.1
    exact (not_lt_of_ge hhi) hlo
  have hBs := congrArg Complex.re (Finset.sum_sdiff hBsub (f := f))
  change (∑ n∈Eo,f n).re+(∑ n∈Bs,f n).re=(∑ n∈(E\Epaid)\Ds,f n).re at hBs
  have hDs := congrArg Complex.re (Finset.sum_sdiff hDsub (f := f))
  change (∑ n∈(E\Epaid)\Ds,f n).re+(∑ n∈Ds,f n).re=(∑ n∈E\Epaid,f n).re at hDs
  rw [← hBs] at hDs
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset
      (Finset.Subset.trans Finset.sdiff_subset
        (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)))
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
      n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)) E)
      (f := f))
  change (∑ n ∈ E\Epaid, f n).re+(∑ n ∈ Epaid, f n).re = (∑ n ∈ E, f n).re at hs
  rw [← hDs] at hs
  let credits := max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0
  let B := wholeTail S N R
  change u^(N+1)*((∑ n ∈ S\(Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B), f n).re+
    max (∑ n ∈ Zs, f n).re 0+max (∑ n ∈ Hs, f n).re 0+
    max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+
    max (∑ n ∈ Ts, f n).re 0+(33/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hSpent := tripleRestSpent_eq (Q := Q) (P := P) (V := V) (R := R) (L := L)
    S η (by omega : 1000 ≤ N) hh hhu w hw
  change tripleRestSpent S N Q P V R η h L w = Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B at hSpent
  rw [←hSpent] at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(33/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
    convert hcore using 1
    dsimp only [credits]
    ring
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(W+G+credits+max (∑ n ∈ Epaid, f n).re 0+(257/512 : ℝ)*(∑ n ∈ Ys, f n).re)-
      (r₀^N*C₀+e j+5*d j+2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+
        2*r₅^N*C₅+2*r₆^N*C₆+6*ownerPaymentError N) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaidMax,hDpaid',hBpaid',hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring



/-- Exhaustive original configurations AFTER the merged global payment.
Only count four, or the many-bin lower growing band beginning at56,
can remain squarefree. Fixed counts are not counted as fresh obstacles. -/
theorem remaining_configuration_cases (u : ℝ) (N K Q P V R : ℕ) (η h L : ℝ)
    (w : ℕ→ℝ) {n : ℕ}
    (hn : n∈
      ((((coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w)\
        (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w).filter
          (fun n => n.primeFactors.card=3 ∨ n.primeFactors.card=5 ∨
            n.primeFactors.card=6 ∨ (7≤n.primeFactors.card ∧ n.primeFactors.card≤55)))\
        dense56Band u N K)\bin56Band u N K)) (hs : Squarefree n) :
    n.primeFactors.card=4 ∨
      (56≤n.primeFactors.card ∧
        (n.primeFactors.card : ℝ)<5*log ((N : ℝ)+1)+2 ∧
        ⌊log ((N : ℝ)+1)/16⌋₊<(cofactorBins N (n/largestPrime n)).card) := by
  obtain ⟨hn,hnotbin⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hn,hnotdense⟩ := Finset.mem_sdiff.mp hn
  rcases ZetaRieszHighSignCoverFloor.remaining_count_cases η h L w hn with h4|hhigh
  · exact Or.inl h4
  · have hE := (Finset.mem_sdiff.mp hn).1
    have hcore := (Finset.mem_sdiff.mp hE).1
    have hnotTriples : n∉radialTriples (coreBand u N K) N η := by
      intro ht
      obtain ⟨M,_,hm⟩ := Finset.mem_biUnion.mp ht
      have hc3 := (Finset.mem_filter.mp hm).2.2.1
      omega
    have hOldE : n∈coreBand u N K\spent (coreBand u N K) N Q P V R η h L w :=
      Finset.mem_sdiff.mpr ⟨hcore,fun hspent => (Finset.mem_sdiff.mp hE).2
        (Finset.mem_sdiff.mpr ⟨hspent,hnotTriples⟩)⟩
    have hupper := unpaid_count_lt _ N Q P V R η h L w hOldE hs
    have hlow : (n.primeFactors.card : ℝ)<5*log ((N : ℝ)+1)+2 := by
      by_contra hb
      exact hnotdense (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨hcore,hs,by omega,le_of_not_gt hb,hupper⟩,hhigh⟩)
    refine Or.inr ⟨hhigh,hlow,?_⟩
    by_contra hb
    exact hnotbin (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hcore,hs,by omega,⟨hlow,le_of_not_gt hb⟩,hupper⟩,hhigh⟩)

end RiemannGaussian.ZetaRieszJoinedPopulationFloor
