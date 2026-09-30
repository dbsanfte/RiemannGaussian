/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPositiveFloor

set_option autoImplicit false

/-!
# Signed four-prime periods away from the supply's smallest-prime boundary

The old supply contains no prime with logarithm at most 2N/5. A complete
largest-prime period whose fixed cofactor contains such a prime is therefore
disjoint from that supply. All original allocation and phase factors remain.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszFourSmallFloor
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

/-- The small-prime condition used to avoid the original four-prime supply. -/
def SmallPrime (N n : ℕ) : Prop :=
  ∃ q ∈ n.primeFactors, Real.log q ≤ 2*(N : ℝ)/5

/-- Original rough cofactors with a supply-excluding small prime. -/
def roughCofactors (N B : ℕ) (v : ℝ) : Finset ℕ :=
  (ZetaRieszFourPositiveFloor.roughCofactors B v).filter (SmallPrime N)

/-- Complete phase periods: the small-prime condition is fixed on the cofactor. -/
def roughPeriod (N B : ℕ) (v y : ℝ) : Finset ℕ :=
  (roughCofactors N B v).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))

private theorem cofactor_subset (N B : ℕ) (v : ℝ) :
    roughCofactors N B v ⊆ cofactors 3 v :=
  Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- A strictly larger owner cannot create the least-prime condition. -/
theorem smallPrime_mul_iff {N a p : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card = 3) (hp : p.Prime)
    (howner : ∀ q ∈ a.primeFactors, q < p) :
    SmallPrime N (a*p) ↔ SmallPrime N a := by
  have hpf : (a*p).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul ha.ne_zero hp.ne_zero,hp.primeFactors,
      Finset.union_singleton]
  constructor
  · rintro ⟨q,hq,hsmall⟩
    rw [hpf] at hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < a.primeFactors.card by omega)
      refine ⟨r,hr,?_⟩
      exact (Real.log_le_log
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
        (by exact_mod_cast (howner r hr).le)).trans hsmall
    · exact ⟨q,hq,hsmall⟩
  · rintro ⟨q,hq,hsmall⟩
    exact ⟨q,by rw [hpf]; exact Finset.mem_insert_of_mem hq,hsmall⟩

theorem roughPeriod_data {N B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod N B v y) :
    Squarefree n ∧ n.primeFactors.card = 4 ∧
      (∀ r ∈ n.primeFactors, B < r) ∧ SmallPrime N n := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hsmall⟩ := Finset.mem_filter.mp ha
  have hold : a*p ∈ ZetaRieszFourPositiveFloor.roughPeriod B v y :=
    Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  have hd := ZetaRieszFourPositiveFloor.roughPeriod_data hv hy hold
  refine ⟨hd.1,hd.2.1,hd.2.2,?_⟩
  have hg := fibre_geometry hv (by rwa [abs_of_pos (by linarith : 0 < y)])
    (Finset.mem_filter.mp ha).1
    (by simpa only [abs_of_pos (by linarith : 0 < y)] using hp)
  have hac := cofactor_data (Finset.mem_filter.mp ha).1
  exact (smallPrime_mul_iff hac.1 hac.2.1 hg.1 hg.2.1).mpr hsmall

/-- The original supply avoids every prime below exp(2N/5). This is
sharper than the earlier N/5 roughness check and follows from its literal boxes. -/
theorem supply_prime_log_gt {N n : ℕ} {h : ℝ}
    (hN : 2000 ≤ N) (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hn : n ∈ radialSupply N h w) :
    ∀ q ∈ n.primeFactors, 2*(N : ℝ)/5 < Real.log q := by
  obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
  have hb := (Finset.mem_filter.mp hM).2
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hwM : h+w M ≤ (M : ℝ)/1000 := by linarith [(hw M hM).2]
  obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  intro q hq
  rw [tuple_primeFactors hh hi hj hk (hw M hM).1 hwM hp] at hq
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
  have hs := start_bounds hh hi hj hk (hw M hM).1 hwM a
  have ht := (tuple_bounds hp a).2.1
  linarith [hs.1,hb.1]

/-- Neither the rough small-four head nor the supply intersects these periods. -/
theorem rough_small_not_spent (S : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 2000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hc : n.primeFactors.card = 4) (hrough : ∀ r ∈ n.primeFactors, Q < r)
    (hsmall : SmallPrime N n) : n ∉ spent S N Q P V R η h L w := by
  intro hn
  have hX : n ∉ radialTriples S N η := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hZ : n ∉ (radialIndices N).biUnion
      (fun M => smallTriples (S\radialTriples S N η) M Q) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hH : n ∉ (radialIndices N).biUnion (fun M => smallFours S M Q) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨r,hr,hrQ⟩ := (Finset.mem_filter.mp hn).2.2.2.2.2.2
    exact (not_lt_of_ge hrQ) (hrough r hr)
  have hF : n ∉ (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hG : n ∉ radialHeads S N P V L := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.2.2
    rcases hm with ⟨h6,_⟩ | ⟨h5,_⟩ <;> omega
  have hT : n ∉ ZetaRieszSevenCountTail.radialTail S N R := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N)
      (Finset.mem_filter.mp hn).2.2.2.2
    omega
  have hC : n ∉ ZetaRieszSevenCountTail.wholeTail S N R := by
    intro hn
    have hm := ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N)
      (Finset.mem_filter.mp hn).2.2
    omega
  have hY : n ∈ radialSupply N h w := by
    simp only [spent,Finset.mem_union] at hn
    tauto
  obtain ⟨q,hq,hqsmall⟩ := hsmall
  have hqbig := supply_prime_log_gt hN hh hhu w hw hY q hq
  exact (not_lt_of_ge hqsmall) hqbig

theorem eventually_roughPeriod_part_floor {e u y ε : ℝ} (he : |e| = 1)
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (v : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      Real.sin (y*v) = 0 → e*Real.cos (y*v) ≤ 0 →
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        ∑ n ∈ roughPeriod N B v y, signedPart e
          (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) y N n := by
  filter_upwards [ZetaRieszTransitionFiveFloor.eventually_core_part_floor
    (k := 3) (by norm_num) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors N B v) hlo hhi (cofactor_subset N B v) hpeak hsign

/-- The cofactor selection is exactly the literal label selection; no
prime period is clipped by imposing the small-prime condition. -/
theorem roughPeriod_eq_filter (N B : ℕ) {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y) :
    roughPeriod N B v y =
      (ZetaRieszFourPositiveFloor.roughPeriod B v y).filter (SmallPrime N) := by
  ext n
  constructor
  · intro hn
    obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
    have ha' := (Finset.mem_filter.mp ha).1
    have horig : n ∈ ZetaRieszFourPositiveFloor.roughPeriod B v y :=
      Finset.mem_biUnion.mpr ⟨a,ha',hn⟩
    have hd := roughPeriod_data hv hy (Finset.mem_biUnion.mpr ⟨a,ha,hn⟩)
    exact Finset.mem_filter.mpr ⟨horig,hd.2.2.2⟩
  · rintro hn
    obtain ⟨hn,hsmall⟩ := Finset.mem_filter.mp hn
    obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hac := cofactor_data (Finset.mem_filter.mp ha).1
    have hg := fibre_geometry hv (by rwa [abs_of_pos (by linarith : 0 < y)])
      (Finset.mem_filter.mp ha).1
      (by simpa only [abs_of_pos (by linarith : 0 < y)] using hp)
    have hsma := (smallPrime_mul_iff hac.1 hac.2.1 hg.1 hg.2.1).mp hsmall
    exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hsma⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

private theorem one_cover_floor (E I : Finset ℕ) (C : ℕ → Finset ℕ)
    (g : ℕ → ℝ) (cost : ℕ → ℝ)
    (hC : ∀ i ∈ I, C i ⊆ E)
    (hd : ∀ i ∈ I, ∀ l ∈ I, i ≠ l → Disjoint (C i) (C l))
    (hp : ∀ i ∈ I, -cost i ≤ ∑ n ∈ C i, g n) :
    (∑ n ∈ E\I.biUnion C, g n)-(∑ i ∈ I, cost i) ≤ ∑ n ∈ E, g n := by
  have hsub : I.biUnion C ⊆ E := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    exact hC i hi hn
  have hs := Finset.sum_sdiff hsub (f := g)
  rw [Finset.sum_biUnion hd] at hs
  have hb := Finset.sum_le_sum hp
  rw [Finset.sum_neg_distrib] at hb
  linarith only [hs,hb]

theorem eventually_unpaid_four_small_negative_cover {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ)
      (I : Finset ℕ) (v : ℝ),
      0 < h → h ≤ 1/20 →
      (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
      Real.cos (y*v) = -1 →
      (∀ i ∈ I, (39/20 : ℝ)*dyadicMomentOrder j ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
        center (v+Real.pi/y) y i+Real.pi/y ≤ (203/100 : ℝ)*dyadicMomentOrder j) →
      let N := dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (dyadicPrimeCount j)
      let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4 ∧ SmallPrime N n)
      let X := fun i => roughPeriod N Q (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart (-1) A L y N n)-
        ε*(∑ i ∈ I, Real.exp (-center (v+Real.pi/y) y i/2)*(center (v+Real.pi/y) y i)^N/N.factorial) ≤
        ∑ n ∈ E, signedPart (-1) A L y N n := by
  have hy0 : 0 < y := by linarith
  have hpi : 0 ≤ Real.pi/y := by positivity
  have hstep : 0 ≤ 2*Real.pi/y := by positivity
  have hsep (b : ℝ) {i l : ℕ} (hil : i < l) :
      center b y i+Real.pi/y ≤ center b y l-Real.pi/y := by
    have hh : (i : ℝ)+1 ≤ l := by exact_mod_cast hil
    have hm := mul_le_mul_of_nonneg_right hh hstep
    dsimp only [center]
    rw [abs_of_pos hy0]
    ring_nf at hm ⊢
    linarith only [hm]
  have hroom : u < Real.exp (-(11/16 : ℝ)) :=
    hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [tendsto_dyadicMomentOrder.eventually
      (eventually_roughPeriod_part_floor (e := -1) (by norm_num) hu hU hy hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hpos hL hlarge hj Q P V R η h w I v hh hhu hw hpeak hI
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4 ∧ SmallPrime N n)
  let X := fun i => roughPeriod N Q (center (v+Real.pi/y) y i) y
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hcount : 3+1 < dyadicPrimeCount j := by
    dsimp [dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ} (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod N Q c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    have hcore : roughPeriod N Q c y ⊆ S :=
      owned_subset_core (k := 3) (by norm_num) j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        hlo hhi (roughCofactors N Q c) (cofactor_subset N Q c)
    intro n hn
    have hd := roughPeriod_data hc hy hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hcore hn,
      rough_small_not_spent S hlarge η hh hhu w hw hd.2.1 hd.2.2.1 hd.2.2.2⟩,
      hd.2.1,hd.2.2.2⟩

  have hvI i (hi : i ∈ I) : 100 ≤ center (v+Real.pi/y) y i := by linarith only [hNR,hpi,(hI i hi).1]
  have hdisjoint (b : ℝ) {i l : ℕ} (hil : i ≠ l)
      (hi : 100 ≤ center b y i) (hl : 100 ≤ center b y l) :
      Disjoint (roughPeriod N Q (center b y i) y) (roughPeriod N Q (center b y l) y) := by
    rcases lt_or_gt_of_ne hil with h | h
    · exact ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hi hl hy _ _
        (cofactor_subset N Q _) (cofactor_subset N Q _) (hsep b h)
    · exact (ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hl hi hy _ _
        (cofactor_subset N Q _) (cofactor_subset N Q _) (hsep b h)).symm
  have hb := one_cover_floor E I X (signedPart (-1) A L y N)
    (fun i => ε*(Real.exp (-center (v+Real.pi/y) y i/2)*
      (center (v+Real.pi/y) y i)^N/N.factorial))
    (fun i hi => howned (hI i hi).1 (hI i hi).2)
    (fun i hi l hl hil => hdisjoint (v+Real.pi/y) hil (hvI i hi) (hvI l hl))
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).2
      simpa only [neg_mul] using hpos Q _ (hI i hi).1 (hI i hi).2 hp.1
        (by rw [hp.2]; norm_num))
  simpa only [← Finset.mul_sum] using hb

private theorem positive_part_sum_eq (A D : Finset ℕ) (L y : ℝ) (N : ℕ) :
    ∑ n ∈ D, signedPart 1 A L y N n =
      (∑ n ∈ D.filter (fun n => 0 < (SquarefreeVaughanLogSource.coefficient L n).re),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : 0 < (SquarefreeVaughanLogSource.coefficient L n).re
  · rw [if_pos hp,← signedPart_add]
    have hz : signedPart (-1) A L y N n = 0 := by
      simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
        -(SquarefreeVaughanLogSource.coefficient L n).re ≤ 0),mul_zero,zero_mul]
    rw [hz,add_zero]
  · rw [if_neg hp]
    simp only [signedPart,one_mul,max_eq_right (le_of_not_gt hp),mul_zero,zero_mul]

private theorem negative_part_sum_eq (A D : Finset ℕ) (L y : ℝ) (N : ℕ) :
    ∑ n ∈ D, signedPart (-1) A L y N n =
      (∑ n ∈ D.filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re < 0),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [Complex.re_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : (SquarefreeVaughanLogSource.coefficient L n).re < 0
  · rw [if_pos hp,← signedPart_add]
    have hz : signedPart 1 A L y N n = 0 := by
      simp only [signedPart,one_mul,max_eq_right hp.le,mul_zero,zero_mul]
    rw [hz,zero_add]
  · rw [if_neg hp]
    simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
      -(SquarefreeVaughanLogSource.coefficient L n).re ≤ 0),mul_zero,zero_mul]

private theorem paid_subset_parts_floor (A D X Y : Finset ℕ) (L y u : ℝ) (N : ℕ)
    {B : ℝ}
    (hB : ∀ F ⊆ D, ‖(u : ℂ)^(N+1)*∑ n ∈ F,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ B) :
    -2*B ≤ u^(N+1)*((∑ n ∈ D\X, signedPart 1 A L y N n)+
      (∑ n ∈ D\Y, signedPart (-1) A L y N n)) := by
  let F := (D\X).filter (fun n => 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
  let G := (D\Y).filter (fun n => (SquarefreeVaughanLogSource.coefficient L n).re < 0)
  have hp := hB F (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset)
  have hn := hB G (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset)
  have hpre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hp)).1
  have hnre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hpre hnre
  rw [positive_part_sum_eq,negative_part_sum_eq]
  change -2*B ≤ u^(N+1)*(_+_)
  linarith only [hpre,hnre]

private theorem unmatched_three_split (S D F T X : Finset ℕ) (f : ℕ → ℝ)
    (hD : D ⊆ S) (hF : F ⊆ S\D) (hT : T ⊆ (S\D)\F)
    (hz : ∀ n ∈ ((S\D)\F)\T, f n = 0 ∨ n ∈ X) :
    (∑ n ∈ S\X, f n) = (∑ n ∈ D\X, f n)+
      (∑ n ∈ F\X, f n)+(∑ n ∈ T\X, f n) := by
  have h₁ := ZetaRieszOwnerTieFloor.missed_boundary_split S D X hD f
  have h₂ := ZetaRieszOwnerTieFloor.missed_boundary_split (S\D) F X hF f
  have h₃ := ZetaRieszOwnerTieFloor.missed_boundary_split ((S\D)\F) T X hT f
  have he₁ : S\(X ∪ D) = (S\D)\X := by
    ext n; simp only [Finset.mem_sdiff,Finset.mem_union]; tauto
  have he₂ : (S\D)\(X ∪ F) = ((S\D)\F)\X := by
    ext n; simp only [Finset.mem_sdiff,Finset.mem_union]; tauto
  have he₃ : ((S\D)\F)\(X ∪ T) = (((S\D)\F)\T)\X := by
    ext n; simp only [Finset.mem_sdiff,Finset.mem_union]; tauto
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃] at h₃
  have hzero : (∑ n ∈ (((S\D)\F)\T)\X, f n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hn,hnot⟩ := Finset.mem_sdiff.mp hn
    exact (hz n hn).resolve_right hnot
  rw [hzero,zero_add] at h₃
  linarith only [h₁,h₂,h₃]

/-- Every unpaid negative-coefficient four-prime label containing a
prime with log at most 2N/5 has an arbitrarily small signed period debit.
The original supply is untouched; close owners and exterior errors are paid. -/
theorem exists_unpaid_four_small_negative_floor {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ),
        0 < h → h ≤ 1/20 →
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4 ∧ SmallPrime N n)
        let I := completeGrid N (Real.pi/y) y
        let J := completeGrid N (Real.pi/y+Real.pi/y) y;
        -u^(N+1)*ε*((∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*
          (center (Real.pi/y) y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
            (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial))-
          4*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)-
          2*r^N*C ≤
            ((u : ℂ)^(N+1)*∑ n ∈ E.filter (fun n =>
              (SquarefreeVaughanLogSource.coefficient L n).re < 0),
              residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r,C,hr,hr1,hC,houter⟩ := exists_outer_subset_bound
  refine ⟨r,C,hr,hr1,hC,?_⟩
  have hy0 : 0 < y := by linarith
  have hπ : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hpeak : Real.cos (y*(Real.pi/y)) = -1 := by
    rw [mul_div_cancel₀ _ hy0.ne',Real.cos_pi]
  filter_upwards [eventually_unpaid_four_small_negative_cover hu hU hy (half_pos hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszOwnerTieFloor.eventually_core_grouped_tie_floor hu hU (half_pos hε)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hperiod htie hN hj Q P V R η h w hh hhu hw
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4 ∧ SmallPrime N n)
  let dom := fun n : ℕ => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
      (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let D := E.filter dom
  let F := (E\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N < Real.log n ∧
    Real.log n ≤ (2029/1000 : ℝ)*N))
  let T := ((E\D)\F).filter (fun n => Squarefree n ∧ ZetaRieszOwnerTieFloor.CloseOwners n)
  let I := completeGrid N (Real.pi/y) y
  let J := completeGrid N (Real.pi/y+Real.pi/y) y
  let X := E
  let Y := J.biUnion (fun i => roughPeriod N Q (center (Real.pi/y+Real.pi/y) y i) y)
  let units₁ := ∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial
  let units₂ := ∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
    (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial
  have units₁pos : 0 ≤ units₁ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
    have hc : 0 ≤ center (Real.pi/y) y i := by linarith only [hg,hπ.le,hNR]
    positivity)
  have hper := hperiod Q P V R η h w J (Real.pi/y) hh hhu hw hpeak
    (fun _ hi => ⟨(Finset.mem_filter.mp hi).2.1,(Finset.mem_filter.mp hi).2.2.1⟩)
  change (∑ n ∈ E\Y, signedPart (-1) A L y N n)-(ε/2)*units₂ ≤
    ∑ n ∈ E, signedPart (-1) A L y N n at hper
  have hNReal : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hFgeo (n : ℕ) (hn : n ∈ (E\D)\F) :
      (244/125 : ℝ)*N < Real.log n ∧ Real.log n ≤ (2029/1000 : ℝ)*N := by
    obtain ⟨hne,hnot⟩ := Finset.mem_sdiff.mp hn
    by_contra hgeo
    exact hnot (Finset.mem_filter.mpr ⟨hne,hgeo⟩)
  have hgood n (hn : n ∈ (((E\D)\F)\T)) :
      (signedPart 1 A L y N n = 0 ∨ n ∈ X) ∧
      (signedPart (-1) A L y N n = 0 ∨ n ∈ Y) := by
    obtain ⟨hnEF,hnotT⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnED,_⟩ := Finset.mem_sdiff.mp hnEF
    obtain ⟨hnE,hnotD⟩ := Finset.mem_sdiff.mp hnED
    obtain ⟨hnUn,hc,hsmall⟩ := Finset.mem_filter.mp hnE
    obtain ⟨hnS,hnot⟩ := Finset.mem_sdiff.mp hnUn
    have hnotdom : ¬dom n := fun hh => hnotD (Finset.mem_filter.mpr ⟨hnE,hh⟩)
    let hres := residualCoefficient A L N n
    by_cases hz : hres = 0
    · change residualCoefficient A L N n = 0 at hz
      have hhzero : signedPart 1 A L y N n = 0 ∧ signedPart (-1) A L y N n = 0 := by
        have hb := ZetaRieszOwnerTieFloor.signedParts_abs_eq A L y N n
        rw [hz,zero_mul,Complex.zero_re,abs_zero] at hb
        constructor <;> apply abs_eq_zero.mp <;> linarith [abs_nonneg (signedPart 1 A L y N n), abs_nonneg (signedPart (-1) A L y N n)]
      exact ⟨Or.inl hhzero.1,Or.inl hhzero.2⟩
    have hs : Squarefree n := by
      by_contra hs
      apply hz
      simp [hres,residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs]
    have hnotTie : ¬ZetaRieszOwnerTieFloor.CloseOwners n :=
      fun hclose => hnotT (Finset.mem_filter.mpr ⟨hnEF,hs,hclose⟩)
    refine ⟨Or.inr hnE,?_⟩
    have hold := (ZetaRieszFourPositiveFloor.interior_parts_covered j hj u hy η h w hN
      (Finset.mem_filter.mpr ⟨hnS,hnotdom⟩) hnot hc (hFgeo n hnEF).1
        (hFgeo n hnEF).2 hnotTie).2
    rcases hold with hz | hmem
    · exact Or.inl hz
    · obtain ⟨i,hi,hnper⟩ := Finset.mem_biUnion.mp hmem
      have hv : 100 ≤ center (Real.pi/y+Real.pi/y) y i := by
        have hb := (Finset.mem_filter.mp hi).2.1
        linarith only [hb,hπ.le,hNReal]
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨i,hi,?_⟩
      rw [roughPeriod_eq_filter N Q hv hy]
      exact Finset.mem_filter.mpr ⟨hnper,hsmall⟩

  have he₁ := unmatched_three_split E D F T X (signedPart 1 A L y N)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (fun n hn => (hgood n hn).1)
  have he₂ := unmatched_three_split E D F T Y (signedPart (-1) A L y N)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (fun n hn => (hgood n hn).2)
  have hLhi : L ≤ (139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le (by omega : 2 ≤ N)
    have hlog : 2*Real.log 2 ≤ (139/100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hDpay := paid_subset_parts_floor A D X Y L y u N (by
    intro G hG
    apply ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A G N (by omega) y
      (by linarith : 0 ≤ u) hU (SquarefreeVaughanLogSource.length_pos u N) hLhi
    intro n hnG
    obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp (hG hnG)
    refine ⟨hs,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
    have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
    have hlogcut : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) = L := by
      simp only [L,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    change Real.log p ≤ L
    rw [← hlogcut]
    exact (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  have hFpay := paid_subset_parts_floor A F X Y L y u N (by
    intro G hG
    exact houter N A G y u (by linarith : 0 ≤ u) hU
      (fun n hn => (Finset.mem_filter.mp (hG hn)).2))
  let B := fun i => T.filter (fun n : ℕ => center (Real.pi/y) y i-Real.pi/y < Real.log n ∧
    Real.log n ≤ center (Real.pi/y) y i+Real.pi/y)
  have hcover : T ⊆ I.biUnion B := by
    intro n hn
    have hg := hFgeo n (Finset.mem_filter.mp hn).1
    obtain ⟨i,hi,hp⟩ := exists_completeGrid_period hN hy
      ⟨le_rfl,by calc
        Real.pi/y ≤ Real.pi/y+Real.pi/y := le_add_of_nonneg_right hπ.le
        _ = 2*Real.pi/y := by ring⟩ hg.1 hg.2
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hn,hp⟩⟩
  have hTpay := htie y T X Y I B (center (Real.pi/y) y) hcover
    (by
      intro i hi
      have hd := (Finset.mem_filter.mp hi).2
      constructor <;> linarith only [hd.1,hd.2.1,hπ.le])
    (by
      intro i hi n hn
      obtain ⟨hnT,hlo,hhi⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnEF,hs,hclose⟩ := Finset.mem_filter.mp hnT
      have hc := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hnEF).1).1).2
      exact ⟨hs,by omega,by omega,⟨by linarith only [hlo,hπu],
        by linarith only [hhi,hπu]⟩,hclose⟩)
  change -(ε/2)*units₁ ≤ (∑ n ∈ T\X, signedPart 1 A L y N n)+
    (∑ n ∈ T\Y, signedPart (-1) A L y N n) at hTpay
  have hTscaled := mul_le_mul_of_nonneg_left hTpay
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hPscaled := mul_le_mul_of_nonneg_left hper
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  dsimp only
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← negative_part_sum_eq]
  change _ ≤ u^(N+1)*(∑ n ∈ E, signedPart (-1) A L y N n)
  have hxempty : E\X = ∅ := Finset.sdiff_self E
  rw [hxempty,Finset.sum_empty] at he₁
  have hunits₂ : 0 ≤ units₂ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hc : 0 ≤ center (Real.pi/y+Real.pi/y) y i := by linarith only [hg,hπ.le,hNReal]
    positivity)
  have hscale := pow_nonneg (by linarith : 0 ≤ u) (N+1)
  have hslack : 0 ≤ u^(N+1)*(ε/2)*(units₁+units₂) :=
    mul_nonneg (mul_nonneg hscale (half_pos hε).le) (add_nonneg units₁pos hunits₂)
  have hs₁ := congrArg (fun x : ℝ => u^(N+1)*x) he₁
  have hs₂ := congrArg (fun x : ℝ => u^(N+1)*x) he₂
  change -u^(N+1)*ε*(units₁+units₂)-
    4*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)-
    2*r^N*C ≤ u^(N+1)*(∑ n ∈ E, signedPart (-1) A L y N n)
  nlinarith only [hDpay,hFpay,hTscaled,hPscaled,hs₁,hs₂,hslack]



/-- Exactly the union of the two disjoint four-prime parts already paid. -/
def PaidFour (N : ℕ) (L : ℝ) (n : ℕ) : Prop :=
  0 < (SquarefreeVaughanLogSource.coefficient L n).re ∨
    ((SquarefreeVaughanLogSource.coefficient L n).re < 0 ∧ SmallPrime N n)

private theorem paidFour_sum (E : Finset ℕ) (f : ℕ → ℂ) (N : ℕ) (L : ℝ) :
    (∑ n ∈ E.filter (fun n => 0 < (SquarefreeVaughanLogSource.coefficient L n).re), f n)+
    (∑ n ∈ (E.filter (SmallPrime N)).filter
      (fun n => (SquarefreeVaughanLogSource.coefficient L n).re < 0), f n) =
    ∑ n ∈ E.filter (PaidFour N L), f n := by
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : 0 < (SquarefreeVaughanLogSource.coefficient L n).re
  · have hn := not_lt_of_ge hp.le
    simp [PaidFour,hp,hn]
  · by_cases hn : (SquarefreeVaughanLogSource.coefficient L n).re < 0
    · by_cases hs : SmallPrime N n <;> simp [PaidFour,hp,hn,hs]
    · simp [PaidFour,hp,hn]

/-- The two paid four-prime parts share one arbitrary radial debit. -/
theorem exists_unpaid_four_away_supply_floor {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ),
        0 < h → h ≤ 1/20 →
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4)
        let I := completeGrid N (Real.pi/y) y
        let J := completeGrid N (Real.pi/y+Real.pi/y) y;
        -u^(N+1)*ε*((∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*
          (center (Real.pi/y) y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
            (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial))-
          8*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)-
          2*r^N*C ≤
            ((u : ℂ)^(N+1)*∑ n ∈ E.filter (PaidFour N L),
              residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hpos⟩ :=
    ZetaRieszFourPositiveFloor.exists_unpaid_four_positive_floor hu hU hy (half_pos hε)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hneg⟩ :=
    exists_unpaid_four_small_negative_floor hu hU hy (half_pos hε)
  refine ⟨max r₁ r₂,C₁+C₂,le_trans hr₁ (le_max_left _ _),
    max_lt hr₁1 hr₂1,add_nonneg hC₁ hC₂,?_⟩
  filter_upwards [hpos,hneg] with j hp hn Q P V R η h w hh hhu hw
  specialize hp Q P V R η h w hh hhu hw
  specialize hn Q P V R η h w hh hhu hw
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hset : (S\spent S N Q P V R η h L w).filter
      (fun n => n.primeFactors.card = 4 ∧ SmallPrime N n) = E.filter (SmallPrime N) := by
    simp only [E,Finset.filter_filter]
  dsimp only at hp hn ⊢
  change _ ≤ ((u : ℂ)^(N+1)*∑ n ∈ ((S\spent S N Q P V R η h L w).filter
    (fun n => n.primeFactors.card = 4 ∧ SmallPrime N n)).filter
      (fun n => (SquarefreeVaughanLogSource.coefficient L n).re < 0), f n).re at hn
  rw [hset] at hn
  have hsum := congrArg (fun x : ℂ => ((u : ℂ)^(N+1)*x).re) (paidFour_sum E f N L)
  rw [mul_add,Complex.add_re] at hsum
  have ht₁ := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hr₁ (le_max_left r₁ r₂) N) hC₁
  have ht₂ := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hr₂ (le_max_right r₁ r₂) N) hC₂
  nlinarith only [hp,hn,hsum,ht₁,ht₂]

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

open ZetaRieszThreeSignCoverFloor (tripleRestSpent nontriple_rest_filter_eq
  tripleRestSpent_eq eventually_core_full_floor_with_triples_rejoined)

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h


open ZetaRieszHighSignCoverFloor (high_rest_filter_eq exists_unpaid_band_floor)

set_option maxHeartbeats 1600000 in
/-- The whole floor pays all counts 3,5,6,7..55, every positive four-prime
coefficient and every negative four-prime coefficient containing a prime
with log at most 2N/5. The SAME supply credit 65/128 remains. Only balanced
negative fours and growing counts remain, apart from zero atoms.
This is a funded signed bound, not the final numerical floor. -/
theorem eventually_joined_floor_with_balanced_fours {u y : ℝ} (hu : 1/2 < u)
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
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n))
        let Eo := E\Epaid
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
            max (∑ n ∈ Epaid, f n).re 0+(65/128 : ℝ)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r₀,C₀,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ := eventually_core_full_floor_with_triples_rejoined hu hU hy
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩  :=
    ZetaRieszFiveSignCoverFloor.exists_unpaid_five_floor hu hU hy (by positivity : 0 < κ/5)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hsix⟩ := ZetaRieszSixSignCoverFloor.exists_unpaid_six_floor hu hU hy (by positivity : 0 < κ/5)
  obtain ⟨r₃,C₃,hr₃,hr₃1,hC₃,hthree⟩ := ZetaRieszThreeSignCoverFloor.exists_unpaid_three_floor hu hU hy
    (by positivity : 0 < κ/5)
  obtain ⟨err₄,herr₄0,herr₄,hhigh⟩ := exists_unpaid_band_floor hu hU hy
    (by positivity : 0 < κ/5)
  obtain ⟨r₅,C₅,hr₅,hr₅1,hC₅,hfour⟩ := exists_unpaid_four_away_supply_floor hu hU hy
    (by positivity : 0 < κ/5)
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
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j,herr₄0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hsix,hthree,hhigh,hfour,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
      with j hj hfive hsix hthree hhigh hfour hbound hN
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
  change -u^(N+1)*(κ/5)*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  change -u^(N+1)*(κ/5)*units-d j-2*r₂^N*C₂ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E6, f n).re at hq
  change -u^(N+1)*(κ/5)*units-d j-2*r₃^N*C₃ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E3, f n).re at ht
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hp hq ht
  change -u^(N+1)*(κ/5)*units-err₄ j ≤
    ((u : ℂ)^(N+1)*∑ n ∈ Ehi, f n).re at hbandFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hbandFloor
  rw [show 8*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(dyadicMomentOrder j : ℝ)/1000000) = 2*d j by dsimp [d]; ring]
    at hfourFloor
  change -u^(N+1)*(κ/5)*units-2*d j-2*r₅^N*C₅ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E4p, f n).re at hfourFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hfourFloor
  have hbudget := period_grids_cost_paid (by omega : 1 ≤ N) hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-5*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j-2*r₅^N*C₅ ≤
      u^(N+1)*((∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
        (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re) := by
    nlinarith only [hscaled,hp,hq,ht,hbandFloor,hfourFloor]
  have hpaidEq := congrArg Complex.re (paid_parts E f N L)
  simp only [Complex.add_re] at hpaidEq
  change (∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
    (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re = (∑ n ∈ Epaid, f n).re at hpaidEq
  rw [hpaidEq] at hpaid
  have hcost : 0 ≤ u^(N+1)*(∑ n ∈ Ys, f n).re/128+5*d j+
      2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅ := by
    positivity [hY.le,hd0 j,herr₄0 j]
  have hpaidMax : u^(N+1)*max (∑ n ∈ Epaid, f n).re 0-
      u^(N+1)*(∑ n ∈ Ys, f n).re/128-5*d j-
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
  have hfinal : u^(N+1)*(W+G+credits+max (∑ n ∈ Epaid, f n).re 0+(65/128 : ℝ)*(∑ n ∈ Ys, f n).re)-
      (r₀^N*C₀+e j+5*d j+2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaidMax,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring




/-- Zero arithmetic real coefficient is an exactly zero literal atom. -/
theorem atom_zero_of_coefficient_re (A : Finset ℕ) (L y : ℝ) (N n : ℕ)
    (hzero : (SquarefreeVaughanLogSource.coefficient L n).re = 0) :
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n = 0 := by
  have hz : SquarefreeVaughanLogSource.coefficient L n = 0 :=
    Complex.ext hzero (ZetaRieszCosineCarrier.coefficient_im_eq_zero L n)
  simp only [residualCoefficient,hz,mul_zero,zero_mul]

/-- Every nonzero remaining low-count atom is negative in arithmetic sign
and has all four prime logarithms greater than 2N/5. -/
theorem remaining_effective_geometry {u : ℝ} {N K Q P V R n : ℕ}
    (A : Finset ℕ) (η h L y : ℝ) (w : ℕ → ℝ)
    (hn : n ∈ (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w)\
      (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w).filter
        (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
          n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n)))
    (hne : residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n ≠ 0) :
    (n.primeFactors.card = 4 ∧ (SquarefreeVaughanLogSource.coefficient L n).re < 0 ∧
      ∀ q ∈ n.primeFactors, 2*(N : ℝ)/5 < Real.log q) ∨
      56 ≤ n.primeFactors.card := by
  obtain ⟨hnE,hnot⟩ := Finset.mem_sdiff.mp hn
  have hncore := (Finset.mem_sdiff.mp hnE).1
  have hnar := (Finset.mem_filter.mp hncore).1
  have hnon := (Finset.mem_filter.mp hnar).1
  have hret := (Finset.mem_sdiff.mp hnon).1
  have horig := (Finset.mem_sdiff.mp hret).1
  have hcount := (Finset.mem_filter.mp (Finset.mem_filter.mp horig).1).2.1
  have hcounts : ¬(n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
      n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
      (n.primeFactors.card = 4 ∧ PaidFour N L n)) :=
    fun hc => hnot (Finset.mem_filter.mpr ⟨hnE,hc⟩)
  by_cases h4 : n.primeFactors.card = 4
  · have hnotPaid : ¬PaidFour N L n := fun hp =>
      hcounts (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4,hp⟩))))
    have hnonpos : (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0 :=
      le_of_not_gt (fun hp => hnotPaid (Or.inl hp))
    have hnzero : (SquarefreeVaughanLogSource.coefficient L n).re ≠ 0 :=
      fun hz => hne (atom_zero_of_coefficient_re A L y N n hz)
    have hneg := lt_of_le_of_ne hnonpos hnzero
    have hnotSmall : ¬SmallPrime N n := fun hs => hnotPaid (Or.inr ⟨hneg,hs⟩)
    refine Or.inl ⟨h4,hneg,?_⟩
    intro q hq
    by_contra hh
    exact hnotSmall ⟨q,hq,le_of_not_gt hh⟩
  · right
    omega

end RiemannGaussian.ZetaRieszFourSmallFloor
