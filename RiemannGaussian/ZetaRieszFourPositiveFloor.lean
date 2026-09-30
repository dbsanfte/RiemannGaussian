/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHighSignCoverFloor
import RiemannGaussian.ZetaRieszFourSupplyAudit

set_option autoImplicit false

/-!
# Paying the positive arithmetic part of the remaining four-prime sector

The original four-prime supply has negative arithmetic coefficient. Its
intersection with the positive sign part is exactly zero. Complete prime
periods therefore pay the positive four-prime part without reusing supply.
The negative arithmetic part stays in the joint floor explicitly.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszFourPositiveFloor
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

/-- Three-prime cofactors above the original small-four-prime threshold. -/
def roughCofactors (B : ℕ) (v : ℝ) : Finset ℕ :=
  (cofactors 3 v).filter (fun a => ∀ r ∈ a.primeFactors, B < r)

/-- Complete largest-prime phase periods with their literal rough cofactors. -/
def roughPeriod (B : ℕ) (v y : ℝ) : Finset ℕ :=
  (roughCofactors B v).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))

theorem roughPeriod_data {B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod B v y) :
    Squarefree n ∧ n.primeFactors.card = 4 ∧ ∀ r ∈ n.primeFactors, B < r := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hrough⟩ := Finset.mem_filter.mp ha
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hg := fibre_geometry hv (by rwa [hyabs]) ha (by simpa only [hyabs] using hp)
  have hd := cofactor_data ha
  rw [Nat.mul_comm a p]
  refine ⟨hg.2.2.1,by simpa using hg.2.2.2.1,?_⟩
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hg.1.ne_zero hd.1.ne_zero,hg.1.primeFactors,Finset.singleton_union]
  have hne : a.primeFactors.Nonempty := Finset.card_pos.mp (by rw [hd.2.1]; norm_num)
  obtain ⟨q,hq⟩ := hne
  have hpB : B < p := (hrough q hq).trans (hg.2.1 q hq)
  intro r hr
  rw [hpf] at hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact hpB
  · exact hrough r hr

/-- A rough spent four-prime label belongs to the negative arithmetic
supply, whose positive sign part is exactly zero. -/
theorem positive_part_zero_of_spent (S A : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 2000 ≤ N) (η y : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hL0 : 0 < L) (hL : ∀ M ∈ radialIndices N,
      (271/200 : ℝ)*M ≤ L ∧ L ≤ (143/100 : ℝ)*M)
    (hc : n.primeFactors.card = 4) (hrough : ∀ r ∈ n.primeFactors, Q < r)
    (hn : n ∈ spent S N Q P V R η h L w) : signedPart 1 A L y N n = 0 := by
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
  exact (ZetaRieszFourSupplyAudit.radial_supply_sign_data (y := y) A hN hh hhu w hw
    hL0 hL hY).2.2.2.1

private theorem sum_inter_unpaid_eq (S C : Finset ℕ) (g : ℕ → ℝ)
    (N Q P V R : ℕ) (η h L : ℝ) (w : ℕ → ℝ)
    (hC : C ⊆ S) (hc : ∀ n ∈ C, n.primeFactors.card = 4)
    (hzero : ∀ n ∈ C, n ∈ spent S N Q P V R η h L w → g n = 0) :
    let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4);
    (∑ n ∈ C ∩ E, g n) = ∑ n ∈ C, g n := by
  dsimp only
  apply Finset.sum_subset Finset.inter_subset_left
  intro n hn hnnot
  apply hzero n hn
  by_contra hnot
  exact hnnot (Finset.mem_inter.mpr ⟨hn,Finset.mem_filter.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hC hn,hnot⟩,hc n hn⟩⟩)

private theorem sdiff_cover_inter (E I : Finset ℕ) (C : ℕ → Finset ℕ) :
    E\I.biUnion (fun i => C i ∩ E) = E\I.biUnion C := by
  ext n
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hn,hnot⟩
    refine ⟨hn,?_⟩
    intro hm
    obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hm
    exact hnot (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_inter.mpr ⟨hm,hn⟩⟩)
  · rintro ⟨hn,hnot⟩
    refine ⟨hn,?_⟩
    intro hm
    obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hm
    exact hnot (Finset.mem_biUnion.mpr ⟨i,hi,(Finset.mem_inter.mp hm).1⟩)

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

theorem eventually_roughPeriod_part_floor {e u y ε : ℝ} (he : |e| = 1)
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (v : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      Real.sin (y*v) = 0 → e*Real.cos (y*v) ≤ 0 →
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        ∑ n ∈ roughPeriod B v y, signedPart e
          (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) y N n := by
  filter_upwards [ZetaRieszTransitionFiveFloor.eventually_core_part_floor
    (k := 3) (by norm_num) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors B v) hlo hhi (Finset.filter_subset _ _) hpeak hsign

theorem owner_gap_mem_roughPeriod {B a p : ℕ} {v y : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = 3) (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧
      Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hgap : ∀ q ∈ a.primeFactors, Real.log q ≤ Real.log p-1/8)
    (hrough : ∀ q ∈ a.primeFactors, B < q) :
    p*a ∈ roughPeriod B v y := by
  have hy0 : 0 < y := by linarith
  have hpi : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast ha.ne_zero)]
  have hla : (199/500 : ℝ)*v < Real.log a := by
    linarith only [hv,hpi,hT.1,hlo]
  have ho (q : ℕ) (hq : q ∈ a.primeFactors) :
      Real.log q ≤ v-1/16-Real.log a := by
    have hg := hgap q hq
    rw [hlog] at hT
    linarith only [hg,hpi,hT.2]
  have ham : a ∈ cofactors 3 v :=
    (mem_cofactors_iff_of_count_le (by norm_num) (by linarith)).mpr ⟨ha,hc,hla,ho⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨ham,hrough⟩,
    Finset.mem_image.mpr ⟨p,?_,Nat.mul_comm a p⟩⟩
  apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
  rw [hlog] at hT
  refine ⟨hp,by linarith only [hT.1],?_⟩
  rw [show v-Real.pi/y-Real.log a+2*Real.pi/y = v+Real.pi/y-Real.log a by ring]
  linarith only [hT.2]

private theorem four_owner_data {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) :
    let p := ZetaRieszPrimeEndpoint.largestPrime n
    let a := n/p;
    p.Prime ∧ p*a = n ∧ Squarefree a ∧ a.primeFactors.card = 3 ∧
      p ∈ n.primeFactors ∧ (∀ q ∈ n.primeFactors, q ≤ p) ∧
      p ∉ a.primeFactors := by
  dsimp only
  let p := ZetaRieszPrimeEndpoint.largestPrime n
  let a := n/p
  have hp : p ∈ n.primeFactors :=
    ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he : p*a = n := by
    dsimp [a]
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
  have hsprod : Squarefree (p*a) := he ▸ hs
  have ha := hsprod.of_mul_right
  have hnot : p ∉ a.primeFactors := by
    intro hh
    exact (hpp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsprod))
      (Nat.dvd_of_mem_primeFactors hh)
  have hpf : n.primeFactors = insert p a.primeFactors := by
    rw [← he,Nat.primeFactors_mul hpp.ne_zero ha.ne_zero,hpp.primeFactors,
      Finset.singleton_union]
  have hcard : a.primeFactors.card = 3 := by
    rw [hpf,Finset.card_insert_of_notMem hnot] at hc
    omega
  have hmax q (hq : q ∈ n.primeFactors) : q ≤ p := by
    dsimp [p,ZetaRieszPrimeEndpoint.largestPrime]
    rw [dif_pos (Finset.card_pos.mp (by omega : 0 < n.primeFactors.card))]
    exact Finset.le_max' _ q hq
  exact ⟨hpp,he,ha,hcard,hp,hmax,hnot⟩

private theorem no_close_owner_gap {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      Real.log q ≤ Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-1/8 := by
  obtain ⟨hpp,he,ha,_,hp,hmax,hnot⟩ := four_owner_data hs hc
  intro q hq
  by_contra hh
  have hqn : q ∈ n.primeFactors := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    hs.ne_zero
  apply hntie
  refine ⟨_,hp,q,hqn,?_,hmax,lt_of_not_ge hh⟩
  intro h
  exact hnot (h ▸ hq)

private theorem mem_four_head_of_geometry {S : Finset ℕ} {N n Q : ℕ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hc : n.primeFactors.card = 4)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ r ∈ n.primeFactors, Real.log r ≤ (1209/2000 : ℝ)*Real.log n)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ Q) :
    n ∈ (radialIndices N).biUnion (fun M => smallFours S M Q) := by
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : M ≤ 2*N := by
        have h' : (M : ℝ) ≤ 2*N := by linarith
        exact_mod_cast h'
      omega
    constructor <;> linarith
  have hmax' : ∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M := by
    intro p hp
    linarith [hmax p hp]
  exact Finset.mem_biUnion.mpr ⟨M,hM,Finset.mem_filter.mpr
    ⟨hnS,hs,hc,by linarith,by linarith,hmax',hsmall⟩⟩

/-- Outside the old small-four head, all retained interior factors are
above Q. The geometric cap is supplied by the paid dominant sector. -/
theorem unpaid_four_rough (S : Finset ℕ) {N n Q P V R : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) (hN : 4000 ≤ N) (hnS : n ∈ S)
    (hnot : n ∉ spent S N Q P V R η h L w) (hs : Squarefree n)
    (hc : n.primeFactors.card = 4)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ r ∈ n.primeFactors, Real.log r ≤ (1209/2000 : ℝ)*Real.log n) :
    ∀ r ∈ n.primeFactors, Q < r := by
  intro r hr
  by_contra hn
  have hH := mem_four_head_of_geometry hN hnS hs hc hlo hhi hmax
    ⟨r,hr,le_of_not_gt hn⟩
  apply hnot
  simp only [spent,Finset.mem_union]
  tauto

private theorem sign_parts_zero_of_residual (A : Finset ℕ) (L y : ℝ) (N n : ℕ)
    (hres : residualCoefficient A L N n = 0) :
    signedPart 1 A L y N n = 0 ∧ signedPart (-1) A L y N n = 0 := by
  have hh := ZetaRieszOwnerTieFloor.signedParts_abs_eq A L y N n
  rw [hres,zero_mul,Complex.zero_re,abs_zero] at hh
  have hp : |signedPart 1 A L y N n| = 0 := by
    linarith only [hh,abs_nonneg (signedPart 1 A L y N n),
      abs_nonneg (signedPart (-1) A L y N n)]
  have hn : |signedPart (-1) A L y N n| = 0 := by
    linarith only [hh,abs_nonneg (signedPart 1 A L y N n),
      abs_nonneg (signedPart (-1) A L y N n)]
  exact ⟨abs_eq_zero.mp hp,abs_eq_zero.mp hn⟩

/-- Complete negative-peak periods give a signed floor on the positive
arithmetic part after its zero intersections with spent supply are removed. -/
theorem eventually_unpaid_four_positive_cover {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ)
      (I : Finset ℕ) (v : ℝ),
      0 < h → h ≤ 1/20 →
      (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
      Real.cos (y*v) = -1 →
      (∀ i ∈ I, (39/20 : ℝ)*dyadicMomentOrder j ≤ center v y i-Real.pi/y ∧
        center v y i+Real.pi/y ≤ (203/100 : ℝ)*dyadicMomentOrder j) →
      let N := dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (dyadicPrimeCount j)
      let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4)
      let X := fun i => roughPeriod Q (center v y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart 1 A L y N n)-
        ε*(∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial) ≤
        ∑ n ∈ E, signedPart 1 A L y N n := by
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
      (eventually_roughPeriod_part_floor (e := 1) (by norm_num) hu hU hy hε),
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hpos hslabs hL hlarge hj Q P V R η h w I v hh hhu hw hpeak hI
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4)
  let X := fun i => roughPeriod Q (center v y i) y
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hcount : 3+1 < dyadicPrimeCount j := by
    dsimp [dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ} (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod Q c y ⊆ S := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    exact owned_subset_core (k := 3) (by norm_num) j hj hcount hu hU hy hc
      (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
      hlo hhi (roughCofactors Q c) (Finset.filter_subset _ _)
  have hvI i (hi : i ∈ I) : 100 ≤ center v y i := by linarith only [hNR,hpi,(hI i hi).1]
  have hXeq i (hi : i ∈ I) :
      (∑ n ∈ X i ∩ E, signedPart 1 A L y N n) = ∑ n ∈ X i, signedPart 1 A L y N n := by
    exact sum_inter_unpaid_eq S (X i) _ N Q P V R η h L w
      (howned (hI i hi).1 (hI i hi).2)
      (fun n hn => (roughPeriod_data (hvI i hi) hy hn).2.1)
      (fun n hn hspent => positive_part_zero_of_spent S A hlarge η y hh hhu w hw
        (SquarefreeVaughanLogSource.length_pos u N)
        (fun M hM => (hslabs M hM).2)
        (roughPeriod_data (hvI i hi) hy hn).2.1
        (roughPeriod_data (hvI i hi) hy hn).2.2 hspent)
  have hdisjoint (b : ℝ) {i l : ℕ} (hil : i ≠ l)
      (hi : 100 ≤ center b y i) (hl : 100 ≤ center b y l) :
      Disjoint (roughPeriod Q (center b y i) y) (roughPeriod Q (center b y l) y) := by
    rcases lt_or_gt_of_ne hil with h | h
    · exact ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hi hl hy _ _
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hsep b h)
    · exact (ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hl hi hy _ _
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hsep b h)).symm
  have hb := one_cover_floor E I (fun i => X i ∩ E) (signedPart 1 A L y N)
    (fun i => ε*(Real.exp (-center v y i/2)*(center v y i)^N/N.factorial))
    (fun _ _ => Finset.inter_subset_right)
    (fun i hi l hl hil => (hdisjoint v hil (hvI i hi) (hvI l hl)).mono
      Finset.inter_subset_left Finset.inter_subset_left)
    (by
      intro i hi
      rw [hXeq i hi]
      have hp := (staggered_peaks hy0 hpeak i).1
      simpa only [neg_mul] using hpos Q _ (hI i hi).1 (hI i hi).2 hp.1
        (by rw [hp.2]; norm_num))
  rw [sdiff_cover_inter] at hb
  simpa only [← Finset.mul_sum] using hb

theorem interior_parts_covered (j : ℕ) (hj : 32 ≤ j) (u : ℝ)
    {y : ℝ} (hy : 54 ≤ y) {Q P V R n : ℕ} (η h : ℝ) (w : ℕ → ℝ)
    (hN : 4000 ≤ dyadicMomentOrder j)
    (hn : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter (fun n : ℕ =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧
          (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hnot : n ∉ spent (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) Q P V R η h (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) w)
    (hc : n.primeFactors.card = 4)
    (hlo : (244/125 : ℝ)*dyadicMomentOrder j < Real.log n)
    (hhi : Real.log n ≤ (2029/1000 : ℝ)*dyadicMomentOrder j)
    (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    let N := dyadicMomentOrder j
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N;
    (signedPart 1 A L y N n = 0 ∨
      n ∈ (completeGrid N (Real.pi/y) y).biUnion
        (fun i => roughPeriod Q (center (Real.pi/y) y i) y)) ∧
    (signedPart (-1) A L y N n = 0 ∨
      n ∈ (completeGrid N (Real.pi/y+Real.pi/y) y).biUnion
        (fun i => roughPeriod Q (center (Real.pi/y+Real.pi/y) y i) y)) := by
  dsimp only
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  by_cases hres : residualCoefficient A L N n = 0
  · have hz := sign_parts_zero_of_residual A L y N n hres
    exact ⟨Or.inl hz.1,Or.inl hz.2⟩
  have hs : Squarefree n := by
    by_contra hs
    apply hres
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs]
  obtain ⟨hpp,he,ha,hac,hp,hmax,_⟩ := four_owner_data hs hc
  let p := ZetaRieszPrimeEndpoint.largestPrime n
  let a := n/p
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast ha.ne_zero)]
  have hplog := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u hn hres p hp
  have hshare : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a := by
    change p*a = n at he
    rw [← he] at hplog
    rw [hlog] at hplog ⊢
    linarith only [hplog]
  have hgap := no_close_owner_gap hs hc hntie
  have hy0 : 0 < y := by linarith
  have hpi : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  obtain ⟨i,hi,hTi⟩ := exists_completeGrid_period hN hy
    (show Real.pi/y ≤ Real.pi/y ∧ Real.pi/y ≤ 2*Real.pi/y by
      constructor
      · rfl
      · calc
          Real.pi/y ≤ Real.pi/y+Real.pi/y := le_add_of_nonneg_right hh.le
          _ = 2*Real.pi/y := by ring) hlo hhi
  obtain ⟨l,hl,hTl⟩ := exists_completeGrid_period hN hy
    (show Real.pi/y ≤ Real.pi/y+Real.pi/y ∧ Real.pi/y+Real.pi/y ≤ 2*Real.pi/y by
      constructor
      · linarith only [hh]
      · exact le_of_eq (by ring)) hlo hhi
  have hv : 100 ≤ center (Real.pi/y) y i := by linarith only [hTi.2,hlo,hpi,hNR]
  have hv' : 100 ≤ center (Real.pi/y+Real.pi/y) y l := by linarith only [hTl.2,hlo,hpi,hNR]
  have hrough := unpaid_four_rough S η h L w hN
    (Finset.mem_filter.mp hn).1 hnot hs hc hlo hhi (by
      intro q hq
      have hb := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u hn hres q hq
      have hl := Real.log_natCast_nonneg n
      linarith only [hb,hl])
  have hrougha (q : ℕ) (hq : q ∈ a.primeFactors) : Q < q := by
    have hqn : q ∈ n.primeFactors := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hq).trans
        (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))) hs.ne_zero
    exact hrough q hqn
  have hhpos := owner_gap_mem_roughPeriod (B := Q) hv hy ha hac hpp
    (he.symm ▸ hTi) hshare hgap hrougha
  have hhneg := owner_gap_mem_roughPeriod (B := Q) hv' hy ha hac hpp
    (he.symm ▸ hTl) hshare hgap hrougha
  rw [he] at hhpos hhneg
  exact ⟨Or.inr (Finset.mem_biUnion.mpr ⟨i,hi,hhpos⟩),
    Or.inr (Finset.mem_biUnion.mpr ⟨l,hl,hhneg⟩)⟩

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

/-- The entire positive arithmetic part of the unpaid four-prime sector has a signed floor
with arbitrarily small complete-period debit and source-geometric errors.
The negative arithmetic part is not included in this payment. -/
theorem exists_unpaid_four_positive_floor {u y ε : ℝ} (hu : 1/2 < u)
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
          4*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)-
          2*r^N*C ≤
            ((u : ℂ)^(N+1)*∑ n ∈ E.filter (fun n =>
              0 < (SquarefreeVaughanLogSource.coefficient L n).re),
              residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r,C,hr,hr1,hC,houter⟩ := exists_outer_subset_bound
  refine ⟨r,C,hr,hr1,hC,?_⟩
  have hy0 : 0 < y := by linarith
  have hπ : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hpeak : Real.cos (y*(Real.pi/y)) = -1 := by
    rw [mul_div_cancel₀ _ hy0.ne',Real.cos_pi]
  filter_upwards [eventually_unpaid_four_positive_cover hu hU hy (half_pos hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszOwnerTieFloor.eventually_core_grouped_tie_floor hu hU (half_pos hε)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hperiod htie hN hj Q P V R η h w hh hhu hw
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 4)
  let dom := fun n : ℕ => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
      (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let D := E.filter dom
  let F := (E\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N < Real.log n ∧
    Real.log n ≤ (2029/1000 : ℝ)*N))
  let T := ((E\D)\F).filter (fun n => Squarefree n ∧ ZetaRieszOwnerTieFloor.CloseOwners n)
  let I := completeGrid N (Real.pi/y) y
  let J := completeGrid N (Real.pi/y+Real.pi/y) y
  let X := I.biUnion (fun i => roughPeriod Q (center (Real.pi/y) y i) y)
  let Y := E
  let units₁ := ∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial
  let units₂ := ∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
    (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial
  have units₁pos : 0 ≤ units₁ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
    have hc : 0 ≤ center (Real.pi/y) y i := by linarith only [hg,hπ.le,hNR]
    positivity)
  have hper := hperiod Q P V R η h w I (Real.pi/y) hh hhu hw hpeak
    (fun _ hi => ⟨(Finset.mem_filter.mp hi).2.1,(Finset.mem_filter.mp hi).2.2.1⟩)
  change (∑ n ∈ E\X, signedPart 1 A L y N n)-(ε/2)*units₁ ≤
    ∑ n ∈ E, signedPart 1 A L y N n at hper
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
    obtain ⟨hnUn,hc⟩ := Finset.mem_filter.mp hnE
    obtain ⟨hnS,hnot⟩ := Finset.mem_sdiff.mp hnUn
    have hnotdom : ¬dom n := fun hh => hnotD (Finset.mem_filter.mpr ⟨hnE,hh⟩)
    let hres := residualCoefficient A L N n
    by_cases hz : hres = 0
    · have hhzero := sign_parts_zero_of_residual A L y N n hz
      exact ⟨Or.inl hhzero.1,Or.inl hhzero.2⟩
    have hs : Squarefree n := by
      by_contra hs
      apply hz
      simp [hres,residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs]
    have hnotTie : ¬ZetaRieszOwnerTieFloor.CloseOwners n :=
      fun hclose => hnotT (Finset.mem_filter.mpr ⟨hnEF,hs,hclose⟩)
    refine ⟨(interior_parts_covered j hj u hy η h w hN
      (Finset.mem_filter.mpr ⟨hnS,hnotdom⟩) hnot hc (hFgeo n hnEF).1
        (hFgeo n hnEF).2 hnotTie).1,Or.inr hnE⟩
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
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul,← positive_part_sum_eq]
  change _ ≤ u^(N+1)*(∑ n ∈ E, signedPart 1 A L y N n)
  have hyempty : E\Y = ∅ := Finset.sdiff_self E
  rw [hyempty,Finset.sum_empty] at he₂
  have hunits₂ : 0 ≤ units₂ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hc : 0 ≤ center (Real.pi/y+Real.pi/y) y i := by linarith only [hg,hπ.le,hNReal]
    positivity)
  have hεunits := mul_nonneg hε.le hunits₂
  have hscale := pow_nonneg (by linarith : 0 ≤ u) (N+1)
  nlinarith only [hDpay,hFpay,hTscaled,hPscaled,he₁,he₂,hεunits,hscale]



private theorem paid_parts (E : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) :
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 5), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 6), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55), f n)+
    (∑ n ∈ (E.filter (fun n : ℕ => n.primeFactors.card = 4)).filter
      (fun n => 0 < (SquarefreeVaughanLogSource.coefficient L n).re), f n) =
    ∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
      n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
      (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
      (n.primeFactors.card = 4 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)), f n := by
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
/-- The whole floor also pays every positive-coefficient four-prime
label, retaining the same 65/128 supply and the joined favorable credit.
Its remaining low-count atoms have nonpositive arithmetic coefficient;
the growing count band begins at fifty-six. All payments are independent
of a zero hypothesis, and the numerical cofinal floor remains open. -/
theorem eventually_joined_floor_with_negative_fours {u y : ℝ} (hu : 1/2 < u)
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
          (n.primeFactors.card = 4 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re))
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
  obtain ⟨r₅,C₅,hr₅,hr₅1,hC₅,hfour⟩ := exists_unpaid_four_positive_floor hu hU hy
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
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+4*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂+2*r₃^(dyadicMomentOrder j)*C₃+err₄ j+2*r₅^(dyadicMomentOrder j)*C₅
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (((((h₀.add heLim).add (hdLim.const_mul (4 : ℝ))).add h₁).add h₂).add h₃).add herr₄ |>.add h₅
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
    (fun n => 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
  let Ehi := E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
  let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re))
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
  change -u^(N+1)*(κ/5)*units-d j-2*r₅^N*C₅ ≤
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
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-4*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j-2*r₅^N*C₅ ≤
      u^(N+1)*((∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
        (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re) := by
    nlinarith only [hscaled,hp,hq,ht,hbandFloor,hfourFloor]
  have hpaidEq := congrArg Complex.re (paid_parts E f L)
  simp only [Complex.add_re] at hpaidEq
  change (∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
    (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re = (∑ n ∈ Epaid, f n).re at hpaidEq
  rw [hpaidEq] at hpaid
  have hcost : 0 ≤ u^(N+1)*(∑ n ∈ Ys, f n).re/128+4*d j+
      2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅ := by
    positivity [hY.le,hd0 j,herr₄0 j]
  have hpaidMax : u^(N+1)*max (∑ n ∈ Epaid, f n).re 0-
      u^(N+1)*(∑ n ∈ Ys, f n).re/128-4*d j-
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
          (n.primeFactors.card = 4 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)) E)
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
      (r₀^N*C₀+e j+4*d j+2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaidMax,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring



/-- A remaining four-prime atom has nonpositive arithmetic coefficient.
All other remaining labels have at least fifty-six prime factors. -/
theorem remaining_count_sign_cases {u : ℝ} {N K Q P V R n : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ)
    (hn : n ∈ (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w)\
      (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w).filter
        (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
          n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re))) :
    (n.primeFactors.card = 4 ∧ (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0) ∨
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
      (n.primeFactors.card = 4 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)) :=
    fun hc => hnot (Finset.mem_filter.mpr ⟨hnE,hc⟩)
  by_cases h4 : n.primeFactors.card = 4
  · exact Or.inl ⟨h4,le_of_not_gt (fun hpos => hcounts (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨h4,hpos⟩)))))⟩
  · right
    omega

end RiemannGaussian.ZetaRieszFourPositiveFloor
