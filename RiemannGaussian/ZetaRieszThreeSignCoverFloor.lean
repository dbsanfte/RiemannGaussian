/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixSignCoverFloor

set_option autoImplicit false

/-!
# Joining all rough triples before the signed period floor

Rejoin the previously paid balanced triples before applying the existing
complete-period estimate. This removes their norm debit and keeps the
original small-prime head, phase, two hinges, allocation and every mask.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszThreeSignCoverFloor
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

/-- Rejoin the old balanced triples to the literal remainder. This removes
only their old debit; every other original paid label remains spent. -/
def tripleRestSpent (S : Finset ℕ) (N Q P V R : ℕ) (η h L : ℝ)
    (w : ℕ → ℝ) : Finset ℕ :=
  spent S N Q P V R η h L w \ radialTriples S N η

/-- Two-prime rough cofactors for the complete triple phase periods. -/
def roughCofactors (B : ℕ) (v : ℝ) : Finset ℕ :=
  (cofactors 2 v).filter (fun a => ∀ r ∈ a.primeFactors, B < r)

/-- Literal rough triples with the unique largest prime in a complete period. -/
def roughPeriod (B : ℕ) (v y : ℝ) : Finset ℕ :=
  (roughCofactors B v).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))

theorem roughPeriod_data {B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod B v y) :
    Squarefree n ∧ n.primeFactors.card = 3 ∧ ∀ r ∈ n.primeFactors, B < r := by
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

theorem rough_three_not_spent (S : Finset ℕ) {N Q P V R B n : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hQ : Q ≤ B) (hc : n.primeFactors.card = 3)
    (hrough : ∀ r ∈ n.primeFactors, B < r) : n ∉ tripleRestSpent S N Q P V R η h L w := by
  intro hn
  change n ∈ spent S N Q P V R η h L w \ radialTriples S N η at hn
  obtain ⟨hn,hX⟩ := Finset.mem_sdiff.mp hn
  have hZ : n ∉ (radialIndices N).biUnion
      (fun M => smallTriples (S\radialTriples S N η) M Q) := by
    intro hm
    obtain ⟨M,_,hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨_,_,_,_,_,_,r,hr,hrQ⟩ := Finset.mem_filter.mp hm
    exact (not_lt_of_ge (hrQ.trans hQ)) (hrough r hr)
  have hH : n ∉ (radialIndices N).biUnion (fun M => smallFours S M Q) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hY : n ∉ radialSupply N h w := by
    intro hn
    have hm := radialSupply_count hN hh hhu w hw hn
    omega
  have hF : n ∉ (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.1
    omega
  have hG : n ∉ radialHeads S N P V L := by
    intro hm
    obtain ⟨M,_,hm⟩ := Finset.mem_biUnion.mp hm
    have hc' := (Finset.mem_filter.mp hm).2.2.2.2
    rcases hc' with ⟨h6,_⟩ | ⟨h5,_⟩ <;> omega
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
  simp only [spent,Finset.mem_union] at hn
  tauto

theorem roughPeriod_subset_unpaid (S : Finset ℕ) {N Q P V R B : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L v y : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hQ : Q ≤ B) (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hcore : roughPeriod B v y ⊆ S) :
    roughPeriod B v y ⊆ S\tripleRestSpent S N Q P V R η h L w := by
  intro n hn
  have hd := roughPeriod_data hv hy hn
  exact Finset.mem_sdiff.mpr ⟨hcore hn,
    rough_three_not_spent S hN η hh hhu w hw hQ hd.2.1 hd.2.2⟩

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
    (k := 2) (by norm_num) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors B v) hlo hhi (Finset.filter_subset _ _) hpeak hsign

theorem owner_gap_mem_roughPeriod {B a p : ℕ} {v y : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = 2) (hp : p.Prime)
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
  have ham : a ∈ cofactors 2 v :=
    (mem_cofactors_iff_of_count_le (by norm_num) (by linarith)).mpr ⟨ha,hc,hla,ho⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨ham,hrough⟩,
    Finset.mem_image.mpr ⟨p,?_,Nat.mul_comm a p⟩⟩
  apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
  rw [hlog] at hT
  refine ⟨hp,by linarith only [hT.1],?_⟩
  rw [show v-Real.pi/y-Real.log a+2*Real.pi/y = v+Real.pi/y-Real.log a by ring]
  linarith only [hT.2]

private theorem three_owner_data {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 3) :
    let p := ZetaRieszPrimeEndpoint.largestPrime n
    let a := n/p;
    p.Prime ∧ p*a = n ∧ Squarefree a ∧ a.primeFactors.card = 2 ∧
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
  have hcard : a.primeFactors.card = 2 := by
    rw [hpf,Finset.card_insert_of_notMem hnot] at hc
    omega
  have hmax q (hq : q ∈ n.primeFactors) : q ≤ p := by
    dsimp [p,ZetaRieszPrimeEndpoint.largestPrime]
    rw [dif_pos (Finset.card_pos.mp (by omega : 0 < n.primeFactors.card))]
    exact Finset.le_max' _ q hq
  exact ⟨hpp,he,ha,hcard,hp,hmax,hnot⟩

private theorem no_close_owner_gap {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 3) (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      Real.log q ≤ Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-1/8 := by
  obtain ⟨hpp,he,ha,_,hp,hmax,hnot⟩ := three_owner_data hs hc
  intro q hq
  by_contra hh
  have hqn : q ∈ n.primeFactors := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    hs.ne_zero
  apply hntie
  refine ⟨_,hp,q,hqn,?_,hmax,lt_of_not_ge hh⟩
  intro h
  exact hnot (h ▸ hq)

/-- A balanced triple is rough at the original small-prime threshold. -/
theorem balanced_triple_rough (S : Finset ℕ) {N Q n : ℕ} {η : ℝ}
    (hη : η ≤ 1/1000) (hQ : Real.log Q ≤ (N : ℝ)/128)
    (hn : n ∈ radialTriples S N η) : ∀ r ∈ n.primeFactors, Q < r := by
  obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
  have hMlo := (Finset.mem_filter.mp hM).2.1
  obtain ⟨_,_,_,_,_,hbal⟩ := Finset.mem_filter.mp hn
  intro r hr
  by_contra hnot
  have hrQ : r ≤ Q := le_of_not_gt hnot
  have hrlog : Real.log r ≤ Real.log Q := Real.log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
    (by exact_mod_cast hrQ)
  have hb := (abs_le.mp (hbal r hr)).1
  have hηM := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (α := ℝ) M)
  have hNR := Nat.cast_nonneg (α := ℝ) N
  linarith

/-- After the balanced triples are rejoined, every remaining interior
triple is rough. Small-prime triples still belong to their old paid union. -/
theorem unpaid_three_rough (S : Finset ℕ) {N n Q P V R : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) (hN : 4000 ≤ N) (hnS : n ∈ S)
    (hnot : n ∉ tripleRestSpent S N Q P V R η h L w)
    (hη : η ≤ 1/1000) (hQ : Real.log Q ≤ (N : ℝ)/128)
    (hs : Squarefree n) (hc : n.primeFactors.card = 3)
    (hphys : ∀ p ∈ n.primeFactors, Real.log p ≤ (601/1000 : ℝ)*Real.log n)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N) :
    ∀ r ∈ n.primeFactors, Q < r := by
  by_cases hX : n ∈ radialTriples S N η
  · exact balanced_triple_rough S hη hQ hX
  intro r hr
  by_contra hn
  have hrQ : r ≤ Q := le_of_not_gt hn
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le
    (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have hMN : M ≤ 2*N := by exact_mod_cast
        (show (M : ℝ) ≤ 2*N by linarith)
      omega
    constructor <;> linarith
  have hZ : n ∈ (radialIndices N).biUnion
      (fun M => smallTriples (S\radialTriples S N η) M Q) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨M,hM,Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hnS,hX⟩,hs,hc,by linarith,by linarith,?_,r,hr,hrQ⟩⟩
    intro p hp
    have hh := hphys p hp
    linarith
  apply hnot
  apply Finset.mem_sdiff.mpr
  refine ⟨?_,hX⟩
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

/-- Both signs of the literal unpaid three-prime contribution are covered
by complete ordinary-prime periods, apart from explicit unmatched parts. -/
theorem eventually_unpaid_three_sign_floor {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ)
      (I J : Finset ℕ) (v : ℝ),
      0 < h → h ≤ 1/20 →
      (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
      Real.cos (y*v) = -1 →
      (∀ i ∈ I, (39/20 : ℝ)*dyadicMomentOrder j ≤ center v y i-Real.pi/y ∧
        center v y i+Real.pi/y ≤ (203/100 : ℝ)*dyadicMomentOrder j) →
      (∀ i ∈ J, (39/20 : ℝ)*dyadicMomentOrder j ≤
        center (v+Real.pi/y) y i-Real.pi/y ∧
        center (v+Real.pi/y) y i+Real.pi/y ≤ (203/100 : ℝ)*dyadicMomentOrder j) →
      let N := dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (dyadicPrimeCount j)
      let E := (S\tripleRestSpent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 3)
      let X := fun i => roughPeriod Q (center v y i) y
      let Y := fun i => roughPeriod Q (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart 1 A L y N n)+
        (∑ n ∈ E\J.biUnion Y, signedPart (-1) A L y N n)-
        ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (∑ n ∈ E, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
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
    tendsto_dyadicMomentOrder.eventually
      (eventually_roughPeriod_part_floor (e := -1) (by norm_num) hu hU hy hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hpos hneg hL hlarge hj Q P V R η h w I J v hh hhu hw hpeak hI hJ
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\tripleRestSpent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 3)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hcount : 2+1 < dyadicPrimeCount j := by
    dsimp [dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ} (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod Q c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    have hcore : roughPeriod Q c y ⊆ S :=
      ZetaRieszTransitionFiveFloor.owned_subset_core (k := 2) (by norm_num)
        j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        hlo hhi (roughCofactors Q c) (Finset.filter_subset _ _)
    have hunpaid := roughPeriod_subset_unpaid (Q := Q) (P := P) (V := V) (R := R)
      (L := L) S hlarge η hh hhu w hw
      (le_refl Q) hc hy hcore
    intro n hn
    exact Finset.mem_filter.mpr ⟨hunpaid hn,(roughPeriod_data hc hy hn).2.1⟩
  let X := fun i => roughPeriod Q (center v y i) y
  let Y := fun i => roughPeriod Q (center (v+Real.pi/y) y i) y
  have hvI i (hi : i ∈ I) : 100 ≤ center v y i := by linarith only [hNR,hpi,(hI i hi).1]
  have hvJ i (hi : i ∈ J) : 100 ≤ center (v+Real.pi/y) y i := by linarith only [hNR,hpi,(hJ i hi).1]
  have hdisjoint (b : ℝ) {i l : ℕ} (hil : i ≠ l)
      (hi : 100 ≤ center b y i) (hl : 100 ≤ center b y l) :
      Disjoint (roughPeriod Q (center b y i) y) (roughPeriod Q (center b y l) y) := by
    rcases lt_or_gt_of_ne hil with h | h
    · exact ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hi hl hy _ _
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hsep b h)
    · exact (ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hl hi hy _ _
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hsep b h)).symm
  have hb := two_cover_floor A E I J X Y L y N
    (fun i => ε*(Real.exp (-center v y i/2)*(center v y i)^N/N.factorial))
    (fun i => ε*(Real.exp (-center (v+Real.pi/y) y i/2)*
      (center (v+Real.pi/y) y i)^N/N.factorial))
    (fun i hi => howned (hI i hi).1 (hI i hi).2)
    (fun i hi => howned (hJ i hi).1 (hJ i hi).2)
    (fun i hi l hl hil => hdisjoint v hil (hvI i hi) (hvI l hl))
    (fun i hi l hl hil => hdisjoint (v+Real.pi/y) hil (hvJ i hi) (hvJ l hl))
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).1
      simpa only [neg_mul] using hpos Q _ (hI i hi).1 (hI i hi).2 hp.1 (by rw [hp.2]; norm_num))
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).2
      simpa only [neg_mul] using hneg Q _ (hJ i hi).1 (hJ i hi).2 hp.1 (by rw [hp.2]; norm_num))
  simpa only [← Finset.mul_sum,← mul_add] using hb

theorem interior_parts_covered (j : ℕ) (hj : 32 ≤ j) (u : ℝ)
    {y : ℝ} (hy : 54 ≤ y) {Q P V R n : ℕ} (η h : ℝ) (w : ℕ → ℝ)
    (hN : 4000 ≤ dyadicMomentOrder j)
    (hη : η ≤ 1/1000) (hQ : Real.log Q ≤ (dyadicMomentOrder j : ℝ)/128)
    (hn : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter (fun n : ℕ =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧
          (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hnot : n ∉ tripleRestSpent (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (dyadicMomentOrder j) Q P V R η h (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) w)
    (hc : n.primeFactors.card = 3)
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
  obtain ⟨hpp,he,ha,hac,hp,hmax,_⟩ := three_owner_data hs hc
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
  have hrough := unpaid_three_rough S η h L w hN
    (Finset.mem_filter.mp hn).1 hnot hη hQ hs hc
    (fun q hq => (ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt
      j hj u hn hres q hq).le) hlo hhi
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

/-- The entire actual unpaid three-prime sector has a signed floor
with arbitrarily small complete-period debit and source-geometric errors.
No arithmetic-sign or interior omission remains in this rejoined triple sector. -/
theorem exists_unpaid_three_floor {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ),
        0 < h → h ≤ 1/20 → η ≤ 1/1000 → Real.log Q ≤ (dyadicMomentOrder j : ℝ)/128 →
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := (S\tripleRestSpent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 3)
        let I := completeGrid N (Real.pi/y) y
        let J := completeGrid N (Real.pi/y+Real.pi/y) y;
        -u^(N+1)*ε*((∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*
          (center (Real.pi/y) y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
            (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial))-
          4*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)-
          2*r^N*C ≤
            ((u : ℂ)^(N+1)*∑ n ∈ E,
              residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨r,C,hr,hr1,hC,houter⟩ := exists_outer_subset_bound
  refine ⟨r,C,hr,hr1,hC,?_⟩
  have hy0 : 0 < y := by linarith
  have hπ : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hpeak : Real.cos (y*(Real.pi/y)) = -1 := by
    rw [mul_div_cancel₀ _ hy0.ne',Real.cos_pi]
  filter_upwards [eventually_unpaid_three_sign_floor hu hU hy (half_pos hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszOwnerTieFloor.eventually_core_grouped_tie_floor hu hU (half_pos hε)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hperiod htie hN hj Q P V R η h w hh hhu hη hQ hw
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\tripleRestSpent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 3)
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
  let Y := J.biUnion (fun i => roughPeriod Q (center (Real.pi/y+Real.pi/y) y i) y)
  let units₁ := ∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial
  let units₂ := ∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
    (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial
  have units₁pos : 0 ≤ units₁ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
    have hc : 0 ≤ center (Real.pi/y) y i := by linarith only [hg,hπ.le,hNR]
    positivity)
  have hper := hperiod Q P V R η h w I J (Real.pi/y) hh hhu hw hpeak
    (fun _ hi => ⟨(Finset.mem_filter.mp hi).2.1,(Finset.mem_filter.mp hi).2.2.1⟩)
    (fun _ hi => ⟨(Finset.mem_filter.mp hi).2.1,(Finset.mem_filter.mp hi).2.2.1⟩)
  change (∑ n ∈ E\X, signedPart 1 A L y N n)+
    (∑ n ∈ E\Y, signedPart (-1) A L y N n)-(ε/2)*(units₁+units₂) ≤
      (∑ n ∈ E, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re at hper
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
    exact interior_parts_covered j hj u hy η h w hN hη hQ
      (Finset.mem_filter.mpr ⟨hnS,hnotdom⟩) hnot hc (hFgeo n hnEF).1 (hFgeo n hnEF).2 hnotTie
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
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  change _ ≤ u^(N+1)*(∑ n ∈ E,
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  have hunits₂ : 0 ≤ units₂ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hc : 0 ≤ center (Real.pi/y+Real.pi/y) y i := by linarith only [hg,hπ.le,hNReal]
    positivity)
  have hεunits := mul_nonneg hε.le hunits₂
  have hscale := pow_nonneg (by linarith : 0 ≤ u) (N+1)
  nlinarith only [hDpay,hFpay,hTscaled,hPscaled,he₁,he₂,hεunits,hscale]


private theorem skip_first_three (X Z H Y : Finset ℕ) :
    Z ∪ H ∪ Y ⊆ X ∪ Z ∪ H ∪ Y := by
  intro n hn
  simp only [Finset.mem_union] at hn ⊢
  tauto

/-- Exact spending when the old balanced triples are retained in the
signed rest. Their half-supply norm debit is refunded, rather than charged
again to the complete triple periods. -/
private theorem re_sum_ge_without_balanced_debit {D Z H F G T Y : Finset ℕ}
    (f : ℕ → ℂ) (hsub : Z ∪ H ∪ Y ∪ F ∪ G ∪ T ⊆ D)
    (hZH : Disjoint Z H) (hZY : Disjoint Z Y) (hHY : Disjoint H Y)
    (hF : Disjoint F (Z ∪ H ∪ Y))
    (hG : Disjoint G (Z ∪ H ∪ Y ∪ F))
    (hT : Disjoint T (Z ∪ H ∪ Y ∪ F ∪ G))
    (hZcost : ‖∑ n ∈ Z, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hHcost : ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hFcost : ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ Y, f n).re)
    (hGcost : ‖∑ n ∈ G, f n‖ ≤ (3/32 : ℝ)*(∑ n ∈ Y, f n).re)
    (hTcost : ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ Y, f n).re) :
    (∑ n ∈ D\(Z ∪ H ∪ Y ∪ F ∪ G ∪ T), f n).re+
      max (∑ n ∈ Z, f n).re 0+max (∑ n ∈ H, f n).re 0+
      max (∑ n ∈ F, f n).re 0+max (∑ n ∈ G, f n).re 0+
      max (∑ n ∈ T, f n).re 0+(33/64 : ℝ)*(∑ n ∈ Y, f n).re ≤
        (∑ n ∈ D, f n).re := by
  have hsum := Finset.sum_sdiff (f := f) hsub
  rw [Finset.sum_union hT.symm,Finset.sum_union hG.symm,
    Finset.sum_union hF.symm,Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hZY,hHY⟩),
    Finset.sum_union hZH] at hsum
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re] at hre
  have hmax (a : ℂ) (c : ℝ) (hc : ‖a‖ ≤ c) : max a.re 0 ≤ a.re+c := by
    have hn := Complex.re_le_norm (-a)
    simp only [Complex.neg_re,norm_neg] at hn
    exact max_le (by linarith only [hc,norm_nonneg a]) (by linarith only [hn,hc])
  have hz := hmax _ _ hZcost
  have hh := hmax _ _ hHcost
  have hf := hmax _ _ hFcost
  have hg := hmax _ _ hGcost
  have ht := hmax _ _ hTcost
  linarith only [hre,hz,hh,hf,hg,ht]

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h

/-- One original supply selection pays every remaining old head and
retains the balanced triples literally. Its available fraction is 33/64,
instead of 1/64, because their half-supply norm debit is no longer spent. -/
theorem eventually_core_floor_with_triples_rejoined {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ c κ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 < c ∧ 0 < κ ∧
      κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialHeads S N P V (SquarefreeVaughanLogSource.length u N)
        let Ts := radialTail S N R
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          (∀ M ∈ radialIndices N,
            c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
              (∑ n ∈ supply M h (v M), f n).re) ∧
          u^(N+1)*(W.re+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(33/64 : ℝ)*(∑ n ∈ Ys, f n).re) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hpay⟩ :=
    ZetaRieszRoughFivePeriodFloor.eventually_joint_slabs_floor_with_period_budget hy
  refine ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hP : Real.log P ≤ ε*N := log_floor_exp_le
    (mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) N))
  have hV : Real.log V ≤ ζ*N := log_floor_exp_le
    (mul_nonneg hζ.le (Nat.cast_nonneg (α := ℝ) N))
  have hR : Real.log R ≤ θ*N := log_floor_exp_le
    (mul_nonneg hθ.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      (0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallHeads S M P V L, f n‖ ≤ (3/32 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTail S N R M, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ supply M h v, f n).re) ∧
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hH,hF,hG,hT,_⟩ := hpay M Q P V R S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallHeads S M P V L) (slabTail S N R M) A L
        (hL M hM).1 (by have := Finset.mem_range.mp (Finset.mem_filter.mp hM).1; omega) hQ hP hV hR (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall,hpos⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall,hpos⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hlo,hhi,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hlo,hhi.le,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hlo,hhi,hcount⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hlo,hhi.le,hcount⟩)
      exact ⟨v,fun _ => ⟨⟨hv,hvu,hY,hX,hZ,hH,hF,hG,hT⟩,hscale⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv' using hex
  let hv := fun (M : ℕ) (hM : M ∈ radialIndices N) => (hv' M hM).1
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ts := radialTail S N R
  let Ys := radialSupply N h v
  have hY : 0 < (∑ n ∈ Ys, f n).re := by
    change 0 < (∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hZpay := norm_radial_payment
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) Q hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment
    (fun _ _ _ _ hne => smallFours_disjoint S Q hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.1)
  have hFpay := norm_radial_payment
    (fun _ _ _ _ hne => smallPositiveFives_disjoint S Q L hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.1)
  have hGpay := norm_radial_payment
    (fun _ _ _ _ hne => smallHeads_disjoint S P V L hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.2.1)
  have hTpay := norm_radial_payment
    (fun _ _ _ _ hne => slabTail_disjoint S N R hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.2.2)
  have hTsub : Ts ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hTcount : ∀ n ∈ Ts, 7 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N) (Finset.mem_filter.mp hn).2.2.2.2
  have hXsub : Xs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hZsub : Zs ⊆ S\Xs := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hHsub : Hs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hFsub : Fs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hGsub : Gs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hG6 : ∀ n ∈ Gs, headCondition L P V n := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.2.2
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact ⟨(Finset.mem_filter.mp hn).2.2.1,(Finset.mem_filter.mp hn).2.2.2.2.2.2.2⟩
  have hX3 : ∀ n ∈ Xs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hZ3 : ∀ n ∈ Zs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hH4 : ∀ n ∈ Hs, n.primeFactors.card = 4 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hY4 : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => (radial_supply_geometry hN hh hhu hvb hn).1
  have hdisj (B C : Finset ℕ) (hB : ∀ n ∈ B, n.primeFactors.card = 3)
      (hC : ∀ n ∈ C, n.primeFactors.card = 4) : Disjoint B C :=
    Finset.disjoint_left.mpr (fun n hb hc => by have := hB n hb; have := hC n hc; omega)
  have hXZ : Disjoint Xs Zs := Finset.disjoint_left.mpr
    (fun _ hx hz => (Finset.mem_sdiff.mp (hZsub hz)).2 hx)
  have hHY : Disjoint Hs Ys := by
    apply Finset.disjoint_left.mpr
    intro n hn hnY
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨_,_,_,_,_,_,r,hr,hrsmall⟩ := Finset.mem_filter.mp hn
    have hrlog := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
      (show (r : ℝ) ≤ Q by exact_mod_cast hrsmall)
    have hh := (radial_supply_geometry hN hh hhu hvb hnY).2 r hr
    have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsuball : Xs ∪ Zs ∪ Hs ∪ Ys ⊆ S := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.union_subset hXsub
        (fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1)) hHsub
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvb M hM).1 (hvb M hM).2 hn
  have hFdisj : Disjoint Fs (Xs ∪ Zs ∪ Hs ∪ Ys) := by
    apply Finset.disjoint_left.mpr
    intro n hnF hn
    have hf := (hF5 n hnF).1
    rcases Finset.mem_union.mp hn with hn | hnY
    · rcases Finset.mem_union.mp hn with hn | hnH
      · rcases Finset.mem_union.mp hn with hnX | hnZ
        · have := hX3 n hnX; omega
        · have := hZ3 n hnZ; omega
      · have := hH4 n hnH; omega
    · have := hY4 n hnY; omega
  have hGdisj : Disjoint Gs (Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs) := by
    apply Finset.disjoint_left.mpr
    intro n hnG hn
    have hg := hG6 n hnG
    have hgcount : n.primeFactors.card = 6 ∨ n.primeFactors.card = 5 := hg.elim
      (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    rcases Finset.mem_union.mp hn with hn | hnF
    · rcases Finset.mem_union.mp hn with hn | hnY
      · rcases Finset.mem_union.mp hn with hn | hnH
        · rcases Finset.mem_union.mp hn with hnX | hnZ
          · have := hX3 n hnX; omega
          · have := hZ3 n hnZ; omega
        · have := hH4 n hnH; omega
      · have := hY4 n hnY; omega
    · rcases hg with ⟨hc,_⟩ | ⟨_,hneg,_⟩
      · have := (hF5 n hnF).1; omega
      · linarith [(hF5 n hnF).2]
  have hTdisj : Disjoint Ts (Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := by
    apply Finset.disjoint_left.mpr
    intro n hnT hn
    have ht := hTcount n hnT
    simp only [Finset.mem_union] at hn
    rcases hn with ((((hn | hn) | hn) | hn) | hn) | hn
    · have := hX3 n hn; omega
    · have := hZ3 n hn; omega
    · have := hH4 n hn; omega
    · have := hY4 n hn; omega
    · have := (hF5 n hn).1; omega
    · rcases hG6 n hn with ⟨hc,_⟩ | ⟨hc,_⟩ <;> omega
  have hZsub' : Zs ⊆ S := fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1
  have hYsub' : Ys ⊆ S := fun _ hn => hsuball (Finset.mem_union_right _ hn)
  have hrestsub : Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ⊆ S :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset
      (Finset.union_subset (Finset.union_subset hZsub' hHsub) hYsub') hFsub) hGsub) hTsub
  have hskip : Zs ∪ Hs ∪ Ys ⊆ Xs ∪ Zs ∪ Hs ∪ Ys := skip_first_three Xs Zs Hs Ys
  have hFrest : Disjoint Fs (Zs ∪ Hs ∪ Ys) := hFdisj.mono_right hskip
  have hskipF := Finset.union_subset_union hskip (Finset.Subset.refl Fs)
  have hGrest : Disjoint Gs (Zs ∪ Hs ∪ Ys ∪ Fs) := hGdisj.mono_right hskipF
  have hTrest : Disjoint Ts (Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := hTdisj.mono_right
    (Finset.union_subset_union hskipF (Finset.Subset.refl Gs))
  have hfloor := re_sum_ge_without_balanced_debit f hrestsub
    (hdisj Zs Hs hZ3 hH4) (hdisj Zs Ys hZ3 hY4) hHY hFrest hGrest hTrest
    hZpay hHpay hFpay hGpay hTpay
  refine ⟨v,hvb,hY,fun M hM => (hv' M hM).2,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm


set_option maxHeartbeats 1200000 in
/-- Rejoining the balanced triples removes exactly that old spent class;
no other head, supply or count-tail label is silently restored. -/
theorem tripleRestSpent_eq (S : Finset ℕ) {N Q P V R : ℕ}
    (η : ℝ) {h L : ℝ} (hN : 1000 ≤ N) (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) :
    tripleRestSpent S N Q P V R η h L w =
      (radialIndices N).biUnion (fun M => smallTriples (S\radialTriples S N η) M Q) ∪
      (radialIndices N).biUnion (fun M => smallFours S M Q) ∪ radialSupply N h w ∪
      (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) ∪
      radialHeads S N P V L ∪ ZetaRieszSevenCountTail.radialTail S N R ∪
      ZetaRieszSevenCountTail.wholeTail S N R := by
  let X := radialTriples S N η
  let B := (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q) ∪
    (radialIndices N).biUnion (fun M => smallFours S M Q) ∪ radialSupply N h w ∪
    (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) ∪
    radialHeads S N P V L ∪ ZetaRieszSevenCountTail.radialTail S N R ∪
    ZetaRieszSevenCountTail.wholeTail S N R
  have hdisj : Disjoint X B := by
    apply Finset.disjoint_left.mpr
    intro n hnX hnB
    have hnXfull := hnX
    obtain ⟨M,_,hnX⟩ := Finset.mem_biUnion.mp hnX
    have hc := (Finset.mem_filter.mp hnX).2.2.1
    change n ∈ B at hnB
    dsimp only [B] at hnB
    simp only [Finset.mem_union] at hnB
    rcases hnB with (((((hn | hn) | hn) | hn) | hn) | hn) | hn
    · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
      have hx := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).2
      exact hx hnXfull
    · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
      have hm := (Finset.mem_filter.mp hn).2.2.1
      omega
    · have hm := radialSupply_count hN hh hhu w hw hn
      omega
    · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
      have hm := (Finset.mem_filter.mp hn).2.2.1
      omega
    · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
      have hm := (Finset.mem_filter.mp hn).2.2.2.2
      rcases hm with ⟨h6,_⟩ | ⟨h5,_⟩ <;> omega
    · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
      have hm := ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N)
        (Finset.mem_filter.mp hn).2.2.2.2
      omega
    · have hm := ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N)
        (Finset.mem_filter.mp hn).2.2
      omega
  have he : spent S N Q P V R η h L w = X ∪ B := by
    ext n
    simp only [spent,X,B,Finset.mem_union]
    tauto
  change (spent S N Q P V R η h L w)\X = B
  rw [he]
  ext n
  simp only [Finset.mem_sdiff,Finset.mem_union]
  constructor
  · tauto
  · intro hn
    exact ⟨Or.inr hn,fun hx => Finset.disjoint_left.mp hdisj hx hn⟩

private theorem missed_subset {S E : Finset ℕ} {N R : ℕ} (hN : 1 ≤ N)
    (hE : ∀ n ∈ E, n.primeFactors.card ≤ 6) :
    wholeTail S N R\radialTail S N R ⊆ S\(E ∪ radialTail S N R) := by
  intro n hn
  obtain ⟨hnW,hnT⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hnS,_,hc⟩ := Finset.mem_filter.mp hnW
  refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
  intro he
  rcases Finset.mem_union.mp he with he | he
  · have := hE n he
    have := ZetaRieszSevenPrimeHead.tailCondition_count_ge hN hc
    omega
  · exact hnT he

private theorem rest_split (S E : Finset ℕ) (N R : ℕ) :
    (S\(E ∪ radialTail S N R))\(wholeTail S N R\radialTail S N R) =
      S\(E ∪ radialTail S N R ∪ wholeTail S N R) := by
  ext n
  simp only [Finset.mem_sdiff,Finset.mem_union]
  tauto

set_option maxHeartbeats 1200000 in
/-- The enlarged count tail, including both radial edges, is paid in the
floor direction. Every earlier radial payment and its signed rest remain. -/
theorem eventually_core_full_floor_with_triples_rejoined {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ c κ r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 < c ∧ 0 < κ ∧
      κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialHeads S N P V (SquarefreeVaughanLogSource.length u N)
        let Ts := radialTail S N R
        let Ys := radialSupply N h v
        let B := wholeTail S N R
        let W := ∑ n ∈ S\(Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          (∀ M ∈ radialIndices N,
            c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
              (∑ n ∈ supply M h (v M), f n).re) ∧
          u^(N+1)*(W.re+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(33/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r^N*C ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hspend⟩ :=
    eventually_core_floor_with_triples_rejoined hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_missed_tail_bound
  refine ⟨η,h,δ,ε,ζ,θ,c,κ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hr,hr1,hC,?_⟩
  filter_upwards [hspend,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hN
  obtain ⟨v,hvb,hY,hscale,hbase⟩ := hj
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
  let Ys := radialSupply N h v
  let Ts := radialTail S N R
  let B := wholeTail S N R
  let E := Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs
  let D := B\Ts
  have hDsub : D ⊆ S\(E ∪ Ts) := missed_subset (by omega : 1 ≤ N)
    (fun n hn => ZetaRieszLogCountTail.old_selection_count_le S η Q P V L (by omega) hh hhu hvb ((Finset.union_subset_union
        (Finset.union_subset_union (skip_first_three Xs Zs Hs Ys) (Finset.Subset.refl Fs))
          (Finset.Subset.refl Gs) hn)))
  have hnorm := hmissed N R S A y u hN (by linarith) hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ r^N*C at hnorm
  have hreal := (Complex.abs_re_le_norm _).trans hnorm
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hreal
  obtain ⟨hlo,hhi⟩ := abs_le.mp hreal
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [rest_split S E N R] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,hscale,?_⟩
  change u^(N+1)*((∑ n ∈ S\(E ∪ Ts ∪ B), f n).re+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(33/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r^N*C ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re
  change u^(N+1)*((∑ n ∈ S\(E ∪ Ts), f n).re+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(33/64 : ℝ)*(∑ n ∈ Ys, f n).re) ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hbase
  rw [← hre] at hbase
  nlinarith only [hbase,hlo]


/-- At every other count, rejoining the balanced triples changes no
original unpaid label. This checks the five/six budget compatibility. -/
theorem nontriple_rest_filter_eq (S : Finset ℕ) (N Q P V R : ℕ) (η h L : ℝ)
    (w : ℕ → ℝ) {k : ℕ} (hk : k ≠ 3) :
    (S\tripleRestSpent S N Q P V R η h L w).filter
      (fun n : ℕ => n.primeFactors.card = k) =
      (S\spent S N Q P V R η h L w).filter
        (fun n : ℕ => n.primeFactors.card = k) := by
  ext n
  have hnot (hc : n.primeFactors.card = k) : n ∉ radialTriples S N η := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have h3 := (Finset.mem_filter.mp hn).2.2.1
    exact hk (hc.symm.trans h3)
  simp only [tripleRestSpent,Finset.mem_filter,Finset.mem_sdiff]
  tauto

set_option maxHeartbeats 1600000 in
/-- The joined floor removes every unpaid triple, five-prime and six-prime
label. Balanced triples participate in the period cancellation, refunding
their old half-supply debit. The SAME original supply retains 65/128;
all other favorable credits and high-count savings remain. Counts four
and at least seven still require a numerical signed floor. -/
theorem eventually_joined_floor_without_triples_fives_or_sixes {u y : ℝ} (hu : 1/2 < u)
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
        let E356 := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6)
        let Eo := E\E356
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
            (65/128 : ℝ)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r₀,C₀,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ := eventually_core_full_floor_with_triples_rejoined hu hU hy
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩  :=
    ZetaRieszFiveSignCoverFloor.exists_unpaid_five_floor hu hU hy (by positivity : 0 < κ/3)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hsix⟩ := ZetaRieszSixSignCoverFloor.exists_unpaid_six_floor hu hU hy (by positivity : 0 < κ/3)
  obtain ⟨r₃,C₃,hr₃,hr₃1,hC₃,hthree⟩ := exists_unpaid_three_floor hu hU hy
    (by positivity : 0 < κ/3)
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
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+3*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂+2*r₃^(dyadicMomentOrder j)*C₃
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := ((((h₀.add heLim).add (hdLim.const_mul (3 : ℝ))).add h₁).add h₂).add h₃
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hsix,hthree,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
      with j hj hfive hsix hthree hbound hN
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
  let E356 := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6)
  let Eo := E\E356
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
  dsimp only at hp hq ht
  rw [←h5eq] at hp
  rw [←h6eq] at hq
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*(κ/3)*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  change -u^(N+1)*(κ/3)*units-d j-2*r₂^N*C₂ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E6, f n).re at hq
  change -u^(N+1)*(κ/3)*units-d j-2*r₃^N*C₃ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E3, f n).re at ht
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hp hq ht
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
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃ ≤
      u^(N+1)*((∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+(∑ n ∈ E6, f n).re) := by
    nlinarith only [hscaled,hp,hq,ht]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have h356 : E3 ∪ (E5 ∪ E6) = E356 := by
    ext n
    simp only [E3,E5,E6,E356,Finset.mem_union,Finset.mem_filter]
    tauto
  have hdis56 : Disjoint E5 E6 := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have h5 := (Finset.mem_filter.mp hn).2
    have h6 := (Finset.mem_filter.mp hm).2
    omega
  have hdis3 : Disjoint E3 (E5 ∪ E6) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have h3 := (Finset.mem_filter.mp hn).2
    rcases Finset.mem_union.mp hm with hm | hm
    · have h5 := (Finset.mem_filter.mp hm).2; omega
    · have h6 := (Finset.mem_filter.mp hm).2; omega
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨ n.primeFactors.card = 6) E)
      (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ E356, f n).re = (∑ n ∈ E, f n).re at hs
  rw [←h356,Finset.sum_union hdis3,Finset.sum_union hdis56,Complex.add_re,Complex.add_re] at hs
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
  have hfinal : u^(N+1)*(W+G+credits+(65/128 : ℝ)*(∑ n ∈ Ys, f n).re)-
      (r₀^N*C₀+e j+3*d j+2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaid,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring

/-- The new main remainder contains exactly the unresolved count four
or the high-count band. No low-count zero atom is hidden in that statement. -/
theorem remaining_count_cases {u : ℝ} {N K Q P V R n : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ)
    (hn : n ∈ (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w)\
      (coreBand u N K\tripleRestSpent (coreBand u N K) N Q P V R η h L w).filter
        (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨ n.primeFactors.card = 6)) :
    n.primeFactors.card = 4 ∨ 7 ≤ n.primeFactors.card := by
  obtain ⟨hnE,hnot⟩ := Finset.mem_sdiff.mp hn
  have hncore := (Finset.mem_sdiff.mp hnE).1
  have hnar := (Finset.mem_filter.mp hncore).1
  have hnon := (Finset.mem_filter.mp hnar).1
  have hret := (Finset.mem_sdiff.mp hnon).1
  have horig := (Finset.mem_sdiff.mp hret).1
  have hcount := (Finset.mem_filter.mp (Finset.mem_filter.mp horig).1).2.1
  have hcounts : ¬(n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨ n.primeFactors.card = 6) :=
    fun hc => hnot (Finset.mem_filter.mpr ⟨hnE,hc⟩)
  omega

end RiemannGaussian.ZetaRieszThreeSignCoverFloor
