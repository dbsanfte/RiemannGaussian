/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveSignCoverFloor

set_option autoImplicit false

/-!
# Paying the remaining six-prime contribution in the joined floor

The old six-prime head uses one threshold P for both arithmetic signs.
Every remaining six-prime label in the radial interior is therefore P-rough.
We retain the exact phase, two hinges, owner allocation and physical masks,
and use the existing complete-period estimate on its five-prime cofactor.
This module targets a signed inequality for the current unpaid carrier.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSixSignCoverFloor
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

/-- Five-prime cofactors above the old six-prime head threshold. -/
def roughCofactors (B : ℕ) (v : ℝ) : Finset ℕ :=
  (cofactors 5 v).filter (fun a => ∀ r ∈ a.primeFactors, B < r)

/-- Complete largest-prime phase periods with their literal rough cofactors. -/
def roughPeriod (B : ℕ) (v y : ℝ) : Finset ℕ :=
  (roughCofactors B v).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))

theorem roughPeriod_data {B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod B v y) :
    Squarefree n ∧ n.primeFactors.card = 6 ∧ ∀ r ∈ n.primeFactors, B < r := by
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

theorem rough_six_not_spent (S : Finset ℕ) {N Q P V R B n : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hP : P ≤ B) (hc : n.primeFactors.card = 6)
    (hrough : ∀ r ∈ n.primeFactors, B < r) : n ∉ spent S N Q P V R η h L w := by
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
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.2.2
    rcases hm with ⟨_,r,hr,hrP⟩ | ⟨h5,_⟩
    · exact (not_lt_of_ge (hrP.trans hP)) (hrough r hr)
    · omega
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
  simp only [spent,Finset.mem_union]
  tauto

theorem roughPeriod_subset_unpaid (S : Finset ℕ) {N Q P V R B : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L v y : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hP : P ≤ B) (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hcore : roughPeriod B v y ⊆ S) :
    roughPeriod B v y ⊆ S\spent S N Q P V R η h L w := by
  intro n hn
  have hd := roughPeriod_data hv hy hn
  exact Finset.mem_sdiff.mpr ⟨hcore hn,
    rough_six_not_spent S hN η hh hhu w hw hP hd.2.1 hd.2.2⟩

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
    (k := 5) (by norm_num) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors B v) hlo hhi (Finset.filter_subset _ _) hpeak hsign

theorem owner_gap_mem_roughPeriod {B a p : ℕ} {v y : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = 5) (hp : p.Prime)
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
  have ham : a ∈ cofactors 5 v :=
    (mem_cofactors_iff_of_count_le (by norm_num) (by linarith)).mpr ⟨ha,hc,hla,ho⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨ham,hrough⟩,
    Finset.mem_image.mpr ⟨p,?_,Nat.mul_comm a p⟩⟩
  apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
  rw [hlog] at hT
  refine ⟨hp,by linarith only [hT.1],?_⟩
  rw [show v-Real.pi/y-Real.log a+2*Real.pi/y = v+Real.pi/y-Real.log a by ring]
  linarith only [hT.2]

private theorem six_owner_data {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 6) :
    let p := ZetaRieszPrimeEndpoint.largestPrime n
    let a := n/p;
    p.Prime ∧ p*a = n ∧ Squarefree a ∧ a.primeFactors.card = 5 ∧
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
  have hcard : a.primeFactors.card = 5 := by
    rw [hpf,Finset.card_insert_of_notMem hnot] at hc
    omega
  have hmax q (hq : q ∈ n.primeFactors) : q ≤ p := by
    dsimp [p,ZetaRieszPrimeEndpoint.largestPrime]
    rw [dif_pos (Finset.card_pos.mp (by omega : 0 < n.primeFactors.card))]
    exact Finset.le_max' _ q hq
  exact ⟨hpp,he,ha,hcard,hp,hmax,hnot⟩

private theorem no_close_owner_gap {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 6) (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      Real.log q ≤ Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-1/8 := by
  obtain ⟨hpp,he,ha,_,hp,hmax,hnot⟩ := six_owner_data hs hc
  intro q hq
  by_contra hh
  have hqn : q ∈ n.primeFactors := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    hs.ne_zero
  apply hntie
  refine ⟨_,hp,q,hqn,?_,hmax,lt_of_not_ge hh⟩
  intro h
  exact hnot (h ▸ hq)

/-- Both arithmetic signs of an unpaid six-prime interior label have
all factors above the original six-prime threshold. -/
theorem unpaid_six_rough (S : Finset ℕ) {N n Q P V R : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) (hN : 4000 ≤ N) (hnS : n ∈ S)
    (hnot : n ∉ spent S N Q P V R η h L w) (hs : Squarefree n)
    (hc : n.primeFactors.card = 6)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N) :
    ∀ r ∈ n.primeFactors, P < r := by
  intro r hr
  by_contra hn
  have hG := ZetaRieszFiveNegativeHead.mem_radialHeads_of_geometry
    (P := P) (V := V) (L := L) hN hnS hs hlo hhi
      (Or.inl ⟨hc,r,hr,le_of_not_gt hn⟩)
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

/-- Both signs of the literal unpaid six-prime contribution are covered
by complete ordinary-prime periods, apart from explicit unmatched parts. -/
theorem eventually_unpaid_six_sign_floor {u y ε : ℝ}
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
      let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 6)
      let X := fun i => roughPeriod P (center v y i) y
      let Y := fun i => roughPeriod P (center (v+Real.pi/y) y i) y;
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
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 6)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hcount : 5+1 < dyadicPrimeCount j := by
    dsimp [dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ} (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod P c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    have hcore : roughPeriod P c y ⊆ S :=
      ZetaRieszTransitionFiveFloor.owned_subset_core (k := 5) (by norm_num)
        j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        hlo hhi (roughCofactors P c) (Finset.filter_subset _ _)
    have hunpaid := roughPeriod_subset_unpaid (Q := Q) (V := V) (R := R)
      (L := L) S hlarge η hh hhu w hw
      (le_refl P) hc hy hcore
    intro n hn
    exact Finset.mem_filter.mpr ⟨hunpaid hn,(roughPeriod_data hc hy hn).2.1⟩
  let X := fun i => roughPeriod P (center v y i) y
  let Y := fun i => roughPeriod P (center (v+Real.pi/y) y i) y
  have hvI i (hi : i ∈ I) : 100 ≤ center v y i := by linarith only [hNR,hpi,(hI i hi).1]
  have hvJ i (hi : i ∈ J) : 100 ≤ center (v+Real.pi/y) y i := by linarith only [hNR,hpi,(hJ i hi).1]
  have hdisjoint (b : ℝ) {i l : ℕ} (hil : i ≠ l)
      (hi : 100 ≤ center b y i) (hl : 100 ≤ center b y l) :
      Disjoint (roughPeriod P (center b y i) y) (roughPeriod P (center b y l) y) := by
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
      simpa only [neg_mul] using hpos P _ (hI i hi).1 (hI i hi).2 hp.1 (by rw [hp.2]; norm_num))
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).2
      simpa only [neg_mul] using hneg P _ (hJ i hi).1 (hJ i hi).2 hp.1 (by rw [hp.2]; norm_num))
  simpa only [← Finset.mul_sum,← mul_add] using hb

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
    (hc : n.primeFactors.card = 6)
    (hlo : (244/125 : ℝ)*dyadicMomentOrder j < Real.log n)
    (hhi : Real.log n ≤ (2029/1000 : ℝ)*dyadicMomentOrder j)
    (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    let N := dyadicMomentOrder j
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N;
    (signedPart 1 A L y N n = 0 ∨
      n ∈ (completeGrid N (Real.pi/y) y).biUnion
        (fun i => roughPeriod P (center (Real.pi/y) y i) y)) ∧
    (signedPart (-1) A L y N n = 0 ∨
      n ∈ (completeGrid N (Real.pi/y+Real.pi/y) y).biUnion
        (fun i => roughPeriod P (center (Real.pi/y+Real.pi/y) y i) y)) := by
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
  obtain ⟨hpp,he,ha,hac,hp,hmax,_⟩ := six_owner_data hs hc
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
  have hrough := unpaid_six_rough S η h L w hN
    (Finset.mem_filter.mp hn).1 hnot hs hc hlo hhi
  have hrougha (q : ℕ) (hq : q ∈ a.primeFactors) : P < q := by
    have hqn : q ∈ n.primeFactors := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hq).trans
        (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))) hs.ne_zero
    exact hrough q hqn
  have hhpos := owner_gap_mem_roughPeriod (B := P) hv hy ha hac hpp
    (he.symm ▸ hTi) hshare hgap hrougha
  have hhneg := owner_gap_mem_roughPeriod (B := P) hv' hy ha hac hpp
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

/-- The entire actual unpaid six-prime sector has a signed floor
with arbitrarily small complete-period debit and source-geometric errors.
No coefficient sign or six-prime interior geometry remains unmatched. -/
theorem exists_unpaid_six_floor {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ),
        0 < h → h ≤ 1/20 →
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 6)
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
  filter_upwards [eventually_unpaid_six_sign_floor hu hU hy (half_pos hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszOwnerTieFloor.eventually_core_grouped_tie_floor hu hU (half_pos hε)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hperiod htie hN hj Q P V R η h w hh hhu hw
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 6)
  let dom := fun n : ℕ => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
      (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let D := E.filter dom
  let F := (E\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N < Real.log n ∧
    Real.log n ≤ (2029/1000 : ℝ)*N))
  let T := ((E\D)\F).filter (fun n => Squarefree n ∧ ZetaRieszOwnerTieFloor.CloseOwners n)
  let I := completeGrid N (Real.pi/y) y
  let J := completeGrid N (Real.pi/y+Real.pi/y) y
  let X := I.biUnion (fun i => roughPeriod P (center (Real.pi/y) y i) y)
  let Y := J.biUnion (fun i => roughPeriod P (center (Real.pi/y+Real.pi/y) y i) y)
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
    exact interior_parts_covered j hj u hy η h w hN
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

/-- The same original supply jointly pays ALL originally unpaid five-
and six-prime labels, leaving 1/128 unspent. All prior favorable credits and
higher-count savings remain. The numerical -79/1000 floor is still open. -/
theorem eventually_joined_floor_without_fives_or_sixes {u y : ℝ} (hu : 1/2 < u)
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
        let E := S\spent S N Q P V R η h L w
        let E56 := E.filter (fun n : ℕ => n.primeFactors.card = 5 ∨ n.primeFactors.card = 6)
        let Eo := E\E56
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
            (∑ n ∈ Ys, f n).re/128)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r₀,C₀,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ := eventually_core_full_floor_with_scale hu hU hy
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩  :=
    ZetaRieszFiveSignCoverFloor.exists_unpaid_five_floor hu hU hy (half_pos hκ)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hsix⟩ := exists_unpaid_six_floor hu hU hy (half_pos hκ)
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
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+2*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (((h₀.add heLim).add (hdLim.const_mul (2 : ℝ))).add h₁).add h₂
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hsix,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1 : ℕ))]
      with j hj hfive hsix hbound hN
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
  let E := S\spent S N Q P V R η h L w
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let E6 := E.filter (fun n : ℕ => n.primeFactors.card = 6)
  let E56 := E.filter (fun n : ℕ => n.primeFactors.card = 5 ∨ n.primeFactors.card = 6)
  let Eo := E\E56
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  have hp := hfive Q P V R η h w hh hhu hw
  have hq := hsix Q P V R η h w hh hhu hw
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*(κ/2)*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  change -u^(N+1)*(κ/2)*units-d j-2*r₂^N*C₂ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E6, f n).re at hq
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hp hq
  have hbudget := period_grids_cost_paid hN hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-2*d j-
      2*r₁^N*C₁-2*r₂^N*C₂ ≤
      u^(N+1)*((∑ n ∈ E5, f n).re+(∑ n ∈ E6, f n).re) := by
    nlinarith only [hscaled,hp,hq]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have h56 : E5 ∪ E6 = E56 := by
    ext n
    simp only [E5,E6,E56,Finset.mem_union,Finset.mem_filter]
    tauto
  have hdis : Disjoint E5 E6 := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have h5 := (Finset.mem_filter.mp hn).2
    have h6 := (Finset.mem_filter.mp hm).2
    omega
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 5 ∨ n.primeFactors.card = 6) E) (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ E56, f n).re = (∑ n ∈ E, f n).re at hs
  rw [←h56,Finset.sum_union hdis,Complex.add_re] at hs
  let credits := max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+
    max (∑ n ∈ Zs, f n).re 0+max (∑ n ∈ Hs, f n).re 0+
    max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+
    max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(∑ n ∈ Ys, f n).re/64)-r₀^N*C₀ ≤
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
  have hfinal : u^(N+1)*(W+G+credits+(∑ n ∈ Ys, f n).re/128)-
      (r₀^N*C₀+e j+2*d j+2*r₁^N*C₁+2*r₂^N*C₂) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaid,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring

end RiemannGaussian.ZetaRieszSixSignCoverFloor
