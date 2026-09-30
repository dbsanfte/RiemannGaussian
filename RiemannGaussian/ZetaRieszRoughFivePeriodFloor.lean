/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerTieFloor
import RiemannGaussian.ZetaRieszPairChamberFloor

set_option autoImplicit false

/-!
# Complete rough five-prime fibres inside the existing unpaid remainder

Roughness is a cofactor mask when the running prime is the unique largest.
The previously spent small-prime five-factor heads cannot clip such a fibre
once its cutoff exceeds both old thresholds. All other old charges have a
different count. The signed period floor therefore applies inside the actual
unpaid ledger, retaining both hinges, allocation and phase.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszRoughFivePeriodFloor
open ZetaRieszFixedCountPeriod ZetaRieszSignedPeriodFloor ZetaRieszStaggeredFloor
open ZetaRieszMultiPeriodSix
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead

/-- The original four-prime cofactor population, with only a roughness
filter. No arithmetic sign or phase is used to select it. -/
def roughCofactors (B : ℕ) (v : ℝ) : Finset ℕ :=
  (cofactors 4 v).filter (fun a => ∀ r ∈ a.primeFactors, B < r)

/-- Complete ordinary-prime periods with the original cofactor geometry. -/
def roughPeriod (B : ℕ) (v y : ℝ) : Finset ℕ :=
  (roughCofactors B v).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))

/-- Every complete fibre is exactly five-prime and rough, including the
running owner prime. The roughness mask creates no prime-period hole. -/
theorem roughPeriod_data {B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod B v y) :
    Squarefree n ∧ n.primeFactors.card = 5 ∧ ∀ r ∈ n.primeFactors, B < r := by
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

/-- Exactly the spent-label union of the current compensated floor.
This is a support abbreviation, not a replacement carrier or new budget. -/
def spent (S : Finset ℕ) (N Q P V R : ℕ) (η h L : ℝ) (w : ℕ → ℝ) : Finset ℕ :=
  let X := radialTriples S N η
  let Z := (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q)
  let H := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Y := radialSupply N h w
  let F := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let G := radialHeads S N P V L
  let T := ZetaRieszSevenCountTail.radialTail S N R
  let C := ZetaRieszSevenCountTail.wholeTail S N R
  X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ T ∪ C

/-- Supply labels retain count four throughout the literal radial core. -/
theorem radialSupply_count {N : ℕ} (hN : 1000 ≤ N) {h : ℝ} (hh : 0 < h)
    (hhu : h ≤ 1/20) (w : ℕ → ℝ)
    (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    {n : ℕ} (hn : n ∈ radialSupply N h w) : n.primeFactors.card = 4 := by
  obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hm := (Finset.mem_filter.mp hM).2.1
  have hnR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hsize : h+w M ≤ (M : ℝ)/1000 := by linarith [(hw M hM).2]
  exact tuple_count hh hi hj hk (hw M hM).1 hsize hp

/-- A rough five-prime label misses EVERY previously spent class. Both
small-prime thresholds are retained separately; no favourable credit is
spent twice when its full owner fibre is added to the new floor. -/
theorem rough_five_not_spent (S : Finset ℕ) {N Q P V R B n : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hQ : Q ≤ B) (hV : V ≤ B) (hc : n.primeFactors.card = 5)
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
    obtain ⟨_,_,_,_,_,⟨r,hr,hrQ⟩,_⟩ := (Finset.mem_filter.mp hn).2
    exact (not_lt_of_ge (hrQ.trans hQ)) (hrough r hr)
  have hG : n ∉ radialHeads S N P V L := by
    intro hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    have hm := (Finset.mem_filter.mp hn).2.2.2.2
    rcases hm with ⟨h6,_⟩ | ⟨_,_,r,hr,hrV⟩
    · omega
    · exact (not_lt_of_ge (hrV.trans hV)) (hrough r hr)
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

/-- The complete original rough periods are contained in the current
unpaid remainder. Earlier radial/head/supply credits create no fibre holes
on this sector once the rough threshold exceeds both old five-prime heads. -/
theorem roughPeriod_subset_unpaid (S : Finset ℕ) {N Q P V R B : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L v y : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hQ : Q ≤ B) (hV : V ≤ B) (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hcore : roughPeriod B v y ⊆ S) :
    roughPeriod B v y ⊆ S\spent S N Q P V R η h L w := by
  intro n hn
  have hd := roughPeriod_data hv hy hn
  exact Finset.mem_sdiff.mpr ⟨hcore hn,
    rough_five_not_spent S hN η hh hhu w hw hQ hV hd.2.1 hd.2.2⟩

/-- The signed five-prime complete-period floor applies to the actual
rough mask, with both Riesz hinges and the full original allocation. -/
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
  filter_upwards [eventually_core_part_floor (k := 4) (by norm_num) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors B v) hlo hhi (Finset.filter_subset _ _) hpeak hsign

/-- Complete rough five-prime periods act directly on the five-prime part
of the CURRENT unpaid remainder. Core inclusion and all previously spent
label exclusions are proved, rather than assumed as cancellation premises.
Both arithmetic signs, both grids and the exact unmatched parts are retained.
The debit is relative to the radial units, not yet a source-scale bound. -/
theorem eventually_unpaid_rough_five_floor {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R B : ℕ) (η h : ℝ) (w : ℕ → ℝ)
      (I J : Finset ℕ) (v : ℝ),
      0 < h → h ≤ 1/20 →
      (∀ M ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        0 ≤ w M ∧ w M ≤ 1/2) → Q ≤ B → V ≤ B →
      Real.cos (y*v) = -1 →
      (∀ i ∈ I, (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
          center v y i-Real.pi/y ∧ center v y i+Real.pi/y ≤
            (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      (∀ i ∈ J, (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
          center (v+Real.pi/y) y i-Real.pi/y ∧ center (v+Real.pi/y) y i+Real.pi/y ≤
            (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
      let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
      let X := fun i => roughPeriod B (center v y i) y
      let Y := fun i => roughPeriod B (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart 1 A L y N n)+
        (∑ n ∈ E\J.biUnion Y, signedPart (-1) A L y N n)-
        ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (∑ n ∈ E, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hroom : u < Real.exp (-(11/16 : ℝ)) :=
    hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_staggered_floor (k := 4) (by norm_num) hu hU hy hε),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)]
      with j hperiod hL hlarge hj Q P V R B η h w I J v hh hhu hw hQ hV hpeak hI hJ
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hpi : 0 ≤ Real.pi/y := by positivity
  have hcount : 4+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    dsimp [ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ}
      (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod B c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    have hcore : roughPeriod B c y ⊆ S :=
      owned_subset_core (k := 4) (by norm_num) j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        hlo hhi (roughCofactors B c) (Finset.filter_subset _ _)
    have hunpaid := roughPeriod_subset_unpaid (P := P) (R := R) (L := L)
      S hlarge η hh hhu w hw hQ hV hc hy hcore
    intro n hn
    exact Finset.mem_filter.mpr ⟨hunpaid hn,(roughPeriod_data hc hy hn).2.1⟩
  have hb := hperiod E I J v
    (fun i => roughCofactors B (center v y i))
    (fun i => roughCofactors B (center (v+Real.pi/y) y i))
    hpeak hI hJ (fun _ _ => Finset.filter_subset _ _) (fun _ _ => Finset.filter_subset _ _)
  dsimp only at hb ⊢
  exact hb (fun i hi => howned (hI i hi).1 (hI i hi).2)
    (fun i hi => howned (hJ i hi).1 (hJ i hi).2)

/-- A phase grid has only a height-dependent number of centers in a
two-unit radial slab. This pays growing grids locally, not by their
whole-core cardinality. The deliberately coarse constant is sufficient. -/
theorem period_card_bound (I : Finset ℕ) {v y t : ℝ} (hy : 54 ≤ y)
    (hI : ∀ i ∈ I, t ≤ center v y i ∧ center v y i ≤ t+2) :
    I.card ≤ ⌊2*y⌋₊+1 := by
  by_cases hne : I.Nonempty
  · let i₀ := I.min' hne
    have hi₀ : i₀ ∈ I := Finset.min'_mem I hne
    have hmin i (hi : i ∈ I) : i₀ ≤ i := Finset.min'_le I i hi
    have hy0 : 0 < y := by linarith
    have hstep : 0 < 2*Real.pi/y := by positivity
    have hsub i (hi : i ∈ I) : i-i₀ ≤ ⌊2*y⌋₊ := by
      have hh : center v y i-center v y i₀ ≤ 2 := by
        linarith only [(hI i hi).2,(hI i₀ hi₀).1]
      have hd : ((i-i₀ : ℕ) : ℝ) = (i : ℝ)-i₀ := Nat.cast_sub (hmin i hi)
      have hb : ((i-i₀ : ℕ) : ℝ)*(2*Real.pi/y) ≤ 2 := by
        dsimp only [center] at hh
        rw [abs_of_pos hy0] at hh
        rw [hd]
        ring_nf at hh ⊢
        linarith only [hh]
      have hc : ((i-i₀ : ℕ) : ℝ)*(2*Real.pi) ≤ 2*y := by
        rw [← mul_div_assoc] at hb
        exact (div_le_iff₀ hy0).mp hb
      apply Nat.le_floor
      have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
      nlinarith only [hc,mul_le_mul_of_nonneg_left hpi (Nat.cast_nonneg (i-i₀))]
    have hc := Finset.card_le_card_of_injOn (fun i => i-i₀)
      (s := I) (t := Finset.range (⌊2*y⌋₊+1))
      (by intro i hi; exact Finset.mem_range.mpr (Nat.lt_add_one_of_le (hsub i hi)))
      (by
        intro i hi j hj he
        change i-i₀ = j-i₀ at he
        have := hmin i hi
        have := hmin j hj
        omega)
    simpa only [Finset.card_range] using hc
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

/-- Radial units at nearby period centers are comparable to the same
actual supply slab, with the ORIGINAL moment order unchanged. -/
theorem radial_unit_le_slab {N M : ℕ} (hM : 0 < M) (hNM : N ≤ 2*M)
    {t : ℝ} (hlo : 2*(M : ℝ) ≤ t) (hhi : t ≤ 2*M+2) :
    Real.exp (-t/2)*t^N/N.factorial ≤
      Real.exp 2*(Real.exp (2*(M : ℝ))*radialEnvelope N M) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have ht : 0 < t := by linarith
  have hnm : (N : ℝ) ≤ 2*M := by exact_mod_cast hNM
  have hratio : t/(2*(M : ℝ)) ≤ Real.exp (1/(M : ℝ)) := by
    have hr : t/(2*(M : ℝ)) ≤ 1+1/(M : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      field_simp
      nlinarith only [hhi]
    exact hr.trans (by simpa only [add_comm] using Real.add_one_le_exp (1/(M : ℝ)))
  have hp := pow_le_pow_left₀ (div_nonneg ht.le (by positivity)) hratio N
  rw [div_pow,← Real.exp_nat_mul] at hp
  have he : (N : ℝ)*(1/(M : ℝ)) ≤ 2 := by
    rw [mul_one_div]
    exact (div_le_iff₀ hMR).mpr hnm
  have hpow : t^N ≤ Real.exp 2*(2*(M : ℝ))^N :=
    (div_le_iff₀ (by positivity)).mp (hp.trans (Real.exp_le_exp.mpr he))
  have hexp : Real.exp (-t/2) ≤ Real.exp (-(M : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul hexp hpow (pow_nonneg ht.le _) (Real.exp_nonneg _))
    (show 0 ≤ (N.factorial : ℝ) by positivity)
  have he : Real.exp (2*(M : ℝ))*Real.exp (-3*(M : ℝ)) = Real.exp (-(M : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact hb.trans_eq (by unfold radialEnvelope; rw [← he]; ring)

/-- On each actual supply slab, ALL complete rough five-prime periods on
both grids can be paid by 1/128 of its positive four-prime supply. The
precision is fixed before N, so the debit does not grow with the number
of radial cells. The phase condition is the existing elementary supply
window, not a new arithmetic cancellation premise. -/
theorem eventually_period_debit_paid {u y h : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hh : 0 < h) (hhu : h ≤ 1/20) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∀ M ∈ radialIndices N,
      ∀ (I J : Finset ℕ) (v w : ℝ),
      0 ≤ w → w ≤ 1/2 →
      (∀ t : ℝ, 2*M+w ≤ t → t ≤ 2*M+w+4*h →
        Real.cos (y*t) ≤ -(1/2 : ℝ)) →
      (∀ i ∈ I, 2*(M : ℝ) ≤ center v y i ∧ center v y i ≤ 2*M+2) →
      (∀ i ∈ J, 2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
        center (v+Real.pi/y) y i ≤ 2*M+2) →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N;
      ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
        (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
          (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
      (1/128 : ℝ)*(∑ n ∈ supply M h w,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨c,hc,hsupply⟩ := eventually_supply_lower hh hhu
  let D : ℝ := ⌊2*y⌋₊+1
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := c/(512*D*Real.exp 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  filter_upwards [hsupply,eventually_length_on_slabs hu hU,eventually_ge_atTop (2 : ℕ)]
    with N hs hL hN M hM I J v w hw hwu hphase hI hJ
  dsimp only
  have hm0 : 0 < M := by
    have hm := (Finset.mem_filter.mp hM).2.1
    have hnR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hmR : (0 : ℝ) < M := by linarith
    exact_mod_cast hmR
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hm0
  have hNM := (hL M hM).1
  have hL0 : 0 < SquarefreeVaughanLogSource.length u N := by
    linarith [(hL M hM).2.1]
  have hp := hs M (ZetaRieszAnnulusJoint.intermediatePrimes u N) w
    (SquarefreeVaughanLogSource.length u N) y hNM hw hwu hL0
      (hL M hM).2.1 (hL M hM).2.2 hphase
  let U := Real.exp (2*(M : ℝ))*radialEnvelope N M
  have hU0 : 0 ≤ U := by dsimp [U]; positivity [radialEnvelope_nonneg N M]
  have hlower : (c/2)*U ≤ (∑ n ∈ supply M h w,
      ZetaRieszJointAllocation.residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    apply le_trans _ hp
    have hratio : (1/2 : ℝ) ≤ (M : ℝ)/(M+1) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hc.le) hU0
    convert hb using 1 <;> dsimp only [U] <;> ring
  have hcI : (I.card : ℝ) ≤ D := by dsimp [D]; exact_mod_cast period_card_bound I hy hI
  have hcJ : (J.card : ℝ) ≤ D := by dsimp [D]; exact_mod_cast period_card_bound J hy hJ
  have hi := Finset.sum_le_sum (fun i hi => radial_unit_le_slab hm0 hNM (hI i hi).1 (hI i hi).2)
  have hj := Finset.sum_le_sum (fun i hi => radial_unit_le_slab hm0 hNM (hJ i hi).1 (hJ i hi).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hi hj
  have hib : (∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial) ≤
      D*Real.exp 2*U := by
    exact hi.trans (by dsimp only [U]; nlinarith only
      [mul_le_mul_of_nonneg_right hcI (mul_nonneg (Real.exp_nonneg 2) hU0)])
  have hjb : (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
      (center (v+Real.pi/y) y i)^N/N.factorial) ≤ D*Real.exp 2*U := by
    exact hj.trans (by dsimp only [U]; nlinarith only
      [mul_le_mul_of_nonneg_right hcJ (mul_nonneg (Real.exp_nonneg 2) hU0)])
  have hbudget := mul_le_mul_of_nonneg_left (add_le_add hib hjb) hε.le
  have heq : ε*(D*Real.exp 2*U+D*Real.exp 2*U) = (1/128 : ℝ)*((c/2)*U) := by
    dsimp [ε]
    field_simp
    ring
  rw [heq] at hbudget
  exact hbudget.trans (mul_le_mul_of_nonneg_left hlower (by norm_num))

/-- The actual elementary phase selection supplies the debit payment.
There is no unproved lower-bound premise for the prime population. -/
theorem exists_period_debit_supply {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h ε : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < ε ∧
      ∀ᶠ N : ℕ in atTop, ∀ M ∈ radialIndices N, ∃ w : ℝ,
        0 ≤ w ∧ w ≤ 1/2 ∧
        (∀ t : ℝ, 2*M+w ≤ t → t ≤ 2*M+w+4*h →
          Real.cos (y*t) ≤ -(1/2 : ℝ)) ∧
        ∀ (I J : Finset ℕ) (v : ℝ),
          (∀ i ∈ I, 2*(M : ℝ) ≤ center v y i ∧ center v y i ≤ 2*M+2) →
          (∀ i ∈ J, 2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
            center (v+Real.pi/y) y i ≤ 2*M+2) →
          let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
          let L := SquarefreeVaughanLogSource.length u N;
          ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
            (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
              (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
          (1/128 : ℝ)*(∑ n ∈ supply M h w,
            ZetaRieszJointAllocation.residualCoefficient A L N n*
              zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  obtain ⟨h,hh,hhu,hphase⟩ := exists_short_negative_window
    (by rw [hyabs]; linarith : 16 ≤ |y|)
  obtain ⟨ε,hε,hpay⟩ := eventually_period_debit_paid hu hU hy hh hhu
  refine ⟨h,ε,hh,hhu,hε,?_⟩
  filter_upwards [hpay] with N hN M hM
  obtain ⟨w,hw,hwu,hcos⟩ := hphase (2*(M : ℝ))
  exact ⟨w,hw,hwu,hcos,fun I J v hI hJ => hN M hM I J v w hw hwu hcos hI hJ⟩

/-- On the actual unpaid five-prime slab, 1/128 of the EXISTING phased
four-prime supply pays every selected complete-period debit. Both missing
arithmetic parts stay explicit. The supply phase is realized by
`exists_period_debit_supply`; count separation prevents reuse of its labels.
This removes the arbitrary period allowance from the joint inequality. -/
theorem eventually_unpaid_rough_five_supply_floor {u y h : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hh : 0 < h) (hhu : h ≤ 1/20) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R B M : ℕ) (η : ℝ) (w : ℕ → ℝ)
      (I J : Finset ℕ) (v : ℝ),
      (∀ m ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        0 ≤ w m ∧ w m ≤ 1/2) → Q ≤ B → V ≤ B →
      M ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      2*(M : ℝ)+2 ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j →
      (∀ t : ℝ, 2*M+w M ≤ t → t ≤ 2*M+w M+4*h →
        Real.cos (y*t) ≤ -(1/2 : ℝ)) → Real.cos (y*v) = -1 →
      (∀ i ∈ I, 2*(M : ℝ) ≤ center v y i-Real.pi/y ∧
        center v y i+Real.pi/y ≤ 2*M+2) →
      (∀ i ∈ J, 2*(M : ℝ) ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
        center (v+Real.pi/y) y i+Real.pi/y ≤ 2*M+2) →
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
      let E := (S\spent S N Q P V R η h L w).filter (fun n : ℕ =>
        n.primeFactors.card = 5 ∧ 2*(M : ℝ) < Real.log n ∧ Real.log n ≤ 2*M+2)
      let X := fun i => roughPeriod B (center v y i) y
      let Y := fun i => roughPeriod B (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart 1 A L y N n)+
        (∑ n ∈ E\J.biUnion Y, signedPart (-1) A L y N n) ≤
        (∑ n ∈ E, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (1/128 : ℝ)*(∑ n ∈ supply M h (w M),
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨ε,hε,hdebit⟩ := eventually_period_debit_paid hu hU hy hh hhu
  have hroom : u < Real.exp (-(11/16 : ℝ)) :=
    hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_staggered_floor (k := 4) (by norm_num) hu hU hy hε),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hdebit,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),eventually_ge_atTop (32 : ℕ)]
      with j hperiod hpay hL hlarge hj Q P V R B M η w I J v hw hQ hV hM hMhi hphase hpeak hI hJ
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n : ℕ =>
    n.primeFactors.card = 5 ∧ 2*(M : ℝ) < Real.log n ∧ Real.log n ≤ 2*M+2)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hpi : 0 ≤ Real.pi/y := by positivity
  have hMlo := (Finset.mem_filter.mp hM).2.1
  have hcount : 4+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    dsimp [ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ} (hlo : 2*(M : ℝ) ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ 2*M+2) : roughPeriod B c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi,hMlo]
    have hcore : roughPeriod B c y ⊆ S :=
      owned_subset_core (k := 4) (by norm_num) j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        (by linarith) (by linarith) (roughCofactors B c) (Finset.filter_subset _ _)
    have hunpaid := roughPeriod_subset_unpaid (P := P) (R := R) (L := L)
      S hlarge η hh hhu w hw hQ hV hc hy hcore
    intro n hn
    have hd := roughPeriod_data hc hy hn
    have ht := owned_log_support hc hy (roughCofactors B c) (Finset.filter_subset _ _) hn
    exact Finset.mem_filter.mpr ⟨hunpaid hn,hd.2.1,by linarith [ht.1],by linarith [ht.2]⟩
  have hf := hperiod E I J v
    (fun i => roughCofactors B (center v y i))
    (fun i => roughCofactors B (center (v+Real.pi/y) y i)) hpeak
      (by intro i hi; constructor <;> linarith [(hI i hi).1,(hI i hi).2])
      (by intro i hi; constructor <;> linarith [(hJ i hi).1,(hJ i hi).2])
      (fun _ _ => Finset.filter_subset _ _) (fun _ _ => Finset.filter_subset _ _)
      (fun i hi => howned (hI i hi).1 (hI i hi).2)
      (fun i hi => howned (hJ i hi).1 (hJ i hi).2)
  have hd := hpay M hM I J v (w M) (hw M hM).1 (hw M hM).2 hphase
    (by intro i hi; constructor <;> linarith [(hI i hi).1,(hI i hi).2])
    (by intro i hi; constructor <;> linarith [(hJ i hi).1,(hJ i hi).2])
  dsimp only [E,S,L,N,A,roughPeriod] at hf hd ⊢
  linarith only [hf,hd]

/-- A growing family of disjoint radial slabs uses AT MOST 1/128 of
the one original radial supply. There is no period allowance left in this
whole unpaid-five-prime inequality. Labels outside the chosen slabs and
both missed sign parts inside them are retained literally. -/
theorem eventually_radial_rough_five_supply_floor {u y h : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hh : 0 < h) (hhu : h ≤ 1/20) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R B : ℕ) (η : ℝ) (w : ℕ → ℝ)
      (H : Finset ℕ) (I J : ℕ → Finset ℕ) (v : ℝ),
      (∀ M ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        0 ≤ w M ∧ w M ≤ 1/2) → Q ≤ B → V ≤ B →
      H ⊆ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      (∀ M ∈ H, 2*(M : ℝ)+2 ≤
        (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      (∀ M ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        ∀ t : ℝ, 2*M+w M ≤ t → t ≤ 2*M+w M+4*h →
          Real.cos (y*t) ≤ -(1/2 : ℝ)) → Real.cos (y*v) = -1 →
      (∀ M ∈ H, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i-Real.pi/y ∧
        center v y i+Real.pi/y ≤ 2*M+2) →
      (∀ M ∈ H, ∀ i ∈ J M, 2*(M : ℝ) ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
        center (v+Real.pi/y) y i+Real.pi/y ≤ 2*M+2) →
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
      let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
      let D := fun M : ℕ => (S\spent S N Q P V R η h L w).filter (fun n : ℕ =>
        n.primeFactors.card = 5 ∧ 2*(M : ℝ) < Real.log n ∧ Real.log n ≤ 2*M+2)
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let X := fun i => roughPeriod B (center v y i) y
      let Y := fun i => roughPeriod B (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\H.biUnion D, f n).re+
        (∑ M ∈ H, ((∑ n ∈ D M\(I M).biUnion X, signedPart 1 A L y N n)+
          (∑ n ∈ D M\(J M).biUnion Y, signedPart (-1) A L y N n))) ≤
        (∑ n ∈ E, f n).re+(1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re := by
  obtain ⟨ε,_,hdebit⟩ := eventually_period_debit_paid hu hU hy hh hhu
  filter_upwards [eventually_unpaid_rough_five_supply_floor hu hU hy hh hhu,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hdebit]
      with j hlocal hpay Q P V R B η w H I J v hw hQ hV hH hMhi hphase hpeak hI hJ
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
  let D := fun M : ℕ => (S\spent S N Q P V R η h L w).filter (fun n : ℕ =>
    n.primeFactors.card = 5 ∧ 2*(M : ℝ) < Real.log n ∧ Real.log n ≤ 2*M+2)
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let X := fun i => roughPeriod B (center v y i) y
  let Y := fun i => roughPeriod B (center (v+Real.pi/y) y i) y
  have hnonneg M (hM : M ∈ radialIndices N) : 0 ≤ (∑ n ∈ supply M h (w M), f n).re := by
    have hz := hpay M hM ∅ ∅ 0 (w M) (hw M hM).1 (hw M hM).2
      (hphase M hM) (by simp) (by simp)
    dsimp only at hz
    simp only [Finset.sum_empty,zero_add,mul_zero] at hz
    change (0 : ℝ) ≤ (1/128 : ℝ)*(∑ n ∈ supply M h (w M), f n).re at hz
    linarith only [hz]
  have hYsum : (∑ M ∈ H, (∑ n ∈ supply M h (w M), f n).re) ≤
      (∑ n ∈ radialSupply N h w, f n).re := by
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hw),Complex.re_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hH (fun M hM _ => hnonneg M hM)
  have hDsub : H.biUnion D ⊆ E := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hn,hc,_⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn,hc⟩
  have hDd : (H : Set ℕ).PairwiseDisjoint D := by
    intro M _ M' _ hne
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have ht := (Finset.mem_filter.mp hn).2.2
    have ht' := (Finset.mem_filter.mp hn').2.2
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (M : ℝ)+1 ≤ M' := by exact_mod_cast h
      linarith only [ht.2,ht'.1,hh]
    · have hh : (M' : ℝ)+1 ≤ M := by exact_mod_cast h
      linarith only [ht'.2,ht.1,hh]
  have hledger := congrArg Complex.re (Finset.sum_sdiff hDsub (f := f))
  rw [Finset.sum_biUnion hDd,Complex.add_re,Complex.re_sum] at hledger
  have hlocal' M (hM : M ∈ H) :
      (∑ n ∈ D M\(I M).biUnion X, signedPart 1 A L y N n)+
        (∑ n ∈ D M\(J M).biUnion Y, signedPart (-1) A L y N n) ≤
        (∑ n ∈ D M, f n).re+(1/128 : ℝ)*(∑ n ∈ supply M h (w M), f n).re :=
    hlocal Q P V R B M η w (I M) (J M) v hw hQ hV (hH hM) (hMhi M hM)
      (hphase M (hH hM)) hpeak (hI M hM) (hJ M hM)
  have hsum := Finset.sum_le_sum hlocal'
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hsupply := mul_le_mul_of_nonneg_left hYsum (by norm_num : (0 : ℝ) ≤ 1/128)
  change (∑ n ∈ E\H.biUnion D, f n).re+
    (∑ M ∈ H, ((∑ n ∈ D M\(I M).biUnion X, signedPart 1 A L y N n)+
      (∑ n ∈ D M\(J M).biUnion Y, signedPart (-1) A L y N n))) ≤
      (∑ n ∈ E, f n).re+(1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re
  rw [Finset.sum_add_distrib]
  simp only [Complex.re_sum] at hledger hsum hsupply ⊢
  linarith only [hledger,hsum,hsupply]

/-- The explicit precision corresponding to ANY already proved positive
supply scale. This allows reuse of the exact earlier head selection,
without choosing another supply phase. -/
theorem period_debit_le_scale {c y : ℝ} (hc : 0 ≤ c) (hy : 54 ≤ y)
    {N M : ℕ} (hM : 0 < M) (hNM : N ≤ 2*M) (I J : Finset ℕ) (v : ℝ)
    (hI : ∀ i ∈ I, 2*(M : ℝ) ≤ center v y i ∧ center v y i ≤ 2*M+2)
    (hJ : ∀ i ∈ J, 2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
      center (v+Real.pi/y) y i ≤ 2*M+2) :
    (c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2))*
      ((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
        (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
          (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
      (c/256)*(Real.exp (2*(M : ℝ))*radialEnvelope N M) := by
  let D : ℝ := ⌊2*y⌋₊+1
  let U := Real.exp (2*(M : ℝ))*radialEnvelope N M
  have hD : 0 < D := by dsimp [D]; positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity [radialEnvelope_nonneg N M]
  have hcI : (I.card : ℝ) ≤ D := by dsimp [D]; exact_mod_cast period_card_bound I hy hI
  have hcJ : (J.card : ℝ) ≤ D := by dsimp [D]; exact_mod_cast period_card_bound J hy hJ
  have hi := Finset.sum_le_sum (fun i hi => radial_unit_le_slab hM hNM (hI i hi).1 (hI i hi).2)
  have hj := Finset.sum_le_sum (fun i hi => radial_unit_le_slab hM hNM (hJ i hi).1 (hJ i hi).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hi hj
  have hbi := mul_le_mul_of_nonneg_right hcI (mul_nonneg (Real.exp_nonneg 2) hU0)
  have hbj := mul_le_mul_of_nonneg_right hcJ (mul_nonneg (Real.exp_nonneg 2) hU0)
  have hsum :
      (∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
        (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
          (center (v+Real.pi/y) y i)^N/N.factorial) ≤ 2*D*Real.exp 2*U := by
    dsimp only [U] at hbi hbj ⊢
    nlinarith only [hi,hj,hbi,hbj]
  have hcost := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ c/(512*D*Real.exp 2) by positivity)
  have he : (c/(512*D*Real.exp 2))*(2*D*Real.exp 2*U) = (c/256)*U := by
    field_simp
    ring
  rw [he] at hcost
  exact hcost

/-- All previous slab charges and the new complete-period charges share
ONE actual prime supply, with an explicit 1/128 reserve remaining. The
previous norm charges, chosen widths and supply scale are retained. In
particular no compatibility between two unrelated existential supply
choices is assumed. The final inequality is on the joined cost itself. -/
theorem eventually_joint_slabs_floor_with_period_budget {y : ℝ} (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ c κ : ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧
      0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 < c ∧ 0 < κ ∧
      κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q P V W : ℕ) (D S H F G T A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → M ≤ 2*N → Real.log Q ≤ δ*N → Real.log P ≤ ε*N →
        Real.log V ≤ ζ*N → Real.log W ≤ θ*N → 0 < L →
        (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*M+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧
            ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*M+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧
          (∃ r ∈ n.primeFactors, r ≤ Q) ∧
            0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*M+2 ∧
          headCondition L P V n) →
        (∀ n ∈ T, Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*M+2 ∧
          ZetaRieszSevenPrimeHead.tailCondition N W n) →
        ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1/2 ∧
          let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := (∑ n ∈ supply M h w, f n).re;
          c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤ Y ∧
          0 < Y ∧
          ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
          ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
          ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
          ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
          ‖∑ n ∈ G, f n‖ ≤ (3/32 : ℝ)*Y ∧
          ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*Y ∧
          ∀ (I J : Finset ℕ) (v : ℝ),
            (∀ i ∈ I, 2*(M : ℝ) ≤ center v y i ∧ center v y i ≤ 2*M+2) →
            (∀ i ∈ J, 2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
              center (v+Real.pi/y) y i ≤ 2*M+2) →
            ‖∑ n ∈ slabTriples D M η, f n‖+‖∑ n ∈ smallTriples S M Q, f n‖+
              ‖∑ n ∈ H, f n‖+‖∑ n ∈ F, f n‖+‖∑ n ∈ G, f n‖+‖∑ n ∈ T, f n‖+
              κ*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
                (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
                  (center (v+Real.pi/y) y i)^N/N.factorial)) ≤ (127/128 : ℝ)*Y := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    eventually_joint_slabs_spending_log_head_with_scale
      (by rw [hyabs]; linarith : 16 ≤ |y|)
  obtain ⟨ε,ζ,hε,hεu,hζ,hζu,hsmall⟩ := eventually_mixed_log_cost
    (show 0 < 3*c/32 by positivity)
  obtain ⟨θ,hθ,hθu,htail⟩ := ZetaRieszSevenPrimeHead.eventually_seven_and_count_cost
    (show 0 < c/64 by positivity)
  let κ := c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,rfl,?_⟩
  filter_upwards [hpay,hsmall,htail,eventually_ge_atTop (2 : ℕ)]
    with N hpay hsmall htail hN M Q P V W D S H F G T A L hNM hMN hQ hP hV hW hL0 hL hLu hH hF hG hT
  obtain ⟨w,hw,hwu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  have hGcost := hsmall M P V G A L y hNM hP hV hL0 hL hG
  have hTcost := htail M W T A L y hNM hMN hW hL0 hL hT
  have hGpay : ‖∑ n ∈ G, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ (3/32 : ℝ)*
        (∑ n ∈ supply M h w, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    have hb := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 3/32)
    exact hGcost.trans (by convert hb using 1; ring)
  have hTpay : ‖∑ n ∈ T, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ (1/64 : ℝ)*
        (∑ n ∈ supply M h w, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    have hb := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/64)
    exact hTcost.trans (by convert hb using 1; ring)
  refine ⟨w,hw,hwu,hscale,hY,hX,hZ,hHpay,hFpay,hGpay,hTpay,?_⟩
  intro I J v hI hJ
  dsimp only
  have hm0 : 0 < M := by omega
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hm0
  let U := Real.exp (2*(M : ℝ))*radialEnvelope N M
  have hU0 : 0 ≤ U := by dsimp [U]; positivity [radialEnvelope_nonneg N M]
  have hlower : (c/2)*U ≤ (∑ n ∈ supply M h w,
      ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    apply le_trans _ hscale
    have hr : (1/2 : ℝ) ≤ (M : ℝ)/(M+1) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hc.le) hU0
    convert hb using 1 <;> dsimp only [U] <;> ring
  have hd := period_debit_le_scale hc.le hy hm0 hNM I J v hI hJ
  have hb := mul_le_mul_of_nonneg_left hlower (by norm_num : (0 : ℝ) ≤ 1/128)
  have hperiod : κ*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
        (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
          (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
      (1/128 : ℝ)*(∑ n ∈ supply M h w,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    exact hd.trans (by convert hb using 1; dsimp only [U]; ring)
  dsimp only at hX hZ hHpay hFpay
  linarith only [hX,hZ,hHpay,hFpay,hGpay,hTpay,hperiod]

end RiemannGaussian.ZetaRieszRoughFivePeriodFloor
