/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSharpSupplyFloor

set_option autoImplicit false

/-!
# Signed cancellation after rejoining the complete four-prime supply

Complete largest-prime periods are applied to the WHOLE literal fixed-count
sector, including the four-prime supply. This avoids the old false
zero-intersection shortcut for negative fours. The resulting signed cost
is explicit; no four-prime positive supply is credited a second time.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszWholeFixedCountFloor
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

open ZetaRieszHighSignCoverFloor (roughCofactors roughPeriod roughPeriod_data
  owner_gap_mem_roughPeriod periodUnits)

theorem eventually_period_part_floor {k : ℕ} (hk : 2 ≤ k) {e u y ε : ℝ} (he : |e| = 1)
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (v : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      Real.sin (y*v) = 0 → e*Real.cos (y*v) ≤ 0 →
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        ∑ n ∈ roughPeriod k B v y, signedPart e
          (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) y N n := by
  filter_upwards [ZetaRieszTransitionFiveFloor.eventually_core_part_floor
    (k := k) (by omega) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors k B v) hlo hhi (Finset.filter_subset _ _) hpeak hsign

private theorem owner_data {k n : ℕ} (hk : 2 ≤ k) (hs : Squarefree n)
    (hc : n.primeFactors.card = k+1) :
    let p := ZetaRieszPrimeEndpoint.largestPrime n
    let a := n/p;
    p.Prime ∧ p*a = n ∧ Squarefree a ∧ a.primeFactors.card = k ∧
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
  have hcard : a.primeFactors.card = k := by
    rw [hpf,Finset.card_insert_of_notMem hnot] at hc
    omega
  have hmax q (hq : q ∈ n.primeFactors) : q ≤ p := by
    dsimp [p,ZetaRieszPrimeEndpoint.largestPrime]
    rw [dif_pos (Finset.card_pos.mp (by omega : 0 < n.primeFactors.card))]
    exact Finset.le_max' _ q hq
  exact ⟨hpp,he,ha,hcard,hp,hmax,hnot⟩

private theorem no_close_owner_gap {k n : ℕ} (hk : 2 ≤ k) (hs : Squarefree n)
    (hc : n.primeFactors.card = k+1) (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      Real.log q ≤ Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-1/8 := by
  obtain ⟨hpp,he,ha,_,hp,hmax,hnot⟩ := owner_data hk hs hc
  intro q hq
  by_contra hh
  have hqn : q ∈ n.primeFactors := (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)))
    hs.ne_zero
  apply hntie
  refine ⟨_,hp,q,hqn,?_,hmax,lt_of_not_ge hh⟩
  intro h
  exact hnot (h ▸ hq)

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

/-- Both signed parts of every whole count sector are covered before
any supply is removed. Periods stay inside the actual core. -/
theorem eventually_whole_count_cover {k : ℕ} (hk : 2 ≤ k) (hku : k ≤ 54) {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (I J : Finset ℕ) (v : ℝ),
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
      let E := S.filter (fun n => n.primeFactors.card = k+1)
      let X := fun i => roughPeriod k 0 (center v y i) y
      let Y := fun i => roughPeriod k 0 (center (v+Real.pi/y) y i) y;
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
      (eventually_period_part_floor hk (e := 1) (by norm_num) hu hU hy hε),
    tendsto_dyadicMomentOrder.eventually
      (eventually_period_part_floor hk (e := -1) (by norm_num) hu hU hy hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hpos hneg hL hlarge hj I J v hpeak hI hJ
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := S.filter (fun n => n.primeFactors.card = k+1)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hcount : k+1 < dyadicPrimeCount j := by
    have hp : 64 ≤ (2 : ℕ)^j := by
      calc
        64 = 2^6 := by norm_num
        _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) (by omega)
    dsimp [dyadicPrimeCount]
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ} (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod k 0 c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    have hcore : roughPeriod k 0 c y ⊆ S :=
      ZetaRieszTransitionFiveFloor.owned_subset_core (k := k) (by omega)
        j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        hlo hhi (roughCofactors k 0 c) (Finset.filter_subset _ _)
    intro n hn
    exact Finset.mem_filter.mpr ⟨hcore hn,(roughPeriod_data (by omega) hc hy hn).2.1⟩
  let X := fun i => roughPeriod k 0 (center v y i) y
  let Y := fun i => roughPeriod k 0 (center (v+Real.pi/y) y i) y
  have hvI i (hi : i ∈ I) : 100 ≤ center v y i := by linarith only [hNR,hpi,(hI i hi).1]
  have hvJ i (hi : i ∈ J) : 100 ≤ center (v+Real.pi/y) y i := by linarith only [hNR,hpi,(hJ i hi).1]
  have hdisjoint (b : ℝ) {i l : ℕ} (hil : i ≠ l)
      (hi : 100 ≤ center b y i) (hl : 100 ≤ center b y l) :
      Disjoint (roughPeriod k 0 (center b y i) y) (roughPeriod k 0 (center b y l) y) := by
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
      simpa only [neg_mul] using hpos 0 _ (hI i hi).1 (hI i hi).2 hp.1 (by rw [hp.2]; norm_num))
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).2
      simpa only [neg_mul] using hneg 0 _ (hJ i hi).1 (hJ i hi).2 hp.1 (by rw [hp.2]; norm_num))
  simpa only [← Finset.mul_sum,← mul_add] using hb

theorem interior_parts_covered {k : ℕ} (hk : 2 ≤ k) (hku : k ≤ 54) (j : ℕ) (hj : 32 ≤ j) (u : ℝ)
    {y : ℝ} (hy : 54 ≤ y) {n : ℕ}
    (hN : 4000 ≤ dyadicMomentOrder j)
    (hn : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter (fun n : ℕ =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧
          (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hc : n.primeFactors.card = k+1)
    (hlo : (244/125 : ℝ)*dyadicMomentOrder j < Real.log n)
    (hhi : Real.log n ≤ (2029/1000 : ℝ)*dyadicMomentOrder j)
    (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    let N := dyadicMomentOrder j
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N;
    (signedPart 1 A L y N n = 0 ∨
      n ∈ (completeGrid N (Real.pi/y) y).biUnion
        (fun i => roughPeriod k 0 (center (Real.pi/y) y i) y)) ∧
    (signedPart (-1) A L y N n = 0 ∨
      n ∈ (completeGrid N (Real.pi/y+Real.pi/y) y).biUnion
        (fun i => roughPeriod k 0 (center (Real.pi/y+Real.pi/y) y i) y)) := by
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
  obtain ⟨hpp,he,ha,hac,hp,hmax,_⟩ := owner_data hk hs hc
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
  have hgap := no_close_owner_gap hk hs hc hntie
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
  have hrougha (q : ℕ) (hq : q ∈ a.primeFactors) : 0 < q :=
    (Nat.prime_of_mem_primeFactors hq).pos
  have hhpos := owner_gap_mem_roughPeriod (B := 0) hku hv hy ha hac hpp
    (he.symm ▸ hTi) hshare hgap hrougha
  have hhneg := owner_gap_mem_roughPeriod (B := 0) hku hv' hy ha hac hpp
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

set_option maxHeartbeats 1200000 in
/-- The WHOLE literal sector at every fixed count 3..55 has arbitrarily
small signed period cost, with geometric dominant/radial errors retained.
At count four this includes every original supply label. -/
theorem exists_core_count_floor {k : ℕ} (hk : 2 ≤ k) (hku : k ≤ 54) {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop,
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := S.filter (fun n => n.primeFactors.card = k+1)
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
  filter_upwards [eventually_whole_count_cover hk hku hu hU hy (half_pos hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszOwnerTieFloor.eventually_core_grouped_tie_floor hu hU (half_pos hε)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hperiod htie hN hj
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := S.filter (fun n => n.primeFactors.card = k+1)
  let dom := fun n : ℕ => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
      (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let D := E.filter dom
  let F := (E\D).filter (fun n : ℕ => ¬((244/125 : ℝ)*N < Real.log n ∧
    Real.log n ≤ (2029/1000 : ℝ)*N))
  let T := ((E\D)\F).filter (fun n => Squarefree n ∧ ZetaRieszOwnerTieFloor.CloseOwners n)
  let I := completeGrid N (Real.pi/y) y
  let J := completeGrid N (Real.pi/y+Real.pi/y) y
  let X := I.biUnion (fun i => roughPeriod k 0 (center (Real.pi/y) y i) y)
  let Y := J.biUnion (fun i => roughPeriod k 0 (center (Real.pi/y+Real.pi/y) y i) y)
  let units₁ := ∑ i ∈ I, Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial
  let units₂ := ∑ i ∈ J, Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
    (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial
  have units₁pos : 0 ≤ units₁ := Finset.sum_nonneg (fun i hi => by
    have hg := (Finset.mem_filter.mp hi).2.1
    have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
    have hc : 0 ≤ center (Real.pi/y) y i := by linarith only [hg,hπ.le,hNR]
    positivity)
  have hper := hperiod I J (Real.pi/y) hpeak
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
    obtain ⟨hnS,hc⟩ := Finset.mem_filter.mp hnE
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
    exact interior_parts_covered hk hku j hj u hy hN
      (Finset.mem_filter.mpr ⟨hnS,hnotdom⟩) hc (hFgeo n hnEF).1 (hFgeo n hnEF).2 hnotTie
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


theorem sum_fixed_parts (E : Finset ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 2 54, ∑ n ∈ E.filter
      (fun n : ℕ => n.primeFactors.card = k+1), f n) =
      ∑ n ∈ E.filter (fun n : ℕ => 3 ≤ n.primeFactors.card ∧
        n.primeFactors.card ≤ 55), f n := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hc : 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55
  · rw [if_pos hc]
    rw [Finset.sum_eq_single (n.primeFactors.card-1)]
    · rw [if_pos (by omega)]
    · intro k _ hk
      exact if_neg (by omega)
    · intro hn
      exact False.elim (hn (Finset.mem_Icc.mpr (by omega)))
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro k hk
    have hb := Finset.mem_Icc.mp hk
    exact if_neg (by omega)

/-- A single signed estimate for EVERY core label at counts 3..55,
including the complete four-prime supply. All masks, allocation and phase
remain literal. The estimate has arbitrary radial cost plus source-o(1)
error, not a numerical absolute floor. -/
theorem exists_core_band_floor {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ err : ℕ → ℝ, (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop,
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := S.filter
          (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55);
        -u^(N+1)*ε*periodUnits N y-err j ≤
          ((u : ℂ)^(N+1)*∑ n ∈ E,
            residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hEach (k : ℕ) : ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      (k ∈ Finset.Icc 2 54 →
        ∀ᶠ j : ℕ in atTop,
          let N := dyadicMomentOrder j
          let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
          let L := SquarefreeVaughanLogSource.length u N
          let S := coreBand u N (dyadicPrimeCount j)
          let E := S.filter
            (fun n : ℕ => n.primeFactors.card = k+1);
          -u^(N+1)*(ε/53)*periodUnits N y-err j ≤
            ((u : ℂ)^(N+1)*∑ n ∈ E,
              residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) := by
    by_cases hk : k ∈ Finset.Icc 2 54
    · obtain ⟨hk,hku⟩ := Finset.mem_Icc.mp hk
      obtain ⟨r,C,hr,hr1,hC,hfloor⟩ := exists_core_count_floor hk hku hu hU hy
        (by positivity : 0 < ε/53)
      let err := fun j => 4*zetaMoebiusLogMajorantMass (1+1/262144)*
        Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)+2*r^(dyadicMomentOrder j)*C
      have h₁ := (ZetaRieszJointDominantFloor.Refined.tendsto_allowance.const_mul
        (2 : ℝ)).comp tendsto_dyadicMomentOrder
      have h₂ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const (2*C)).comp
        tendsto_dyadicMomentOrder
      have hlim : Tendsto err atTop (𝓝 0) := by
        have ht := h₁.add h₂
        simp only [mul_zero,zero_mul,zero_add] at ht
        convert ht using 1
        funext j
        dsimp [err,Function.comp_def]
        ring
      refine ⟨err,(fun j => by
        dsimp [err]
        positivity [zetaMoebiusLogMajorantMass_nonneg (1+1/262144)]),hlim,?_⟩
      intro _
      filter_upwards [hfloor] with j hj
      have hb := hj
      dsimp only at hb ⊢
      dsimp only [err,periodUnits]
      linarith only [hb]
    · exact ⟨fun _ => 0,fun _ => le_rfl,tendsto_const_nhds,fun h => False.elim (hk h)⟩
  choose err he0 helim he using hEach
  let error := fun j => ∑ k ∈ Finset.Icc 2 54, err k j
  have hlim : Tendsto error atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.Icc 2 54) (fun k _ => helim k))
  refine ⟨error,(fun j => Finset.sum_nonneg (fun k _ => he0 k j)),hlim,?_⟩
  have hband := (eventually_all_finset (Finset.Icc 2 54)).mpr he
  filter_upwards [hband] with j hj
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := S
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb k (hk : k ∈ Finset.Icc 2 54) := hj k hk
  have hs := Finset.sum_le_sum hb
  simp only [← Complex.ofReal_pow,Complex.re_ofReal_mul,Complex.re_sum] at hs ⊢
  change _ ≤ ∑ k ∈ Finset.Icc 2 54, u^(N+1)*∑ n ∈ E.filter
    (fun n : ℕ => n.primeFactors.card = k+1), (f n).re at hs
  rw [← Finset.mul_sum,sum_fixed_parts E (fun n => (f n).re)] at hs
  change -u^(N+1)*ε*periodUnits N y-error j ≤
    u^(N+1)*∑ n ∈ E.filter
      (fun n : ℕ => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55), (f n).re
  convert hs using 1
  dsimp only [error]
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  norm_num
  ring


end RiemannGaussian.ZetaRieszWholeFixedCountFloor
