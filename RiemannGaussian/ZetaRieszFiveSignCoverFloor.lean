/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTransitionFiveFloor

set_option autoImplicit false

/-!
# Sign-specific rough five-prime covers in the actual unpaid carrier

The positive arithmetic part needs only the positive-head threshold Q;
the negative part needs only the negative-head threshold V. Other spent
five-prime heads have the opposite arithmetic sign and hence contribute
exactly zero to that part. The complete prime periods can therefore be
retained before restricting to the unpaid set, without using a head credit
twice. No norm or new prime-density estimate is used for this cancellation.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszFiveSignCoverFloor
open ZetaRieszTransitionFiveFloor ZetaRieszStaggeredFloor
open ZetaRieszRoughFivePeriodFloor (spent radialSupply_count)
open ZetaRieszRoughFiveJoinedFloor
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic (weight weight_nonneg)
open ZetaRieszMultiPeriodSix
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead ZetaRieszSevenCountTail

private theorem five_spent_heads (S : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hc : n.primeFactors.card = 5) (hn : n ∈ spent S N Q P V R η h L w) :
    n ∈ (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) ∨
      n ∈ radialHeads S N P V L := by
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
  by_contra hnot
  push Not at hnot
  simp only [spent,Finset.mem_union] at hn
  tauto

/-- A spent label with all factors above Q contributes zero to the positive
arithmetic part: only a negative-coefficient head can contain it. -/
theorem positive_part_zero_of_spent (S A : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 1000 ≤ N) (η y : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hc : n.primeFactors.card = 5) (hrough : ∀ r ∈ n.primeFactors, Q < r)
    (hn : n ∈ spent S N Q P V R η h L w) : signedPart 1 A L y N n = 0 := by
  rcases five_spent_heads S hN η hh hhu w hw hc hn with hF | hG
  · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hF
    obtain ⟨_,_,_,_,_,_,⟨r,hr,hrQ⟩,_⟩ := (Finset.mem_filter.mp hn)
    exact False.elim ((not_lt_of_ge hrQ) (hrough r hr))
  · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hG
    have hhead := (Finset.mem_filter.mp hn).2.2.2.2
    rcases hhead with ⟨h6,_⟩ | ⟨_,hneg,_⟩
    · omega
    · simp only [signedPart,one_mul,max_eq_right hneg.le,mul_zero,zero_mul]

/-- A spent label with all factors above V contributes zero to the negative
arithmetic part: only a positive-coefficient head can contain it. -/
theorem negative_part_zero_of_spent (S A : Finset ℕ) {N Q P V R n : ℕ}
    (hN : 1000 ≤ N) (η y : ℝ) {h L : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hc : n.primeFactors.card = 5) (hrough : ∀ r ∈ n.primeFactors, V < r)
    (hn : n ∈ spent S N Q P V R η h L w) : signedPart (-1) A L y N n = 0 := by
  rcases five_spent_heads S hN η hh hhu w hw hc hn with hF | hG
  · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hF
    have hpos := (Finset.mem_filter.mp hn).2.2.2.2.2.2.2
    simp only [signedPart,neg_one_mul,max_eq_right (by linarith :
      -(SquarefreeVaughanLogSource.coefficient L n).re ≤ 0),mul_zero,zero_mul]
  · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hG
    have hhead := (Finset.mem_filter.mp hn).2.2.2.2
    rcases hhead with ⟨h6,_⟩ | ⟨_,_,r,hr,hrV⟩
    · omega
    · exact False.elim ((not_lt_of_ge hrV) (hrough r hr))

private theorem sum_inter_unpaid_eq (S C : Finset ℕ) (g : ℕ → ℝ)
    (N Q P V R : ℕ) (η h L : ℝ) (w : ℕ → ℝ)
    (hC : C ⊆ S) (hc : ∀ n ∈ C, n.primeFactors.card = 5)
    (hzero : ∀ n ∈ C, n ∈ spent S N Q P V R η h L w → g n = 0) :
    let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5);
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

/-- Each arithmetic sign uses exactly its own already-paid head threshold.
Opposite-sign head intersections are zero before taking any norm. -/
theorem eventually_unpaid_five_sign_floor {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ)
      (I J : Finset ℕ) (v : ℝ),
      0 < h → h ≤ 1/20 →
      (∀ M ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        0 ≤ w M ∧ w M ≤ 1/2) →
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
      let X := fun i => roughPeriod Q (center v y i) y
      let Y := fun i => roughPeriod V (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart 1 A L y N n)+
        (∑ n ∈ E\J.biUnion Y, signedPart (-1) A L y N n)-
        ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (∑ n ∈ E, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hy0 : 0 < y := by linarith
  have hpi : 0 ≤ Real.pi/y := by positivity
  have hstep : 0 ≤ 2*Real.pi/y := by positivity
  have hsep (b : ℝ) {i j : ℕ} (hij : i < j) :
      center b y i+Real.pi/y ≤ center b y j-Real.pi/y := by
    have hh : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
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
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hcount : 4+1 < dyadicPrimeCount j := by
    dsimp [dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned (B : ℕ) {c : ℝ}
      (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod B c y ⊆ S := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    exact owned_subset_core (k := 4) (by norm_num) j hj hcount hu hU hy hc
      (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
      hlo hhi (roughCofactors B c) (Finset.filter_subset _ _)
  let X := fun i => roughPeriod Q (center v y i) y
  let Y := fun i => roughPeriod V (center (v+Real.pi/y) y i) y
  have hvI i (hi : i ∈ I) : 100 ≤ center v y i := by linarith only [hNR,hpi,(hI i hi).1]
  have hvJ i (hi : i ∈ J) : 100 ≤ center (v+Real.pi/y) y i := by linarith only [hNR,hpi,(hJ i hi).1]
  have hXeq i (hi : i ∈ I) :
      (∑ n ∈ X i ∩ E, signedPart 1 A L y N n) = ∑ n ∈ X i, signedPart 1 A L y N n := by
    exact sum_inter_unpaid_eq S (X i) _ N Q P V R η h L w
      (howned Q (hI i hi).1 (hI i hi).2)
      (fun n hn => (roughPeriod_data (hvI i hi) hy hn).2.1)
      (fun n hn hspent =>
        positive_part_zero_of_spent S A hlarge η y hh hhu w hw
          (roughPeriod_data (hvI i hi) hy hn).2.1
          (roughPeriod_data (hvI i hi) hy hn).2.2 hspent)
  have hYeq i (hi : i ∈ J) :
      (∑ n ∈ Y i ∩ E, signedPart (-1) A L y N n) = ∑ n ∈ Y i, signedPart (-1) A L y N n := by
    exact sum_inter_unpaid_eq S (Y i) _ N Q P V R η h L w
      (howned V (hJ i hi).1 (hJ i hi).2)
      (fun n hn => (roughPeriod_data (hvJ i hi) hy hn).2.1)
      (fun n hn hspent =>
        negative_part_zero_of_spent S A hlarge η y hh hhu w hw
          (roughPeriod_data (hvJ i hi) hy hn).2.1
          (roughPeriod_data (hvJ i hi) hy hn).2.2 hspent)
  have hdisjoint (B : ℕ) (b : ℝ) {i l : ℕ} (hil : i ≠ l)
      (hi : 100 ≤ center b y i) (hl : 100 ≤ center b y l) :
      Disjoint (roughPeriod B (center b y i) y) (roughPeriod B (center b y l) y) := by
    rcases lt_or_gt_of_ne hil with h | h
    · exact ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hi hl hy _ _
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hsep b h)
    · exact (ZetaRieszTransitionFiveFloor.owned_disjoint_of_separated hl hi hy _ _
        (Finset.filter_subset _ _) (Finset.filter_subset _ _) (hsep b h)).symm
  have hb := two_cover_floor A E I J (fun i => X i ∩ E) (fun i => Y i ∩ E) L y N
    (fun i => ε*(Real.exp (-center v y i/2)*(center v y i)^N/N.factorial))
    (fun i => ε*(Real.exp (-center (v+Real.pi/y) y i/2)*
      (center (v+Real.pi/y) y i)^N/N.factorial))
    (fun _ _ => Finset.inter_subset_right) (fun _ _ => Finset.inter_subset_right)
    (fun i hi l hl hil => (hdisjoint Q v hil (hvI i hi) (hvI l hl)).mono
      Finset.inter_subset_left Finset.inter_subset_left)
    (fun i hi l hl hil => (hdisjoint V (v+Real.pi/y) hil (hvJ i hi) (hvJ l hl)).mono
      Finset.inter_subset_left Finset.inter_subset_left)
    (by
      intro i hi
      rw [hXeq i hi]
      have hp := (staggered_peaks hy0 hpeak i).1
      simpa only [neg_mul] using hpos Q _ (hI i hi).1 (hI i hi).2 hp.1 (by rw [hp.2]; norm_num))
    (by
      intro i hi
      rw [hYeq i hi]
      have hp := (staggered_peaks hy0 hpeak i).2
      simpa only [neg_mul] using hneg V _ (hJ i hi).1 (hJ i hi).2 hp.1 (by rw [hp.2]; norm_num))
  rw [sdiff_cover_inter,sdiff_cover_inter] at hb
  simpa only [← Finset.mul_sum,← mul_add] using hb

/-- The whole joined floor retains each original favorable credit and its
1/128 supply reserve, while the five-prime covers use Q and V separately.
There is no max(Q,V) gap and no additional period charge. The remaining
unmatched arithmetic parts stay explicit; this is not the numerical floor. -/
theorem eventually_joined_floor_with_signed_rough_periods {u y : ℝ} (hu : 1/2 < u)
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
        let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
        let Eo := E\E5
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          ∀ (H : Finset ℕ) (I J : ℕ → Finset ℕ) (v : ℝ),
            H ⊆ radialIndices N →
            Real.cos (y*v) = -1 →
            (∀ M ∈ H, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
              center v y i < 2*M+2) →
            (∀ M ∈ H, ∀ i ∈ J M,
              2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
              center (v+Real.pi/y) y i < 2*M+2) →
            (∀ i ∈ H.biUnion I, (39/20 : ℝ)*N ≤ center v y i-Real.pi/y ∧
              center v y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
            (∀ i ∈ H.biUnion J,
              (39/20 : ℝ)*N ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
              center (v+Real.pi/y) y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
            let X := (H.biUnion I).biUnion (fun i => roughPeriod Q (center v y i) y)
            let Y := (H.biUnion J).biUnion (fun i => roughPeriod V (center (v+Real.pi/y) y i) y)
            let U := (∑ n ∈ E5\X, signedPart 1 A L y N n)+
              (∑ n ∈ E5\Y, signedPart (-1) A L y N n);
            u^(N+1)*(U+W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
              max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
              max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
              (∑ n ∈ Ys, f n).re/128)-err j ≤
                ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr,hr1,hC,hbase⟩ := eventually_core_full_floor_with_scale hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,
    eventually_unpaid_five_sign_floor hu hU hy hκ,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1 : ℕ))]
      with j hj hrough hbound hN
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
  let Eo := E\E5
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  intro H I J v hH hpeak hI hJ hiCore hjCore
  have hp := hrough Q P V R η h w (H.biUnion I) (H.biUnion J) v
    hh hhu hw hpeak hiCore hjCore
  have hd := period_grids_cost_paid hN hc hy hhu hκeq w f H I J
    hw hscale hH hI hJ
  let X := (H.biUnion I).biUnion (fun i => roughPeriod Q (center v y i) y)
  let Y := (H.biUnion J).biUnion (fun i => roughPeriod V (center (v+Real.pi/y) y i) y)
  let U := (∑ n ∈ E5\X, signedPart 1 A L y N n)+
    (∑ n ∈ E5\Y, signedPart (-1) A L y N n)
  have hpaid : U ≤ (∑ n ∈ E5, f n).re+(∑ n ∈ Ys, f n).re/128 := by
    change U-κ*((∑ i ∈ H.biUnion I,
      Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ H.biUnion J, Real.exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)) ≤ (∑ n ∈ E5, f n).re at hp
    change _ ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hd
    linarith only [hp,hd]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 5) E) (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ E5, f n).re = (∑ n ∈ E, f n).re at hs
  let credits := max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+
    max (∑ n ∈ Zs, f n).re 0+max (∑ n ∈ Hs, f n).re 0+
    max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+
    max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
    convert hcore using 1
    dsimp only [credits]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hpaid (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(U+W+G+credits+(∑ n ∈ Ys, f n).re/128)-(r^N*C+e j) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hscaled,hb,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring


private theorem mem_positive_head_of_geometry {S : Finset ℕ} {N n Q : ℕ} {L : ℝ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ r ∈ n.primeFactors, Real.log r ≤ (1209/2000 : ℝ)*Real.log n)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ Q) :
    n ∈ (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L) := by
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
    ⟨hnS,hs,hc,by linarith,by linarith,hmax',hsmall,hpos⟩⟩

/-- Inside the retained radial interior, every positive unpaid five-prime
coefficient has all factors above its OWN positive-head threshold Q. -/
theorem unpaid_positive_rough (S : Finset ℕ) {N n Q P V R : ℕ} (η h L : ℝ) (w : ℕ → ℝ)
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hnot : n ∉ spent S N Q P V R η h L w)
    (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hmax : ∀ r ∈ n.primeFactors, Real.log r ≤ (1209/2000 : ℝ)*Real.log n) :
    ∀ r ∈ n.primeFactors, Q < r := by
  intro r hr
  by_contra hn
  have hF := mem_positive_head_of_geometry hN hnS hs hc hpos hlo hhi hmax
    ⟨r,hr,le_of_not_gt hn⟩
  apply hnot
  simp only [spent,Finset.mem_union]
  tauto

/-- The negative unpaid part analogously retains the separate threshold V.
No cofactor share or phase condition is imposed on this support conclusion. -/
theorem unpaid_negative_rough (S : Finset ℕ) {N n Q P V R : ℕ} (η h L : ℝ) (w : ℕ → ℝ)
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hnot : n ∉ spent S N Q P V R η h L w)
    (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hneg : (SquarefreeVaughanLogSource.coefficient L n).re < 0)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N) :
    ∀ r ∈ n.primeFactors, V < r := by
  intro r hr
  by_contra hn
  have hG := mem_radialHeads_of_geometry (P := P) hN hnS hs hlo hhi
    (Or.inr ⟨hc,hneg,r,hr,le_of_not_gt hn⟩)
  apply hnot
  simp only [spent,Finset.mem_union]
  tauto

private theorem roughPeriod_max_share {B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod B v y) :
    ∀ q ∈ n.primeFactors, Real.log q ≤ (1209/2000 : ℝ)*Real.log n := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hg := ZetaRieszTransitionFiveFloor.fibre_geometry hv (by rwa [hyabs])
    (Finset.mem_filter.mp ha).1 (by simpa only [hyabs] using hp)
  simpa only [Nat.mul_comm a p] using hg.2.2.2.2.2.2

/-- Every positive arithmetic part in the share transition is either zero
or in the enlarged Q-cover. No max(Q,V) roughness hypothesis is needed. -/
theorem transition_positive_zero_or_covered (S A : Finset ℕ) {N Q P V R a p : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) {v y : ℝ}
    (hN : 4000 ≤ N) (hnS : p*a ∈ S) (hnot : p*a ∉ spent S N Q P V R η h L w)
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a) (hc : a.primeFactors.card = 4)
    (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hhi : Real.log a ≤ (407/1000 : ℝ)*Real.log (p*a : ℕ))
    (hcorelo : (244/125 : ℝ)*N < Real.log (p*a : ℕ))
    (hcorehi : Real.log (p*a : ℕ) ≤ (2029/1000 : ℝ)*N) :
    signedPart 1 A L y N (p*a) = 0 ∨ p*a ∈ roughPeriod Q v y := by
  by_cases hpos : 0 < (SquarefreeVaughanLogSource.coefficient L (p*a)).re
  swap
  · left
    simp only [signedPart,one_mul,max_eq_right (le_of_not_gt hpos),mul_zero,zero_mul]
  have hn0 := transition_mem_roughPeriod (B := 0) hv hy ha hc hp hT hlo hhi
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hd := roughPeriod_data hv hy hn0
  have hr := unpaid_positive_rough S η h L w hN hnS hnot hd.1 hd.2.1 hpos
    hcorelo hcorehi (roughPeriod_max_share hv hy hn0)
  right
  apply transition_mem_roughPeriod hv hy ha hc hp hT hlo hhi
  intro q hq
  exact hr q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_mul_left a p)) hd.1.ne_zero)

/-- The matching negative transition part is zero or in the V-cover;
previously paid positive heads create no loss or extra norm charge. -/
theorem transition_negative_zero_or_covered (S A : Finset ℕ) {N Q P V R a p : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) {v y : ℝ}
    (hN : 4000 ≤ N) (hnS : p*a ∈ S) (hnot : p*a ∉ spent S N Q P V R η h L w)
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a) (hc : a.primeFactors.card = 4)
    (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hhi : Real.log a ≤ (407/1000 : ℝ)*Real.log (p*a : ℕ))
    (hcorelo : (244/125 : ℝ)*N < Real.log (p*a : ℕ))
    (hcorehi : Real.log (p*a : ℕ) ≤ (2029/1000 : ℝ)*N) :
    signedPart (-1) A L y N (p*a) = 0 ∨ p*a ∈ roughPeriod V v y := by
  by_cases hneg : (SquarefreeVaughanLogSource.coefficient L (p*a)).re < 0
  swap
  · left
    simp only [signedPart,neg_one_mul,max_eq_right
      (neg_nonpos.mpr (le_of_not_gt hneg)),mul_zero,zero_mul]
  have hn0 := transition_mem_roughPeriod (B := 0) hv hy ha hc hp hT hlo hhi
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hd := roughPeriod_data hv hy hn0
  have hr := unpaid_negative_rough S η h L w hN hnS hnot hd.1 hd.2.1 hneg hcorelo hcorehi
  right
  apply transition_mem_roughPeriod hv hy ha hc hp hT hlo hhi
  intro q hq
  exact hr q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_mul_left a p)) hd.1.ne_zero)

/-- The entire separated-owner positive part beyond cofactor share 399/1000
is zero or covered at its own Q threshold. There is no upper-share cutoff. -/
theorem owner_gap_positive_zero_or_covered (S A : Finset ℕ) {N Q P V R a p : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) {v y : ℝ}
    (hN : 4000 ≤ N) (hnS : p*a ∈ S) (hnot : p*a ∉ spent S N Q P V R η h L w)
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a) (hc : a.primeFactors.card = 4)
    (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hgap : ∀ q ∈ a.primeFactors, Real.log q ≤ Real.log p-1/8)
    (hcorelo : (244/125 : ℝ)*N < Real.log (p*a : ℕ))
    (hcorehi : Real.log (p*a : ℕ) ≤ (2029/1000 : ℝ)*N) :
    signedPart 1 A L y N (p*a) = 0 ∨ p*a ∈ roughPeriod Q v y := by
  by_cases hpos : 0 < (SquarefreeVaughanLogSource.coefficient L (p*a)).re
  swap
  · left
    simp only [signedPart,one_mul,max_eq_right (le_of_not_gt hpos),mul_zero,zero_mul]
  have hn0 := owner_gap_mem_roughPeriod (B := 0) hv hy ha hc hp hT hlo hgap
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hd := roughPeriod_data hv hy hn0
  have hr := unpaid_positive_rough S η h L w hN hnS hnot hd.1 hd.2.1 hpos
    hcorelo hcorehi (roughPeriod_max_share hv hy hn0)
  right
  apply owner_gap_mem_roughPeriod hv hy ha hc hp hT hlo hgap
  intro q hq
  exact hr q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_mul_left a p)) hd.1.ne_zero)

/-- The entire separated-owner negative part beyond the paid dominant
cutoff is zero or covered at V, without any common roughness threshold. -/
theorem owner_gap_negative_zero_or_covered (S A : Finset ℕ) {N Q P V R a p : ℕ}
    (η h L : ℝ) (w : ℕ → ℝ) {v y : ℝ}
    (hN : 4000 ≤ N) (hnS : p*a ∈ S) (hnot : p*a ∉ spent S N Q P V R η h L w)
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a) (hc : a.primeFactors.card = 4)
    (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hgap : ∀ q ∈ a.primeFactors, Real.log q ≤ Real.log p-1/8)
    (hcorelo : (244/125 : ℝ)*N < Real.log (p*a : ℕ))
    (hcorehi : Real.log (p*a : ℕ) ≤ (2029/1000 : ℝ)*N) :
    signedPart (-1) A L y N (p*a) = 0 ∨ p*a ∈ roughPeriod V v y := by
  by_cases hneg : (SquarefreeVaughanLogSource.coefficient L (p*a)).re < 0
  swap
  · left
    simp only [signedPart,neg_one_mul,max_eq_right
      (neg_nonpos.mpr (le_of_not_gt hneg)),mul_zero,zero_mul]
  have hn0 := owner_gap_mem_roughPeriod (B := 0) hv hy ha hc hp hT hlo hgap
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hd := roughPeriod_data hv hy hn0
  have hr := unpaid_negative_rough S η h L w hN hnS hnot hd.1 hd.2.1 hneg hcorelo hcorehi
  right
  apply owner_gap_mem_roughPeriod hv hy ha hc hp hT hlo hgap
  intro q hq
  exact hr q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_mul_left a p)) hd.1.ne_zero)

/-- All complete periods in the original core, assigned by their centres
rather than clipped separately at every radial slab. -/
def completeGrid (N : ℕ) (b y : ℝ) : Finset ℕ :=
  (Finset.range (⌈3*((N : ℝ)+1)/(2*Real.pi/y)⌉₊+1)).filter (fun i =>
    (39/20 : ℝ)*N ≤ center b y i-Real.pi/y ∧
    center b y i+Real.pi/y ≤ (203/100 : ℝ)*N ∧
    ⌊center b y i/2⌋₊ ∈ radialIndices N)

/-- The same complete grid, indexed by the half-open centre slab. -/
def slabGrid (N : ℕ) (b y : ℝ) (M : ℕ) : Finset ℕ :=
  (completeGrid N b y).filter (fun i => 2*(M : ℝ) ≤ center b y i ∧
    center b y i < 2*M+2)

private theorem center_slab {c : ℝ} (hc : 0 ≤ c) :
    2*(⌊c/2⌋₊ : ℝ) ≤ c ∧ c < 2*(⌊c/2⌋₊ : ℝ)+2 := by
  have hlo := Nat.floor_le (show 0 ≤ c/2 by positivity)
  have hhi := Nat.lt_floor_add_one (c/2)
  constructor <;> linarith

/-- Every complete period is assigned to exactly one centre slab; periods
crossing a slab endpoint retain all of their literal prime incidences. -/
theorem biUnion_slabGrid_eq (N : ℕ) (b y : ℝ) :
    (radialIndices N).biUnion (slabGrid N b y) = completeGrid N b y := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨M,_,hi⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hi).1
  · intro i hi
    have hd := (Finset.mem_filter.mp hi).2
    have hc : 0 ≤ center b y i := by
      have hM := (Finset.mem_filter.mp hd.2.2).2.1
      by_contra h
      have hz : ⌊center b y i/2⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [hz] at hM
      norm_num at hM
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact Finset.mem_biUnion.mpr ⟨⌊center b y i/2⌋₊,hd.2.2,
      Finset.mem_filter.mpr ⟨hi,center_slab hc⟩⟩

/-- Both staggered grids cover every total logarithm in the retained
radial interior. This is deterministic half-open coverage, including
exact phase endpoints, with every selected period wholly inside the core. -/
theorem exists_completeGrid_period {N : ℕ} (hN : 4000 ≤ N) {y b T : ℝ}
    (hy : 54 ≤ y) (hb : Real.pi/y ≤ b ∧ b ≤ 2*Real.pi/y)
    (hlo : (244/125 : ℝ)*N < T) (hhi : T ≤ (2029/1000 : ℝ)*N) :
    ∃ i ∈ completeGrid N b y, center b y i-Real.pi/y < T ∧
      T ≤ center b y i+Real.pi/y := by
  have hy0 : 0 < y := by linarith
  have hh : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hhu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  let d := 2*Real.pi/y
  have hd : 0 < d := by dsimp [d]; positivity
  have hdeq : d = 2*(Real.pi/y) := by dsimp [d]; ring
  have hdu : d ≤ 1/8 := by linarith only [hdeq,hhu]
  have hb2 : b ≤ 2*(Real.pi/y) := by convert hb.2 using 1; ring
  let x := (T-b-Real.pi/y)/d
  have hx : 0 ≤ x := div_nonneg
    (by linarith only [hlo,hNR,hb2,hhu]) hd.le
  let i := ⌈x⌉₊
  have hic : x ≤ (i : ℝ) := Nat.le_ceil x
  have hit : (i : ℝ) < x+1 := Nat.ceil_lt_add_one hx
  have hlow := mul_lt_mul_of_pos_right hit hd
  have hupp := mul_le_mul_of_nonneg_right hic hd.le
  have heq : x*d = T-b-Real.pi/y := by dsimp [x]; exact div_mul_cancel₀ _ hd.ne'
  rw [add_mul,heq,one_mul] at hlow
  rw [heq] at hupp
  have hc : center b y i = b+(i : ℝ)*d := by
    dsimp only [center,d]
    rw [abs_of_pos hy0]
  have hperiod : center b y i-Real.pi/y < T ∧ T ≤ center b y i+Real.pi/y := by
    rw [hc]
    constructor <;> linarith only [hlow,hupp,hdeq]
  have hbound : (i : ℝ) < 3*((N : ℝ)+1)/d := by
    apply (lt_div_iff₀ hd).mpr
    linarith only [hlow,hb.1,hhi,hhu,hNR,hdu,hh]
  have hir : i < ⌈3*((N : ℝ)+1)/d⌉₊+1 := by
    have hle := (hbound.trans_le (Nat.le_ceil (3*((N : ℝ)+1)/d))).le
    have hn : i ≤ ⌈3*((N : ℝ)+1)/d⌉₊ := by exact_mod_cast hle
    omega
  have hc0 : 0 ≤ center b y i := by linarith only [hperiod.2,hlo,hhu,hNR]
  have hslab := center_slab hc0
  have hM : ⌊center b y i/2⌋₊ ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : (⌊center b y i/2⌋₊ : ℝ) ≤ 2*N := by
        linarith only [hslab.1,hperiod.1,hhi,hhu,hNR]
      have hn : ⌊center b y i/2⌋₊ ≤ 2*N := by exact_mod_cast h
      omega
    constructor <;> linarith only [hslab.1,hslab.2,hperiod.1,hperiod.2,hlo,hhi,hhu,hNR]
  refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hir,?_,?_,hM⟩,hperiod⟩
  · linarith only [hperiod.2,hlo,hhu,hNR]
  · linarith only [hperiod.1,hhi,hhu,hNR]

private theorem five_owner_data {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) :
    let p := ZetaRieszPrimeEndpoint.largestPrime n
    let a := n/p;
    p.Prime ∧ p*a = n ∧ Squarefree a ∧ a.primeFactors.card = 4 ∧
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
  have hcard : a.primeFactors.card = 4 := by
    rw [hpf,Finset.card_insert_of_notMem hnot] at hc
    omega
  have hmax q (hq : q ∈ n.primeFactors) : q ≤ p := by
    dsimp [p,ZetaRieszPrimeEndpoint.largestPrime]
    rw [dif_pos (Finset.card_pos.mp (by omega : 0 < n.primeFactors.card))]
    exact Finset.le_max' _ q hq
  exact ⟨hpp,he,ha,hcard,hp,hmax,hnot⟩

private theorem no_close_owner_gap {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) (hntie : ¬ZetaRieszOwnerTieFloor.CloseOwners n) :
    ∀ q ∈ (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors,
      Real.log q ≤ Real.log (ZetaRieszPrimeEndpoint.largestPrime n)-1/8 := by
  obtain ⟨hpp,he,ha,_,hp,hmax,hnot⟩ := five_owner_data hs hc
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

/-- After the already-paid dominant deletion, BOTH nonzero five-prime
sign parts in the radial interior are covered by deterministic complete
periods unless the two largest prime logarithms are less than 1/8 apart.
All small-prime and original support masks remain in the unpaid set. -/
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
    (hc : n.primeFactors.card = 5)
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
        (fun i => roughPeriod V (center (Real.pi/y+Real.pi/y) y i) y)) := by
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
  obtain ⟨hpp,he,ha,hac,hp,hmax,_⟩ := five_owner_data hs hc
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
  have hhpos := owner_gap_positive_zero_or_covered S A η h L w hN
    (he.symm ▸ (Finset.mem_filter.mp hn).1) (he.symm ▸ hnot) hv hy ha hac hpp
    (he.symm ▸ hTi) hshare hgap (he.symm ▸ hlo) (he.symm ▸ hhi)
  have hhneg := owner_gap_negative_zero_or_covered S A η h L w hN
    (he.symm ▸ (Finset.mem_filter.mp hn).1) (he.symm ▸ hnot) hv' hy ha hac hpp
    (he.symm ▸ hTl) hshare hgap (he.symm ▸ hlo) (he.symm ▸ hhi)
  rw [he] at hhpos hhneg
  exact ⟨hhpos.imp_right (fun hc => Finset.mem_biUnion.mpr ⟨i,hi,hc⟩),
    hhneg.imp_right (fun hc => Finset.mem_biUnion.mpr ⟨l,hl,hc⟩)⟩

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

/-- Every retained mask on either outer radial strip has a geometric
source payment. The same estimate applies to each signed subset, so no
clipped phase endpoint survives as an unestimated five-prime boundary. -/
theorem exists_outer_subset_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (A D : Finset ℕ) (y u : ℝ),
        0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        (∀ n ∈ D, ¬((244/125 : ℝ)*N < Real.log n ∧
          Real.log n ≤ (2029/1000 : ℝ)*N)) →
        ‖(u : ℂ)^(N+1)*∑ n ∈ D,
          residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,h⟩ := ZetaArithmeticDeviationBounds.exists_uniform_deviation_bound
    (1 : Polynomial ℂ) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 244/125) (by norm_num) (by norm_num : (2 : ℝ) < 2029/1000)
    radial_edge_costs.1 radial_edge_costs.2
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro N A D y u hu hU hD
  have he : LogarithmicDeviation.deviationBand D (244/125) (2029/1000) N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnD,hlo,hhi⟩ := Finset.mem_filter.mp hn
    exact hD n hnD ⟨hlo,hhi⟩
  have hb := h N D (residualCoefficient A (SquarefreeVaughanLogSource.length u N) N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu hU
  simpa only [he,Finset.sum_empty,sub_zero,zetaPrimeLogKernel,
    SquarefreeEulerQuadratic.primeFilterKernel_one] using hb

/-- The ENTIRE actual unpaid five-prime sector has a signed floor with
arbitrarily small complete-period debit and source-geometric errors.
The dominant allocation, close-owner boundary and outer radial strips
are paid here; no unmatched five-prime sign part remains in this inequality. -/
theorem exists_unpaid_five_floor {u y ε : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) (hε : 0 < ε) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∀ (Q P V R : ℕ) (η h : ℝ) (w : ℕ → ℝ),
        0 < h → h ≤ 1/20 →
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) →
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
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
  filter_upwards [eventually_unpaid_five_sign_floor hu hU hy (half_pos hε),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszOwnerTieFloor.eventually_core_grouped_tie_floor hu hU (half_pos hε)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hperiod htie hN hj Q P V R η h w hh hhu hw
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
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
  let Y := J.biUnion (fun i => roughPeriod V (center (Real.pi/y+Real.pi/y) y i) y)
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

/-- The entire unpaid five-prime sector leaves the actual joined floor.
The SAME original supply pays its complete-period and close-owner costs,
with 1/128 still unspent. Every older credit, other unpaid count, higher-count
saving and geometric error remains. This does not evaluate the remaining
signed aggregate or assert the numerical -79/1000 floor. -/
theorem eventually_joined_floor_without_fives {u y : ℝ} (hu : 1/2 < u)
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
        let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
        let Eo := E\E5
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
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩ := exists_unpaid_five_floor hu hU hy hκ
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
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+d j+2*r₁^(dyadicMomentOrder j)*C₁
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := ((h₀.add heLim).add hdLim).add h₁
    simp only [zero_mul,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1 : ℕ))]
      with j hj hfive hbound hN
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
  let Eo := E\E5
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
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*κ*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  have hbudget := period_grids_cost_paid hN hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-d j-2*r₁^N*C₁ ≤
      ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re := by
    linarith only [hscaled,hp]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb hpaid
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 5) E) (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ E5, f n).re = (∑ n ∈ E, f n).re at hs
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
      (r₀^N*C₀+e j+d j+2*r₁^N*C₁) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaid,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring

end RiemannGaussian.ZetaRieszFiveSignCoverFloor
