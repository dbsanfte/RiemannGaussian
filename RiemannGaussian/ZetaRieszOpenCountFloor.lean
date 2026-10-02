/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFixedOwnerPairFloor

/-!
# Join the native count bands before spending parity partners

The existing whole floor permits both positive-part credits to be kept
with their actual signed coefficients. Rejoining them removes the artificial
fixed/dense/few-bin/many-bin boundaries from admissible partner support.
The original four-prime supply debit remains once, including its overlap.
Every included label of count at least five has original coefficient one.
Matching capacity and the signed unmatched floor remain open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszOpenCountFloor
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency ZetaRieszParityPacket
open ZetaRieszSevenCountTail ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor
open ZetaRieszDenseCountCoverFloor ZetaRieszFewBinCoverFloor
open ZetaRieszLowCountRefund (tailCost wholeTail_zero_eq)

/-- This is a union of ORIGINAL support sets, not a completed carrier.
Every formerly separated count/bin band below the whole tail is included. -/
def openSupport (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (S\wholeTail S N 0) ∪ radialTail S N 0

/-- The existing fixed/dense/few-bin credits, used once in their signed form. -/
def paidSupport (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (((coreBand u N K).filter (fun n : ℕ =>
    3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)) ∪ dense56Band u N K) ∪
      bin56Band u N K

/-- All original credited native labels lie below the whole logarithmic
tail. The real count/bin boundaries do not create a support gap here. -/
theorem paidSupport_subset {N : ℕ} (hN : 1000 ≤ N) (u : ℝ) (K : ℕ) :
    paidSupport u N K ⊆ coreBand u N K\wholeTail (coreBand u N K) N 0 := by
  intro n hn
  rcases Finset.mem_union.mp hn with hn|hn
  · rcases Finset.mem_union.mp hn with hn|hn
    · obtain ⟨hn,hcnt⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_sdiff.mpr ⟨hn,?_⟩
      rw [wholeTail_zero_eq]
      intro ht
      have hc := (Finset.mem_filter.mp ht).2.2
      have hh := ZetaRieszRejoinedSupplyFloor.countThreshold_gt_fiftyFive hN
      omega
    · obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn,_,_,_,hcnt⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_sdiff.mpr ⟨hn,by
        rw [wholeTail_zero_eq]
        intro ht
        exact (not_le_of_gt hcnt) (Finset.mem_filter.mp ht).2.2⟩
  · obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,_,_,_,hcnt⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_sdiff.mpr ⟨hn,by
      rw [wholeTail_zero_eq]
      intro ht
      exact (not_le_of_gt hcnt) (Finset.mem_filter.mp ht).2.2⟩

/-- Recombine every original credited count/bin population in the SAME
complex sum. This adds no favorable credit or new prime label. -/
theorem sum_openSupport_eq (S P : Finset ℕ) (N : ℕ)
    (hP : P ⊆ S\wholeTail S N 0) (f : ℕ → ℂ) :
    (∑ n ∈ openSupport S N,f n) =
      (∑ n ∈ S\(P ∪ wholeTail S N 0),f n)+
      (∑ n ∈ P,f n)+(∑ n ∈ radialTail S N 0,f n) := by
  have hd : Disjoint (S\wholeTail S N 0) (radialTail S N 0) := by
    apply Finset.disjoint_left.mpr
    intro n hn ht
    exact (Finset.mem_sdiff.mp hn).2
      (ZetaRieszRejoinedSupplyFloor.radialTail_subset_whole S N 0 ht)
  have he : (S\wholeTail S N 0)\P=S\(P ∪ wholeTail S N 0) := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [openSupport,Finset.sum_union hd,← Finset.sum_sdiff (f := f) hP,he]

/-- Retain all original count/bin partners with signed coefficient one,
the previously proved owner crop, and the SAME supply debit. No bin or
dense-count condition remains in the main support. The numerical floor
and matching capacity are still open. -/
theorem eventually_joined_floor_open_counts {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j,0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j),0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N K
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let R := openSupport S N\ZetaRieszSharpOwnerPayment.sector u N K
        let Y := radialSupply N h w
        0 < (∑ n ∈ Y,f n).re ∧
          u^(N+1)*((∑ n ∈ R,f n).re-
            (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Y,f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    eventually_joined_floor_rejoined_populations hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨e,he0,he,hfloor⟩ := hbase ε hε
  refine ⟨fun j => e j+ZetaRieszSharpOwnerPayment.allowance (dyadicMomentOrder j),
    (fun j => add_nonneg (he0 j) (ZetaRieszSharpOwnerPayment.allowance_nonneg _)),?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using
      he.add (ZetaRieszSharpOwnerPayment.tendsto_allowance.comp tendsto_dyadicMomentOrder)
  · filter_upwards [hfloor,eventually_ge_atTop (32 : ℕ),
      tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
      with j hj hj32 hN
    obtain ⟨w,hw,hpos,hbound⟩ := hj
    refine ⟨w,hw,hpos,?_⟩
    let N := dyadicMomentOrder j
    let K := dyadicPrimeCount j
    let S := coreBand u N K
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let P := paidSupport u N K
    let H := S\(P ∪ wholeTail S N 0)
    let T := radialTail S N 0
    let Y := radialSupply N h w
    have hsum := congrArg Complex.re (sum_openSupport_eq S P N (paidSupport_subset hN u K) f)
    simp only [Complex.add_re] at hsum
    change (∑ n ∈ openSupport S N,f n).re=
      (∑ n ∈ H,f n).re+(∑ n ∈ P,f n).re+(∑ n ∈ T,f n).re at hsum
    have hlo : u^(N+1)*((∑ n ∈ openSupport S N,f n).re-
        (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Y,f n).re)-e j ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
      have hp := le_max_left (∑ n ∈ P,f n).re 0
      have ht := le_max_left (∑ n ∈ T,f n).re 0
      have hu0 : 0 ≤ u^(N+1) := by positivity
      change u^(N+1)*((∑ n ∈ H,f n).re+max (∑ n ∈ P,f n).re 0+
        max (∑ n ∈ T,f n).re 0-
          (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Y,f n).re)-e j ≤ _ at hbound
      rw [hsum]
      nlinarith only [hbound,hp,ht,hu0]
    have hcrop := ZetaRieszSharpOwnerPayment.subset_crop_floor j hj32 hu.le hU y
      (openSupport S N)
    change u^(N+1)*(∑ n ∈ openSupport S N\ZetaRieszSharpOwnerPayment.sector u N K,f n).re-
      ZetaRieszSharpOwnerPayment.allowance N ≤ u^(N+1)*(∑ n ∈ openSupport S N,f n).re at hcrop
    change u^(N+1)*((∑ n ∈ openSupport S N\ZetaRieszSharpOwnerPayment.sector u N K,f n).re-
      (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Y,f n).re)-
        (e j+ZetaRieszSharpOwnerPayment.allowance N) ≤ _
    nlinarith only [hlo,hcrop]

/-- The unchanged supply overlap is retained exactly. There is ONE
signed coefficient, not a separate favorable label and a separate debit. -/
def joinedFunding (R Y : Finset ℕ) (debit : ℝ) (n : ℕ) : ℝ :=
  (if n ∈ R then 1 else 0)-debit*(if n ∈ Y then 1 else 0)

/-- Incorporate the SAME debit inside the original complex sum. No
disjointness is assumed and an overlapping supply label receives1-debit. -/
theorem joinedFunding_sum (R Y : Finset ℕ) (debit : ℝ) (f : ℕ → ℂ) :
    (∑ n ∈ R ∪ Y,(joinedFunding R Y debit n : ℂ)*f n)=
      (∑ n ∈ R,f n)-(debit : ℂ)*(∑ n ∈ Y,f n) := by
  have hi (V : Finset ℕ) (hV : V ⊆ R ∪ Y) :
      (∑ n ∈ R ∪ Y,Complex.ofReal (if n ∈ V then 1 else 0)*f n)=∑ n ∈ V,f n := by
    simp only [apply_ite,Complex.ofReal_one,Complex.ofReal_zero,
      ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hV]
  have hR := hi R (Finset.subset_union_left)
  have hY := hi Y (Finset.subset_union_right)
  simp only [joinedFunding,Complex.ofReal_sub,Complex.ofReal_mul,sub_mul,mul_assoc,
    Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hR,hY]

/-- Above prime count four the ORIGINAL funding coefficient is exactly
one on the joined support, even across every previous count/bin boundary.
There is no assumed equality of partners' funding weights. -/
theorem joinedFunding_one_above_four {N : ℕ} (hN : 1000 ≤ N) {h : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/20) (w : ℕ → ℝ)
    (hw : ∀ M ∈ radialIndices N,0 ≤ w M ∧ w M ≤ 1/2)
    (R : Finset ℕ) (debit : ℝ) {n : ℕ} (hn : n ∈ R)
    (hc : 5 ≤ n.primeFactors.card) :
    joinedFunding R (radialSupply N h w) debit n=1 := by
  have hY : n ∉ radialSupply N h w := by
    intro hy
    have ht := ZetaRieszRoughFivePeriodFloor.radialSupply_count hN hh hhu w hw hy
    omega
  simp only [joinedFunding,if_pos hn,if_neg hY,mul_zero,sub_zero]

/-- The actual funding supply has all prime logarithms below3N/5.
This is a literal tuple bound and does not approximate prime density. -/
theorem radialSupply_prime_log_le {N : ℕ} (hN : 1000 ≤ N) {h : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/20) (w : ℕ → ℝ)
    (hw : ∀ M ∈ radialIndices N,0 ≤ w M ∧ w M ≤ 1/2)
    {n p : ℕ} (hn : n ∈ radialSupply N h w) (hp : p.Prime) (hd : p ∣ n) :
    log p ≤ (3/5 : ℝ)*N := by
  obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨a,_,hpa⟩ := (hp.prime.dvd_finsetProd_iff v).mp hd
  have he : p=v a := (Nat.prime_dvd_prime_iff_eq hp (tuple_bounds hv a).1).mp hpa
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hMb := (Finset.mem_filter.mp hM).2
  have hsize : h+w M ≤ (M : ℝ)/1000 := by linarith [(hw M hM).2]
  have hb := start_bounds hh hi hj hk (hw M hM).1 hsize a
  have hl := (tuple_bounds hv a).2.2
  rw [he]
  linarith [hb.2,hMb.2]

/-- Every original inner hinge on the core has a prime logarithm at
least18N/25. In particular it cannot be a four-prime funding label. -/
theorem innerHinge_prime_log_lower {N p q b : ℕ} {L : ℝ}
    (hp : p.Prime) (hb : b ≠ 0)
    (hi : ZetaRieszInnerHingeTransport.InnerHinge L p q b)
    (hL : (11/8 : ℝ)*N ≤ L) (hT : log (p*(q*b) : ℕ) ≤ (203/100 : ℝ)*N) :
    (18/25 : ℝ)*N ≤ log p := by
  have hlog : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hb)]
  have hsmall := hi.2.1
  have hhinge := hi.2.2.1
  rw [hlog] at hhinge
  linarith

/-- No admissible inner-hinge label meets the original supply, INCLUDING
count four. The two actual prime-log geometries are disjoint. -/
theorem innerHinge_not_radialSupply {N p q b : ℕ} (hN : 1000 ≤ N) {h L : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/20) (w : ℕ → ℝ)
    (hw : ∀ M ∈ radialIndices N,0 ≤ w M ∧ w M ≤ 1/2)
    (hp : p.Prime) (hb : b ≠ 0)
    (hi : ZetaRieszInnerHingeTransport.InnerHinge L p q b)
    (hL : (11/8 : ℝ)*N ≤ L) (hT : log (p*(q*b) : ℕ) ≤ (203/100 : ℝ)*N) :
    p*(q*b) ∉ radialSupply N h w := by
  intro hn
  have hlo := innerHinge_prime_log_lower hp hb hi hL hT
  have hhi := radialSupply_prime_log_le hN hh hhu w hw hn hp (dvd_mul_right p (q*b))
  have hnR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- Every literal joined inner-hinge partner has funding coefficient1,
even in the old count-four band. This follows from exact supply geometry,
not a postulated partner-funding equality. -/
theorem joinedFunding_one_innerHinge {N p q b : ℕ} (hN : 1000 ≤ N) {h L : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/20) (w : ℕ → ℝ)
    (hw : ∀ M ∈ radialIndices N,0 ≤ w M ∧ w M ≤ 1/2)
    (R : Finset ℕ) (debit : ℝ) (hn : p*(q*b) ∈ R)
    (hp : p.Prime) (hb : b ≠ 0)
    (hi : ZetaRieszInnerHingeTransport.InnerHinge L p q b)
    (hL : (11/8 : ℝ)*N ≤ L) (hT : log (p*(q*b) : ℕ) ≤ (203/100 : ℝ)*N) :
    joinedFunding R (radialSupply N h w) debit (p*(q*b))=1 := by
  have hY := innerHinge_not_radialSupply hN hh hhu w hw hp hb hi hL hT
  simp only [joinedFunding,if_pos hn,if_neg hY,mul_zero,sub_zero]

/-- One absolute matched price for the newly joined original support.
The funding constant is1, not the old4+abs(epsilon) envelope. -/
def matchingBudget (N : ℕ) (y : ℝ) : ℝ :=
  (168*ZetaRieszWideOwnerAudit.radiusCeiling*(1+|y|)+
    2*ZetaRieszWideOwnerAudit.radiusCeiling*zetaMoebiusLogMajorantMass (1+1/262144))*
      ((N : ℝ)+1)^3*exp (-(N : ℝ)/1250)+
  (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
    ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))

/-- Both matching costs have strict geometric source decay; no
relative-supply payment is promoted to an absolute estimate. -/
theorem tendsto_matchingBudget (y : ℝ) :
    Tendsto (fun N : ℕ => matchingBudget N y) atTop (𝓝 0) := by
  have hgap := ZetaRieszInnerHingeGapPayment.tendsto_gap_price
    (168*ZetaRieszWideOwnerAudit.radiusCeiling*(1+|y|)+
      2*ZetaRieszWideOwnerAudit.radiusCeiling*zetaMoebiusLogMajorantMass (1+1/262144))
  have ho := tendsto_ownerPaymentError
  simpa only [matchingBudget,ownerPaymentError,add_zero] using hgap.add ho

/-- Directly remove any admissible fixed-owner matching from the
CURRENT joined signed floor, with no equality-of-funding hypothesis and
no bin/count-sector boundary price. The same supply debit and every
original unmatched atom are retained. Native coverage is not asserted. -/
theorem floor_after_matching (A R Y : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : ZetaRieszPairMatching.separatedPairs E) (hR : E ⊆ R ×ˢ R)
    {N : ℕ} (hN : 32 ≤ N) (Q K : ℕ)
    (hQ : ZetaRieszPairMatching.matchedVertices E ⊆ Finset.Icc 1 Q)
    (hlogQ : log Q ≤ 3*((N : ℝ)+1)) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y debit err : ℝ)
    (hD : ZetaRieszPairMatching.matchedVertices E ⊆ literalWindow N)
    (hdata : ∀ n ∈ ZetaRieszPairMatching.matchedVertices E,
      Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ ZetaRieszPrimeEndpoint.largestPrime n ∈ A)
    (hfix : ∀ e ∈ E,
      ZetaRieszPrimeEndpoint.largestPrime e.1=ZetaRieszPrimeEndpoint.largestPrime e.2)
    (hgap : ∀ e ∈ E,|log e.1-log e.2| ≤ exp (-(N : ℝ)/1000))
    (hgeom : ∀ e ∈ E,∃ p p' q b b' : ℕ,
      p.Prime ∧ p'.Prime ∧ q.Prime ∧ Squarefree b ∧ Squarefree b' ∧
      2 ≤ b.primeFactors.card ∧ 2 ≤ b'.primeFactors.card ∧ ¬q ∣ b ∧ ¬q ∣ b' ∧
      ¬p ∣ q*b ∧ ¬p' ∣ q*b' ∧ μ b'= -(μ b) ∧ e.1=p*(q*b) ∧ e.2=p'*(q*b') ∧
      ZetaRieszInnerHingeTransport.InnerHinge L p q b ∧
        ZetaRieszInnerHingeTransport.InnerHinge L p' q b')
    (hfloor : u^(N+1)*((∑ n ∈ R,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      debit*(∑ n ∈ Y,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-err ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re) :
    u^(N+1)*((∑ n ∈ R\ZetaRieszPairMatching.matchedVertices E,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      debit*(∑ n ∈ Y,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)-err-matchingBudget N y ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  have hb := ZetaRieszFixedOwnerPairFloor.matching_original_signed_error A R E hE hR
    hN Q hQ hlogQ hL hu hU (by norm_num : (0 : ℝ) < 1) y (fun _ => 1)
    (by intro _ _; norm_num) hD hdata hfix (by intro _ _; rfl) hgap hgeom
  simp only [one_mul,mul_one] at hb
  change ‖(u : ℂ)^(N+1)*((∑ n ∈ R,residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      ∑ n ∈ R\ZetaRieszPairMatching.matchedVertices E,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤ matchingBudget N y at hb
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  have he (z : ℂ) : ((u : ℂ)^(N+1)*z).re=u^(N+1)*z.re := by
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [he,Complex.sub_re] at hr
  nlinarith only [hr,hfloor]

end RiemannGaussian.ZetaRieszOpenCountFloor
