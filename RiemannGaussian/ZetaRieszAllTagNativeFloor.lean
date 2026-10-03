/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeHeadPeriods

/-!
# Pay every small-prime tag in the native owner window

Use the checked signed counting theorem with ALL primes through N^3 as
possible least tags, including primes below N^2. The original native
count/window theorem supplies the physical masks without deleting these
tags. The error budget is unchanged. No zero hypothesis is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszAllTagNativeFloor
open ZetaRieszTaggedCoreWindow ZetaRieszOwnerLatticePhase
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszPrimeEndpoint ZetaRieszCutoffPeriodFloor
open ZetaRieszSmallTagNativeFloor (smallPrimes owners owners_data
  eventually_native_comparison comparisonCutoff length_upper
  nonownerBudget nonownerBudget_tendsto)

/-- Every least small-prime tag is retained, including tags <=N^2. -/
def rows (u : ℝ) (j : ℕ) : Finset (ℕ×ℕ) :=
  (selectedRows (smallPrimes (dyadicMomentOrder j))
    (smallPrimes (dyadicMomentOrder j)) (owners u (dyadicMomentOrder j))
      (dyadicMomentOrder j)).filter (fun pa =>
        (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j)

/-- Disjoint physical product labels of the complete small-prime union. -/
def labels (u : ℝ) (j : ℕ) : Finset ℕ :=
  (rows u j).image (fun pa => pa.1*pa.2)

theorem rows_data {u : ℝ} {j : ℕ} (hN : 64≤dyadicMomentOrder j)
    {pa : ℕ×ℕ} (hpa : pa∈rows u j) :
    pa.1.Prime ∧ Squarefree pa.2 ∧ 1<pa.2 ∧ ¬pa.2.Prime ∧ pa.2<pa.1 ∧
      pa.1∈owners u (dyadicMomentOrder j) ∧
      pa.2∈Finset.Ioc (coreFloor (dyadicMomentOrder j) (log pa.1) (39/20))
        (coreFloor (dyadicMomentOrder j) (log pa.1) (203/100)) ∧
      (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j := by
  obtain ⟨hs,hcount⟩ := Finset.mem_filter.mp hpa
  have h := selectedRows_data _ _ _ _ hs
  obtain ⟨hp,hA,hlo,hhi⟩ := owners_data h.1
  have hn : (64 : ℝ)≤dyadicMomentOrder j := by exact_mod_cast hN
  have hc : log pa.1≤(4/3 : ℝ)*dyadicMomentOrder j := by linarith only [hhi,hn]
  have hm := (coreFloor_geometry hN hc).1
  have hg := full_core_owner_geometry hN hp hlo hhi
  refine ⟨hp,h.2.2.1,?_,h.2.2.2.1,(Finset.mem_Ioc.mp h.2.1).2.trans_lt hg.1,
    h.1,h.2.1,hcount⟩
  have ha := (Finset.mem_Ioc.mp h.2.1).1
  omega

theorem rows_injective {u : ℝ} {j : ℕ} (hN : 64≤dyadicMomentOrder j) :
    Set.InjOn (fun pa : ℕ×ℕ => pa.1*pa.2) (rows u j) :=
  ZetaRieszRoughOwnerComparison.owned_rows_injective _ (fun pa hpa => by
    have h := rows_data hN hpa
    exact ⟨h.1,h.2.1,h.2.2.2.2.1⟩)

/-- The disjoint paid labels satisfy every original native mask. The
proof rules out the old cancellation/dominant sectors using their exact
share thresholds; no mask-completion error is being assumed. -/
theorem eventually_labels_subset_native {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ j in atTop, labels u j⊆ZetaRieszPaidIncidenceFloor.nativeLabels u j ∧
      ∀ n∈labels u j, Squarefree n := by
  have hs : u≤exp (-(11/16 : ℝ)) := hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le
  filter_upwards [eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ)),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszMaskSupport.eventually_length_lower (by linarith : 0<u) hs)]
    with j hj hN hL
  have hd n (hn : n∈labels u j) :
      n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j ∧ Squarefree n := by
    obtain ⟨⟨p,a⟩,hpa,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hpp,has,ha1,hap,haplt,hP,hi,hcount⟩ := rows_data hN hpa
    obtain ⟨_,hA,hlo,hhi⟩ := owners_data hP
    have hpad : ¬p∣a := fun h =>
      (Nat.le_of_dvd (by omega : 0<a) h).not_gt haplt
    have hsf : Squarefree (p*a) := Nat.squarefree_mul_iff.mpr
      ⟨hpp.coprime_iff_not_dvd.mpr hpad,hpp.squarefree,has⟩
    have hc3 := ZetaRieszMaskSupport.eligible_product_count_ge_three hpp
      (show eligibleCofactor p a from ⟨has,by omega,hap,hpad⟩)
    have hb := (coreFloor_membership (dyadicMomentOrder j) (log p) (by omega : 0<a)).mp hi
    have hl : log (p*a : ℕ)=log p+log a := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
        (by exact_mod_cast (Nat.ne_of_gt (by omega : 0<a)))]
    have hw : p*a∈literalWindow (dyadicMomentOrder j) := by
      apply (mem_literalWindow _ _).mpr
      rw [hl]
      have hn : (0 : ℝ)≤dyadicMomentOrder j := Nat.cast_nonneg _
      constructor <;> linarith only [hb.1,hb.2,hn]
    have hmax : largestPrime (p*a)=p :=
      ZetaRieszPrimeIntervals.largestPrime_mul p a hpp has.ne_zero (fun q hq =>
        (Nat.le_of_dvd (by omega : 0<a) (Nat.dvd_of_mem_primeFactors hq)).trans_lt haplt)
    have hqle q (hq : q∈(p*a).primeFactors) : q≤p := by
      rw [← hmax]
      have he : (p*a).primeFactors.Nonempty := ⟨q,hq⟩
      rw [largestPrime,dif_pos he]
      exact Finset.le_max' _ _ hq
    have hphys : ∀ q∈(p*a).primeFactors,
        q<(ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2 :=
      fun q hq => (hqle q hq).trans_lt
        ((ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mp hA).2.2
    have hcK := hcount.trans_le (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2
    have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu hs hL hw hsf hc3 hcK hphys
    have hpnd := (full_core_owner_geometry hN hpp hlo hhi).2 a hi
    have hqnd q (hq : q∈(p*a).primeFactors) :
        log q<(13/20 : ℝ)*log (p*a : ℕ) :=
      (log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
        (by exact_mod_cast hqle q hq)).trans_lt hpnd
    have hlog0 : 0<log (p*a : ℕ) := by
      rw [hl]
      nlinarith only [hb.1,Nat.cast_nonneg (α:=ℝ) (dyadicMomentOrder j)]
    have hnoc : p*a∉cancellingSector u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
      intro hh
      obtain ⟨_,_,_,_,_,q,hq,_,_,_,hshare⟩ := Finset.mem_filter.mp hh
      have hq0 := (Nat.prime_of_mem_primeFactors hq).pos
      have hqa0 : 0<(p*a)/q := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) (Nat.dvd_of_mem_primeFactors hq)) hq0
      have hquot : log (p*a : ℕ)=log ((p*a)/q : ℕ)+log q := by
        conv_lhs => rw [← Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hq)]
        rw [Nat.cast_mul,log_mul (by exact_mod_cast Nat.ne_of_gt hqa0)
          (by exact_mod_cast Nat.ne_of_gt hq0)]
      have hd := (div_le_iff₀ hlog0).mp hshare
      have hnd := hqnd q hq
      linarith only [hd,hquot,hnd,hlog0]
    have hret : p*a∈ZetaRieszMaskSupport.retainedBand u (dyadicMomentOrder j) (dyadicPrimeCount j) :=
      Finset.mem_sdiff.mpr ⟨hm,hnoc⟩
    have hnod : p*a∉ZetaRieszDominantAllocation.dominantSector u (dyadicMomentOrder j)
        (dyadicPrimeCount j) := by
      intro hh
      obtain ⟨_,_,_,_,q,hq,_,_,hg⟩ := Finset.mem_filter.mp hh
      exact (hqnd q hq).not_ge hg
    have hnond : p*a∈ZetaRieszDominantAllocation.nondominantBand u (dyadicMomentOrder j)
        (dyadicPrimeCount j) := Finset.mem_sdiff.mpr ⟨hret,hnod⟩
    have hnarrow : p*a∈ZetaRieszTypeII.narrowBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
      apply Finset.mem_filter.mpr
      rw [hl]
      refine ⟨hnond,hb.1,?_⟩
      linarith only [hb.2,Nat.cast_nonneg (α:=ℝ) (dyadicMomentOrder j)]
    have hcore : p*a∈ZetaRieszParityPacket.coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
      apply Finset.mem_filter.mpr
      rw [hl]
      exact ⟨hnarrow,hb⟩
    refine ⟨?_,hsf⟩
    unfold ZetaRieszPaidIncidenceFloor.nativeLabels
    rw [ZetaRieszJointCountFloor.coreBand_count_filter _ _ _ _
      (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2]
    exact Finset.mem_filter.mpr ⟨hcore,hcount⟩
  exact ⟨fun n hn => (hd n hn).1,fun n hn => (hd n hn).2⟩

/-- The original full allocation, on the disjoint native paid labels. -/
def packet (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈labels u j,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

/-- The same population with only its canonical owner's old allocation. -/
def ownerPacket (u y : ℝ) (j : ℕ) : ℝ :=
  u^(dyadicMomentOrder j+1)*∑ n∈labels u j,
    (residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

theorem eventually_ownerPacket_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop, |ownerPacket u y j| ≤ selectedNativeBudget u y j := by
  filter_upwards [eventually_cropped_selected_core_bound,
    tendsto_dyadicMomentOrder.eventually (eventually_native_comparison hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ)),
    tendsto_dyadicMomentOrder.eventually (ZetaRieszMaskSupport.eventually_length_lower
      (by linarith : 0<u) (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le))]
    with j hj hg hN hL
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let Q := (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hpos : 0<L := by dsimp only [L]; linarith only [hL,hn]
  have hQ : log Q≤(203/100 : ℝ)*N := by
    have he : log Q=L := by
      simp only [Q,L,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    rw [he]
    have hl := length_upper hu.le (show 2≤N by omega)
    linarith only [hl,hn]
  have h := hj (smallPrimes N) (smallPrimes N)
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) (owners u N)
    (fun _ => comparisonCutoff N) Q L u y hpos (by linarith) hU hy
    (fun r hr => by
      have h := Nat.mem_primesLE.mp hr
      exact ⟨h.2,h.1⟩)
    (Finset.Subset.refl _)
    (fun p hp => by
      obtain ⟨hpp,hA,hpQ,hp1,hpc,hpL,_⟩ := hg p hp
      exact ⟨hpp,hA,hpQ,hp1,hpc,hpL⟩) hQ
    (fun p hp => by
      obtain ⟨_,_,_,_,_,_,hM,hX,_⟩ := hg p hp
      exact ⟨hM,hX⟩)
    (fun p hp => by
      obtain ⟨_,_,_,_,_,_,_,_,hR⟩ := hg p hp
      exact hR)
  have hi := Finset.sum_image (rows_injective (u:=u) hN)
    (f:=fun n => (residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime n}) L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)
  unfold ownerPacket labels
  rw [hi]
  exact h

/-- One signed row/count budget plus one existing nonowner error. -/
def budget (u y : ℝ) (j : ℕ) : ℝ :=
  selectedNativeBudget u y j+nonownerBudget (dyadicMomentOrder j)

theorem budget_tendsto (u y : ℝ) : Tendsto (budget u y) atTop (𝓝 0) := by
  have ht := (selectedNativeBudget_tendsto u y).add
    (nonownerBudget_tendsto.comp tendsto_dyadicMomentOrder)
  change Tendsto (fun j => selectedNativeBudget u y j+nonownerBudget (dyadicMomentOrder j))
    atTop (𝓝 0)
  simpa only [Function.comp_apply,zero_add] using ht

/-- An independent arithmetic estimate for actual native labels, full
allocation and full phase. It assumes neither a zero nor an arithmetic
cancellation bound. Every least-tag/count/nonowner payment occurs once. -/
theorem eventually_packet_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop, |packet u y j|≤budget u y j := by
  filter_upwards [eventually_ownerPacket_bound hu hU hy,
    eventually_labels_subset_native hu hU,
    tendsto_dyadicMomentOrder.eventually (ZetaRieszMaskSupport.eventually_length_lower
      (by linarith : 0<u) (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ))]
    with j howner hsub hL hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hpos : 0<L := by dsimp only [L]; linarith only [hL,hn]
  have hW : labels u j⊆literalWindow N := fun n hn =>
    ZetaRieszNonownerAllocation.coreBand_subset_literalWindow _ _ _ (hsub.1 hn)
  have he := ZetaRieszNonownerAllocation.residual_sub_owner_bound
    (fun _ => A) (labels u j) (fun _ => (1 : ℂ)) hpos N hW
      (fun _ _ => by norm_num) y (by linarith : 0≤u)
        (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  simp only [one_mul] at he
  have hdiff : |packet u y j-ownerPacket u y j|≤nonownerBudget N := by
    have hr := Complex.abs_re_le_norm ((u : ℂ)^(N+1)*∑ n∈labels u j,
      (residualCoefficient A L N n-residualCoefficient (A∩{largestPrime n}) L N n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    have hh := hr.trans he
    simpa only [packet,ownerPacket,sub_mul,Finset.sum_sub_distrib,mul_sub,Complex.sub_re,
      ← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_sum,zero_mul,sub_zero,nonownerBudget] using hh
  have ht := abs_add_le (packet u y j-ownerPacket u y j) (ownerPacket u y j)
  unfold budget
  have htri : |packet u y j|≤|packet u y j-ownerPacket u y j|+|ownerPacket u y j| :=
    by simpa only [sub_add_cancel] using ht
  linarith only [htri,hdiff,howner]

theorem tendsto_packet {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (packet u y) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (budget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_packet_bound hu hU hy

/-- Retaining ALL least small tags requires no larger error budget. -/
theorem budget_eq_previous (u y : ℝ) (j : ℕ) :
    budget u y j=ZetaRieszSmallTagNativeFloor.budget u y j := rfl

private theorem exists_leastTag (T : Finset ℕ) (a : ℕ) :
    (∃ r∈T,(¬∃ q∈leastTagExclusions T r,q∣a) ∧ r∣a) ↔ ∃ r∈T,r∣a := by
  constructor
  · rintro ⟨r,hr,_,hra⟩
    exact ⟨r,hr,hra⟩
  · intro h
    have he : (T.filter (fun r => r∣a)).Nonempty := by
      obtain ⟨r,hr,hra⟩ := h
      exact ⟨r,Finset.mem_filter.mpr ⟨hr,hra⟩⟩
    let r := (T.filter (fun r => r∣a)).min' he
    have hr := Finset.mem_filter.mp (Finset.min'_mem _ he)
    refine ⟨r,hr.1,?_,hr.2⟩
    rintro ⟨q,hq,hqa⟩
    have hq' := Finset.mem_filter.mp hq
    have hmin : r≤q := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hq'.1,hqa⟩)
    exact (not_lt_of_ge hmin) hq'.2

private theorem mem_rows {u : ℝ} {j : ℕ} {pa : ℕ×ℕ} :
    pa∈rows u j ↔ pa.1∈owners u (dyadicMomentOrder j) ∧
      pa.2∈Finset.Ioc (coreFloor (dyadicMomentOrder j) (log pa.1) (39/20))
        (coreFloor (dyadicMomentOrder j) (log pa.1) (203/100)) ∧
      Squarefree pa.2 ∧ ¬pa.2.Prime ∧
      (∃ r∈smallPrimes (dyadicMomentOrder j),r∣pa.2) ∧
      (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j := by
  constructor
  · intro h
    obtain ⟨hs,hcount⟩ := Finset.mem_filter.mp h
    obtain ⟨hp,hi,hsf,hnp,htag⟩ := selectedRows_data _ _ _ _ hs
    exact ⟨hp,hi,hsf,hnp,(exists_leastTag _ _).mp htag,hcount⟩
  · rintro ⟨hp,hi,hsf,hnp,htag,hcount⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨⟨pa.1,pa.2⟩,?_,by simp⟩,hcount⟩
    exact Finset.mem_sigma.mpr ⟨hp,Finset.mem_filter.mpr
      ⟨hi,hsf,hnp,(exists_leastTag _ _).mpr htag⟩⟩

private theorem mem_roughRows {u : ℝ} {j : ℕ} {pa : ℕ×ℕ} :
    pa∈ZetaRieszRoughPrimePairCancellation.rows u j ↔
      pa.1∈owners u (dyadicMomentOrder j) ∧
      pa.2∈Finset.Ioc (coreFloor (dyadicMomentOrder j) (log pa.1) (39/20))
        (coreFloor (dyadicMomentOrder j) (log pa.1) (203/100)) ∧
      Squarefree pa.2 ∧ ¬pa.2.Prime ∧
      (¬∃ r∈smallPrimes (dyadicMomentOrder j),r∣pa.2) ∧
      (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j := by
  constructor
  · intro h
    obtain ⟨hs,hcount⟩ := Finset.mem_filter.mp h
    obtain ⟨hp,hi,hsf,hnp,htag⟩ := ZetaRieszRoughPrimePairCancellation.completeRows_data hs
    exact ⟨hp,hi,hsf,hnp,htag,hcount⟩
  · rintro ⟨hp,hi,hsf,hnp,htag,hcount⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨⟨pa.1,pa.2⟩,?_,by simp⟩,hcount⟩
    exact Finset.mem_sigma.mpr ⟨hp,Finset.mem_filter.mpr ⟨hi,hsf,hnp,htag⟩⟩

/-- All cofactor geometries are now covered in the retained owner range:
there is NO small/rough or least-prime restriction on the right. -/
theorem owner_rows_complete {u : ℝ} {j : ℕ} {pa : ℕ×ℕ} :
    pa∈rows u j∪ZetaRieszRoughPrimePairCancellation.rows u j ↔
      pa.1∈owners u (dyadicMomentOrder j) ∧
      pa.2∈Finset.Ioc (coreFloor (dyadicMomentOrder j) (log pa.1) (39/20))
        (coreFloor (dyadicMomentOrder j) (log pa.1) (203/100)) ∧
      Squarefree pa.2 ∧ ¬pa.2.Prime ∧
      (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j := by
  rw [Finset.mem_union,mem_rows,mem_roughRows]
  by_cases h : ∃ r∈smallPrimes (dyadicMomentOrder j),r∣pa.2 <;> simp [h]

/-- Every previous small-tag payment is included, never spent twice. -/
theorem previous_labels_subset (u : ℝ) (j : ℕ) :
    ZetaRieszSmallTagNativeFloor.labels u j⊆labels u j := by
  intro n hn
  obtain ⟨pa,hpa,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hs,hcount⟩ := Finset.mem_filter.mp hpa
  have hd := selectedRows_data _ _ _ _ hs
  obtain ⟨r,hr,_hrest,hra⟩ := hd.2.2.2.2
  have hrT : r∈smallPrimes (dyadicMomentOrder j) := (Finset.mem_filter.mp hr).1
  exact Finset.mem_image.mpr ⟨pa,mem_rows.mpr
    ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,⟨r,hrT,hra⟩,hcount⟩,rfl⟩

/-- Exactly the additional native labels, excluding all previously paid
small-tag labels. Full allocation and product phase remain unchanged. -/
def addedPacket (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*
    ∑ n∈labels u j\ZetaRieszSmallTagNativeFloor.labels u j,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

theorem addedPacket_eq (u y : ℝ) (j : ℕ) :
    addedPacket u y j=packet u y j-ZetaRieszSmallTagNativeFloor.packet u y j := by
  simp only [addedPacket,Finset.sum_sdiff_eq_sub (previous_labels_subset u j),mul_sub,
    Complex.sub_re,packet,ZetaRieszSmallTagNativeFloor.packet]

/-- A quantitative INDEPENDENT signed saving on the newly covered
population only. The old tags are not credited for a second time. -/
theorem eventually_addedPacket_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,|addedPacket u y j|≤2*ZetaRieszSmallTagNativeFloor.budget u y j := by
  filter_upwards [eventually_packet_bound hu hU hy,
    ZetaRieszSmallTagNativeFloor.eventually_packet_bound hu hU hy] with j hnew hold
  rw [addedPacket_eq]
  have htri : |packet u y j-ZetaRieszSmallTagNativeFloor.packet u y j|≤
      |packet u y j|+|ZetaRieszSmallTagNativeFloor.packet u y j| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le (packet u y j) 0 (ZetaRieszSmallTagNativeFloor.packet u y j)
  exact htri.trans (by
    rw [budget_eq_previous] at hnew
    linarith only [hnew,hold])

theorem tendsto_addedPacket {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (addedPacket u y) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using
    (ZetaRieszSmallTagNativeFloor.budget_tendsto u y).const_mul 2)
  simpa only [Real.norm_eq_abs] using eventually_addedPacket_bound hu hU hy

/-- The small and rough owner populations are exactly disjoint. -/
theorem labels_disjoint_rough {u : ℝ} {j : ℕ} (hN : 64≤dyadicMomentOrder j) :
    Disjoint (labels u j) (ZetaRieszRoughPrimePairCancellation.labels u j) := by
  apply Finset.disjoint_left.mpr
  intro n hn ht
  obtain ⟨pa,hpa,hepa⟩ := Finset.mem_image.mp hn
  obtain ⟨pb,hpb,hepb⟩ := Finset.mem_image.mp ht
  let E := rows u j∪ZetaRieszRoughPrimePairCancellation.rows u j
  have hg z (hz : z∈E) : z.1.Prime ∧ Squarefree z.2 ∧ z.2<z.1 := by
    rcases Finset.mem_union.mp hz with h | h
    · have hd := rows_data hN h
      exact ⟨hd.1,hd.2.1,hd.2.2.2.2.1⟩
    · have hd := ZetaRieszRoughPrimePairCancellation.rows_data hN h
      exact ⟨hd.1,hd.2.1,hd.2.2.2.2.1⟩
  have he : pa=pb := ZetaRieszRoughOwnerComparison.owned_rows_injective E hg
    (Finset.mem_union_left _ hpa) (Finset.mem_union_right _ hpb) (hepa.trans hepb.symm)
  have hsmall := (mem_rows.mp hpa).2.2.2.2.1
  have hrough := (mem_roughRows.mp hpb).2.2.2.2.1
  rw [he] at hsmall
  exact hrough hsmall

/-- The complete owner population, with every original native mask. -/
def fullLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  labels u j∪ZetaRieszRoughPrimePairCancellation.labels u j

theorem eventually_fullLabels_subset_native {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ j in atTop,fullLabels u j⊆ZetaRieszPaidIncidenceFloor.nativeLabels u j ∧
      ∀ n∈fullLabels u j,Squarefree n := by
  filter_upwards [eventually_labels_subset_native hu hU,
    ZetaRieszRoughPrimePairCancellation.eventually_labels_subset_native hu hU]
    with j hs hr
  exact ⟨Finset.union_subset hs.1 hr.1,fun n hn =>
    (Finset.mem_union.mp hn).elim (hs.2 n) (hr.2 n)⟩

/-- The literal FULL allocation and phase on the complete owner band. -/
def fullPacket (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈fullLabels u j,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

theorem fullPacket_eq {u y : ℝ} {j : ℕ} (hN : 64≤dyadicMomentOrder j) :
    fullPacket u y j=packet u y j+ZetaRieszRoughPrimePairCancellation.packet u y j := by
  simp only [fullPacket,fullLabels,Finset.sum_union (labels_disjoint_rough hN),mul_add,
    Complex.add_re,packet,ZetaRieszRoughPrimePairCancellation.packet]

/-- An INDEPENDENT signed estimate for every cofactor geometry/count in
the entire retained owner band PLUS the same literal prime head. The
previous error budget is unchanged; no zero hypothesis is assumed. -/
theorem eventually_full_packet_joint_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |fullPacket u y j+ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)|≤
        ZetaRieszRoughPrimePairCancellation.combinedBudget u y j := by
  filter_upwards [eventually_packet_bound hu hU hy,
    ZetaRieszRoughPrimePairCancellation.eventually_packet_joint_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ))] with j hs hr hN
  rw [fullPacket_eq hN,add_assoc]
  exact (abs_add_le _ _).trans (by
    simpa only [budget_eq_previous,ZetaRieszRoughPrimePairCancellation.combinedBudget] using
      add_le_add hs hr)

theorem tendsto_full_packet_add_head {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => fullPacket u y j+
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (ZetaRieszRoughPrimePairCancellation.combinedBudget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_full_packet_joint_bound hu hU hy

/-- Remove the complete owner band inside the ORIGINAL native increment. -/
def fullPaidIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  ZetaRieszComplexNullFloor.increment (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)
    N (fullLabels u j)
    (ZetaRieszComplexProjection.sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      L u y N) L (ZetaRieszSmallTagNativeFloor.realParameters p) k

theorem eventually_sum_fullPaidIncrement {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,∀ p : Fin 5→ℝ,
      (∑ k∈Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j),
        fullPaidIncrement u y j p k)=fullPacket u y j := by
  filter_upwards [eventually_fullLabels_subset_native hu hU] with j hj p
  have hc : ∀ n∈fullLabels u j,3≤n.primeFactors.card := fun _ hn =>
    ZetaRieszJointPrimeEnergy.core_count (hj.1 hn)
  have hX : ∀ n∈fullLabels u j,n≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := fun _ hn =>
    (Finset.le_sup (f:=id) (hj.1 hn)).trans (le_max_right _ _)
  unfold fullPaidIncrement
  dsimp only
  rw [ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _ hj.2 hc hX]
  simp only [ZetaRieszSmallTagNativeFloor.realParameters,Function.update_self,zero_mul,sub_zero]
  unfold ZetaRieszComplexProjection.complexPrefix fullPacket
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [corrected_prefix_eq (hj.2 n hn) (hc n hn) (hX n hn)]
  have hnp : ¬n.Prime := by
    intro hp
    have h := hc n hn
    simp only [hp.primeFactors,Finset.card_singleton] at h
    omega
  simp only [ZetaRieszComplexProjection.sourceWeight,residualCoefficient,
    SquarefreeVaughanLogSource.coefficient,if_pos (And.intro (hj.2 n hn) hnp)]
  push_cast
  ring

/-- Price the entire still-unpaid native main jointly with the head.
Only exact zero extension changes the endpoint. -/
def cost (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (ZetaRieszPrimeHeadPeriods.endpoint u j)) (cutoffPeriod y) (fun k =>
    (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
      ZetaRieszSmallTagNativeFloor.step u y j p q a k-fullPaidIncrement u y j p k else 0)-
        ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k)

private theorem sum_extend (X Y : ℕ) (hXY : X≤Y) (t : ℕ→ℝ) :
    (∑ k∈Finset.Icc 1 Y,if k≤X then t k else 0)=∑ k∈Finset.Icc 1 X,t k := by
  have hsub : Finset.Icc 1 X⊆Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hXY
  rw [← Finset.sum_subset (f:=fun k => if k≤X then t k else 0) hsub (by
    intro k hk hnot
    have hlo := (Finset.mem_Icc.mp hk).1
    have hx : ¬k≤X := fun hx => hnot (Finset.mem_Icc.mpr ⟨hlo,hx⟩)
    simp only [if_neg hx])]
  exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_Icc.mp hk).2)

/-- The new entire-band arithmetic payment is ACTUALLY spent in the
floor. Every outside owner and all free null/tangent columns remain. -/
theorem eventually_joined_floor_pruned {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -cost u y j (p j) (q j) (a j)-ZetaRieszRoughPrimePairCancellation.combinedBudget u y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_full_packet_joint_bound hu hU hy,
    eventually_sum_fullPaidIncrement hu hU y] with j hb he
  have hphysical : ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j)≤
      ZetaRieszPrimeHeadPeriods.endpoint u j := le_max_right _ _
  have hnative : ZetaRieszPaidIncidenceFloor.nativeEndpoint u j≤
      ZetaRieszPrimeHeadPeriods.endpoint u j := le_max_left _ _
  have hf := block_floor (Finset.Icc 1 (ZetaRieszPrimeHeadPeriods.endpoint u j))
    (cutoffPeriod y) (fun k =>
      (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
        ZetaRieszSmallTagNativeFloor.step u y j (p j) (q j) (a j) k-
          fullPaidIncrement u y j (p j) k else 0)-
            ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k)
  rw [Finset.sum_sub_distrib,ZetaRieszPrimeHeadPeriods.sum_headIncrement hphysical,
    sum_extend _ _ hnative,Finset.sum_sub_distrib,
    ZetaRieszSmallTagNativeFloor.sum_step,he (p j)] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  change -cost u y j (p j) (q j) (a j)≤Q.re-fullPacket u y j-
    ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) at hf
  change -cost u y j (p j) (q j) (a j)-
    ZetaRieszRoughPrimePairCancellation.combinedBudget u y j-
      (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hr,(abs_le.mp hb).1,abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Alternative complete prices, never stacked overlapping payments. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszPrimeHeadPeriods.price u y j p q a)
    (cost u y j p q a+ZetaRieszRoughPrimePairCancellation.combinedBudget u y j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszPrimeHeadPeriods.price u y j p q a := min_le_left _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_pruned hu hU hy p q a,
    ZetaRieszPrimeHeadPeriods.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszPrimeHeadPeriods.price u y j (p j) (q j) (a j))
    (cost u y j (p j) (q j) (a j)+ZetaRieszRoughPrimePairCancellation.combinedBudget u y j)
    with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- The cofinal whole-price premise is explicitly OPEN. The independent
entire-owner payment above is not a numerical floor or zero exclusion. -/
theorem false_of_cofinal_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ)
    (hcost : ∃ᶠ j in atTop,
      price (3/2-rho.1.re) rho.1.im j (p j) (q j) (a j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor hu hU hy p q a
  exact (hcost.and_eventually hf).mono (fun j hj => by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])


end RiemannGaussian.ZetaRieszAllTagNativeFloor
