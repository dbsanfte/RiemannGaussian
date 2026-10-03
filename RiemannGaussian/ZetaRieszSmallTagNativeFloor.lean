/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTaggedCoreWindow
import RiemannGaussian.ZetaRieszPaidIncidenceFloor

/-!
# Spend the signed complete small-tag rows on the native floor

The choices below are the original physical primes, length and count crop.
No new counting or cancellation hypothesis is imposed. The complete signed
row is paid before its cutoff variation is priced. The remaining numerical
whole-floor threshold is not asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSmallTagNativeFloor
open ZetaRieszTaggedCoreWindow ZetaRieszOwnerLatticePhase
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszPrimeEndpoint ZetaRieszCutoffPeriodFloor

/-- All small primes are present in the exclusion measure, not just a tag. -/
def smallPrimes (N : ℕ) : Finset ℕ := Nat.primesLE (N^3)

/-- The least tag is above the original physical lower cutoff. -/
def retainedTags (N : ℕ) : Finset ℕ := (smallPrimes N).filter (fun r => N^2<r)

/-- These owners support the entire original core cofactor interval. -/
def owners (u : ℝ) (N : ℕ) : Finset ℕ :=
  (ZetaRieszAnnulusJoint.intermediatePrimes u N).filter (fun p =>
    (51/50 : ℝ)*N≤log p ∧ log p≤(5/4 : ℝ)*N)

/-- One native count crop, applied to disjoint owner/cofactor rows. -/
def rows (u : ℝ) (j : ℕ) : Finset (ℕ×ℕ) :=
  (selectedRows (smallPrimes (dyadicMomentOrder j))
    (retainedTags (dyadicMomentOrder j)) (owners u (dyadicMomentOrder j))
      (dyadicMomentOrder j)).filter (fun pa =>
        (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j)

/-- Product labels, each represented by its unique original owner row. -/
def labels (u : ℝ) (j : ℕ) : Finset ℕ :=
  (rows u j).image (fun pa => pa.1*pa.2)

theorem owners_data {u : ℝ} {N p : ℕ} (hp : p∈owners u N) :
    p.Prime ∧ p∈ZetaRieszAnnulusJoint.intermediatePrimes u N ∧
      (51/50 : ℝ)*N≤log p ∧ log p≤(5/4 : ℝ)*N := by
  obtain ⟨hA,hlog⟩ := Finset.mem_filter.mp hp
  exact ⟨((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hA).1,hA,hlog⟩

/-- A single explicit cutoff suffices for every retained owner. -/
def comparisonCutoff (N : ℕ) : ℕ := ⌊exp ((N : ℝ)/2)⌋₊

private theorem coreFloor_lower {N : ℕ} (hN : 64≤N) {c : ℝ}
    (hc : c≤(5/4 : ℝ)*N) :
    exp ((2/3 : ℝ)*N)≤coreFloor N c (39/20) := by
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hsmall : 2≤exp ((N : ℝ)/30) := by
    have h := add_one_le_exp ((N : ℝ)/30)
    linarith only [h,hn]
  have hone : 1≤exp ((2/3 : ℝ)*N) := one_le_exp (by positivity)
  have hsum : exp ((2/3 : ℝ)*N)+1≤exp ((39/20 : ℝ)*N-c) := by
    calc
      _ ≤ 2*exp ((2/3 : ℝ)*N) := by linarith only [hone]
      _ ≤ exp ((N : ℝ)/30)*exp ((2/3 : ℝ)*N) :=
        mul_le_mul_of_nonneg_right hsmall (exp_pos _).le
      _ = exp ((7/10 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      _ ≤ _ := exp_le_exp.mpr (by linarith only [hc])
  have hf : exp ((39/20 : ℝ)*N-c)<(coreFloor N c (39/20) : ℝ)+1 :=
    Nat.lt_floor_add_one _
  linarith only [hsum,hf]

theorem comparisonCutoff_geometry {N : ℕ} (hN : 64≤N) {c L : ℝ}
    (hc : c≤(5/4 : ℝ)*N) (hlo : (51/50 : ℝ)*N≤c)
    (hL : L≤(139/100 : ℝ)*N) :
    0<comparisonCutoff N ∧ comparisonCutoff N≤coreFloor N c (39/20) ∧
      (comparisonCutoff N)^4≤(coreFloor N c (39/20))^3 ∧
      L-c≤log (comparisonCutoff N+1 : ℕ) := by
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hpos : 0<comparisonCutoff N := Nat.floor_pos.mpr (one_le_exp (by positivity))
  have hR : (comparisonCutoff N : ℝ)≤exp ((N : ℝ)/2) := Nat.floor_le (exp_pos _).le
  have hM := coreFloor_lower hN hc
  have hRM : comparisonCutoff N≤coreFloor N c (39/20) := by
    exact_mod_cast hR.trans ((exp_le_exp.mpr (by linarith only [hn])).trans hM)
  have hpow : (comparisonCutoff N)^4≤(coreFloor N c (39/20))^3 := by
    have h1 := pow_le_pow_left₀ (by positivity : 0≤(comparisonCutoff N : ℝ)) hR 4
    have h2 := pow_le_pow_left₀ (exp_pos ((2/3 : ℝ)*N)).le hM 3
    rw [← exp_nat_mul] at h1 h2
    norm_num only [Nat.cast_ofNat] at h1 h2
    have he : (4 : ℝ)*((N : ℝ)/2)=3*((2/3 : ℝ)*N) := by ring
    rw [he] at h1
    exact_mod_cast h1.trans h2
  have hr1 : exp ((N : ℝ)/2)<(comparisonCutoff N : ℝ)+1 := Nat.lt_floor_add_one _
  have hlog : (N : ℝ)/2≤log (comparisonCutoff N+1 : ℕ) := by
    have h := log_le_log (exp_pos ((N : ℝ)/2)) hr1.le
    simpa only [log_exp,Nat.cast_add,Nat.cast_one] using h
  exact ⟨hpos,hRM,hpow,by linarith only [hlog,hlo,hL,hn]⟩

theorem eventually_cube_below_core :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, c≤(4/3 : ℝ)*N →
      N^3≤coreFloor N c (39/20) := by
  have hdec := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    3 (exp_pos (-(1/2 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/2 : ℝ)<0))
  have hb := hdec.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hb,eventually_ge_atTop (64 : ℕ)] with N hb hN c hc
  have hp : (N : ℝ)^3≤((N : ℝ)+1)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have he : (exp (-(1/2 : ℝ)))^N=exp (-(N : ℝ)/2) := by
    rw [← exp_nat_mul]; congr 1; ring
  rw [he,show -(N : ℝ)/2=-((N : ℝ)/2) by ring,exp_neg,← div_eq_mul_inv] at hb
  have hlarge := (coreFloor_geometry hN hc).2.2.1
  have hcub : (N : ℝ)^3≤exp ((N : ℝ)/2) :=
    hp.trans ((div_lt_one (exp_pos _)).mp hb).le
  exact_mod_cast hcub.trans hlarge

theorem length_upper {u : ℝ} (hu : 1/2≤u) {N : ℕ} (hN : 2≤N) :
    SquarefreeVaughanLogSource.length u N≤(139/100 : ℝ)*N := by
  have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have hn : (0 : ℝ)≤N := Nat.cast_nonneg _
  nlinarith only [h,log_two_lt_d9,hn]

/-- All comparison premises follow from the actual length and physical set. -/
theorem eventually_native_comparison {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ p∈owners u N,
      p.Prime ∧ p∈ZetaRieszAnnulusJoint.intermediatePrimes u N ∧
      p≤(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 ∧
      1≤log p ∧ log p≤(4/3 : ℝ)*N ∧
      log p≤SquarefreeVaughanLogSource.length u N ∧
      N^3≤coreFloor N (log p) (39/20) ∧ coreFloor N (log p) (203/100)<p ∧
      0<comparisonCutoff N ∧ comparisonCutoff N≤coreFloor N (log p) (39/20) ∧
      (comparisonCutoff N)^4≤(coreFloor N (log p) (39/20))^3 ∧
      SquarefreeVaughanLogSource.length u N-log p≤log (comparisonCutoff N+1 : ℕ) := by
  have hs : u≤exp (-(11/16 : ℝ)) := hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le
  filter_upwards [eventually_ge_atTop (64 : ℕ),eventually_cube_below_core,
    ZetaRieszMaskSupport.eventually_length_lower (by linarith : 0<u) hs]
    with N hN hcube hL p hp
  obtain ⟨hpp,hA,hlo,hhi⟩ := owners_data hp
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hc : log p≤(4/3 : ℝ)*N := by linarith only [hhi,hn]
  have hcut := comparisonCutoff_geometry hN hhi hlo (length_upper hu.le (by omega : 2≤N))
  refine ⟨hpp,hA,((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hA).2.2.le,
    by linarith only [hlo,hn],hc,hhi.trans hL,hcube _ hc,
    (full_core_owner_geometry hN hpp hlo hhi).1,hcut⟩

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
  have h := hj (smallPrimes N) (retainedTags N)
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) (owners u N)
    (fun _ => comparisonCutoff N) Q L u y hpos (by linarith) hU hy
    (fun r hr => by
      have h := Nat.mem_primesLE.mp hr
      exact ⟨h.2,h.1⟩)
    (Finset.filter_subset _ _)
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

/-- This is the previous global nonowner error, restricted once to the
paid labels. It is not added again to another nonowner credit. -/
def nonownerBudget (N : ℕ) : ℝ :=
  (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
    ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))

theorem nonownerBudget_tendsto : Tendsto nonownerBudget atTop (𝓝 0) := by
  have hr : 0<ZetaRieszNonownerAllocation.nonownerRate := by
    unfold ZetaRieszNonownerAllocation.nonownerRate
    positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    1 hr (ZetaRieszNonownerAllocation.nonownerRate_bounds.2.trans (by norm_num))).mul_const
      ((4/3 : ℝ)*((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
  simp only [pow_one,zero_mul] at ht
  convert ht using 1
  funext N
  unfold nonownerBudget
  ring

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

/-- Keep all complex logarithmic nulls, but use zero imaginary tilt:
the independently paid estimate here is a real signed estimate. -/
def realParameters (p : Fin 5→ℝ) : Fin 5→ℝ := Function.update p 0 0

/-- The whole native increment, retaining all free complex nulls and
tangents. Only this alternative's imaginary tilt is set to zero. -/
def step (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := (ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree
  let X := ZetaRieszPaidIncidenceFloor.nativeEndpoint u j
  let W := ZetaRieszComplexProjection.sourceWeight A L u y N
  ZetaRieszComplexNullFloor.increment X N S W L (realParameters p) k+
    ZetaRieszTangentCubicCredit.extendedIncrement X N S W L q a k

theorem sum_step (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    (∑ k∈Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j),step u y j p q a k)=
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := (ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree
  have hs : ∀ n∈S,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n∈S,3≤n.primeFactors.card := fun _ hn =>
    ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n∈S,n≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := fun _ hn =>
    (Finset.le_sup (f:=id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  unfold step
  dsimp only
  rw [Finset.sum_add_distrib,ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _ hs hc hX,
    ZetaRieszTangentCubicCredit.sum_extendedIncrement_zero _ _ _ _ _ q a hs hc hX,add_zero]
  simp only [realParameters,Function.update_self,zero_mul,sub_zero]
  have he := ZetaRieszComplexProjection.native_prefix_eq
    (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (ZetaRieszPaidIncidenceFloor.nativeLabels u j) L u y N
      (fun _ hn => ZetaRieszJointPrimeEnergy.core_count hn)
  dsimp only at he
  change ZetaRieszComplexProjection.complexPrefix (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j) S
    (ZetaRieszComplexProjection.sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      L u y N) (correctedProfile (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j) L 1 0)=
    (u : ℂ)^(N+1)*ZetaRieszParityPacket.coreResponse u y N
      (ZetaRieszNearCriticalCountPayment.countCeiling j) at he
  rw [he]

/-- The paid row is removed INSIDE every native cutoff increment; its
signed total, rather than its absolute cutoff variation, is funded. -/
def paidIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  ZetaRieszComplexNullFloor.increment (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)
    N (labels u j)
    (ZetaRieszComplexProjection.sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      L u y N) L (realParameters p) k

private theorem subset_prefix_eq (A D : Finset ℕ) (X : ℕ) (L u y : ℝ) (N : ℕ)
    (hs : ∀ n∈D,Squarefree n) (hc : ∀ n∈D,3≤n.primeFactors.card) (hX : ∀ n∈D,n≤X) :
    ZetaRieszComplexProjection.complexPrefix X D
      (ZetaRieszComplexProjection.sourceWeight A L u y N) (correctedProfile X L 1 0)=
      (u : ℂ)^(N+1)*∑ n∈D,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  unfold ZetaRieszComplexProjection.complexPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [corrected_prefix_eq (hs n hn) (hc n hn) (hX n hn)]
  have hnp : ¬n.Prime := by
    intro hp
    have h := hc n hn
    simp only [hp.primeFactors,Finset.card_singleton] at h
    omega
  simp only [ZetaRieszComplexProjection.sourceWeight,residualCoefficient,
    SquarefreeVaughanLogSource.coefficient,if_pos (And.intro (hs n hn) hnp)]
  push_cast
  ring

theorem eventually_sum_paidIncrement {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop, ∀ p : Fin 5→ℝ,
      (∑ k∈Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j),paidIncrement u y j p k)=
        packet u y j := by
  filter_upwards [eventually_labels_subset_native hu hU] with j hj p
  have hc : ∀ n∈labels u j,3≤n.primeFactors.card := fun _ hn =>
    ZetaRieszJointPrimeEnergy.core_count (hj.1 hn)
  have hX : ∀ n∈labels u j,n≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := fun _ hn =>
    (Finset.le_sup (f:=id) (hj.1 hn)).trans (le_max_right _ _)
  unfold paidIncrement
  dsimp only
  rw [ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _ hj.2 hc hX]
  simp only [realParameters,Function.update_self,zero_mul,sub_zero]
  rw [subset_prefix_eq _ _ _ _ _ _ _ hj.2 hc hX]
  rfl

/-- All remaining labels/counts/cutoffs stay joined before period clipping. -/
def restCost (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)) (cutoffPeriod y)
    (fun k => step u y j p q a k-paidIncrement u y j p k)

private theorem increment_sdiff (X N : ℕ) (S D : Finset ℕ) (hD : D⊆S)
    (W : ℕ→ℂ) (L : ℝ) (p : Fin 5→ℝ) (k : ℕ) :
    ZetaRieszComplexNullFloor.increment X N S W L p k-
      ZetaRieszComplexNullFloor.increment X N D W L p k=
        ZetaRieszComplexNullFloor.increment X N (S\D) W L p k := by
  have he w : ZetaRieszCofactorPhaseEnergy.correlation (S\D) w k=
      ZetaRieszCofactorPhaseEnergy.correlation S w k-
        ZetaRieszCofactorPhaseEnergy.correlation D w k :=
    Finset.sum_sdiff_eq_sub hD
  simp only [ZetaRieszComplexNullFloor.increment,he]
  ring

/-- The main null-corrected response REALLY contains only unpaid labels
after subtraction. Whole tangent corrections remain exact free nulls;
their signed cost is retained, not spent as an additional row credit. -/
theorem eventually_step_sub_paid {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop, ∀ (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) (k : ℕ),
      let N := dyadicMomentOrder j;
      let L := SquarefreeVaughanLogSource.length u N;
      let X := ZetaRieszPaidIncidenceFloor.nativeEndpoint u j;
      let S := (ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree;
      let W := ZetaRieszComplexProjection.sourceWeight
        (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N;
      step u y j p q a k-paidIncrement u y j p k=
        ZetaRieszComplexNullFloor.increment X N (S\labels u j) W L (realParameters p) k+
          ZetaRieszTangentCubicCredit.extendedIncrement X N S W L q a k := by
  filter_upwards [eventually_labels_subset_native hu hU] with j hj p q a k
  dsimp only
  have hd : labels u j⊆(ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree :=
    fun n hn => Finset.mem_filter.mpr ⟨hj.1 hn,hj.2 n hn⟩
  unfold step paidIncrement
  dsimp only
  rw [add_sub_right_comm,increment_sdiff _ _ _ _ hd]

/-- A whole-floor inequality actually spending the newly paid population.
The combined remaining cutoff cost is explicit, not assumed bounded. -/
theorem eventually_joined_floor_pruned {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -restCost u y j (p j) (q j) (a j)-budget u y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_packet_bound hu hU hy,eventually_sum_paidIncrement hu hU y]
    with j hb he
  have hf := ZetaRieszPaidIncidenceFloor.pruned_block_floor
    (Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)) (cutoffPeriod y)
    (step u y j (p j) (q j) (a j)) (paidIncrement u y j (p j))
      (E:=budget u y j) (by rw [he (p j)]; exact hb)
  rw [sum_step] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  change -restCost u y j (p j) (q j) (a j)-budget u y j≤Q.re at hf
  change -restCost u y j (p j) (q j) (a j)-budget u y j-
    (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hr,abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Alternate whole prices, never stacked credits. Keep the old optimum
whenever deleting these rows would worsen a particular period price. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszPaidIncidenceFloor.nativePrunedPrice u y j q a)
    (restCost u y j p q a+budget u y j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszPaidIncidenceFloor.nativePrunedPrice u y j q a := min_le_left _ _

theorem price_le_pruned (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤restCost u y j p q a+budget u y j := min_le_right _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_pruned hu hU hy p q a,
    ZetaRieszPaidIncidenceFloor.eventually_joined_floor_with_pruned_price hu hU hy q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszPaidIncidenceFloor.nativePrunedPrice u y j (q j) (a j))
    (restCost u y j (p j) (q j) (a j)+budget u y j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- The improvement is against ONE already valid price. It can be zero;
no positive fraction of the global floor deficit is asserted. -/
def gain (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  ZetaRieszPaidIncidenceFloor.nativePrunedPrice u y j q a-price u y j p q a

theorem gain_nonneg (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    0≤gain u y j p q a := sub_nonneg.mpr (price_le_previous u y j p q a)

/-- Explicit OPEN endgame premise: the pruned whole price must still be
bounded cofinally. The independent row estimate above does not prove this. -/
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

end RiemannGaussian.ZetaRieszSmallTagNativeFloor
