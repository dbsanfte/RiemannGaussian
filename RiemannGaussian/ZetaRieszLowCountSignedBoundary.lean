/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalHighOwnerPayment

/-!
# Join the retained prime and prime-pair boundary before paying its edges

The original allocated/sieved head is a suballocation of the new full
unallocated prime correction. Their difference is kept on each physical
label. Joining that difference with the original semiprime response gives
a coefficient between `-log n` and zero. Only exterior/partial phase
periods are estimated by a norm; the whole signed interior stays unpaid.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLowCountSignedBoundary
open ZetaRieszUnallocatedOwnerPayment ZetaRieszUnallocatedOwnerPhase
open ZetaRieszOwnerLatticePhase ZetaRieszGlobalBulkPayment
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalHighOwnerPayment
open ZetaRieszGlobalHeadCentralPayment ZetaRieszPrimeEndpoint
open ZetaRieszGlobalPeriodEdgePayment ZetaRieszPrimeCountFrequency

/-- Actual ordinary-prime slots in the new correction, with the original
wide radial window and EVERY owner through the moving length. -/
def correctionIncidences (u : ℝ) (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (highOwners u N).sigma (fun p =>
    (Finset.Ioc (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100))).filter Nat.Prime)

/-- Physical product of the canonical larger prime and its prime cofactor. -/
def correctionProduct (e : Σ _ : ℕ, ℕ) : ℕ := e.1*e.2

/-- Unique integer labels of every literal unallocated correction incidence. -/
def correctionLabels (u : ℝ) (N : ℕ) : Finset ℕ :=
  (correctionIncidences u N).image correctionProduct

private theorem correction_data {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈correctionIncidences u N) :
    e.1∈highOwners u N ∧ e.2∈Finset.Ioc (coreFloor N (log e.1) (39/20))
      (coreFloor N (log e.1) (203/100)) ∧ e.2.Prime ∧
      e.2<e.1 ∧ log e.2≤SquarefreeVaughanLogSource.length u N := by
  obtain ⟨hp,hq'⟩ := Finset.mem_sigma.mp he
  obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq'
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hLlo : (51/50 : ℝ)*N≤SquarefreeVaughanLogSource.length u N := by
    nlinarith only [hlo,Nat.cast_nonneg (α:=ℝ) N]
  have hd := cofactor_window_data hu (by omega : 64≤N) hp hLlo hq
  exact ⟨hp,hq,hqp,hd.2⟩

theorem correction_largest {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈correctionIncidences u N) :
    largestPrime (correctionProduct e)=e.1 := by
  obtain ⟨hp,_hq,hqp,hlt,_hL⟩ := correction_data hu hU hN he
  apply ZetaRieszPrimeIntervals.largestPrime_mul e.1 e.2 (highOwner_data hp).1 hqp.ne_zero
  intro q hq
  rw [hqp.primeFactors,Finset.mem_singleton] at hq
  subst q
  exact hlt

theorem correction_injective {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    Set.InjOn correctionProduct (correctionIncidences u N) := by
  intro e he f hf h
  have hp : e.1=f.1 := by
    rw [← correction_largest hu hU hN he,← correction_largest hu hU hN hf,h]
  have h0 := (highOwner_data (correction_data hu hU hN he).1).1.pos
  have hq : e.2=f.2 := by
    apply Nat.eq_of_mul_eq_mul_left h0
    simpa only [correctionProduct,←hp] using h
  exact Sigma.ext hp (heq_of_eq hq)

private theorem correction_squarefree {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈correctionIncidences u N) :
    Squarefree (correctionProduct e) := by
  obtain ⟨hp,_hq,hqp,hlt,_hL⟩ := correction_data hu hU hN he
  have hpp := (highOwner_data hp).1
  have hnot : ¬e.1∣e.2 := fun h => hlt.ne' ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp h)
  exact Nat.squarefree_mul_iff.mpr ⟨hpp.coprime_iff_not_dvd.mpr hnot,
    hpp.squarefree,hqp.squarefree⟩

theorem correction_not_prime {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈correctionLabels u N) : ¬n.Prime := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,_hq,hqp,_⟩ := correction_data hu hU hN he
  exact Nat.not_prime_mul (highOwner_data hp).1.ne_one hqp.ne_one

/-- Exact unallocated coefficient; no ownerWeight or sieve is inserted. -/
def correctionCoefficient (u : ℝ) (N n : ℕ) : ℂ :=
  ((log n/SquarefreeVaughanLogSource.length u N*
    (SquarefreeVaughanLogSource.length u N-log (largestPrime n)) : ℝ) : ℂ)

private theorem correctionCoefficient_pair {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈correctionIncidences u N) :
    correctionCoefficient u N (correctionProduct e)=
      ((log (correctionProduct e)/SquarefreeVaughanLogSource.length u N*
        (SquarefreeVaughanLogSource.length u N-log e.1) : ℝ) : ℂ) := by
  unfold correctionCoefficient
  rw [correction_largest hu hU hN he]

theorem correctionCoefficient_bounds {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈correctionLabels u N) :
    0≤(correctionCoefficient u N n).re ∧
      (correctionCoefficient u N n).re≤log n := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,_⟩ := correction_data hu hU hN he
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hc := (highOwner_data hp).2.2.2
  rw [correctionCoefficient_pair hu hU hN he,Complex.ofReal_re]
  refine ⟨mul_nonneg (div_nonneg (log_natCast_nonneg _) hL.le) (by linarith),?_⟩
  calc
    _ ≤ log (correctionProduct e)/SquarefreeVaughanLogSource.length u N*
        SquarefreeVaughanLogSource.length u N :=
      mul_le_mul_of_nonneg_left (by linarith [log_natCast_nonneg e.1])
        (div_nonneg (log_natCast_nonneg _) hL.le)
    _ = _ := div_mul_cancel₀ _ hL.ne'

private theorem correction_atom_re {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈correctionIncidences u N) (y : ℝ) :
    ((u : ℂ)^(N+1)*correctionCoefficient u N (correctionProduct e)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (correctionProduct e)).re=
      u^(N+1)/(SquarefreeVaughanLogSource.length u N*e.1)*
        (SquarefreeVaughanLogSource.length u N-log e.1)*
          densityTest N (log e.1) y e.2 := by
  obtain ⟨hp,_hq,hqp,_⟩ := correction_data hu hU hN he
  have hpp := (highOwner_data hp).1
  have hlog : log (correctionProduct e)=log e.1+log e.2 := by
    rw [correctionProduct,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast hqp.ne_zero)]
  have hk := ZetaRieszCosineCarrier.re_filterKernel_one N y (correctionProduct e)
  have hk' : (zetaPrimeLogKernel N (3/2+Complex.I*y) (correctionProduct e)).re=
      exp (-(3/2 : ℝ)*log (correctionProduct e))*log (correctionProduct e)^N/N.factorial*
        cos (y*log (correctionProduct e)) := by
    simpa only [zetaPrimeFilterKernel,ZetaRieszCosineCarrier.factorialPolynomial_one,
      zetaPrimeLogKernel,zetaPrimeFeature,neg_mul,Nat.cast_mul] using hk
  have hx : (0 : ℝ)<correctionProduct e := by exact_mod_cast Nat.mul_pos hpp.pos hqp.pos
  have hex : exp (-(3/2 : ℝ)*log (correctionProduct e))=
      exp (-log (correctionProduct e)/2)/(correctionProduct e : ℝ) := by
    rw [show -(3/2 : ℝ)*log (correctionProduct e)=
      -log (correctionProduct e)/2+-log (correctionProduct e) by ring,
      exp_add,exp_neg,exp_log hx]
    ring
  have htest := densityTest_eq (N:=N) (c:=log e.1) (x:=(e.2 : ℝ)) (by
    have hl := log_pos (by exact_mod_cast hpp.two_le : (1 : ℝ)<e.1)
    linarith [log_natCast_nonneg e.2]) y
  rw [correctionCoefficient_pair hu hU hN he]
  simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hk',hex,hlog,htest]
  simp only [correctionProduct,Nat.cast_mul,ZetaRieszSmoothOwnerDiscrepancy.radial,pow_succ]
  ring

/-- The literal new correction has ONE incidence per physical label. -/
theorem highPrimeCorrection_eq_label_sum {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    highPrimeCorrection u y N=
      ((u : ℂ)^(N+1)*∑ n∈correctionLabels u N,
        correctionCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [correctionLabels,Finset.sum_image (correction_injective hu hU hN),
    Finset.mul_sum,Complex.re_sum]
  simp_rw [←mul_assoc]
  rw [Finset.sum_congr rfl (fun e he => correction_atom_re hu hU hN he y)]
  simp only [correctionIncidences,Finset.sum_sigma,Finset.sum_filter]
  unfold highPrimeCorrection primeCorrection
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hq : q.Prime
  · simp only [if_pos hq]
  · simp only [if_neg hq,mul_zero]

/-- Every slot in the SAME original head also occurs in the new full
correction. This statement retains its exact owner and cofactor masks. -/
theorem headLabels_subset_correction (u : ℝ) (N : ℕ) :
    headLabels u N⊆correctionLabels u N := by
  intro n hn
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq'⟩ := Finset.mem_sigma.mp he
  obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq'
  obtain ⟨hpp,hA,hlo,_hhi⟩ := ZetaRieszSmallTagNativeFloor.owners_data hp
  have hphys := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N e.1).mp hA).2.2
  have hpL : log e.1≤SquarefreeVaughanLogSource.length u N := by
    unfold SquarefreeVaughanLogSource.length
    apply log_le_log (by exact_mod_cast hpp.pos)
    exact_mod_cast hphys.le
  have hpH : e.1∈highOwners u N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hpp.pos,?_⟩,hpp,hlo⟩
    apply Nat.le_floor
    rw [←exp_log (by exact_mod_cast hpp.pos : (0 : ℝ)<e.1)]
    exact exp_le_exp.mpr hpL
  exact Finset.mem_image.mpr ⟨e,Finset.mem_sigma.mpr
    ⟨hpH,Finset.mem_filter.mpr ⟨hq,hqp⟩⟩,rfl⟩

/-- Pointwise cancellation of the allocated head against its full
unallocated correction. Neither factor is normed separately. -/
theorem head_le_correction {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈headLabels u N) :
    0≤(headCoefficient u N n).re ∧
      (headCoefficient u N n).re≤(correctionCoefficient u N n).re := by
  have hm := headLabels_subset_correction u N hn
  have hc := correctionCoefficient_bounds hu hU hN hm
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq'⟩ := Finset.mem_sigma.mp he
  obtain ⟨_hq,hqp⟩ := Finset.mem_filter.mp hq'
  have hl := largestPrime_label (by omega : 64≤N) he
  have hpp := (ZetaRieszSmallTagNativeFloor.owners_data hp).1
  have hco : ZetaRieszOwnedCells.ownerCofactor (label e)=e.2 := by
    unfold ZetaRieszOwnedCells.ownerCofactor
    rw [hl,label,Nat.mul_div_right _ hpp.pos]
  have hn1 : 1<label e := by
    unfold label
    nlinarith only [hpp.two_le,hqp.two_le]
  have hw := ZetaRieszOwnerMaximal.ownerWeight_bounds N
    (x:=log e.2/log (label e)) (div_nonneg (log_natCast_nonneg _) (log_natCast_nonneg _)) (by
      apply (div_le_one (log_pos (by exact_mod_cast hn1))).mpr
      rw [label,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hqp.ne_zero)]
      linarith [log_natCast_nonneg e.1])
  have hs : 0≤ZetaRieszUnsignedDivisorError.sieve (ZetaRieszSmallTagNativeFloor.smallPrimes N) e.2 ∧
      ZetaRieszUnsignedDivisorError.sieve (ZetaRieszSmallTagNativeFloor.smallPrimes N) e.2≤1 := by
    unfold ZetaRieszUnsignedDivisorError.sieve
    split_ifs <;> norm_num
  have hbase : 0≤log (label e)/SquarefreeVaughanLogSource.length u N*
      (SquarefreeVaughanLogSource.length u N-log e.1) := by
    simpa only [correctionCoefficient,hl,Complex.ofReal_re] using hc.1
  simp only [headCoefficient,correctionCoefficient,hl,hco,Complex.ofReal_re]
  refine ⟨mul_nonneg (mul_nonneg hbase hw.1) hs.1,?_⟩
  exact (mul_le_of_le_one_right (mul_nonneg hbase hw.1) hs.2).trans
    (mul_le_of_le_one_right hbase hw.2)

private theorem completed_bounds_of_cap {L : ℝ} (hL : 0<L) {n : ℕ}
    (hs : Squarefree n) (hR : 0≤VaughanLogAverage.riesz L n)
    (hRL : VaughanLogAverage.riesz L n≤L) :
    -log n≤(completedCoefficient L n).re ∧ (completedCoefficient L n).re≤0 := by
  have hfac : 0≤log n/L := div_nonneg (log_natCast_nonneg _) hL.le
  have hprod : log n/L*VaughanLogAverage.riesz L n≤log n := by
    calc
      _ ≤ log n/L*L := mul_le_mul_of_nonneg_left hRL hfac
      _ = _ := div_mul_cancel₀ _ hL.ne'
  simp only [completedCoefficient,if_pos hs,Complex.ofReal_re]
  rw [show -log n*VaughanLogAverage.riesz L n/L=
    -(log n/L*VaughanLogAverage.riesz L n) by ring]
  constructor <;> nlinarith only [hprod,mul_nonneg hfac hR]

/-- Low-count coefficients have a logarithmic cap, independently of
their phase and without any physical-prime restriction. -/
theorem completed_low_bounds {L : ℝ} (hL : 0<L) {n : ℕ}
    (hn : n.Prime ∨ (Squarefree n ∧ n.primeFactors.card=2)) :
    -log n≤(completedCoefficient L n).re ∧ (completedCoefficient L n).re≤0 := by
  rcases hn with hp | ⟨hs,hc⟩
  · have he := SquarefreeVaughanLogSource.coefficient_eq_completed_with_prime hL n
    have hz : SquarefreeVaughanLogSource.coefficient L n=0 := by
      simp only [SquarefreeVaughanLogSource.coefficient,hp,not_true_eq_false,and_false,if_false]
    change SquarefreeVaughanLogSource.coefficient L n=completedCoefficient L n+_ at he
    rw [hz,if_pos hp] at he
    have hcc : completedCoefficient L n=-((log n*min L (log n)/L : ℝ) : ℂ) := by
      linear_combination -he
    rw [hcc,Complex.neg_re,Complex.ofReal_re]
    have hm : 0 ≤ min L (log n) := le_min hL.le (log_natCast_nonneg _)
    have hprod : log n*min L (log n)/L≤log n := by
      apply (div_le_iff₀ hL).mpr
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (log_natCast_nonneg _)
    constructor <;> nlinarith only [hprod,div_nonneg
      (mul_nonneg (log_natCast_nonneg n) hm) hL.le]
  · obtain ⟨p,q,hpq,hset⟩ := Finset.card_eq_two.mp hc
    have hp : p∈n.primeFactors := by rw [hset]; simp
    have hq : q∈n.primeFactors := by rw [hset]; simp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hprod := Nat.prod_primeFactors_of_squarefree hs
    rw [hset,Finset.prod_pair hpq] at hprod
    have ht := ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent L hpp hqp hpq
    have h0 := (ZetaRieszSemiprimePrefixDecay.riesz_semiprime_bounds L hpp hqp hpq).1
    have hcap : VaughanLogAverage.riesz L (p*q)≤L := by
      rw [ht]
      have hm : max 0 (L-log p-log q) ≤ max 0 (L-log q) :=
        max_le_max_left 0 (by linarith [log_natCast_nonneg p])
      unfold ZetaSquarefreeRieszWindows.primePairTent
      rw [max_eq_right hL.le]
      linarith only [hm,le_max_left 0 (L-log p)]
    rw [←hprod]
    exact completed_bounds_of_cap hL (hprod ▸ hs) h0 hcap

/-- On every new correction label the two hinges JOIN to the smaller
prime logarithm. This is exact on the ORIGINAL full window. -/
theorem completed_sub_correction_eq {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈correctionIncidences u N) :
    completedCoefficient (SquarefreeVaughanLogSource.length u N) (correctionProduct e)-
      correctionCoefficient u N (correctionProduct e)=
        ((-log (correctionProduct e)*log e.2/SquarefreeVaughanLogSource.length u N : ℝ) : ℂ) := by
  obtain ⟨hp,hq,hqp,hlt,hqL⟩ := correction_data hu hU hN he
  have hpp := (highOwner_data hp).1
  have hpL := (highOwner_data hp).2.2.2
  let L := SquarefreeVaughanLogSource.length u N
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hs := correction_squarefree hu hU hN he
  have hlog : log (correctionProduct e)=log e.1+log e.2 := by
    rw [correctionProduct,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast hqp.ne_zero)]
  have hw := (coreFloor_membership N (log e.1) hqp.pos).mp hq
  have hLu := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hT : L≤log (correctionProduct e) := by
    dsimp only [L]
    rw [hlog]
    nlinarith only [hw.1,hLu,Nat.cast_nonneg (α:=ℝ) N]
  have hr : VaughanLogAverage.riesz L (correctionProduct e)=log (correctionProduct e)-L := by
    rw [show correctionProduct e=e.1*e.2 from rfl,
      ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent L hpp hqp hlt.ne']
    unfold ZetaSquarefreeRieszWindows.primePairTent
    rw [max_eq_right hL.le,max_eq_right (sub_nonneg.mpr hpL),
      max_eq_right (sub_nonneg.mpr hqL),
      max_eq_left (by linarith only [hT,hlog])]
    change _=log (correctionProduct e)-L
    rw [hlog]
    dsimp only [L]
    ring
  rw [correctionCoefficient_pair hu hU hN he]
  simp only [completedCoefficient,if_pos hs,←Complex.ofReal_sub]
  change ((-log (correctionProduct e)*VaughanLogAverage.riesz L (correctionProduct e)/L-
    log (correctionProduct e)/L*(L-log e.1) : ℝ) : ℂ)=_
  rw [hr,hlog]
  push_cast
  ring

theorem completed_sub_correction_bounds {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈correctionLabels u N) :
    -log n≤(completedCoefficient (SquarefreeVaughanLogSource.length u N) n-
      correctionCoefficient u N n).re ∧
      (completedCoefficient (SquarefreeVaughanLogSource.length u N) n-
        correctionCoefficient u N n).re≤0 := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
  have hqL := (correction_data hu hU hN he).2.2.2.2
  have hL := SquarefreeVaughanLogSource.length_pos u N
  rw [completed_sub_correction_eq hu hU hN he,Complex.ofReal_re]
  rw [show -log (correctionProduct e)*log e.2/SquarefreeVaughanLogSource.length u N=
    -(log (correctionProduct e)/SquarefreeVaughanLogSource.length u N*log e.2) by ring]
  have h0 : 0≤log (correctionProduct e)/SquarefreeVaughanLogSource.length u N :=
    div_nonneg (log_natCast_nonneg _) hL.le
  have hh : log (correctionProduct e)/SquarefreeVaughanLogSource.length u N*log e.2≤
      log (correctionProduct e) := by
    calc
      _ ≤ log (correctionProduct e)/SquarefreeVaughanLogSource.length u N*
          SquarefreeVaughanLogSource.length u N := mul_le_mul_of_nonneg_left hqL h0
      _ = _ := div_mul_cancel₀ _ hL.ne'
  constructor <;> nlinarith only [hh,mul_nonneg h0 (log_natCast_nonneg e.2)]

/-- One common support for ALL four retained low-count terms. -/
def joinedLabels (u : ℝ) (N : ℕ) : Finset ℕ :=
  (primeLabels N∪semiprimeLabels N)∪correctionLabels u N

/-- Exact signed coefficient, after both corrections have been joined
on the same label. Every original head/allocation/sieve mask stays literal. -/
def joinedCoefficient (u : ℝ) (N n : ℕ) : ℂ :=
  (if n∈primeLabels N∪semiprimeLabels N then
    completedCoefficient (SquarefreeVaughanLogSource.length u N) n else 0)+
    (if n∈headLabels u N then headCoefficient u N n else 0)-
    (if n∈correctionLabels u N then correctionCoefficient u N n else 0)

/-- Whole-population coefficient bound after SIGNED same-label
cancellation. It is used ONLY to pay exterior/partial phase periods. -/
theorem joinedCoefficient_bounds {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (n : ℕ) :
    -log n≤(joinedCoefficient u N n).re ∧ (joinedCoefficient u N n).re≤0 := by
  let L := SquarefreeVaughanLogSource.length u N
  let b := if n∈primeLabels N∪semiprimeLabels N then (completedCoefficient L n).re else 0
  let h := if n∈headLabels u N then (headCoefficient u N n).re else 0
  let c := if n∈correctionLabels u N then (correctionCoefficient u N n).re else 0
  have hb : -log n≤b ∧ b≤0 := by
    dsimp only [b]
    split_ifs with hn
    · apply completed_low_bounds (SquarefreeVaughanLogSource.length_pos u N)
      rcases Finset.mem_union.mp hn with hp | hs
      · exact Or.inl (Finset.mem_filter.mp hp).2
      · exact Or.inr (Finset.mem_filter.mp hs).2
    · exact ⟨neg_nonpos.mpr (log_natCast_nonneg _),le_refl _⟩
  have hh : 0≤h ∧ h≤c := by
    dsimp only [h,c]
    by_cases hn : n∈headLabels u N
    · rw [if_pos hn,if_pos (headLabels_subset_correction u N hn)]
      exact head_le_correction hu hU hN hn
    · rw [if_neg hn]
      split_ifs with hc
      · exact ⟨le_refl _,(correctionCoefficient_bounds hu hU hN hc).1⟩
      · exact ⟨le_refl _,le_refl _⟩
  have hbc : -log n≤b-c := by
    dsimp only [b,c]
    by_cases hc : n∈correctionLabels u N
    · rw [if_pos hc]
      by_cases hn : n∈primeLabels N∪semiprimeLabels N
      · rw [if_pos hn]
        simpa only [L,Complex.sub_re] using (completed_sub_correction_bounds hu hU hN hc).1
      · rw [if_neg hn]
        have hbnd := (correctionCoefficient_bounds hu hU hN hc).2
        linarith only [hbnd]
    · rw [if_neg hc,sub_zero]
      exact hb.1
  have he : (joinedCoefficient u N n).re=b+h-c := by
    unfold joinedCoefficient
    dsimp only [b,h,c,L]
    split_ifs <;> simp only [Complex.sub_re,Complex.add_re,Complex.zero_re]
  rw [he]
  constructor <;> linarith only [hb.2,hh.1,hh.2,hbc]

theorem joinedCoefficient_real (u : ℝ) (N n : ℕ) :
    joinedCoefficient u N n=((joinedCoefficient u N n).re : ℂ) := by
  have hb : (completedCoefficient (SquarefreeVaughanLogSource.length u N) n).im=0 := by
    unfold completedCoefficient
    split_ifs <;> rfl
  have hh : (headCoefficient u N n).im=0 := rfl
  have hc : (correctionCoefficient u N n).im=0 := rfl
  apply Complex.ext
  · rfl
  · unfold joinedCoefficient
    split_ifs <;> simp only [Complex.add_im,Complex.sub_im,hb,hh,hc,
      Complex.zero_im,add_zero,sub_zero,Complex.ofReal_im]

/-- ONE original divisor-log cap covers the joined four-term coefficient,
not four separate positive prices. This does not bound its interior sum. -/
theorem joinedCoefficient_majorant {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (n : ℕ) :
    ‖joinedCoefficient u N n‖≤zetaMoebiusLogMajorant n := by
  have hb := joinedCoefficient_bounds hu hU hN n
  rw [joinedCoefficient_real,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos hb.2]
  apply le_trans (by linarith only [hb.1])
    (ZetaRieszCentralWindow.log_le_divisor_majorant n)

private theorem masked_sum {S T : Finset ℕ} (hST : S⊆T) (f : ℕ→ℂ) :
    (∑ n∈T,if n∈S then f n else 0)=∑ n∈S,f n := by
  rw [←Finset.sum_subset (f:=fun n => if n∈S then f n else 0) hST (by
    intro n _hn hns
    exact if_neg hns)]
  exact Finset.sum_congr rfl (fun n hn => if_pos hn)

private theorem prime_semiprime_disjoint (N : ℕ) :
    Disjoint (primeLabels N) (semiprimeLabels N) := by
  apply Finset.disjoint_left.mpr
  intro n hp hs
  have hpp := (Finset.mem_filter.mp hp).2
  have hc := (Finset.mem_filter.mp hs).2.2
  simp only [hpp.primeFactors,Finset.card_singleton] at hc
  omega

private theorem joined_sum_eq (u : ℝ) (N : ℕ) (y : ℝ) :
    (∑ n∈joinedLabels u N,joinedCoefficient u N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
      (∑ n∈primeLabels N,completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
      (∑ n∈semiprimeLabels N,completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
      (∑ n∈headLabels u N,headCoefficient u N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      (∑ n∈correctionLabels u N,correctionCoefficient u N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  have hl : primeLabels N∪semiprimeLabels N⊆joinedLabels u N := Finset.subset_union_left
  have hc : correctionLabels u N⊆joinedLabels u N := Finset.subset_union_right
  have hh := (headLabels_subset_correction u N).trans hc
  simp only [joinedCoefficient,sub_mul,add_mul,ite_mul,zero_mul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [masked_sum hl,masked_sum hh,masked_sum hc,
    Finset.sum_union (prime_semiprime_disjoint N)]

/-- Exact equality with the EXISTING retained signed main. This is used
to spend the joint geometric edge estimate, not to create another source. -/
theorem lowCountBoundary_eq_joined {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) (y : ℝ) :
    lowCountBoundary u y j=
      ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈joinedLabels u (dyadicMomentOrder j),
        joinedCoefficient u (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re := by
  rw [joined_sum_eq,mul_sub,mul_add,mul_add,Complex.sub_re,Complex.add_re,Complex.add_re,
    ←originalHead_eq_label_sum (by omega : 64≤dyadicMomentOrder j) y,
    ZetaRieszPrimeHeadPolePayment.originalHead_re,
    ←highPrimeCorrection_eq_label_sum hu hU hN y]
  rfl

/-- The retained SIGNED complete-period aggregate; all four original
components have already been joined on their common physical labels. -/
def lowCountPeriods (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  ((u : ℂ)^(N+1)*∑ n∈completePeriodLabels (joinedLabels u N) N y,
    joinedCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re

/-- Concrete joint saving: ONE geometric budget pays all partial-period
and outer-window terms of the remaining prime/prime-pair main. The signed
complete-period main is NEVER assigned a positive atom allowance. -/
theorem lowCountBoundary_sub_periods_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hN : 65536≤dyadicMomentOrder j) {y : ℝ} (hy : 54≤|y|) :
    |lowCountBoundary u y j-lowCountPeriods u y j|≤
      ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*periodEdgeConstant := by
  have h := (Classical.choose_spec exists_whole_period_edge_bound).2
    (dyadicMomentOrder j) (joinedLabels u (dyadicMomentOrder j))
      (joinedCoefficient u (dyadicMomentOrder j)) (by omega : 64≤dyadicMomentOrder j)
        (fun n _hn => joinedCoefficient_majorant hu hU hN n)
          y u hy (by linarith : 0≤u) hU
  have hr := (Complex.abs_re_le_norm _).trans h
  rw [mul_sub,Complex.sub_re] at hr
  rw [lowCountBoundary_eq_joined hu hU hN y]
  exact hr

/-- Native payments plus the ONE newly joined partial-period error. No
earlier head price or old four-component period payment is spent again. -/
def nativeSignedPeriodBudget (u y : ℝ) (j : ℕ) : ℝ :=
  nativeLowCountBudget u y j+
    ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*periodEdgeConstant

theorem nativeSignedPeriodBudget_tendsto (u y : ℝ) :
    Tendsto (nativeSignedPeriodBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => nativeLowCountBudget u y j+
    ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*periodEdgeConstant) atTop (𝓝 0)
  have hp := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    ZetaRieszLargeOrderCore.rate_bounds.1.le ZetaRieszLargeOrderCore.rate_bounds.2).mul_const
      periodEdgeConstant).comp tendsto_dyadicMomentOrder
  simpa only [Function.comp_def,zero_mul,add_zero] using
    (nativeLowCountBudget_tendsto u y).add hp

/-- Spend the independent boundary saving inside the SAME native floor
ledger. The only unpaid target is the ONE signed complete-period scalar. -/
theorem eventually_native_signed_period_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
        lowCountPeriods u y j|≤nativeSignedPeriodBudget u y j := by
  filter_upwards [eventually_native_lowCount_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hn hN
  have he := lowCountBoundary_sub_periods_bound hu.le hU hN hy
  unfold nativeSignedPeriodBudget
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp hn).1,(abs_le.mp hn).2,
    (abs_le.mp he).1,(abs_le.mp he).2]

theorem tendsto_native_plus_lowCountPeriods {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
          lowCountPeriods u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (nativeSignedPeriodBudget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_native_signed_period_bound hu hU hy

/-- Actual one-sided native inequality after all low-count boundary
families have been paid jointly. `lowCountPeriods<=399/5000+o(1)` remains
OPEN; neither the floor nor any zero exclusion is inferred here. -/
theorem eventually_native_signed_period_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -lowCountPeriods u y j-nativeSignedPeriodBudget u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_signed_period_bound hu hU hy] with j hj
  linarith only [(abs_le.mp hj).1]

end RiemannGaussian.ZetaRieszLowCountSignedBoundary
