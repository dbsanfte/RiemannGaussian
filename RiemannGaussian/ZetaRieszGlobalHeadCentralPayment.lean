/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalBoundaryPruning

/-!
# Pay the full head's radial mismatch, then join its semiprime boundary

The SAME full head is not paid to zero. Only its two exterior radial
strips are paid, uniformly in height, with the existing geometric rate.
On the remaining central labels, the head cancels against the literal
semiprime completion BEFORE any norm. The other signed boundaries remain
joined and their required cofinal upper bound remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalHeadCentralPayment
open ZetaRieszGlobalBoundaryPruning ZetaRieszGlobalCentralPayment
open ZetaRieszGlobalBulkPayment ZetaRieszBalancedRadialPayment
open ZetaRieszPrimeHeadPolePayment ZetaRieszPrimeHeadTransport
open ZetaRieszGlobalCompletionBoundary
open ZetaRieszSmallTagNativeFloor (owners owners_data smallPrimes)
open ZetaRieszOwnerMaximal (ownerWeight ownerWeight_bounds)
open ZetaRieszPrimeCountFrequency

/-- Original head pairs; only the identically zero nonprime slots are
removed. The original owner, physical, sieve and radial masks stay exact. -/
def pairs (u : ℝ) (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (owners u N).sigma (fun p => (pairInterval N p).filter Nat.Prime)

/-- The physical product of a canonical owner and its prime cofactor. -/
def label (e : Σ _ : ℕ, ℕ) : ℕ := e.1*e.2

private theorem pair_data {u : ℝ} {N : ℕ} {e : Σ _ : ℕ, ℕ}
    (he : e∈pairs u N) :
    e.1∈owners u N ∧ e.2∈pairInterval N e.1 ∧ e.2.Prime := by
  simpa only [pairs,Finset.mem_sigma,Finset.mem_filter] using he

/-- The larger original head prime is the canonical owner of its label. -/
theorem largestPrime_label {u : ℝ} {N : ℕ} (hN : 64≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈pairs u N) :
    ZetaRieszPrimeEndpoint.largestPrime (label e)=e.1 := by
  obtain ⟨hp,hq,hqp⟩ := pair_data he
  apply ZetaRieszPrimeIntervals.largestPrime_mul _ _ (owners_data hp).1 hqp.ne_zero
  intro q hq'
  rw [hqp.primeFactors,Finset.mem_singleton] at hq'
  subst q
  exact pair_cofactor_lt_owner hN hp hq

/-- Each original pair is counted ONCE on the physical label axis. -/
theorem label_injective {u : ℝ} {N : ℕ} (hN : 64≤N) :
    Set.InjOn label (pairs u N) := by
  intro e he f hf h
  have hp : e.1=f.1 := by
    rw [← largestPrime_label hN he,← largestPrime_label hN hf,h]
  have h0 := (owners_data (pair_data he).1).1.pos
  have hq : e.2=f.2 := by
    apply Nat.eq_of_mul_eq_mul_left h0
    simpa only [label,← hp] using h
  exact Sigma.ext hp (heq_of_eq hq)

/-- Exact physical product labels of the SAME full original head. -/
def headLabels (u : ℝ) (N : ℕ) : Finset ℕ := (pairs u N).image label

private theorem pair_squarefree {u : ℝ} {N : ℕ} (hN : 64≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈pairs u N) : Squarefree (label e) := by
  obtain ⟨hp,hq,hqp⟩ := pair_data he
  have hpp := (owners_data hp).1
  have hpq : e.1≠e.2 := (pair_cofactor_lt_owner hN hp hq).ne'
  have hcop := hpp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp h))
  exact Nat.squarefree_mul_iff.mpr ⟨hcop,hpp.squarefree,hqp.squarefree⟩

private theorem pair_count {u : ℝ} {N : ℕ} (hN : 64≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈pairs u N) : (label e).primeFactors.card=2 := by
  obtain ⟨hp,hq,hqp⟩ := pair_data he
  have hpp := (owners_data hp).1
  have hpq : e.1≠e.2 := (pair_cofactor_lt_owner hN hp hq).ne'
  simp only [label,Nat.primeFactors_mul hpp.ne_zero hqp.ne_zero,
    hpp.primeFactors,hqp.primeFactors,Finset.union_singleton]
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hpq.symm),
    Finset.card_singleton]

/-- Head coefficient in the canonical product coordinates. No limiting
allocation or count density replaces the exact ownerWeight or sieve. -/
def headCoefficient (u : ℝ) (N n : ℕ) : ℂ :=
  let p := ZetaRieszPrimeEndpoint.largestPrime n
  let q := ZetaRieszOwnedCells.ownerCofactor n
  let L := SquarefreeVaughanLogSource.length u N
  ((log n/L*(L-log p)*ownerWeight N (log q/log n)*
    ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) q : ℝ) : ℂ)

private theorem kernel_phase (N : ℕ) (y : ℝ) (n : ℕ) :
    zetaPrimeLogKernel N (3/2+Complex.I*y) n=
      ((log n^N/(N.factorial : ℝ)*exp (-(3/2 : ℝ)*log n) : ℝ) : ℂ)*
        Complex.exp (Complex.I*((-(y*log n) : ℝ) : ℂ)) := by
  unfold zetaPrimeLogKernel zetaPrimeFeature
  rw [show -((3/2+Complex.I*y)*(log n : ℂ))=
    ((-(3/2 : ℝ)*log n : ℝ) : ℂ)+Complex.I*((-(y*log n) : ℝ) : ℂ) by
      push_cast; ring,Complex.exp_add,← Complex.ofReal_exp]
  push_cast
  ring

private theorem coefficient_pair {u : ℝ} {N : ℕ} (hN : 64≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈pairs u N) :
    headCoefficient u N (label e)=
      ((log (label e)/SquarefreeVaughanLogSource.length u N*
        (SquarefreeVaughanLogSource.length u N-log e.1)*
        ownerWeight N (log e.2/log (label e))*
        ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) e.2 : ℝ) : ℂ) := by
  obtain ⟨hp,hq,hqp⟩ := pair_data he
  have hm : ∀ q∈e.2.primeFactors,q<e.1 := by
    intro q h
    rw [hqp.primeFactors,Finset.mem_singleton] at h
    subst q
    exact pair_cofactor_lt_owner hN hp hq
  unfold headCoefficient
  rw [largestPrime_label hN he]
  rw [show label e=e.1*e.2 from rfl,
    ZetaRieszPrimeIntervals.ownerCofactor_mul _ _ (owners_data hp).1 hqp.ne_zero hm]

/-- Every label retains the original complex product phase. -/
theorem originalPair_eq_label_atom {u : ℝ} {N : ℕ} (hN : 64≤N)
    {e : Σ _ : ℕ, ℕ} (he : e∈pairs u N) (y : ℝ) :
    originalPair u y N e.1 e.2=
      (u : ℂ)^(N+1)*headCoefficient u N (label e)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (label e) := by
  obtain ⟨hp,hq,hqp⟩ := pair_data he
  have hpp := (owners_data hp).1
  have ht : log (label e)=log e.1+log e.2 := by
    rw [label,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast hqp.ne_zero)]
  have hExp : exp (-(3/2 : ℝ)*log (label e))=
      exp (-log (label e)/2)/((label e : ℕ) : ℝ) := by
    rw [show -(3/2 : ℝ)*log (label e)=
      -log (label e)/2+-log (label e) by ring,exp_add,exp_neg,
      exp_log (by exact_mod_cast Nat.mul_pos hpp.pos hqp.pos)]
    ring
  rw [coefficient_pair hN he,kernel_phase,hExp,ht]
  simp only [originalPair,rawAmount,if_pos hqp,character,
    ZetaRieszSmoothOwnerDiscrepancy.radial,label,Nat.cast_mul,pow_succ]
  push_cast
  ring

/-- Join the original head on its product axis, with no repeated labels. -/
theorem originalHead_eq_label_sum {u : ℝ} {N : ℕ} (hN : 64≤N) (y : ℝ) :
    originalHead u y N=(u : ℂ)^(N+1)*∑ n∈headLabels u N,
      headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  rw [headLabels,Finset.sum_image (label_injective hN)]
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc]
  have he : (∑ e∈pairs u N,originalPair u y N e.1 e.2)=originalHead u y N := by
    simp only [pairs,Finset.sum_sigma,Finset.sum_filter,originalHead]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.Prime
    · simp only [if_pos hq]
    · simp only [originalPair,rawAmount,if_neg hq,mul_zero,
        Complex.ofReal_zero,zero_mul]
  rw [← he]
  exact Finset.sum_congr rfl (fun e he => originalPair_eq_label_atom hN he y)

/-- On every original head label, the exact positive head coefficient
is dominated by the OPPOSITE semiprime coefficient. This is a same-label
cancellation, with the original allocation and sieve still present. -/
theorem headCoefficient_bounds {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈headLabels u N) :
    0≤(headCoefficient u N n).re ∧
      (headCoefficient u N n).re≤
        -(completedCoefficient (SquarefreeVaughanLogSource.length u N) n).re := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,hqp⟩ := pair_data he
  have hs := pair_squarefree (by omega : 64≤N) he
  let L := SquarefreeVaughanLogSource.length u N
  let H := (L-log e.1)*ownerWeight N (log e.2/log (label e))
  let R := VaughanLogAverage.riesz L (label e)
  have hL : 0<L := SquarefreeVaughanLogSource.length_pos u N
  have ht : log (label e)=log e.1+log e.2 := by
    rw [label,Nat.cast_mul,log_mul (by exact_mod_cast (owners_data hp).1.ne_zero)
      (by exact_mod_cast hqp.ne_zero)]
  have hh : 0≤H := by
    have hm := (ZetaRieszOwnerCompletionAudit.allocated_head_le_boundary hu hU hN hp hq hqp).1
    simpa only [H,ht,L] using hm
  have hHR : H≤R := by
    have hm := pair_response_sub_head_lower hu hU hN hp hq hqp
    have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
    dsimp only [H,R,L]
    rw [ht]
    change _≤VaughanLogAverage.riesz _ (e.1*e.2)
    nlinarith only [hm,hN0]
  have hS : 0≤ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) e.2 ∧
      ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) e.2≤1 := by
    unfold ZetaRieszUnsignedDivisorError.sieve
    split_ifs <;> norm_num
  have hfac : 0≤log (label e)/L := div_nonneg (log_natCast_nonneg _) hL.le
  rw [coefficient_pair (by omega : 64≤N) he]
  simp only [completedCoefficient,if_pos hs,Complex.ofReal_re]
  rw [show log (label e)/SquarefreeVaughanLogSource.length u N*
    (SquarefreeVaughanLogSource.length u N-log e.1)*
    ownerWeight N (log e.2/log (label e))=log (label e)/L*H by dsimp [L,H]; ring]
  change 0≤log (label e)/L*H*ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) e.2 ∧
    log (label e)/L*H*ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) e.2≤
      -(-log (label e)*R/L)
  constructor
  · exact mul_nonneg (mul_nonneg hfac hh) hS.1
  · calc
      _ ≤ log (label e)/L*H := mul_le_of_le_one_right (mul_nonneg hfac hh) hS.2
      _ ≤ log (label e)/L*R := mul_le_mul_of_nonneg_left hHR hfac
      _ = _ := by ring

private theorem headCoefficient_real (u : ℝ) (N n : ℕ) :
    headCoefficient u N n=((headCoefficient u N n).re : ℂ) := by
  simp only [headCoefficient,Complex.ofReal_re]

private theorem completedCoefficient_real (L : ℝ) (n : ℕ) :
    completedCoefficient L n=((completedCoefficient L n).re : ℂ) := by
  unfold completedCoefficient
  split_ifs <;> simp only [Complex.ofReal_re,Complex.zero_re,Complex.ofReal_zero]

/-- The exact head coefficient obeys the funded divisor-log majorant. -/
theorem headCoefficient_majorant {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈headLabels u N) :
    ‖headCoefficient u N n‖≤zetaMoebiusLogMajorant n := by
  have hh := headCoefficient_bounds hu hU hN hn
  have hc := completedCoefficient_norm_le (SquarefreeVaughanLogSource.length_pos u N) n
  have hr : ‖headCoefficient u N n‖≤
      ‖completedCoefficient (SquarefreeVaughanLogSource.length u N) n‖ := by
    rw [headCoefficient_real,completedCoefficient_real,Complex.norm_real,
      Complex.norm_real,Real.norm_of_nonneg hh.1,Real.norm_eq_abs]
    have hn0 : (completedCoefficient (SquarefreeVaughanLogSource.length u N) n).re≤0 := by
      linarith only [hh.1,hh.2]
    rw [abs_of_nonpos hn0]
    exact hh.2
  exact hr.trans hc

/-- Only the two radial strips of the SAME full head are projected. -/
def centralHeadLabels (u : ℝ) (N : ℕ) : Finset ℕ :=
  LogarithmicDeviation.deviationBand (headLabels u N) (1971/1000) (2029/1000) N

/-- The original head on its literal central physical labels, with every
factorial allocation and ordinary-prime condition unchanged. -/
def centralHead (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈centralHeadLabels u N,
    headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- Fund the entire radial mask mismatch before cancelling with central
semiprimes. The head itself is NOT paid to zero. -/
theorem full_sub_centralHead_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) (y : ℝ) :
    ‖originalHead u y N-centralHead u y N‖≤
      ZetaRieszLargeOrderCore.rate^N*radialConstant := by
  have h := (Classical.choose_spec ZetaRieszLargeOrderCore.exists_edge_bound).2
    N (headLabels u N) (headCoefficient u N) (fun _ hn =>
      headCoefficient_majorant hu hU hN hn) y u (by linarith : 0≤u) hU
  rw [originalHead_eq_label_sum (by omega : 64≤N) y]
  simpa only [centralHead,centralHeadLabels,radialConstant,mul_sub] using h

/-- The head's newly funded radial mismatch vanishes at native orders. -/
theorem tendsto_full_sub_centralHead {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => originalHead u y (dyadicMomentOrder j)-
      centralHead u y (dyadicMomentOrder j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ radialBudget_tendsto
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))]
    with j hj
  exact full_sub_centralHead_bound hu hU hj y

/-- Every projected head label is a genuine CENTRAL semiprime. Neither
ordinary primes nor unmatched semiprimes are silently included here. -/
theorem centralHeadLabels_subset_semiprime {u : ℝ} {N : ℕ} (hN : 64≤N) :
    centralHeadLabels u N⊆semiprimeLabels N := by
  intro n hn
  obtain ⟨hhead,hlo,hhi⟩ := Finset.mem_filter.mp hn
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hhead
  have hs := pair_squarefree hN he
  have hc := pair_count hN he
  have hn0 : (0 : ℝ)<label e := by exact_mod_cast Nat.pos_of_ne_zero hs.ne_zero
  have hNp : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hf : label e∈fullLabels N := by
    apply Finset.mem_Ioc.mpr
    constructor
    · apply (Nat.floor_lt (exp_pos _).le).mpr
      rw [sub_zero]
      apply (exp_lt_exp.mpr (show (39/20 : ℝ)*N<log (label e) by
        nlinarith only [hlo,hNp])).trans_eq (exp_log hn0)
    · apply Nat.le_floor
      rw [sub_zero,← exp_log hn0]
      apply exp_le_exp.mpr
      nlinarith only [hhi,hNp]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hf,hlo,hhi⟩,hs,hc⟩

private theorem norm_head_atom_independent_height (u y : ℝ) (N n : ℕ) :
    ‖(u : ℂ)^(N+1)*headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖=
      ‖(u : ℂ)^(N+1)*headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*0) n‖ := by
  simp only [norm_mul,norm_zetaPrimeLogKernel,zetaPrimeExpWeight,
    Complex.add_re,Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,sub_zero,add_zero]

private theorem norm_completed_atom_independent_height (u y : ℝ) (N n : ℕ) :
    ‖(u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖=
      ‖(u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*0) n‖ := by
  simp only [norm_mul,norm_zetaPrimeLogKernel,zetaPrimeExpWeight,
    Complex.add_re,Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,mul_zero,sub_zero,add_zero]

/-- The full semiprime diagonal price; it is a diagnostic allowance,
not asserted bounded cofinally. Matching head credit is subtracted only
AFTER the same physical atoms have been joined. -/
def semiprimePrice (u : ℝ) (N : ℕ) : ℝ :=
  ∑ n∈semiprimeLabels N,
    ‖(u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*0) n‖

/-- Exact nonnegative mass of the matching CENTRAL head atoms. This is
not an independently spent norm allowance for the signed head. -/
def centralHeadMass (u : ℝ) (N : ℕ) : ℝ :=
  ∑ n∈centralHeadLabels u N,
    ‖(u : ℂ)^(N+1)*headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*0) n‖

/-- All central same-label cancellations joined before taking a norm.
The other semiprime labels remain in their original price. -/
theorem central_semiprime_head_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) (y : ℝ) :
    ‖completionTerm u y N (semiprimeLabels N)+centralHead u y N‖≤
      semiprimePrice u N-centralHeadMass u N := by
  let S := semiprimeLabels N
  let H := centralHeadLabels u N
  let a := fun n => (u : ℂ)^(N+1)*
    completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let b := fun n => (u : ℂ)^(N+1)*headCoefficient u N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hHS : H⊆S := centralHeadLabels_subset_semiprime (by omega : 64≤N)
  have he : completionTerm u y N S+centralHead u y N=
      ∑ n∈S\H,a n+∑ n∈H,(a n+b n) := by
    have hs := Finset.sum_sdiff hHS (f:=a)
    simp only [completionTerm,centralHead,Finset.mul_sum] at hs ⊢
    dsimp only [a,b,H,S] at hs ⊢
    rw [Finset.sum_add_distrib]
    simp only [mul_assoc] at hs ⊢
    rw [← hs]
    ring
  have hj n (hn : n∈H) : ‖a n+b n‖=‖a n‖-‖b n‖ := by
    have hd := headCoefficient_bounds hu hU hN (Finset.mem_filter.mp hn).1
    have ha : (completedCoefficient (SquarefreeVaughanLogSource.length u N) n).re≤0 := by
      linarith only [hd.1,hd.2]
    have hab : (completedCoefficient (SquarefreeVaughanLogSource.length u N) n).re+
      (headCoefficient u N n).re≤0 := by linarith only [hd.2]
    dsimp only [a,b]
    rw [show (u : ℂ)^(N+1)*completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n+
      (u : ℂ)^(N+1)*headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n=
        (u : ℂ)^(N+1)*(completedCoefficient (SquarefreeVaughanLogSource.length u N) n+
          headCoefficient u N n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n by ring]
    simp only [norm_mul]
    rw [headCoefficient_real,completedCoefficient_real,← Complex.ofReal_add]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos ha,
      abs_of_nonpos hab,abs_of_nonneg hd.1]
    ring
  rw [he]
  apply ((norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))).trans
  rw [show (∑ n∈H,‖a n+b n‖)=∑ n∈H,(‖a n‖-‖b n‖) from
    Finset.sum_congr rfl hj,Finset.sum_sub_distrib]
  have hs := Finset.sum_sdiff hHS (f:=fun n => ‖a n‖)
  rw [← add_sub_assoc]
  rw [show (∑ n∈S\H,‖a n‖)+(∑ n∈H,‖a n‖)-(∑ n∈H,‖b n‖)=
    (∑ n∈S,‖a n‖)-(∑ n∈H,‖b n‖) by linear_combination hs]
  dsimp only [S,H,a,b]
  simp_rw [norm_completed_atom_independent_height u y N,
    norm_head_atom_independent_height u y N]
  exact le_rfl

private theorem head_atom_norm_eq_zero_re {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536≤N) (hn : n∈headLabels u N) :
    ‖(u : ℂ)^(N+1)*headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*0) n‖=
      ((u : ℂ)^(N+1)*headCoefficient u N n*zetaPrimeLogKernel N (3/2+Complex.I*0) n).re := by
  let a := u^(N+1)*(headCoefficient u N n).re*
    (log n^N/(N.factorial : ℝ)*exp (-(3/2 : ℝ)*log n))
  have ha : 0≤a := by
    have hh := (headCoefficient_bounds hu hU hN hn).1
    have hlog := log_natCast_nonneg n
    have hu0 : 0≤u := by linarith only [hu]
    dsimp only [a]
    positivity
  have he : (u : ℂ)^(N+1)*headCoefficient u N n*
      zetaPrimeLogKernel N (3/2+Complex.I*0) n=(a : ℂ) := by
    have hk := kernel_phase N 0 n
    simp only [Complex.ofReal_zero] at hk
    rw [hk,headCoefficient_real]
    simp only [zero_mul,neg_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
    dsimp only [a]
    push_cast
    rfl
  rw [he,Complex.norm_of_nonneg ha,Complex.ofReal_re]

/-- This is the mass of the matching physical head, evaluated at zero
height ONLY to measure the exact same-label credit. The actual signed
head at height y remains in the joined estimate. -/
theorem centralHeadMass_eq_zero_re {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) : centralHeadMass u N=(centralHead u 0 N).re := by
  unfold centralHeadMass centralHead
  rw [Finset.mul_sum]
  simp only [Complex.re_sum,mul_assoc,Complex.ofReal_zero]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [mul_assoc] using
    head_atom_norm_eq_zero_re hu hU hN (Finset.mem_filter.mp hn).1

/-- The full head's zero-height mass differs from the central matching
credit by only the funded radial error. No numerical value is assigned
to the existing finite radial constant. -/
theorem fullHead_sub_centralMass_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) :
    |ZetaRieszRoughPrimePairCancellation.nativeHead u 0 N-centralHeadMass u N|≤
      ZetaRieszLargeOrderCore.rate^N*radialConstant := by
  have h := (Complex.abs_re_le_norm (originalHead u 0 N-centralHead u 0 N)).trans
    (full_sub_centralHead_bound hu hU hN 0)
  simpa only [Complex.sub_re,originalHead_re,centralHeadMass_eq_zero_re hu hU hN] using h

/-- WHOLE central semiprime population plus the SAME FULL head. The
coupled norm loses one full head mass, with only a geometric boundary
error. Compared with the separated price, the saving is TWO head masses
minus that error. This is not a bounded cofinal floor allowance. -/
theorem full_semiprime_head_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) (y : ℝ) :
    ‖completionTerm u y N (semiprimeLabels N)+originalHead u y N‖≤
      semiprimePrice u N-ZetaRieszRoughPrimePairCancellation.nativeHead u 0 N+
        2*(ZetaRieszLargeOrderCore.rate^N*radialConstant) := by
  have hj := central_semiprime_head_bound hu hU hN y
  have he := full_sub_centralHead_bound hu hU hN y
  have hm := (abs_le.mp (fullHead_sub_centralMass_bound hu hU hN)).2
  have h : ‖completionTerm u y N (semiprimeLabels N)+originalHead u y N‖≤
      ‖completionTerm u y N (semiprimeLabels N)+centralHead u y N‖+
        ‖originalHead u y N-centralHead u y N‖ := by
    rw [show completionTerm u y N (semiprimeLabels N)+originalHead u y N=
      (completionTerm u y N (semiprimeLabels N)+centralHead u y N)+
      (originalHead u y N-centralHead u y N) by ring]
    exact norm_add_le _ _
  linarith only [h,hj,he,hm]

/-- Apply the global cancellation INSIDE the current signed boundary.
Primes and raw high owners remain ONE signed scalar, never separately
norm-priced or claimed to decay. -/
theorem prunedBoundary_upper {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j : ℕ}
    (hj : 65536≤dyadicMomentOrder j) (y : ℝ) :
    (prunedBoundary u y j).re≤
      (completionTerm u y (dyadicMomentOrder j) (primeLabels (dyadicMomentOrder j))+
        completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)).re+
      semiprimePrice u (dyadicMomentOrder j)-
        ZetaRieszRoughPrimePairCancellation.nativeHead u 0 (dyadicMomentOrder j)+
      2*radialBudget j := by
  have h := (Complex.re_le_norm
    (completionTerm u y (dyadicMomentOrder j) (semiprimeLabels (dyadicMomentOrder j))+
      originalHead u y (dyadicMomentOrder j))).trans (full_semiprime_head_bound hu hU hj y)
  simp only [Complex.add_re,originalHead_re] at h ⊢
  unfold prunedBoundary
  dsimp only
  simp only [Complex.add_re,Complex.ofReal_re]
  unfold radialBudget
  linarith only [h]

/-- This concrete joined saving is spent in the whole native floor.
The remaining signed prime/raw-owner scalar and semiprime-minus-head
price are explicit; their cofinal size is NOT assumed small. -/
theorem eventually_native_floor_with_semiprime_credit {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -(completionTerm u y (dyadicMomentOrder j) (primeLabels (dyadicMomentOrder j))+
        completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)).re-
      semiprimePrice u (dyadicMomentOrder j)+
        ZetaRieszRoughPrimePairCancellation.nativeHead u 0 (dyadicMomentOrder j)-
      (nativePrunedBudget u y j+2*radialBudget j)≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_pruned_floor hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hn hj
  have hp := prunedBoundary_upper (by linarith : 1/2≤u) hU hj y
  linarith only [hn,hp]

end RiemannGaussian.ZetaRieszGlobalHeadCentralPayment
