/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallTagNativeFloor

/-!
# Signed cancellation of complete rough rows with their prime head

Keep the ordinary-prime subtraction as part of the joint target. The
integer-density main is paid only after its full phase has been summed.
All composite counts and the original owner allocation remain. No bound
on the surviving prime-pair head itself is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszRoughPrimePairCancellation
open ZetaRieszOwnerLatticePhase ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszRoughOwnerComparison ZetaRieszCofactorDiscrepancy
open ZetaRieszJointAllocation ZetaRieszPrimeEndpoint ZetaRieszPrimeCountFrequency
open ZetaRieszCutoffPeriodFloor
open ZetaRieszLongCutoffError (roughDensityPrefix)
open ZetaRieszUnsignedDivisorError (sieve)

/-- The signed cutoff scalar, with all divisor signs retained. -/
def densityScalar (S : Finset ℕ) (R : ℕ) (b : ℝ) : ℝ :=
  ∑ D∈Finset.Icc 1 R,
    (max 0 (b-log D)-max 0 (b-log (D+1 : ℕ)))*roughDensityPrefix S D

/-- The original singleton-owner row, with squarefree/composite/rough
masks inside the finite arithmetic sum. -/
def row (S A : Finset ℕ) (N M X p : ℕ) (L y : ℝ) : ℝ :=
  ∑ a∈(Finset.Ioc M X).filter (fun a =>
    Squarefree a ∧ ¬a.Prime ∧ ¬∃ q∈S, q∣a),
    (residualCoefficient (A∩{largestPrime (p*a)}) L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re

/-- The literal ordinary-prime cofactor correction. The smooth owner
allocation is kept EXACTLY, including on this completed prime head. -/
def head (S : Finset ℕ) (N M X p : ℕ) (L y : ℝ) : ℝ :=
  ((L-log p)/(L*p))*∑ q∈Finset.Ioc M X,
    if q.Prime then ownerTest N (log p) y q*sieve S q else 0

/-- The signed integer-density main; no prime-count split is made. -/
def main (S : Finset ℕ) (N M X R p : ℕ) (L y : ℝ) : ℝ :=
  (densityScalar S R (L-log p)/(L*p))*∑ a∈Finset.Ioc M X, ownerTest N (log p) y a

private theorem shell_sum (M X N : ℕ) (c y : ℝ) (f : ℕ→ℝ) :
    (∑ a∈Finset.Icc 1 X,shellWeight M X (ownerAmplitude N c) y c a*f a)=
      ∑ a∈Finset.Ioc M X,ownerTest N c y a*f a := by
  have hs : Finset.Ioc M X⊆Finset.Icc 1 X := fun n hn =>
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,(Finset.mem_Ioc.mp hn).2⟩
  rw [← Finset.sum_subset (f:=fun a => shellWeight M X (ownerAmplitude N c) y c a*f a)
    hs (by
      intro a ha hn
      have hx := (Finset.mem_Icc.mp ha).2
      have hm : ¬M<a := fun h => hn (Finset.mem_Ioc.mpr ⟨h,hx⟩)
      simp only [shellWeight,hm,false_and,ite_false,zero_mul])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [shellWeight,if_pos (Finset.mem_Ioc.mp ha),ownerTest_nat]

/-- A complete dyadic row has a signed comparison for ROW + HEAD.
Taking separate positive costs for its composite counts is unnecessary. -/
theorem shell_joint_comparison (S A : Finset ℕ) (hS : ∀ q∈S,q.Prime)
    {N M X R p : ℕ} (hN : 32≤N) (hM : 0<M) (hMX : M<X) (hXM : X≤2*M)
    (hRM : R≤M) (hcut : R^4≤M^3) (hlarge : exp ((N : ℝ)/2)≤M)
    (hp : p.Prime) (hXp : X<p) (hpA : p∈A) {L u : ℝ} (hL : 0<L)
    (hpL : log p≤L) (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hend : L-log p≤log (R+1 : ℕ)) (y : ℝ) :
    |u^(N+1)*(row S A N M X p L y+head S N M X p L y-main S N M X R p L y)|≤
      (2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹ := by
  have he := literal_rough_owner_error_cap S A hS hN hM hMX hXM hRM hcut hlarge
    hp hXp hpA hL hpL hu hU hend y
  dsimp only at he
  have h0 := shell_sum M X N (log p) y (fun _ => 1)
  simp only [mul_one] at h0
  have h1 := shell_sum M X N (log p) y (fun a => if a.Prime then sieve S a else 0)
  simp only [mul_ite,mul_zero] at h1
  rw [← Finset.sum_filter] at h1
  rw [h0,h1] at he
  convert he using 1
  congr 2
  unfold row head main densityScalar
  ring

private theorem partition_sum (f : ℕ→ℝ) (a : ℕ→ℕ) (ha : Monotone a) (b : ℕ) :
    (∑ i∈Finset.range b,∑ n∈Finset.Ioc (a i) (a (i+1)),f n)=
      ∑ n∈Finset.Ioc (a 0) (a b),f n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ,ih]
    exact Finset.sum_Ioc_consecutive f (ha (Nat.zero_le b)) (ha (Nat.le_succ b))

private def front (M X i : ℕ) : ℕ := min X (2^i*M)

private theorem front_monotone (M X : ℕ) : Monotone (front M X) := by
  intro i j hij
  unfold front
  exact min_le_min_left X (Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by omega : 1≤2) hij))

private theorem front_bounds {M X : ℕ} (hMX : M≤X) (i : ℕ) :
    M≤front M X i ∧ front M X i≤X := by
  refine ⟨le_min hMX ?_,min_le_left _ _⟩
  have h : 1≤2^i := Nat.one_le_pow i 2 (by omega)
  simpa using Nat.mul_le_mul_right M h

private theorem front_dyadic {M X i : ℕ} (hi : front M X i<front M X (i+1)) :
    front M X (i+1)≤2*front M X i := by
  have hp : 2^i*M<X := by
    by_contra h
    have he : front M X i=X := min_eq_left (by omega)
    have hb : front M X (i+1)≤X := min_le_left _ _
    omega
  rw [show front M X i=2^i*M from min_eq_right hp.le]
  have hb : front M X (i+1)≤2^(i+1)*M := min_le_right _ _
  rw [pow_succ] at hb
  nlinarith only [hb]

private theorem core_cover {N : ℕ} (hN : 64≤N) {c : ℝ} (hc : c≤(4/3 : ℝ)*N) :
    coreFloor N c (203/100)≤2^N*coreFloor N c (39/20) := by
  have hwide := (coreFloor_geometry hN hc).2.2.2.1
  have he : exp (1/10 : ℝ)≤2 := by
    have hl := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    have hlog : (1/10 : ℝ)≤log 2 := by norm_num at hl; linarith
    simpa only [exp_log (by norm_num : (0 : ℝ)<2)] using exp_le_exp.mpr hlog
  have hn := pow_le_pow_left₀ (exp_pos (1/10 : ℝ)).le he N
  rw [← exp_nat_mul] at hn
  have hh := hwide.trans (mul_le_mul_of_nonneg_left
    (show exp ((N : ℝ)/10)≤(2 : ℝ)^N by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hn)
      (Nat.cast_nonneg _))
  exact_mod_cast (show (coreFloor N c (203/100) : ℝ)≤
    (2 : ℝ)^N*coreFloor N c (39/20) by simpa only [mul_comm] using hh)

/-- Join ALL radial rows with the SAME signed density scalar and the
SAME prime head before applying the complete-window phase estimate. -/
theorem core_joint_comparison (S A : Finset ℕ) (hS : ∀ q∈S,q.Prime)
    {N R p : ℕ} (hN : 64≤N) (hp : p.Prime) (hpA : p∈A)
    (hcN : log p≤(4/3 : ℝ)*N) (hXp : coreFloor N (log p) (203/100)<p)
    (hRM : R≤coreFloor N (log p) (39/20))
    (hcut : R^4≤(coreFloor N (log p) (39/20))^3) {L u : ℝ}
    (hL : 0<L) (hpL : log p≤L) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hend : L-log p≤log (R+1 : ℕ)) (y : ℝ) :
    |u^(N+1)*(row S A N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p L y+
      head S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p L y-
      main S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) R p L y)|≤
      (N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹ := by
  let M := coreFloor N (log p) (39/20)
  let X := coreFloor N (log p) (203/100)
  obtain ⟨hM,hMX,hlarge,_hwide,_hlo,_hhi⟩ := coreFloor_geometry hN hcN
  change 1≤M at hM
  change M≤X at hMX
  change exp ((N : ℝ)/2)≤M at hlarge
  have h0 : front M X 0=M := by simp [front,min_eq_right hMX]
  have hn : front M X N=X := min_eq_left (core_cover hN hcN)
  let B := (2*u*ZetaRieszLongCutoffError.countingConstant*
    ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
      exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹
  have hB : 0≤B := by
    dsimp [B]
    positivity [ZetaRieszLongCutoffError.countingConstant_pos,
      ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S]
  let F := fun a : ℕ =>
    (if Squarefree a ∧ ¬a.Prime ∧ ¬∃ q∈S,q∣a then
      (residualCoefficient (A∩{largestPrime (p*a)}) L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re else 0)+
      ((L-log p)/(L*p))*(if a.Prime then ownerTest N (log p) y a*sieve S a else 0)-
        (densityScalar S R (L-log p)/(L*p))*ownerTest N (log p) y a
  have hj m x : row S A N m x p L y+head S N m x p L y-main S N m x R p L y=
      ∑ a∈Finset.Ioc m x,F a := by
    simp only [row,head,main,Finset.sum_filter,F,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,← Finset.mul_sum]
  have hloc i (_hi : i∈Finset.range N) :
      |u^(N+1)*∑ a∈Finset.Ioc (front M X i) (front M X (i+1)),F a|≤B := by
    have hmi := front_bounds hMX i
    have hxi := front_bounds hMX (i+1)
    rcases eq_or_lt_of_le (front_monotone M X (Nat.le_succ i)) with he | hi
    · rw [he]
      simp only [Finset.Ioc_self,Finset.sum_empty,mul_zero,abs_zero]
      exact hB
    · rw [← hj]
      exact shell_joint_comparison S A hS (by omega : 32≤N) (by omega) hi
        (front_dyadic hi) (hRM.trans hmi.1) (hcut.trans (Nat.pow_le_pow_left hmi.1 3))
        (hlarge.trans (by exact_mod_cast hmi.1)) hp (hxi.2.trans_lt hXp) hpA
          hL hpL hu hU hend y
  have he := partition_sum F (front M X) (front_monotone M X) N
  rw [h0,hn] at he
  rw [hj,← he,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum hloc
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  exact hh.trans_eq (by dsimp [B]; ring)

private theorem profile_steps {R : ℕ} (f : ℕ→ℝ) :
    (∑ D∈Finset.Icc 1 R,(f D-f (D+1)))=f 1-f (R+1) := by
  have he : Finset.Icc 1 R=Finset.Ico 1 (R+1) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel,Nat.add_zero,Nat.zero_add,Nat.add_comm,
    Nat.add_left_comm,Nat.add_assoc] using Finset.sum_range_sub' (fun i => f (i+1)) R

/-- A scalar cap used only after the complete signed lattice sum has
its independent phase saving. -/
theorem densityScalar_bound (S : Finset ℕ) (hS : ∀ q∈S,q.Prime)
    {R : ℕ} {b : ℝ} (hb : 0≤b) (hend : b≤log (R+1 : ℕ)) :
    |densityScalar S R b|≤b*(1+log R) := by
  let f := fun D : ℕ => max 0 (b-log D)
  have hsum : (∑ D∈Finset.Icc 1 R,(f D-f (D+1)))=b := by
    rw [profile_steps f]
    simp only [f,Nat.cast_one,log_one,sub_zero,max_eq_right hb,
      max_eq_left (sub_nonpos.mpr hend)]
  unfold densityScalar
  calc
    _ ≤ ∑ D∈Finset.Icc 1 R,|(f D-f (D+1))*roughDensityPrefix S D| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ D∈Finset.Icc 1 R,(f D-f (D+1))*(1+log R) := by
      apply Finset.sum_le_sum
      intro D hD
      have hd := Finset.mem_Icc.mp hD
      have hlog := log_le_log (show (0 : ℝ)<D by exact_mod_cast hd.1)
        (show (D : ℝ)≤(D+1 : ℕ) by exact_mod_cast Nat.le_succ D)
      have hs : 0≤f D-f (D+1) :=
        sub_nonneg.mpr (max_le_max_left 0 (by linarith only [hlog]))
      rw [abs_mul,abs_of_nonneg hs]
      apply mul_le_mul_of_nonneg_left
        ((ZetaRieszLongCutoffError.roughDensityPrefix_bound S hS D).trans ?_) hs
      have hl := log_le_log (show (0 : ℝ)<D by exact_mod_cast hd.1)
        (show (D : ℝ)≤R by exact_mod_cast hd.2)
      linarith only [hl]
    _ = _ := by rw [← Finset.sum_mul,hsum]

/-- The full signed main, with the old owner allocation and every
cofactor count, has the already-certified geometric phase saving. -/
theorem normalized_main_core_bound (S : Finset ℕ) (hS : ∀ q∈S,q.Prime)
    {N R p : ℕ} (hN : 64≤N) (hR : 0<R) (hp : p.Prime)
    (hc : 1≤log p) (hcN : log p≤(4/3 : ℝ)*N) {L u y : ℝ}
    (hpL : log p≤L) (hend : L-log p≤log (R+1 : ℕ)) (hlogR : log R≤2*N)
    (hy : 54≤|y|) (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    |u^(N+1)*main S N (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100)) R p L y|≤
      ((1+2*(N : ℝ))/(p : ℝ))*ownerSamplingBudget u y N := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hL : 0<L := by linarith only [hc,hpL]
  have hR1 : (1 : ℝ)≤R := by exact_mod_cast hR
  have hs := densityScalar_bound S hS (sub_nonneg.mpr hpL) hend
  have hsb : |densityScalar S R (L-log p)|≤L*(1+2*(N : ℝ)) := by
    have hr0 := log_nonneg hR1
    have hbL : L-log p≤L := by linarith only [hc]
    have h := mul_le_mul hbL (add_le_add_left hlogR 1) (by linarith only [hr0]) hL.le
    exact hs.trans (by simpa only [add_comm] using h)
  have hd : |densityScalar S R (L-log p)|/(L*p)≤(1+2*(N : ℝ))/(p : ℝ) :=
    (div_le_div_of_nonneg_right hsb (mul_pos hL hp0).le).trans_eq (by field_simp)
  have hw : |u^(N+1)*(∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100)),ownerTest N (log p) y a)|≤
        ownerSamplingBudget u y N := by
    simpa only [ownerTest_nat] using normalized_core_lattice_sum_bound hN hc hcN hy hu hU
  unfold main
  have he : |u^(N+1)*((densityScalar S R (L-log p)/(L*p))*
      ∑ a∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)),
        ownerTest N (log p) y a)|=
      (|densityScalar S R (L-log p)|/(L*p))*|u^(N+1)*
        ∑ a∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)),
          ownerTest N (log p) y a| := by
    simp only [abs_mul,abs_div,abs_of_nonneg (mul_pos hL hp0).le]
    ring
  rw [he]
  exact mul_le_mul hd hw (abs_nonneg _) (by positivity)

/-- Explicit source-normalized price for the joint rough rows and their
ordinary-prime correction. Both terms have strict geometric saving. -/
def jointBudget (u y : ℝ) (N : ℕ) : ℝ :=
  8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)^3*
    exp (-(3/500 : ℝ)*N)+8*((N : ℝ)+1)^2*ownerSamplingBudget u y N

/-- Sum owners by their harmonic weight, after joining all counts and
radial shells. The exact signed prime head is part of the inequality. -/
theorem global_core_joint_bound (S A P : Finset ℕ) {N Q : ℕ} (R : ℕ→ℕ)
    (hN : 64≤N) (hS : ∀ q∈S,q.Prime) {L u y : ℝ}
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (hP : ∀ p∈P,p.Prime ∧ p∈A ∧ p≤Q ∧ 1≤log p ∧
      log p≤(4/3 : ℝ)*N ∧ log p≤L ∧ coreFloor N (log p) (203/100)<p)
    (hQ : log Q≤(203/100 : ℝ)*N)
    (hR : ∀ p∈P,0<R p ∧ R p≤coreFloor N (log p) (39/20) ∧
      (R p)^4≤(coreFloor N (log p) (39/20))^3 ∧
        L-log p≤log (R p+1 : ℕ) ∧ log (R p)≤2*N)
    (hrate : ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*
      exp (-(7/1000 : ℝ)*N)≤exp (-(3/500 : ℝ)*N)) :
    |u^(N+1)*∑ p∈P,(row S A N (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100)) p L y+
        head S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p L y)|≤
          jointBudget u y N := by
  let B := ownerSamplingBudget u y N
  have hB : 0≤B := by dsimp [B,ownerSamplingBudget]; positivity
  have hh : (∑ p∈P,(p : ℝ)⁻¹)≤1+(203/100 : ℝ)*N :=
    (marked_harmonic_bound P (fun p hp => ⟨(hP p hp).1,(hP p hp).2.2.1⟩)).trans
      (by linarith only [hQ])
  have he p (hp : p∈P) :
      |u^(N+1)*(row S A N (coreFloor N (log p) (39/20))
        (coreFloor N (log p) (203/100)) p L y+
          head S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p L y)|≤
      ((N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
        exp (-(3/500 : ℝ)*N))+(1+2*(N : ℝ))*B)*(p : ℝ)⁻¹ := by
    obtain ⟨hpp,hpa,_hpq,hc,hcN,hpL,hXp⟩ := hP p hp
    obtain ⟨hRp,hRM,hcut,hend,hlogR⟩ := hR p hp
    have hL : 0<L := by linarith only [hc,hpL]
    have hc0 := core_joint_comparison S A hS hN hpp hpa hcN hXp hRM hcut
      hL hpL hu hU hend y
    have hm := normalized_main_core_bound S hS hN hRp hpp hc hcN hpL hend hlogR hy hu hU
    change |u^(N+1)*main S N (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100)) (R p) p L y|≤((1+2*(N : ℝ))/(p : ℝ))*B at hm
    have hc1 : (N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹≤
        (N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
          exp (-(3/500 : ℝ)*N))*(p : ℝ)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hrate
        (show 0≤(N : ℝ)*2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
          ((N : ℝ)+1)*(p : ℝ)⁻¹ by
          positivity [ZetaRieszLongCutoffError.countingConstant_pos])
      convert h using 1 <;> first | rfl | ring_nf
    have h := (abs_add_le
      (u^(N+1)*(row S A N (coreFloor N (log p) (39/20))
        (coreFloor N (log p) (203/100)) p L y+
          head S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p L y-
            main S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) (R p) p L y))
      (u^(N+1)*main S N (coreFloor N (log p) (39/20))
        (coreFloor N (log p) (203/100)) (R p) p L y)).trans
          (add_le_add (hc0.trans hc1) hm)
    convert h using 1 <;> first | rfl | ring_nf
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p∈P,((N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
      ((N : ℝ)+1)*exp (-(3/500 : ℝ)*N))+(1+2*(N : ℝ))*B)*(p : ℝ)⁻¹ :=
        Finset.sum_le_sum he
    _ = ((N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
      ((N : ℝ)+1)*exp (-(3/500 : ℝ)*N))+(1+2*(N : ℝ))*B)*∑ p∈P,(p : ℝ)⁻¹ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((N : ℝ)*(2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
      ((N : ℝ)+1)*exp (-(3/500 : ℝ)*N))+(1+2*(N : ℝ))*B)*
        (1+(203/100 : ℝ)*N) := by
      apply mul_le_mul_of_nonneg_left hh
      positivity [ZetaRieszLongCutoffError.countingConstant_pos]
    _ ≤ jointBudget u y N := by
      have hn : 0≤(N : ℝ) := Nat.cast_nonneg N
      have hfac : 1+(203/100 : ℝ)*N≤(5/2 : ℝ)*((N : ℝ)+1) := by linarith
      have hp0 : (N : ℝ)*((N : ℝ)+1)*(1+(203/100 : ℝ)*N)≤4*((N : ℝ)+1)^3 := by
        calc
          _ ≤ ((N : ℝ)+1)*((N : ℝ)+1)*((5/2 : ℝ)*((N : ℝ)+1)) := by gcongr; linarith
          _ ≤ _ := by nlinarith only [pow_nonneg (show 0≤(N : ℝ)+1 by linarith) 3]
      have hp1 : (1+2*(N : ℝ))*(1+(203/100 : ℝ)*N)≤8*((N : ℝ)+1)^2 := by
        calc
          _ ≤ (2*((N : ℝ)+1))*((5/2 : ℝ)*((N : ℝ)+1)) := by gcongr; linarith
          _ ≤ _ := by nlinarith only [sq_nonneg ((N : ℝ)+1)]
      have he0 := mul_le_mul_of_nonneg_right hp0
        (show 0≤2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
          exp (-(3/500 : ℝ)*N) by positivity [ZetaRieszLongCutoffError.countingConstant_pos])
      have he1 := mul_le_mul_of_nonneg_right hp1 hB
      have h := add_le_add he0 he1
      change _≤8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)^3*
        exp (-(3/500 : ℝ)*N)+8*((N : ℝ)+1)^2*B
      convert h using 1 <;> first | rfl | ring_nf

/-- The joint price tends to zero independently of any zeta-zero
hypothesis. The fixed phase height changes constants only. -/
theorem jointBudget_tendsto (u y : ℝ) : Tendsto (jointBudget u y) atTop (𝓝 0) := by
  have h0 : 0<exp (-3/500 : ℝ) := exp_pos _
  have h1 : exp (-3/500 : ℝ)<1 := exp_lt_one_iff.mpr (by norm_num)
  have h := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3 h0 h1).const_mul
    (8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|))).add
      ((ownerSamplingBudget_polynomial_tendsto 2 u y).const_mul 8)
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← exp_nat_mul]
  dsimp [jointBudget]
  ring

open ZetaRieszTaggedCoreWindow (full_core_owner_geometry)
open ZetaRieszSmallTagNativeFloor (smallPrimes owners comparisonCutoff owners_data
  eventually_native_comparison length_upper nonownerBudget nonownerBudget_tendsto realParameters)

/-- The signed prime-pair head on the actual physical owner set. It is
retained, not claimed negligible or replaced by a completed product. -/
def nativeHead (u y : ℝ) (N : ℕ) : ℝ :=
  u^(N+1)*∑ p∈owners u N,head (smallPrimes N) N
    (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p
      (SquarefreeVaughanLogSource.length u N) y

/-- All rough composite owner incidences over the literal full radial
window, before the original native count crop is imposed. -/
def completeRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  ((owners u N).sigma (fun p =>
    (Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100))).filter
      (fun a => Squarefree a ∧ ¬a.Prime ∧ ¬∃ q∈smallPrimes N,q∣a))).image
        (fun pa => (pa.1,pa.2))

theorem completeRows_data {u : ℝ} {N : ℕ} {pa : ℕ×ℕ} (h : pa∈completeRows u N) :
    pa.1∈owners u N ∧ pa.2∈Finset.Ioc (coreFloor N (log pa.1) (39/20))
      (coreFloor N (log pa.1) (203/100)) ∧ Squarefree pa.2 ∧ ¬pa.2.Prime ∧
        ¬∃ q∈smallPrimes N,q∣pa.2 := by
  obtain ⟨⟨p,a⟩,ha,he⟩ := Finset.mem_image.mp h
  obtain ⟨hp,ha⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hi,hs⟩ := Finset.mem_filter.mp ha
  cases he
  exact ⟨hp,hi,hs⟩

theorem completeRows_sum (u y L : ℝ) (N : ℕ) (A : Finset ℕ) :
    (∑ pa∈completeRows u N,(residualCoefficient (A∩{largestPrime (pa.1*pa.2)})
      L N (pa.1*pa.2)*zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2)).re)=
        ∑ p∈owners u N,row (smallPrimes N) A N
          (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) p L y := by
  rw [completeRows,Finset.sum_image (by
    intro pa _ pb _ he
    exact Sigma.ext (congrArg Prod.fst he) (by
      cases pa; cases pb; simpa using congrArg Prod.snd he)),Finset.sum_sigma]
  rfl

/-- All geometric and counting premises are now discharged at the
actual moving length and physical endpoint. No arithmetic estimate is
assumed; the exact ordinary-prime correction is still joined. -/
theorem eventually_complete_joint_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ N : ℕ in atTop,
      |u^(N+1)*∑ pa∈completeRows u N,
        (residualCoefficient
          (ZetaRieszAnnulusJoint.intermediatePrimes u N∩{largestPrime (pa.1*pa.2)})
          (SquarefreeVaughanLogSource.length u N) N (pa.1*pa.2)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2)).re+nativeHead u y N|≤
              jointBudget u y N := by
  filter_upwards [eventually_cubic_counting_rate,eventually_native_comparison hu hU,
    eventually_ge_atTop (64 : ℕ)] with N hrate hg hN
  let L := SquarefreeVaughanLogSource.length u N
  let Q := (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hQ : log Q≤(203/100 : ℝ)*N := by
    have he : log Q=L := by
      simp only [Q,L,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    rw [he]
    have hl := length_upper hu.le (show 2≤N by omega)
    linarith only [hl,hn]
  have hS : ∀ q∈smallPrimes N,q.Prime ∧ q≤N^3 := by
    intro q hq
    have h := Nat.mem_primesLE.mp hq
    exact ⟨h.2,h.1⟩
  have h := global_core_joint_bound (smallPrimes N)
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) (owners u N)
    (fun _ => comparisonCutoff N) hN (fun q hq => (hS q hq).1)
    (by linarith) hU hy
    (fun p hp => by
      obtain ⟨hpp,hA,hpQ,hp1,hpc,hpL,_hM,hX,_⟩ := hg p hp
      exact ⟨hpp,hA,hpQ,hp1,hpc,hpL,hX⟩) hQ
    (fun p hp => by
      obtain ⟨_,_,_,_,_,_,_,_,hR,hRM,hcut,hend⟩ := hg p hp
      have hr : (comparisonCutoff N : ℝ)≤exp ((N : ℝ)/2) := Nat.floor_le (exp_pos _).le
      have hl := log_le_log (show (0 : ℝ)<comparisonCutoff N by exact_mod_cast hR) hr
      rw [log_exp] at hl
      exact ⟨hR,hRM,hcut,hend,by linarith only [hl,hn]⟩)
    (hrate (smallPrimes N) hS)
  rw [Finset.sum_add_distrib,← completeRows_sum,mul_add] at h
  exact h

/-- The retained head is literally one weighted prime-pair sum. Every
prime cofactor in this window already lies above the sieve threshold. -/
theorem eventually_nativeHead_eq_prime_pairs {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      nativeHead u y N=u^(N+1)*∑ p∈owners u N,
        ((SquarefreeVaughanLogSource.length u N-log p)/
          (SquarefreeVaughanLogSource.length u N*p))*
            ∑ q∈(Finset.Ioc (coreFloor N (log p) (39/20))
              (coreFloor N (log p) (203/100))).filter Nat.Prime,
                ownerAmplitude N (log p) q*cos (y*(log p+log q))/(q : ℝ) := by
  filter_upwards [eventually_native_comparison hu hU] with N hg
  unfold nativeHead
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  unfold head
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqp : q.Prime
  · have hM := (hg p hp).2.2.2.2.2.2.1
    have hqN : N^3<q := hM.trans_lt (Finset.mem_Ioc.mp hq).1
    have hrest : ¬∃ r∈smallPrimes N,r∣q := by
      rintro ⟨r,hr,hrq⟩
      have hrp := Nat.mem_primesLE.mp hr
      have he := (Nat.prime_dvd_prime_iff_eq hrp.2 hqp).mp hrq
      omega
    rw [if_pos hqp,sieve,if_pos ⟨hqp.squarefree,hrest⟩,mul_one,if_pos hqp,ownerTest_nat]
  · simp only [if_neg hqp]

/-- The exact original native count crop, on the same complete rows. -/
def rows (u : ℝ) (j : ℕ) : Finset (ℕ×ℕ) :=
  (completeRows u (dyadicMomentOrder j)).filter (fun pa =>
    (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j)

/-- Unique physical product labels on which the joint signed bound
will be spent inside the original cutoff ledger. -/
def labels (u : ℝ) (j : ℕ) : Finset ℕ := (rows u j).image (fun pa => pa.1*pa.2)

theorem rows_data {u : ℝ} {j : ℕ} (hN : 64≤dyadicMomentOrder j)
    {pa : ℕ×ℕ} (hpa : pa∈rows u j) :
    pa.1.Prime ∧ Squarefree pa.2 ∧ 1<pa.2 ∧ ¬pa.2.Prime ∧ pa.2<pa.1 ∧
      pa.1∈owners u (dyadicMomentOrder j) ∧
      pa.2∈Finset.Ioc (coreFloor (dyadicMomentOrder j) (log pa.1) (39/20))
        (coreFloor (dyadicMomentOrder j) (log pa.1) (203/100)) ∧
      (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j := by
  obtain ⟨hs,hcount⟩ := Finset.mem_filter.mp hpa
  have h := completeRows_data hs
  obtain ⟨hp,_hA,hlo,hhi⟩ := owners_data h.1
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
  owned_rows_injective _ (fun pa hpa => by
    have h := rows_data hN hpa
    exact ⟨h.1,h.2.1,h.2.2.2.2.1⟩)

/-- One complete-window joint comparison and exactly one already
proved native count-crop error. -/
def croppedBudget (u y : ℝ) (j : ℕ) : ℝ :=
  jointBudget u y (dyadicMomentOrder j)+ZetaRieszNearCriticalCountPayment.allowance j

theorem croppedBudget_tendsto (u y : ℝ) : Tendsto (croppedBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => jointBudget u y (dyadicMomentOrder j)+
    ZetaRieszNearCriticalCountPayment.allowance j) atTop (𝓝 0)
  have h := ((jointBudget_tendsto u y).comp tendsto_dyadicMomentOrder).add
    ZetaRieszNearCriticalCountPayment.tendsto_allowance
  simpa only [Function.comp_apply,zero_add] using h

/-- Independent signed cancellation on the actual native count crop.
The prime correction keeps its original smooth owner allocation. -/
theorem eventually_cropped_joint_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*∑ pa∈rows u j,
        (residualCoefficient
          (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)∩
            {largestPrime (pa.1*pa.2)})
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
          (dyadicMomentOrder j) (pa.1*pa.2)*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) (pa.1*pa.2)).re+
              nativeHead u y (dyadicMomentOrder j)|≤croppedBudget u y j := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_complete_joint_bound hu hU hy),
    eventually_owned_count_boundary,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ)),
    tendsto_dyadicMomentOrder.eventually (ZetaRieszMaskSupport.eventually_length_lower
      (by linarith : 0<u) (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le))]
    with j hj hcount hN hL
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let E := completeRows u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let f := fun pa : ℕ×ℕ => (residualCoefficient (A∩{largestPrime (pa.1*pa.2)})
    L N (pa.1*pa.2)*zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2)).re
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hpos : 0<L := by dsimp only [L]; linarith only [hL,hn]
  have hgeom pa (hpa : pa∈E) : pa.1.Prime ∧ Squarefree pa.2 ∧ pa.2<pa.1 := by
    have h := completeRows_data hpa
    obtain ⟨hpp,_hA,hlo,hhi⟩ := owners_data h.1
    exact ⟨hpp,h.2.2.1,(Finset.mem_Ioc.mp h.2.1).2.trans_lt
      (full_core_owner_geometry hN hpp hlo hhi).1⟩
  have hlog pa (hpa : pa∈E) : log (pa.1*pa.2 : ℕ)≤(203/100 : ℝ)*N := by
    have h := completeRows_data hpa
    have hg := hgeom pa hpa
    have hb := (coreFloor_membership N (log pa.1) (Nat.pos_of_ne_zero hg.2.1.ne_zero)).mp h.2.1
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hg.1.ne_zero)
      (by exact_mod_cast hg.2.1.ne_zero)]
    exact hb.2
  have h := hcount E A L u y hpos (by linarith) hU hgeom hlog
  have hhigh : |u^(N+1)*∑ pa∈E.filter
      (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤(pa.1*pa.2).primeFactors.card),
        f pa|≤ZetaRieszNearCriticalCountPayment.allowance j := by
    have hh := (Complex.abs_re_le_norm _).trans h
    simpa only [f,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_sum,zero_mul,sub_zero] using hh
  have hsplit := congrArg (fun z : ℝ => u^(N+1)*z)
    (Finset.sum_filter_add_sum_filter_not E
      (fun pa => (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j) f)
  simp only [not_lt,mul_add] at hsplit
  change |u^(N+1)*∑ pa∈E,f pa+nativeHead u y N|≤jointBudget u y N at hj
  change |u^(N+1)*∑ pa∈E.filter
    (fun pa => (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j),
      f pa+nativeHead u y N|≤jointBudget u y N+ZetaRieszNearCriticalCountPayment.allowance j
  apply abs_le.mpr
  constructor <;> linarith only [hsplit,(abs_le.mp hj).1,(abs_le.mp hj).2,
    (abs_le.mp hhigh).1,(abs_le.mp hhigh).2]

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


/-- The original FULL allocation on the literal rough native labels. -/
def packet (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈labels u j,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

/-- Only the canonical owner's old allocation, on exactly the same labels. -/
def ownerPacket (u y : ℝ) (j : ℕ) : ℝ :=
  u^(dyadicMomentOrder j+1)*∑ n∈labels u j,
    (residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

theorem eventually_ownerPacket_joint_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop, |ownerPacket u y j+nativeHead u y (dyadicMomentOrder j)|≤croppedBudget u y j := by
  filter_upwards [eventually_cropped_joint_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ))] with j hj hN
  have hi := Finset.sum_image (rows_injective (u:=u) hN)
    (f:=fun n => (residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)∩{largestPrime n})
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re)
  unfold ownerPacket labels
  rw [hi]
  exact hj

/-- One joint signed row/count price and one restricted existing
nonowner payment. The prime head remains inside the signed target. -/
def budget (u y : ℝ) (j : ℕ) : ℝ :=
  croppedBudget u y j+nonownerBudget (dyadicMomentOrder j)

theorem budget_tendsto (u y : ℝ) : Tendsto (budget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => croppedBudget u y j+nonownerBudget (dyadicMomentOrder j))
    atTop (𝓝 0)
  have h := (croppedBudget_tendsto u y).add
    (nonownerBudget_tendsto.comp tendsto_dyadicMomentOrder)
  simpa only [Function.comp_apply,zero_add] using h

/-- An independent signed estimate for the actual rough carrier PLUS
its exact prime-cofactor head, retaining the full original allocation.
Neither summand is asserted small separately. -/
theorem eventually_packet_joint_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop, |packet u y j+nativeHead u y (dyadicMomentOrder j)|≤budget u y j := by
  filter_upwards [eventually_ownerPacket_joint_bound hu hU hy,
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
  have ht := abs_add_le (packet u y j-ownerPacket u y j)
    (ownerPacket u y j+nativeHead u y N)
  have heq : (packet u y j-ownerPacket u y j)+(ownerPacket u y j+nativeHead u y N)=
      packet u y j+nativeHead u y N := by ring
  rw [heq] at ht
  unfold budget
  linarith only [ht,hdiff,howner]

/-- The retained signed rough response is source-equivalent to MINUS
one explicit prime-pair head. No source identity or zero hypothesis was
used to obtain this arithmetic estimate. -/
theorem tendsto_packet_add_nativeHead {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => packet u y j+nativeHead u y (dyadicMomentOrder j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (budget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_packet_joint_bound hu hU hy

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


/-- The two physical populations are disjoint. A label with a selected
least small prime cannot simultaneously have a completely rough cofactor. -/
theorem labels_disjoint_smallTags {u : ℝ} {j : ℕ} (hN : 64≤dyadicMomentOrder j) :
    Disjoint (labels u j) (ZetaRieszSmallTagNativeFloor.labels u j) := by
  apply Finset.disjoint_left.mpr
  intro n hn ht
  obtain ⟨pa,hpa,hepa⟩ := Finset.mem_image.mp hn
  obtain ⟨pb,hpb,hepb⟩ := Finset.mem_image.mp ht
  have hprod : pa.1*pa.2=pb.1*pb.2 := hepa.trans hepb.symm
  let E := rows u j∪ZetaRieszSmallTagNativeFloor.rows u j
  have hg z (hz : z∈E) : z.1.Prime ∧ Squarefree z.2 ∧ z.2<z.1 := by
    rcases Finset.mem_union.mp hz with h | h
    · have hd := rows_data hN h
      exact ⟨hd.1,hd.2.1,hd.2.2.2.2.1⟩
    · have hd := ZetaRieszSmallTagNativeFloor.rows_data hN h
      exact ⟨hd.1,hd.2.1,hd.2.2.2.2.1⟩
  have he : pa=pb := owned_rows_injective E hg
    (Finset.mem_union_left _ hpa) (Finset.mem_union_right _ hpb) hprod
  have hr := completeRows_data (Finset.mem_filter.mp hpa).1
  have hs := ZetaRieszTaggedCoreWindow.selectedRows_data _ _ _ _ (Finset.mem_filter.mp hpb).1
  obtain ⟨r,hrt,_hrest,hra⟩ := hs.2.2.2.2
  have hrS : r∈smallPrimes (dyadicMomentOrder j) := (Finset.mem_filter.mp hrt).1
  rw [he] at hr
  exact hr.2.2.2.2 ⟨r,hrS,hra⟩

private theorem increment_sdiff (X N : ℕ) (S D : Finset ℕ) (hD : D⊆S)
    (W : ℕ→ℂ) (L : ℝ) (p : Fin 5→ℝ) (k : ℕ) :
    ZetaRieszComplexNullFloor.increment X N S W L p k-
      ZetaRieszComplexNullFloor.increment X N D W L p k=
        ZetaRieszComplexNullFloor.increment X N (S\D) W L p k := by
  have he w : ZetaRieszCofactorPhaseEnergy.correlation (S\D) w k=
      ZetaRieszCofactorPhaseEnergy.correlation S w k-
        ZetaRieszCofactorPhaseEnergy.correlation D w k := Finset.sum_sdiff_eq_sub hD
  simp only [ZetaRieszComplexNullFloor.increment,he]
  ring

/-- The remaining null-corrected main is EXACTLY on the original
native squarefree labels minus both disjoint paid populations. Whole
tangent corrections stay joined; no cutoff variation is double funded. -/
theorem eventually_step_sub_paid {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,∀ (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) (k : ℕ),
      let N := dyadicMomentOrder j;
      let L := SquarefreeVaughanLogSource.length u N;
      let X := ZetaRieszPaidIncidenceFloor.nativeEndpoint u j;
      let S := (ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree;
      let W := ZetaRieszComplexProjection.sourceWeight
        (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N;
      ZetaRieszSmallTagNativeFloor.step u y j p q a k-
        ZetaRieszSmallTagNativeFloor.paidIncrement u y j p k-paidIncrement u y j p k=
          ZetaRieszComplexNullFloor.increment X N
            ((S\ZetaRieszSmallTagNativeFloor.labels u j)\labels u j) W L (realParameters p) k+
              ZetaRieszTangentCubicCredit.extendedIncrement X N S W L q a k := by
  filter_upwards [eventually_labels_subset_native hu hU,
    ZetaRieszSmallTagNativeFloor.eventually_step_sub_paid hu hU y,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ))]
    with j hj hs hN p q a k
  have hd := labels_disjoint_smallTags (u:=u) hN
  have hr : labels u j⊆
      ((ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree)\
        ZetaRieszSmallTagNativeFloor.labels u j := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hj.1 hn,hj.2 n hn⟩,
      fun ht => Finset.disjoint_left.mp hd hn ht⟩
  rw [hs p q a k]
  unfold paidIncrement
  dsimp only
  rw [add_sub_right_comm,increment_sdiff _ _ _ _ hr]

/-- All unpaid counts and cutoffs remain joined. Both proven signed
payments are removed before clipping any complete prime period. -/
def restCost (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  ZetaRieszCutoffPeriodFloor.blockCost
    (Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j))
    (ZetaRieszCutoffPeriodFloor.cutoffPeriod y) (fun k =>
      ZetaRieszSmallTagNativeFloor.step u y j p q a k-
        ZetaRieszSmallTagNativeFloor.paidIncrement u y j p k-paidIncrement u y j p k)

/-- Source-small errors only. The exact signed prime-pair head is
kept separate and is never hidden in this budget. -/
def combinedBudget (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszSmallTagNativeFloor.budget u y j+budget u y j

theorem combinedBudget_tendsto (u y : ℝ) : Tendsto (combinedBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => ZetaRieszSmallTagNativeFloor.budget u y j+budget u y j)
    atTop (𝓝 0)
  simpa only [zero_add] using (ZetaRieszSmallTagNativeFloor.budget_tendsto u y).add
    (budget_tendsto u y)

/-- The global floor ACTUALLY spends the new joint cancellation.
The remaining price is one joined cutoff cost PLUS the signed prime
head. This is an inequality for the original joinedPhysical; a numerical
bound on that signed price is still open. -/
theorem eventually_joined_floor_pruned {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -restCost u y j (p j) (q j) (a j)-nativeHead u y (dyadicMomentOrder j)-
        combinedBudget u y j-ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_packet_joint_bound hu hU hy,eventually_sum_paidIncrement hu hU y,
    ZetaRieszSmallTagNativeFloor.eventually_packet_bound hu hU hy,
    ZetaRieszSmallTagNativeFloor.eventually_sum_paidIncrement hu hU y]
    with j hrough he hsmall hes
  have hf := ZetaRieszCutoffPeriodFloor.block_floor
    (Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j))
    (ZetaRieszCutoffPeriodFloor.cutoffPeriod y) (fun k =>
      ZetaRieszSmallTagNativeFloor.step u y j (p j) (q j) (a j) k-
        ZetaRieszSmallTagNativeFloor.paidIncrement u y j (p j) k-
          paidIncrement u y j (p j) k)
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,ZetaRieszSmallTagNativeFloor.sum_step,
    he (p j),hes (p j)] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  change -restCost u y j (p j) (q j) (a j)≤
    Q.re-ZetaRieszSmallTagNativeFloor.packet u y j-packet u y j at hf
  change -restCost u y j (p j) (q j) (a j)-nativeHead u y (dyadicMomentOrder j)-
    (ZetaRieszSmallTagNativeFloor.budget u y j+budget u y j)-
      (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hr,(abs_le.mp hrough).1,(abs_le.mp hsmall).1,
    abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Alternative whole-floor prices, never stacked credits. Retain the
previous floor whenever the new signed prime-head price is larger. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszSmallTagNativeFloor.price u y j p q a)
    (restCost u y j p q a+nativeHead u y (dyadicMomentOrder j)+combinedBudget u y j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszSmallTagNativeFloor.price u y j p q a := min_le_left _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_pruned hu hU hy p q a,
    ZetaRieszSmallTagNativeFloor.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszSmallTagNativeFloor.price u y j (p j) (q j) (a j))
    (restCost u y j (p j) (q j) (a j)+nativeHead u y (dyadicMomentOrder j)+combinedBudget u y j)
    with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- This reduction is concrete, but the cofinal numerical price premise
is OPEN. Joint cancellation does not itself prove a zero exclusion. -/
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

end RiemannGaussian.ZetaRieszRoughPrimePairCancellation
