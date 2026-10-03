/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTaggedOwnerPhase

/-!
# Signed estimate on complete literal tagged-owner core rows

Complete core windows are partitioned into finite capped dyadic intervals.
The already-proved centered errors are summed. The SAME density scalar and
signed phase main recombine exactly across those intervals, and ONLY THEN
the independent whole-window phase estimate is used.

No arithmetic cofactor series is completed, no count is deleted, and no
additional internal mask is assumed negligible.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszTaggedCoreWindow
open ZetaRieszTaggedOwnerComparison ZetaRieszTaggedOwnerPhase
open ZetaRieszOwnerLatticePhase ZetaRieszSmoothOwnerDiscrepancy

private theorem partition_sum (f : ℕ→ℝ) (a : ℕ→ℕ) (ha : Monotone a) (b : ℕ) :
    (∑ i∈Finset.range b, ∑ n∈Finset.Ioc (a i) (a (i+1)), f n)=
      ∑ n∈Finset.Ioc (a 0) (a b), f n := by
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
  have hpow : 2^i*M<X := by
    by_contra h
    have he : front M X i=X := min_eq_left (by omega)
    have hb : front M X (i+1)≤X := min_le_left _ _
    omega
  have he : front M X i=2^i*M := min_eq_right hpow.le
  rw [he]
  have hb : front M X (i+1)≤2^(i+1)*M := min_le_right _ _
  rw [pow_succ] at hb
  nlinarith only [hb]

private theorem core_cover {N : ℕ} (hN : 64≤N) {c : ℝ} (hc : c≤(4/3 : ℝ)*N) :
    coreFloor N c (203/100)≤2^N*coreFloor N c (39/20) := by
  obtain ⟨_hM,_hMX,_hlarge,hwide,_hlo,_hhi⟩ := coreFloor_geometry hN hc
  have hlog : (1/10 : ℝ)≤log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    linarith only [h]
  have he : exp (1/10 : ℝ)≤2 := by
    simpa only [exp_log (by norm_num : (0 : ℝ)<2)] using exp_le_exp.mpr hlog
  have hn := pow_le_pow_left₀ (exp_pos (1/10 : ℝ)).le he N
  rw [← exp_nat_mul] at hn
  have heq : (N : ℝ)/10=(N : ℝ)*(1/10) := by ring
  rw [← heq] at hn
  have h := hwide.trans (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))
  exact_mod_cast (show (coreFloor N c (203/100) : ℝ)≤
    (2 : ℝ)^N*coreFloor N c (39/20) by simpa only [mul_comm] using h)

/-- The literal owner rows join with their squarefree, tag, rough and
composite masks intact. The main scalar is identical on every interval. -/
theorem core_comparison_bound (S A : Finset ℕ) (hS : ∀ q∈S, q.Prime)
    {N R r p : ℕ} (hN : 64≤N) (hp : p.Prime) (hr : r.Prime) (hpA : p∈A)
    (_hc : 1≤log p) (hcN : log p≤(4/3 : ℝ)*N)
    (hrM : r≤coreFloor N (log p) (39/20))
    (hXp : coreFloor N (log p) (203/100)<p)
    (hRM : R≤coreFloor N (log p) (39/20))
    (hcut : R^4≤(coreFloor N (log p) (39/20))^3)
    {L u : ℝ} (hL : 0<L) (hpL : log p≤L) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hend : L-log p≤log (R+1 : ℕ)) (y : ℝ) :
    |u^(N+1)*(taggedOwnerRow S A N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y-
      taggedOwnerMain S N (coreFloor N (log p) (39/20))
        (coreFloor N (log p) (203/100)) R r p L y)|≤
      (N : ℝ)*(8*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹ := by
  let M := coreFloor N (log p) (39/20)
  let X := coreFloor N (log p) (203/100)
  obtain ⟨hM,hMX,hlarge,_hwide,_hlo,_hhi⟩ := coreFloor_geometry hN hcN
  change 1≤M at hM
  change M≤X at hMX
  change exp ((N : ℝ)/2)≤M at hlarge
  have h0 : front M X 0=M := by simp [front,min_eq_right hMX]
  have hendFront : front M X N=X := min_eq_left (core_cover hN hcN)
  let B := (8*u*ZetaRieszLongCutoffError.countingConstant*
    ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
      exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹
  have hB : 0≤B := by
    dsimp [B]
    positivity [ZetaRieszLongCutoffError.countingConstant_pos,
      ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S]
  let F := fun a : ℕ => if Squarefree a ∧ ¬a.Prime ∧ (¬∃ q∈S, q∣a) ∧ r∣a then
    (ZetaRieszJointAllocation.residualCoefficient
      (A∩{ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re else 0
  let G := fun a : ℕ =>
    (taggedRieszScalar S r R (L-log p)/(L*p))*
      (ownerAmplitude N (log p) a*cos (y*(log p+log a))/(a : ℝ))
  have hrow m x : taggedOwnerRow S A N m x r p L y=∑ a∈Finset.Ioc m x, F a := by
    simp only [taggedOwnerRow,Finset.sum_filter,F]
  have hmain m x : taggedOwnerMain S N m x R r p L y=∑ a∈Finset.Ioc m x, G a := by
    rw [taggedOwnerMain_eq_sum]
    dsimp [G]
    rw [← Finset.mul_sum]
    ring
  have hlocal i (_hi : i∈Finset.range N) :
      |u^(N+1)*(taggedOwnerRow S A N (front M X i) (front M X (i+1)) r p L y-
        taggedOwnerMain S N (front M X i) (front M X (i+1)) R r p L y)|≤B := by
    have hmi := front_bounds hMX i
    have hxi := front_bounds hMX (i+1)
    have hic := front_monotone M X (Nat.le_succ i)
    rcases eq_or_lt_of_le hic with he | hi
    · rw [he,hrow,hmain]
      simp only [Finset.Ioc_self,Finset.sum_empty,sub_self,mul_zero,abs_zero]
      exact hB
    · have h := literal_tagged_owner_error S A hS hr (hrM.trans hmi.1)
        (by omega : 32≤N) (by omega : 0<front M X i) hi (front_dyadic hi)
        (hRM.trans hmi.1) (hcut.trans (Nat.pow_le_pow_left hmi.1 3))
        (hlarge.trans (by exact_mod_cast hmi.1)) hp (hxi.2.trans_lt hXp) hpA
        hL hpL hu hU hend y
      exact h
  have hjoinF := partition_sum F (front M X) (front_monotone M X) N
  have hjoinG := partition_sum G (front M X) (front_monotone M X) N
  rw [h0,hendFront] at hjoinF hjoinG
  change |u^(N+1)*(taggedOwnerRow S A N M X r p L y-taggedOwnerMain S N M X R r p L y)|≤_
  rw [hrow,hmain,← hjoinF,← hjoinG,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
  simp_rw [hrow,hmain] at h
  calc
    _ ≤ _ := h
    _ = _ := by dsimp [B]; ring

/-- A genuine independent signed bound for the LITERAL complete tagged
owner row. This is not merely a norm estimate for its smooth surrogate. -/
theorem literal_tagged_core_bound (S A : Finset ℕ) (hS : ∀ q∈S, q.Prime)
    {N R r p : ℕ} (hN : 64≤N) (hp : p.Prime) (hr : r.Prime) (hR : 0<R) (hpA : p∈A)
    (hc : 1≤log p) (hcN : log p≤(4/3 : ℝ)*N)
    (hrM : r≤coreFloor N (log p) (39/20))
    (hXp : coreFloor N (log p) (203/100)<p)
    (hRM : R≤coreFloor N (log p) (39/20))
    (hcut : R^4≤(coreFloor N (log p) (39/20))^3)
    {L u y : ℝ} (hL : 0<L) (hpL : log p≤L) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (hend : L-log p≤log (R+1 : ℕ)) :
    |u^(N+1)*taggedOwnerRow S A N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y|≤
      (N : ℝ)*(8*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹+
        (2*(1+2*(N : ℝ))/(p : ℝ))*ownerSamplingBudget u y N := by
  have hlogR : log R≤2*(N : ℝ) := by
    have hr0 : (0 : ℝ)<R := by exact_mod_cast hR
    have hfloor : (coreFloor N (log p) (39/20) : ℝ)≤exp ((39/20 : ℝ)*N-log p) :=
      Nat.floor_le (exp_pos _).le
    have h := log_le_log hr0 ((show (R : ℝ)≤coreFloor N (log p) (39/20) by
      exact_mod_cast hRM).trans hfloor)
    rw [log_exp] at h
    nlinarith only [h,hc,Nat.cast_nonneg (α := ℝ) N]
  have he := core_comparison_bound S A hS hN hp hr hpA hc hcN hrM hXp hRM hcut
    hL hpL hu hU hend y
  have hm := normalized_tagged_main_core_bound S hS hN hr hR hp hc hcN hpL hend hlogR hy hu hU
  have h := (abs_add_le
    (u^(N+1)*(taggedOwnerRow S A N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y-
        taggedOwnerMain S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) R r p L y))
    (u^(N+1)*taggedOwnerMain S N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) R r p L y)).trans
      (add_le_add he hm)
  have heq : u^(N+1)*(taggedOwnerRow S A N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y-
        taggedOwnerMain S N (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) R r p L y)+
      u^(N+1)*taggedOwnerMain S N
        (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) R r p L y=
      u^(N+1)*taggedOwnerRow S A N
        (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y := by ring
  rw [heq] at h
  exact h

/-- Joint price for the SAME complete literal owner rows. All terms have
strict geometric decay after a fixed polynomial aggregation cost. -/
def taggedCoreBudget (u y : ℝ) (N : ℕ) : ℝ :=
  20*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)^6*
    exp (-(3/500 : ℝ)*N)+10*((N : ℝ)+1)^5*ownerSamplingBudget u y N

/-- An independent joined signed estimate on all retained tagged owners
and ALL cofactor counts in the complete core window. Arithmetic holes remain
in the measure, not in a jagged zero-extension of the phase weight.

The original native count crop is a separate, previously proved boundary
payment on these incidences. Arbitrary internal/share masks are not removed. -/
theorem eventually_global_literal_tagged_core_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (T V A P : Finset ℕ) (S : ℕ→Finset ℕ)
      (R : ℕ→ℕ) (Q : ℕ) (L u y : ℝ),
      0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling → 54≤|y| →
      (∀ r∈T, r.Prime ∧ r≤N^3) → V⊆T → (∀ r∈V, S r⊆T) →
      (∀ p∈P, p.Prime ∧ p∈A ∧ p≤Q ∧ 1≤log p ∧ log p≤(4/3 : ℝ)*N ∧ log p≤L) →
      log Q≤(203/100 : ℝ)*N →
      (∀ p∈P, N^3≤coreFloor N (log p) (39/20) ∧ coreFloor N (log p) (203/100)<p) →
      (∀ p∈P, 0<R p ∧ R p≤coreFloor N (log p) (39/20) ∧
        (R p)^4≤(coreFloor N (log p) (39/20))^3 ∧ L-log p≤log (R p+1 : ℕ)) →
      |u^(N+1)*∑ p∈P, ∑ r∈V, taggedOwnerRow (S r) A N
        (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y|≤
        taggedCoreBudget u y N := by
  filter_upwards [ZetaRieszRoughOwnerComparison.eventually_cubic_counting_rate,
    eventually_ge_atTop (64 : ℕ)] with N hrate hN
  intro T V A P S R Q L u y hL hu hU hy hT hV hS hP hQ hshell hcut
  let D := ∑ p∈P, ∑ r∈V, taggedOwnerMain (S r) N
    (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) (R p) r p L y
  let J := ∑ p∈P, ∑ r∈V, taggedOwnerRow (S r) A N
    (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y
  let B := 8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
    (N : ℝ)*((N : ℝ)+1)*exp (-(3/500 : ℝ)*N)
  have hB : 0≤B := by dsimp [B]; positivity [ZetaRieszLongCutoffError.countingConstant_pos]
  have hcard : (V.card : ℝ)≤(N : ℝ)^3 := by
    have hs : V⊆Finset.Icc 1 (N^3) := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨(hT r (hV hr)).1.pos,(hT r (hV hr)).2⟩
    have h := Finset.card_le_card hs
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hh : (∑ p∈P, (p : ℝ)⁻¹)≤1+(203/100 : ℝ)*N :=
    (marked_harmonic_bound P (fun p hp => ⟨(hP p hp).1,(hP p hp).2.2.1⟩)).trans
      (by linarith only [hQ])
  have he p (hp : p∈P) r (hr : r∈V) :
      |u^(N+1)*(taggedOwnerRow (S r) A N
        (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y-
        taggedOwnerMain (S r) N (coreFloor N (log p) (39/20))
          (coreFloor N (log p) (203/100)) (R p) r p L y)|≤B*(p : ℝ)⁻¹ := by
    have ht r' (hr' : r'∈S r) : r'.Prime := (hT r' (hS r hr hr')).1
    have h := core_comparison_bound (S r) A ht hN (hP p hp).1 (hT r (hV hr)).1
      (hP p hp).2.1 (hP p hp).2.2.2.1 (hP p hp).2.2.2.2.1
      ((hT r (hV hr)).2.trans (hshell p hp).1) (hshell p hp).2
      (hcut p hp).2.1 (hcut p hp).2.2.1 hL (hP p hp).2.2.2.2.2 hu hU
      (hcut p hp).2.2.2 y
    have hrateS := hrate (S r) (fun q hq => hT q (hS r hr hq))
    have hc := mul_le_mul_of_nonneg_left hrateS
      (show 0≤(N : ℝ)*(8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*
        ((N : ℝ)+1))*(p : ℝ)⁻¹ by
        positivity [ZetaRieszLongCutoffError.countingConstant_pos])
    apply h.trans
    convert hc using 1 <;> ring
  have herr : |u^(N+1)*(J-D)|≤B*(N : ℝ)^3*(1+(203/100 : ℝ)*N) := by
    dsimp [J,D]
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p∈P, ∑ r∈V, B*(p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [← Finset.sum_sub_distrib,Finset.mul_sum]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (he p hp))
      _ = B*(V.card : ℝ)*(∑ p∈P, (p : ℝ)⁻¹) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ _ := by gcongr
  have hmain : |u^(N+1)*D|≤10*((N : ℝ)+1)^5*ownerSamplingBudget u y N := by
    apply global_core_tagged_main_bound hN T V P S hT hV hS R hu hU hy
      (fun p hp => ⟨(hP p hp).1,(hP p hp).2.2.1,(hP p hp).2.2.2⟩) hQ
    intro p hp
    have hr0 : (0 : ℝ)<R p := by exact_mod_cast (hcut p hp).1
    have hfloor : (coreFloor N (log p) (39/20) : ℝ)≤exp ((39/20 : ℝ)*N-log p) :=
      Nat.floor_le (exp_pos _).le
    have h := log_le_log hr0 ((show (R p : ℝ)≤coreFloor N (log p) (39/20) by
      exact_mod_cast (hcut p hp).2.1).trans hfloor)
    rw [log_exp] at h
    refine ⟨(hcut p hp).1,(hcut p hp).2.2.2,?_⟩
    nlinarith only [h,(hP p hp).2.2.2.1,Nat.cast_nonneg (α := ℝ) N]
  have hprice : B*(N : ℝ)^3*(1+(203/100 : ℝ)*N)≤
      20*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)^6*
        exp (-(3/500 : ℝ)*N) := by
    have hn : 0≤(N : ℝ) := Nat.cast_nonneg N
    have hp : (N : ℝ)*((N : ℝ)+1)*(N : ℝ)^3*(1+(203/100 : ℝ)*N)≤
        (5/2 : ℝ)*((N : ℝ)+1)^6 := by
      have h4 := pow_le_pow_left₀ hn (show (N : ℝ)≤N+1 by linarith) 4
      have hl : 1+(203/100 : ℝ)*N≤(5/2 : ℝ)*((N : ℝ)+1) := by linarith
      calc
        _ = (N : ℝ)^4*((N : ℝ)+1)*(1+(203/100 : ℝ)*N) := by ring
        _ ≤ ((N : ℝ)+1)^4*((N : ℝ)+1)*((5/2 : ℝ)*((N : ℝ)+1)) := by gcongr
        _ = _ := by ring
    have h := mul_le_mul_of_nonneg_left hp
      (show 0≤8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*exp (-(3/500 : ℝ)*N) by
        positivity [ZetaRieszLongCutoffError.countingConstant_pos])
    calc
      _ = (8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*exp (-(3/500 : ℝ)*N))*
        ((N : ℝ)*((N : ℝ)+1)*(N : ℝ)^3*(1+(203/100 : ℝ)*N)) := by dsimp [B]; ring
      _ ≤ _ := h
      _ = _ := by ring
  change |u^(N+1)*J|≤_
  have h := (abs_add_le (u^(N+1)*(J-D)) (u^(N+1)*D)).trans
    (add_le_add (herr.trans hprice) hmain)
  have heq : u^(N+1)*(J-D)+u^(N+1)*D=u^(N+1)*J := by ring
  rw [heq] at h
  exact h

theorem taggedCoreBudget_tendsto (u y : ℝ) :
    Tendsto (taggedCoreBudget u y) atTop (𝓝 0) := by
  have h0 : 0<exp (-3/500 : ℝ) := exp_pos _
  have h1 : exp (-3/500 : ℝ)<1 := exp_lt_one_iff.mpr (by norm_num)
  have h := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 6 h0 h1).const_mul
    (20*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|))).add
      (global_core_tagged_main_budget_tendsto u y)
  simp only [mul_zero,zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← exp_nat_mul]
  dsimp [taggedCoreBudget]
  ring

/-- A concrete original owner regime admitting COMPLETE windows, with
the nondominant mask automatic throughout. The interval is not a
continuum approximation to the old factorial allocation. -/
theorem full_core_owner_geometry {N p : ℕ} (hN : 64≤N) (hp : p.Prime)
    (hlo : (51/50 : ℝ)*N≤log p) (hhi : log p≤(5/4 : ℝ)*N) :
    coreFloor N (log p) (203/100)<p ∧
      ∀ a∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)),
        log p<(13/20 : ℝ)*log (p*a : ℕ) := by
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hc : log p≤(4/3 : ℝ)*N := by linarith only [hhi,hn]
  have hM := (coreFloor_geometry hN hc).1
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hx : coreFloor N (log p) (203/100)<p := by
    have hf : (coreFloor N (log p) (203/100) : ℝ)≤exp ((203/100 : ℝ)*N-log p) :=
      Nat.floor_le (exp_pos _).le
    have he : exp ((203/100 : ℝ)*N-log p)<exp (log p) :=
      exp_lt_exp.mpr (by linarith only [hlo,hn])
    rw [exp_log hp0] at he
    exact_mod_cast hf.trans_lt he
  refine ⟨hx,?_⟩
  intro a ha
  have ha0 : 0<a := by have h := (Finset.mem_Ioc.mp ha).1; omega
  have hband := (coreFloor_membership N (log p) ha0).mp ha
  have hat : (0 : ℝ)<a := by exact_mod_cast ha0
  have he : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul hp0.ne' hat.ne']
  rw [he]
  nlinarith only [hband.1,hhi,hn]

/-- A CANONICAL tag allows every larger small prime to remain. This is
not the older exactly-one-small-prime restriction `T.erase r`. -/
def leastTagExclusions (T : Finset ℕ) (r : ℕ) : Finset ℕ := T.filter (fun q => q<r)

theorem leastTagExclusions_subset (T : Finset ℕ) (r : ℕ) : leastTagExclusions T r⊆T :=
  Finset.filter_subset _ _

theorem leastTag_minimal (T : Finset ℕ) {r a q : ℕ}
    (hrest : ¬∃ z∈leastTagExclusions T r, z∣a) (hq : q∈T) (hqa : q∣a) : r≤q := by
  by_contra h
  have hqr : q<r := by omega
  exact hrest ⟨q,Finset.mem_filter.mpr ⟨hq,hqr⟩,hqa⟩

/-- Counts and additional cofactor primes do not multiply an incidence. -/
theorem leastTag_unique (T : Finset ℕ) {r q a : ℕ} (hr : r∈T) (hq : q∈T)
    (hra : r∣a) (hqa : q∣a)
    (hrestR : ¬∃ z∈leastTagExclusions T r, z∣a)
    (hrestQ : ¬∃ z∈leastTagExclusions T q, z∣a) : r=q :=
  le_antisymm (leastTag_minimal T hrestR hq hqa) (leastTag_minimal T hrestQ hr hra)

private theorem leastTag_sum (T : Finset ℕ) (a : ℕ) (F : ℝ) :
    (∑ r∈T, if (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a then F else 0)=
      if ∃ r∈T, r∣a then F else 0 := by
  by_cases he : ∃ r∈T, r∣a
  · let D := T.filter (fun r => r∣a)
    have hD : D.Nonempty := by
      obtain ⟨r,hr,hra⟩ := he
      exact ⟨r,Finset.mem_filter.mpr ⟨hr,hra⟩⟩
    let r := D.min' hD
    have hr : r∈T ∧ r∣a := Finset.mem_filter.mp (Finset.min'_mem D hD)
    have hrest : ¬∃ q∈leastTagExclusions T r, q∣a := by
      rintro ⟨q,hq,hqa⟩
      have hq' := Finset.mem_filter.mp hq
      have hmin : r≤q := Finset.min'_le D q (Finset.mem_filter.mpr ⟨hq'.1,hqa⟩)
      omega
    have hi q (hq : q∈T) :
        ((¬∃ z∈leastTagExclusions T q, z∣a) ∧ q∣a) ↔ q=r := by
      constructor
      · intro h
        exact (leastTag_unique T hr.1 hq hr.2 h.2 hrest h.1).symm
      · rintro rfl
        exact ⟨hrest,hr.2⟩
    rw [if_pos he]
    simp_rw [Finset.sum_congr rfl (fun q hq => if_congr (hi q hq) rfl rfl)]
    simp only [Finset.sum_ite_eq',if_pos hr.1]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro r hr
    have hnot : ¬r∣a := fun hd => he ⟨r,hr,hd⟩
    simp only [hnot,and_false,ite_false]

/-- Exact finite union: every label with ANY small cofactor prime occurs
once, regardless of how many more such primes divide it. -/
theorem leastTag_partition (T : Finset ℕ) (M X : ℕ) (F : ℕ→ℝ) :
    (∑ r∈T, ∑ a∈Finset.Ioc M X,
      if (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a then F a else 0)=
      ∑ a∈Finset.Ioc M X, if ∃ r∈T, r∣a then F a else 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => leastTag_sum T a (F a))

/-- Choosing tags above N² enforces the ORIGINAL lower physical mask,
even when arbitrarily many other small primes remain in the cofactor. -/
theorem leastTag_physical_prime_support (T : Finset ℕ) {N r a p : ℕ}
    (hN : 1≤N) (hT : ∀ q, q.Prime → q≤N^3 → q∈T) (hrN : N^2<r)
    (hrest : ¬∃ q∈leastTagExclusions T r, q∣a) (ha : Squarefree a) (hap : a<p) :
    ∀ q∈a.primeFactors, N^2<q ∧ q<p := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqa := Nat.dvd_of_mem_primeFactors hq
  have hlo : N^2<q := by
    by_contra hn
    have hqN : q≤N^2 := by omega
    have hNC : N^2≤N^3 := by
      calc
        _ = N^2*1 := by rw [Nat.mul_one]
        _ ≤ N^2*N := Nat.mul_le_mul_left _ hN
        _ = _ := by ring
    have hmin := leastTag_minimal T hrest (hT q hqp (hqN.trans hNC)) hqa
    omega
  exact ⟨hlo,(Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hqa).trans_lt hap⟩

private theorem selectedTag_sum (T V : Finset ℕ) (hV : V⊆T) (a : ℕ) (F : ℝ) :
    (∑ r∈V, if (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a then F else 0)=
      if ∃ r∈V, (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a then F else 0 := by
  by_cases he : ∃ r∈V, (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a
  · obtain ⟨r,hr,hrest,hra⟩ := he
    rw [if_pos ⟨r,hr,hrest,hra⟩]
    rw [Finset.sum_eq_single_of_mem r hr (by
      intro q hq hqr
      have hn : ¬((¬∃ z∈leastTagExclusions T q, z∣a) ∧ q∣a) := by
        intro h
        exact hqr (leastTag_unique T (hV hq) (hV hr) h.2 hra h.1 hrest)
      simp only [if_neg hn])]
    have hrr : (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a := ⟨hrest,hra⟩
    simp only [if_pos hrr]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro r hr
    have hn : ¬((¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a) :=
      fun h => he ⟨r,hr,h⟩
    simp only [if_neg hn]

/-- Exact physical labels of the joined least-tag family. A retained tag
may be selected above N², but every larger small prime remains allowed. -/
def selectedCofactors (T V : Finset ℕ) (N p : ℕ) : Finset ℕ :=
  (Finset.Ioc (coreFloor N (log p) (39/20))
    (coreFloor N (log p) (203/100))).filter (fun a =>
      Squarefree a ∧ ¬a.Prime ∧
        ∃ r∈V, (¬∃ q∈leastTagExclusions T r, q∣a) ∧ r∣a)

/-- Distinct literal owner/cofactor pairs selected by the canonical least
tag, with every complete core-window label retained. -/
def selectedRows (T V P : Finset ℕ) (N : ℕ) : Finset (ℕ×ℕ) :=
  (P.sigma (fun p => selectedCofactors T V N p)).image (fun pa => (pa.1,pa.2))

theorem selectedRows_data (T V P : Finset ℕ) (N : ℕ) {pa : ℕ×ℕ}
    (h : pa∈selectedRows T V P N) :
    pa.1∈P ∧ pa.2∈Finset.Ioc (coreFloor N (log pa.1) (39/20))
      (coreFloor N (log pa.1) (203/100)) ∧ Squarefree pa.2 ∧ ¬pa.2.Prime ∧
        ∃ r∈V, (¬∃ q∈leastTagExclusions T r, q∣pa.2) ∧ r∣pa.2 := by
  obtain ⟨⟨p,a⟩,ha,he⟩ := Finset.mem_image.mp h
  obtain ⟨hp,ha⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hi,hs⟩ := Finset.mem_filter.mp ha
  cases he
  exact ⟨hp,hi,hs⟩

/-- The global tag sum is exactly one literal physical sum. No source
credit is multiplied by the number of primes or cofactor counts. -/
theorem selectedRows_sum (T V P A : Finset ℕ) (hV : V⊆T) (N : ℕ) (L y : ℝ) :
    (∑ pa∈selectedRows T V P N,
      (ZetaRieszJointAllocation.residualCoefficient
        (A∩{ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)}) L N (pa.1*pa.2)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2)).re)=
      ∑ p∈P, ∑ r∈V, taggedOwnerRow (leastTagExclusions T r) A N
        (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) r p L y := by
  rw [selectedRows,Finset.sum_image (by
    intro pa _ pb _ he
    exact Sigma.ext (congrArg Prod.fst he) (by
      cases pa; cases pb; simpa using congrArg Prod.snd he)),Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [selectedCofactors,Finset.sum_filter]
  simp only [taggedOwnerRow,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : Squarefree a ∧ ¬a.Prime
  · have h := selectedTag_sum T V hV a
      (ZetaRieszJointAllocation.residualCoefficient
        (A∩{ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re
    simpa only [hs.1,hs.2,not_false_eq_true,true_and] using h.symm
  · have hn : ¬Squarefree a ∨ a.Prime := by tauto
    rcases hn with hn | hn
    · simp only [hn,false_and,ite_false,Finset.sum_const_zero]
    · simp only [hn,not_true_eq_false,and_false,false_and,ite_false,Finset.sum_const_zero]

/-- The ACTUAL native count crop costs its already-proved allowance on
these joined labels. Tags do not introduce any additional count credit. -/
theorem eventually_selected_count_boundary :
    ∀ᶠ j : ℕ in atTop, ∀ (T V P A : Finset ℕ) (L u y : ℝ),
      0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ p∈P, p.Prime ∧ log p≤(4/3 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
        coreFloor (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (log p) (203/100)<p) →
      |u^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ∑ pa∈(selectedRows T V P (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)).filter
          (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤(pa.1*pa.2).primeFactors.card),
          (ZetaRieszJointAllocation.residualCoefficient
            (A∩{ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)}) L
              (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (pa.1*pa.2)*
                zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
                  (3/2+Complex.I*y) (pa.1*pa.2)).re|≤
        ZetaRieszNearCriticalCountPayment.allowance j := by
  filter_upwards [ZetaRieszRoughOwnerComparison.eventually_owned_count_boundary,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ))]
    with j hj hN T V P A L u y hL hu hU hP
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  have hd pa (hpa : pa∈selectedRows T V P N) :
      pa.1.Prime ∧ Squarefree pa.2 ∧ pa.2<pa.1 := by
    have h := selectedRows_data T V P N hpa
    exact ⟨(hP pa.1 h.1).1,h.2.2.1,(Finset.mem_Ioc.mp h.2.1).2.trans_lt (hP pa.1 h.1).2.2⟩
  have hl pa (hpa : pa∈selectedRows T V P N) :
      log (pa.1*pa.2 : ℕ)≤(203/100 : ℝ)*N := by
    have h := selectedRows_data T V P N hpa
    have ha0 : 0<pa.2 := by
      have hm := (coreFloor_geometry hN (hP pa.1 h.1).2.1).1
      have hi := (Finset.mem_Ioc.mp h.2.1).1
      omega
    have hb := (coreFloor_membership N (log pa.1) ha0).mp h.2.1
    rw [Nat.cast_mul,log_mul
      (show (pa.1 : ℝ)≠0 by exact_mod_cast (hd pa hpa).1.ne_zero)
      (show (pa.2 : ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt ha0))]
    exact hb.2
  have h := hj (selectedRows T V P N) A L u y hL hu hU hd hl
  have hre := Complex.abs_re_le_norm ((u : ℂ)^(N+1)*
    ∑ pa∈(selectedRows T V P N).filter
      (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤(pa.1*pa.2).primeFactors.card),
      ZetaRieszJointAllocation.residualCoefficient
        (A∩{ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)}) L N (pa.1*pa.2)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2))
  apply le_trans ?_ h
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_sum,zero_mul,sub_zero] using hre

/-- One joined source-scale price for the signed complete-window family
and its existing native count boundary. Both terms tend to zero. -/
def selectedNativeBudget (u y : ℝ) (j : ℕ) : ℝ :=
  taggedCoreBudget u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)+
    ZetaRieszNearCriticalCountPayment.allowance j

theorem selectedNativeBudget_tendsto (u y : ℝ) :
    Tendsto (selectedNativeBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => taggedCoreBudget u y
    (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)+
      ZetaRieszNearCriticalCountPayment.allowance j) atTop (𝓝 0)
  have h := ((taggedCoreBudget_tendsto u y).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add
      ZetaRieszNearCriticalCountPayment.tendsto_allowance
  simpa only [Function.comp_apply,zero_add] using h

/-- An independent bound on the LITERAL joined least-tag population
with its ACTUAL native count crop retained. Its entire signed contribution
tends to zero; this is not a bound on the rest of the whole carrier. -/
theorem eventually_cropped_selected_core_bound :
    ∀ᶠ j : ℕ in atTop, ∀ (T V A P : Finset ℕ) (R : ℕ→ℕ) (Q : ℕ) (L u y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j;
      0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling → 54≤|y| →
      (∀ r∈T, r.Prime ∧ r≤N^3) → V⊆T →
      (∀ p∈P, p.Prime ∧ p∈A ∧ p≤Q ∧ 1≤log p ∧ log p≤(4/3 : ℝ)*N ∧ log p≤L) →
      log Q≤(203/100 : ℝ)*N →
      (∀ p∈P, N^3≤coreFloor N (log p) (39/20) ∧ coreFloor N (log p) (203/100)<p) →
      (∀ p∈P, 0<R p ∧ R p≤coreFloor N (log p) (39/20) ∧
        (R p)^4≤(coreFloor N (log p) (39/20))^3 ∧ L-log p≤log (R p+1 : ℕ)) →
      |u^(N+1)*∑ pa∈(selectedRows T V P N).filter
        (fun pa => (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j),
          (ZetaRieszJointAllocation.residualCoefficient
            (A∩{ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)}) L N (pa.1*pa.2)*
              zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2)).re|≤
        selectedNativeBudget u y j := by
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    eventually_global_literal_tagged_core_bound,eventually_selected_count_boundary]
    with j hj hc
  intro T V A P R Q L u y
  dsimp only
  intro hL hu hU hy hT hV hP hQ hshell hcut
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let E := selectedRows T V P N
  let f := fun pa : ℕ×ℕ =>
    (ZetaRieszJointAllocation.residualCoefficient
      (A∩{ZetaRieszPrimeEndpoint.largestPrime (pa.1*pa.2)}) L N (pa.1*pa.2)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (pa.1*pa.2)).re
  have hfull : |u^(N+1)*∑ pa∈E,f pa|≤taggedCoreBudget u y N := by
    have h := hj T V A P (leastTagExclusions T) R Q L u y
      hL hu hU hy hT hV (fun r _ => leastTagExclusions_subset T r) hP hQ hshell hcut
    rw [← selectedRows_sum T V P A hV N L y] at h
    exact h
  have hhigh : |u^(N+1)*∑ pa∈E.filter
      (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤(pa.1*pa.2).primeFactors.card),
        f pa|≤ZetaRieszNearCriticalCountPayment.allowance j :=
    hc T V P A L u y hL hu hU (fun p hp =>
      ⟨(hP p hp).1,(hP p hp).2.2.2.2.1,(hshell p hp).2⟩)
  have hsplit := congrArg (fun z : ℝ => u^(N+1)*z)
    (Finset.sum_filter_add_sum_filter_not E
      (fun pa => (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j) f)
  simp only [not_lt,mul_add] at hsplit
  change |u^(N+1)*∑ pa∈E.filter
    (fun pa => (pa.1*pa.2).primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j), f pa|≤_
  unfold selectedNativeBudget
  apply abs_le.mpr
  constructor <;> linarith only [hsplit,(abs_le.mp hfull).1,(abs_le.mp hfull).2,
    (abs_le.mp hhigh).1,(abs_le.mp hhigh).2]

end RiemannGaussian.ZetaRieszTaggedCoreWindow
