/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRoughOwnerComparison

/-!
# Joined comparison for owners with one tagged small cofactor prime

Selecting a prime divisor is an exact difference of roughness measures.
The original owner weight, all factorial orders and the product phase are
unchanged. On large cofactor rows the ordinary-prime heads cancel exactly.
Only the centered comparison error is paid; the signed density difference
is not asserted to satisfy the numerical floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszTaggedOwnerComparison
open ZetaRieszCofactorPhaseEnergy ZetaRieszCofactorDiscrepancy
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszRoughOwnerComparison
open ZetaRieszUnsignedDivisorError (sieve)
open ZetaRieszLongCutoffError (roughDensityPrefix)

/-- The mark is in the counting measure, never the smooth phase weight. -/
def taggedSieve (S : Finset ℕ) (r n : ℕ) : ℝ :=
  sieve S n-sieve (insert r S) n

/-- Every other excluded prime and squarefreeness are retained exactly. -/
theorem taggedSieve_eq (S : Finset ℕ) (r n : ℕ) :
    taggedSieve S r n =
      if Squarefree n ∧ (¬∃ q ∈ S, q∣n) ∧ r∣n then 1 else 0 := by
  by_cases hs : Squarefree n <;>
    by_cases hS : ∃ q ∈ S, q∣n <;> by_cases hr : r∣n <;>
      simp [taggedSieve,sieve,hs,hS,hr]

/-- Keep the complete signed divisor profile as one arithmetic scalar. -/
def taggedDensityPrefix (S : Finset ℕ) (r D : ℕ) : ℝ :=
  roughDensityPrefix S D-roughDensityPrefix (insert r S) D

/-- No positive part, absolute value or prime-count allowance is inserted. -/
def taggedRieszScalar (S : Finset ℕ) (r R : ℕ) (b : ℝ) : ℝ :=
  ∑ D ∈ Finset.Icc 1 R,
    (max 0 (b-log D)-max 0 (b-log (D+1 : ℕ)))*taggedDensityPrefix S r D

private theorem insert_prime (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    {r : ℕ} (hr : r.Prime) : ∀ q ∈ insert r S, q.Prime := by
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact hr
  · exact hS q hq

/-- A tagged prime cofactor must be the tag itself, below the row. -/
theorem tagged_prime_head_eq_zero (S : Finset ℕ) {r M X : ℕ}
    (hr : r.Prime) (hrM : r≤M) (a : ℕ → ℝ) (y c : ℝ) :
    (∑ q ∈ (Finset.Icc 1 X).filter Nat.Prime,
      shellWeight M X a y c q*sieve S q) =
    ∑ q ∈ (Finset.Icc 1 X).filter Nat.Prime,
      shellWeight M X a y c q*sieve (insert r S) q := by
  apply Finset.sum_congr rfl
  intro q hq
  have hqp := (Finset.mem_filter.mp hq).2
  by_cases hd : r∣q
  · have he : r=q := (Nat.dvd_prime_two_le hqp hr.two_le).mp hd
    have hlo : ¬M<q := by omega
    simp [shellWeight,hlo]
  · have he : sieve S q=sieve (insert r S) q := by simp [sieve,hd]
    rw [he]

private theorem cost_insert_le (S : Finset ℕ) (r : ℕ) :
    ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert r S) ≤
      3*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S := by
  by_cases hr : r∈S
  · rw [Finset.insert_eq_of_mem hr]
    nlinarith [ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S]
  have ht : 0≤zetaPrimeExpWeight (3/4) r := (exp_pos _).le
  have hu : zetaPrimeExpWeight (3/4) r≤1 := by
    rw [zetaPrimeExpWeight,exp_le_one_iff]
    nlinarith [log_natCast_nonneg r]
  have hw : 1+primeSquareCorrectedWeight (3/4) r≤3 := by
    unfold primeSquareCorrectedWeight
    nlinarith [mul_le_mul_of_nonneg_left hu ht]
  unfold ZetaRieszPrimeWeightedSieve.sieveCost
  rw [Finset.prod_insert hr]
  exact mul_le_mul_of_nonneg_right hw
    (ZetaRieszPrimeWeightedSieve.sieveCost_nonneg (3/4) S)

private theorem tagged_filter_sum (S : Finset ℕ) (r : ℕ) (M X : ℕ)
    (F : ℕ → ℝ) :
    (∑ a ∈ (Finset.Ioc M X).filter (fun a =>
      Squarefree a ∧ ¬a.Prime ∧ (¬∃ q ∈ S, q∣a) ∧ r∣a), F a) =
      (∑ a ∈ (Finset.Ioc M X).filter (fun a =>
        Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ S, q∣a), F a)-
      ∑ a ∈ (Finset.Ioc M X).filter (fun a =>
        Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ insert r S, q∣a), F a := by
  simp only [Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : Squarefree a <;> by_cases hp : a.Prime <;>
    by_cases hS : ∃ q ∈ S, q∣a <;> by_cases hr : r∣a <;>
      simp [hs,hp,hS,hr]

/-- A direct signed estimate for ORIGINAL owner atoms. All counts and
both sieves are joined before estimating their centered difference.
The ordinary-prime head is zero here by arithmetic, not a norm payment. -/
theorem literal_tagged_owner_error (S A : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) {N M X R r : ℕ} (hr : r.Prime) (hrM : r≤M)
    (hN : 32≤N) (hM : 0<M) (hMX : M<X) (hXM : X≤2*M)
    (hRM : R≤M) (hcut : R^4≤M^3) (hlarge : exp ((N : ℝ)/2)≤M)
    {p : ℕ} (hp : p.Prime) (hXp : X<p) (hpA : p∈A)
    {L u : ℝ} (hL : 0<L) (hpL : log p≤L) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hend : L-log p≤log (R+1 : ℕ)) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N (log p)) y (log p);
    |u^(N+1)*((∑ a ∈ (Finset.Ioc M X).filter (fun a =>
      Squarefree a ∧ ¬a.Prime ∧ (¬∃ q ∈ S, q∣a) ∧ r∣a),
      (ZetaRieszJointAllocation.residualCoefficient
        (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-
      (taggedRieszScalar S r R (L-log p)*
        (∑ a ∈ Finset.Icc 1 X, w a))/(L*p))| ≤
      (8*u*ZetaRieszLongCutoffError.countingConstant*
        ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S*(6+|y|)*((N : ℝ)+1)*
          exp (-(7/1000 : ℝ)*N))*(p : ℝ)⁻¹ := by
  let w := shellWeight M X (ownerAmplitude N (log p)) y (log p)
  let F := fun a => (ZetaRieszJointAllocation.residualCoefficient
    (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re
  let V := fun T : Finset ℕ => ∑ a ∈ (Finset.Ioc M X).filter (fun a =>
    Squarefree a ∧ ¬a.Prime ∧ ¬∃ q ∈ T, q∣a), F a
  let H := fun T : Finset ℕ =>
    (∑ D ∈ Finset.Icc 1 R,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix T D)*
        (∑ a ∈ Finset.Icc 1 X, w a)-
    (L-log p)*(∑ q ∈ (Finset.Icc 1 X).filter Nat.Prime, w q*sieve T q)
  let B := 2*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
    exp (-(7/1000 : ℝ)*N)*(p : ℝ)⁻¹
  have hB : 0≤B := by dsimp [B]; positivity [ZetaRieszLongCutoffError.countingConstant_pos]
  have h0 : |u^(N+1)*(V S-H S/(L*p))|≤
      B*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) S := by
    have h := literal_rough_owner_error_cap S A hS hN hM hMX hXM hRM hcut hlarge
      hp hXp hpA hL hpL hu hU hend y
    exact h.trans_eq (by dsimp [V,F,H,w,B]; ring)
  have h1 : |u^(N+1)*(V (insert r S)-H (insert r S)/(L*p))|≤
      B*ZetaRieszPrimeWeightedSieve.sieveCost (3/4) (insert r S) := by
    have h := literal_rough_owner_error_cap (insert r S) A (insert_prime S hS hr)
      hN hM hMX hXM hRM hcut hlarge hp hXp hpA hL hpL hu hU hend y
    exact h.trans_eq (by dsimp [V,F,H,w,B]; ring)
  have hh : H S-H (insert r S)=taggedRieszScalar S r R (L-log p)*
      (∑ a ∈ Finset.Icc 1 X, w a) := by
    have hh := tagged_prime_head_eq_zero (X := X) S hr hrM
      (ownerAmplitude N (log p)) y (log p)
    change _ = _ at hh
    dsimp [H,taggedRieszScalar,taggedDensityPrefix]
    simp only [mul_sub,Finset.sum_sub_distrib]
    dsimp [w] at *
    rw [hh]
    ring
  dsimp only
  rw [tagged_filter_sum S r M X F,← hh]
  change |u^(N+1)*((V S-V (insert r S))-(H S-H (insert r S))/(L*p))|≤_
  rw [show u^(N+1)*((V S-V (insert r S))-(H S-H (insert r S))/(L*p)) =
    u^(N+1)*(V S-H S/(L*p))-u^(N+1)*(V (insert r S)-H (insert r S)/(L*p)) by ring]
  apply (abs_sub _ _).trans
  apply (add_le_add h0 h1).trans
  have hc := mul_le_mul_of_nonneg_left (cost_insert_le S r) hB
  dsimp [B] at *
  nlinarith only [hc]

/-- In the selected population, count two is impossible: its cofactor
contains the tag and is larger than the tag. -/
theorem tagged_cofactor_not_prime {r a M : ℕ} (hr : r.Prime)
    (hrM : r≤M) (hMa : M<a) (hra : r∣a) : ¬a.Prime := by
  intro ha
  have he := (Nat.dvd_prime_two_le ha hr.two_le).mp hra
  omega

/-- The literal tagged Riesz coefficient is the TWO hinges together.
Their Möbius signs and their moving translated cutoffs are unchanged. -/
theorem tagged_riesz_two_hinges {r a : ℕ} (hr : r.Prime)
    (ha : Squarefree a) (hra : r∣a) (b : ℝ) :
    VaughanLogAverage.riesz b a = VaughanLogAverage.riesz b (a/r)-
      VaughanLogAverage.riesz (b-log r) (a/r) := by
  have he : r*(a/r)=a := Nat.mul_div_cancel' hra
  have hs := Nat.squarefree_mul_iff.mp (he.symm ▸ ha)
  have hd : ¬r∣a/r := hr.coprime_iff_not_dvd.mp hs.1
  have h := ZetaSquarefreeRieszWindows.riesz_prime_mul b hr hd
  rwa [he] at h

/-- Exactly one small cofactor prime is a disjoint tag, not one incidence
per divisor. This prevents multiplying the actual carrier by its count. -/
theorem unique_small_tag (T : Finset ℕ) {r q a : ℕ}
    (_hr : r∈T) (hq : q∈T) (_hra : r∣a) (hqa : q∣a)
    (hrest : ¬∃ z ∈ T.erase r, z∣a) : r=q := by
  by_contra hne
  exact hrest ⟨q,Finset.mem_erase.mpr ⟨Ne.symm hne,hq⟩,hqa⟩

/-- Taking T to contain EVERY prime through N³ and retaining only tags
above N² enforces the ORIGINAL lower physical prime mask exactly.
The complete owner geometry enforces the upper mask below the owner. -/
theorem tagged_physical_prime_support (T : Finset ℕ) {N r a p : ℕ}
    (hN : 1≤N) (hT : ∀ q, q.Prime → q≤N^3 → q∈T)
    (hr : r∈T) (hrN : N^2<r) (hra : r∣a)
    (hrest : ¬∃ q ∈ T.erase r, q∣a) (ha : Squarefree a) (hap : a<p) :
    ∀ q ∈ a.primeFactors, N^2<q ∧ q<p := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqa := Nat.dvd_of_mem_primeFactors hq
  have hlo : N^2<q := by
    by_contra hn
    have hqN : q≤N^2 := le_of_not_gt hn
    have hNC : N^2≤N^3 := by
      calc
        _ = N^2*1 := by rw [Nat.mul_one]
        _ ≤ N^2*N := Nat.mul_le_mul_left _ hN
        _ = _ := by ring
    have he := unique_small_tag T hr (hT q hqp (hqN.trans hNC)) hra hqa hrest
    omega
  exact ⟨hlo,(Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hqa).trans_lt hap⟩

/-- A sector of the original owner carrier, with its exact allocation. -/
def taggedOwnerRow (S A : Finset ℕ) (N M X r p : ℕ) (L y : ℝ) : ℝ :=
  ∑ a ∈ (Finset.Ioc M X).filter (fun a =>
    Squarefree a ∧ ¬a.Prime ∧ (¬∃ q ∈ S, q∣a) ∧ r∣a),
    (ZetaRieszJointAllocation.residualCoefficient
      (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re

/-- The main remains one signed scalar times one signed phase sum. -/
def taggedOwnerMain (S : Finset ℕ) (N M X R r p : ℕ) (L y : ℝ) : ℝ :=
  (taggedRieszScalar S r R (L-log p)*
    (∑ a ∈ Finset.Icc 1 X,
      shellWeight M X (ownerAmplitude N (log p)) y (log p) a))/(L*p)

/-- Quantitative endpoint audit for the WHOLE physical log window.
This is not a bound for its interior or for an arbitrary partial row. -/
theorem core_endpoint_rates {u : ℝ} (_hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    (u*(39/20))*exp (1/40 : ℝ)≤exp (-(1/200000 : ℝ)) ∧
      (u*(203/100))*exp (-(3/200 : ℝ))≤exp (-(1/200000 : ℝ)) := by
  have hlo : ZetaRieszWideOwnerAudit.radiusCeiling*(39/20)≤
      exp (-(1/40 : ℝ)-1/200000) := by
    have h := add_one_le_exp (-((1/40 : ℝ)+1/200000)/4)
    have hp := pow_le_pow_left₀
      (by norm_num : (0 : ℝ)≤-((1/40 : ℝ)+1/200000)/4+1) h 4
    rw [← exp_nat_mul] at hp
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hp ⊢
    linarith only [hp]
  have hhi : ZetaRieszWideOwnerAudit.radiusCeiling*(203/100)≤
      exp ((3/200 : ℝ)-1/200000) := by
    have h := sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ)≤(3/200 : ℝ)-1/200000) 4
    norm_num [Finset.sum_range_succ,ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    linarith only [h]
  constructor
  · calc
      _ ≤ exp (-(1/40 : ℝ)-1/200000)*exp (1/40 : ℝ) :=
        mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right hU (by norm_num : (0 : ℝ)≤39/20)).trans hlo)
          (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  · calc
      _ ≤ exp ((3/200 : ℝ)-1/200000)*exp (-(3/200 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right hU (by norm_num : (0 : ℝ)≤203/100)).trans hhi)
          (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring

private theorem endpoint_radial_cap (N : ℕ) {u a : ℝ} (hu : 0≤u) (ha : 0<a) :
    u^(N+1)*radial N (a*N) ≤
      ((N : ℝ)+1)*(u*a)*((u*a)*exp (1-a/2))^N := by
  have h := pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) (N+1)
  have hm := mul_le_mul_of_nonneg_left h
    (show 0≤((N : ℝ)+1)*(u*a)^(N+1)*exp (-a*N/2) by positivity)
  have hf : (N.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hn : (N : ℝ)+1≠0 := by positivity
  have he : u^(N+1)*radial N (a*N)=
      (((N : ℝ)+1)*(u*a)^(N+1)*exp (-a*N/2))*
        ((N : ℝ)^(N+1)/((N+1).factorial : ℝ)) := by
    rw [radial,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow,mul_pow]
    field_simp
  rw [he]
  apply hm.trans_eq
  have hx : exp (-a*N/2)*exp (N : ℝ)=exp ((N : ℝ)*(1-a/2)) := by
    rw [← exp_add]; congr 1; ring
  calc
    _ = ((N : ℝ)+1)*(u*a)^(N+1)*(exp (-a*N/2)*exp (N : ℝ)) := by ring
    _ = ((N : ℝ)+1)*(u*a)^(N+1)*exp ((N : ℝ)*(1-a/2)) := by rw [hx]
    _ = _ := by
      rw [mul_pow (u*a) (exp (1-a/2)) N,← exp_nat_mul,pow_succ (u*a) N]
      ring

/-- Both literal radial endpoints have a fixed geometric source margin,
including the successor factorial order. No sign of the interior main
or arbitrary mask completion is inferred from this boundary estimate. -/
theorem normalized_core_endpoint_radial {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*radial N ((39/20 : ℝ)*N) ≤
      ((N : ℝ)+1)*(u*(39/20))*exp (-(N : ℝ)/200000) ∧
    u^(N+1)*radial N ((203/100 : ℝ)*N) ≤
      ((N : ℝ)+1)*(u*(203/100))*exp (-(N : ℝ)/200000) := by
  obtain ⟨hlo,hhi⟩ := core_endpoint_rates hu hU
  have h1 := endpoint_radial_cap N hu (by norm_num : (0 : ℝ)<39/20)
  have h2 := endpoint_radial_cap N hu (by norm_num : (0 : ℝ)<203/100)
  norm_num only at h1 h2
  constructor
  · apply h1.trans
    have h := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0≤u*(39/20)*exp (1/40 : ℝ)) hlo N)
      (show 0≤((N : ℝ)+1)*(u*(39/20)) by positivity)
    rw [← exp_nat_mul] at h
    have he : (N : ℝ)*(-(1/200000 : ℝ))=-(N : ℝ)/200000 := by ring
    simpa only [he] using h
  · apply h2.trans
    have h := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0≤u*(203/100)*exp (-(3/200 : ℝ))) hhi N)
      (show 0≤((N : ℝ)+1)*(u*(203/100)) by positivity)
    convert h using 1
    rw [← exp_nat_mul]
    congr 1
    ring

/-- All small tags and owners aggregate before any real-part bound.
Every row is an original unique-owner incidence with exactly ONE prime
from T. The growing tag count costs only a polynomial in the ERROR.
The two sieve mains are not norm-paid separately. -/
theorem eventually_joint_one_small_owner_error :
    ∀ᶠ N : ℕ in atTop, ∀ (T V A P : Finset ℕ) (M X R : ℕ → ℕ) (Q : ℕ)
      (L u y : ℝ), 0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ r ∈ T, r.Prime ∧ r≤N^3) →
      V⊆T →
      (∀ p ∈ P, p.Prime ∧ p∈A ∧ log p≤L ∧ p≤Q) →
      log Q≤(203/100 : ℝ)*N →
      (∀ p ∈ P, 0<M p ∧ M p<X p ∧ X p≤2*M p ∧ X p<p ∧ N^3≤M p) →
      (∀ p ∈ P, R p≤M p ∧ (R p)^4≤(M p)^3 ∧
        exp ((N : ℝ)/2)≤M p ∧ L-log p≤log (R p+1 : ℕ)) →
      |u^(N+1)*((∑ p ∈ P, ∑ r ∈ V,
        taggedOwnerRow (T.erase r) A N (M p) (X p) r p L y)-
        ∑ p ∈ P, ∑ r ∈ V,
          taggedOwnerMain (T.erase r) N (M p) (X p) (R p) r p L y)| ≤
      (8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
        (N : ℝ)^3*(1+(203/100 : ℝ)*N))*exp (-(3/500 : ℝ)*N) := by
  filter_upwards [eventually_cubic_counting_rate,eventually_ge_atTop (32 : ℕ)]
    with N hrate hN T V A P M X R Q L u y hL hu hU hT hV hP hQ hshell hcut
  let B := 8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)
  have hB : 0≤B := by dsimp [B]; positivity [ZetaRieszLongCutoffError.countingConstant_pos]
  have hcard : (V.card : ℝ)≤(N : ℝ)^3 := by
    have hs : V⊆Finset.Icc 1 (N^3) := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨(hT r (hV hr)).1.pos,(hT r (hV hr)).2⟩
    have hc := Finset.card_le_card hs
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at hc
    exact_mod_cast hc
  have hh : (∑ p ∈ P, (p : ℝ)⁻¹)≤1+(203/100 : ℝ)*N :=
    (marked_harmonic_bound P (fun p hp =>
      ⟨(hP p hp).1,(hP p hp).2.2.2⟩)).trans
        (by simpa only [add_comm] using add_le_add_left hQ 1)
  have he p (hp : p∈P) r (hr : r∈V) :
      |u^(N+1)*(taggedOwnerRow (T.erase r) A N (M p) (X p) r p L y-
        taggedOwnerMain (T.erase r) N (M p) (X p) (R p) r p L y)| ≤
        B*exp (-(3/500 : ℝ)*N)*(p : ℝ)⁻¹ := by
    obtain ⟨hpP,hpA,hpL,_⟩ := hP p hp
    obtain ⟨hM,hMX,hXM,hXp,hNM⟩ := hshell p hp
    obtain ⟨hRM,hcutp,hlarge,hend⟩ := hcut p hp
    have hs : ∀ q ∈ T.erase r, q.Prime ∧ q≤N^3 :=
      fun q hq => hT q (Finset.mem_of_mem_erase hq)
    have h := literal_tagged_owner_error (T.erase r) A (fun q hq => (hs q hq).1)
      (hT r (hV hr)).1 ((hT r (hV hr)).2.trans hNM) hN hM hMX hXM hRM hcutp hlarge
      hpP hXp hpA hL hpL hu hU hend y
    change |u^(N+1)*(taggedOwnerRow (T.erase r) A N (M p) (X p) r p L y-
      taggedOwnerMain (T.erase r) N (M p) (X p) (R p) r p L y)|≤_ at h
    apply h.trans
    have hc := mul_le_mul_of_nonneg_left (hrate (T.erase r) hs) hB
    have hd := mul_le_mul_of_nonneg_right hc (by positivity : 0≤(p : ℝ)⁻¹)
    convert hd using 1
    dsimp [B]
    ring
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ P, ∑ r ∈ V, B*exp (-(3/500 : ℝ)*N)*(p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun r hr => he p hp r hr))
    _ = B*exp (-(3/500 : ℝ)*N)*V.card*(∑ p ∈ P, (p : ℝ)⁻¹) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ B*exp (-(3/500 : ℝ)*N)*(N : ℝ)^3*(1+(203/100 : ℝ)*N) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcard (mul_nonneg hB (exp_pos _).le)) hh
        (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = _ := by dsimp [B]; ring

/-- The enlarged global comparison price still tends to zero. -/
theorem tagged_comparison_budget_tendsto (u y : ℝ) :
    Tendsto (fun N : ℕ =>
      (8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)*((N : ℝ)+1)*
        (N : ℝ)^3*(1+(203/100 : ℝ)*N))*exp (-(3/500 : ℝ)*N)) atTop (𝓝 0) := by
  let C := 8*u*ZetaRieszLongCutoffError.countingConstant*(6+|y|)
  have h0 : 0<exp (-3/500 : ℝ) := exp_pos _
  have h1 : exp (-3/500 : ℝ)<1 := exp_lt_one_iff.mpr (by norm_num)
  have h k := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric k h0 h1
  have he := (((h 5).const_mul (C*(203/100))).add
    ((h 4).const_mul (C*(1-4*(203/100))))).add
    (((h 3).const_mul (C*(-3+6*(203/100)))).add
    (((h 2).const_mul (C*(3-4*(203/100)))).add
      ((h 1).const_mul (C*(-1+203/100)))))
  simp only [mul_zero,add_zero] at he
  apply he.congr'
  filter_upwards [] with N
  rw [← exp_nat_mul]
  dsimp [C]
  ring

/-- Tagging the one-small-prime population does not duplicate any native
label. All further physical/radial/count masks can remain in E. -/
theorem tagged_rows_injective (T : Finset ℕ) (E : Finset (ℕ×ℕ×ℕ))
    (hE : ∀ pra ∈ E, pra.1.Prime ∧ Squarefree pra.2.2 ∧ pra.2.2<pra.1 ∧
      pra.2.1∈T ∧ pra.2.1∣pra.2.2 ∧ ¬∃ q ∈ T.erase pra.2.1, q∣pra.2.2) :
    Set.InjOn (fun pra : ℕ×ℕ×ℕ => pra.1*pra.2.2) (E : Set (ℕ×ℕ×ℕ)) := by
  let F := E.image (fun pra => (pra.1,pra.2.2))
  have hi := owned_rows_injective F (by
    intro pa hpa
    obtain ⟨pra,hpra,rfl⟩ := Finset.mem_image.mp hpa
    have h := hE pra hpra
    exact ⟨h.1,h.2.1,h.2.2.1⟩)
  intro pra hpra prb hprb he
  have hpa : (pra.1,pra.2.2)∈F := Finset.mem_image.mpr ⟨pra,hpra,rfl⟩
  have hpb : (prb.1,prb.2.2)∈F := Finset.mem_image.mpr ⟨prb,hprb,rfl⟩
  have hab := hi hpa hpb he
  have hp := congrArg Prod.fst hab
  have ha := congrArg Prod.snd hab
  have hd := hE pra hpra
  have hd' := hE prb hprb
  have hr := unique_small_tag T hd.2.2.2.1 hd'.2.2.2.1
    hd.2.2.2.2.1 (ha.symm ▸ hd'.2.2.2.2.1) hd.2.2.2.2.2
  exact Prod.ext hp (Prod.ext hr ha)

/-- The native high-count boundary is the SAME existing payment on
actual labels, transferred injectively through the disjoint small tags.
All additional masks may remain in E; no extra count credit is created. -/
theorem eventually_tagged_count_boundary :
    ∀ᶠ j : ℕ in atTop, ∀ (T : Finset ℕ) (E : Finset (ℕ×ℕ×ℕ))
      (A : Finset ℕ) (L u y : ℝ),
      0<L → 0≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      (∀ pra ∈ E, pra.1.Prime ∧ Squarefree pra.2.2 ∧ pra.2.2<pra.1 ∧
        pra.2.1∈T ∧ pra.2.1∣pra.2.2 ∧ ¬∃ q ∈ T.erase pra.2.1, q∣pra.2.2) →
      (∀ pra ∈ E, log (pra.1*pra.2.2 : ℕ)≤(203/100 : ℝ)*
        ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      ‖(u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ∑ pra ∈ E.filter (fun pra => ZetaRieszNearCriticalCountPayment.countCeiling j≤
          (pra.1*pra.2.2).primeFactors.card),
          ZetaRieszJointAllocation.residualCoefficient
            (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (pra.1*pra.2.2)}) L
              (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (pra.1*pra.2.2)*
            zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
              (3/2+Complex.I*y) (pra.1*pra.2.2)‖ ≤
        ZetaRieszNearCriticalCountPayment.allowance j := by
  filter_upwards [eventually_owned_count_boundary]
    with j hj T E A L u y hL hu hU hE hlog
  let F := E.image (fun pra => (pra.1,pra.2.2))
  have h := hj F A L u y hL hu hU
    (by
      intro pa hpa
      obtain ⟨pra,hpra,rfl⟩ := Finset.mem_image.mp hpa
      have hd := hE pra hpra
      exact ⟨hd.1,hd.2.1,hd.2.2.1⟩)
    (by
      intro pa hpa
      obtain ⟨pra,hpra,rfl⟩ := Finset.mem_image.mp hpa
      exact hlog pra hpra)
  have he : F.filter (fun pa => ZetaRieszNearCriticalCountPayment.countCeiling j≤
      (pa.1*pa.2).primeFactors.card) =
      (E.filter (fun pra => ZetaRieszNearCriticalCountPayment.countCeiling j≤
        (pra.1*pra.2.2).primeFactors.card)).image (fun pra => (pra.1,pra.2.2)) := by
    ext pa
    simp only [F,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨pra,hpra,rfl⟩,hc⟩
      exact ⟨pra,⟨hpra,hc⟩,rfl⟩
    · rintro ⟨pra,⟨hpra,hc⟩,rfl⟩
      exact ⟨⟨pra,hpra,rfl⟩,hc⟩
  rw [he] at h
  have hi := tagged_rows_injective T E hE
  rw [Finset.sum_image (by
    intro pra hpra prb hprb he
    apply hi (Finset.mem_filter.mp hpra).1 (Finset.mem_filter.mp hprb).1
    exact congrArg (fun pa : ℕ×ℕ => pa.1*pa.2) he)] at h
  exact h

end RiemannGaussian.ZetaRieszTaggedOwnerComparison
