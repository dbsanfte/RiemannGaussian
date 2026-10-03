/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerCompletionAudit
import RiemannGaussian.ZetaRieszSemiprimePrefixDecay

/-!
# Cancellation of the global semiprime boundary with the same prime head

Global squarefree completion and completion at the smaller marked prime
produce DIFFERENT boundaries. The latter reinforces the head, as already
proved. The former subtracts the full semiprime response. On the same
literal head labels it has the opposite sign, and its amplitude dominates
the head. Join them before pricing; their norm loses exactly the head norm.

The ordinary-prime and raw high-owner completion boundaries remain unpaid.
This is not a payment of the head itself or an independent whole floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalCompletionBoundary
open ZetaRieszPrimeHeadTransport ZetaRieszPrimeHeadPolePayment
open ZetaRieszSmallTagNativeFloor (owners owners_data smallPrimes)
open ZetaRieszOwnerMaximal (ownerWeight ownerWeight_bounds)

private theorem pair_total_log_lower {u : ℝ} {N p q : ℕ}
    (_hp : p∈owners u N) (hq : q∈pairInterval N p) (_hqp : q.Prime) :
    (39/20 : ℝ)*N<log p+log q := by
  have hf := Nat.lt_floor_add_one (exp ((39/20 : ℝ)*N-log p))
  have hi := (Finset.mem_Ioc.mp hq).1
  have hqr : (ZetaRieszOwnerLatticePhase.coreFloor N (log p) (39/20) : ℝ)+1≤q := by
    exact_mod_cast (show ZetaRieszOwnerLatticePhase.coreFloor N (log p) (39/20)+1≤q by omega)
  have hl := log_lt_log (exp_pos _) (hf.trans_le hqr)
  rw [log_exp] at hl
  linarith only [hl]

/-- The global completion uses the full semiprime tent, not the earlier
ordinary-prime cofactor response `L-log q`. -/
theorem original_pair_riesz_eq {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) :
    VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (p*q)=
      log p+log q-SquarefreeVaughanLogSource.length u N := by
  have hpp := (owners_data hp).1
  have hpq : p≠q := (pair_cofactor_lt_owner (by omega : 64≤N) hp hq).ne'
  have hpL := owner_log_le_length hp
  have hqhi := ZetaRieszOwnerCompletionAudit.pair_cofactor_log_upper hp hq hqp
  have hLlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hLhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have htotal := pair_total_log_lower hp hq hqp
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL := SquarefreeVaughanLogSource.length_pos u N
  rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hpp hqp hpq]
  unfold ZetaSquarefreeRieszWindows.primePairTent
  rw [max_eq_right hL.le,max_eq_right (by linarith only [hpL]),
    max_eq_right (by linarith only [hqhi,hLlo,hN0]),
    max_eq_left (by linarith only [htotal,hLhi,hN0])]
  ring

/-- All original head allocations are retained. The difference is
uniformly positive before the COMMON physical phase is evaluated. -/
theorem pair_response_sub_head_lower {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) :
    (17/100 : ℝ)*N≤
      VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (p*q)-
        (SquarefreeVaughanLogSource.length u N-log p)*
          ownerWeight N (log q/(log p+log q)) := by
  obtain ⟨hpl,hql⟩ := head_prime_logs hp hq
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hp0 : 0<log p := by linarith only [hpl,hN0]
  have hq0 : 0<log q := by linarith only [hql,hN0]
  have hw := ownerWeight_bounds N
    (div_nonneg hq0.le (add_pos hp0 hq0).le)
    ((div_le_one (add_pos hp0 hq0)).mpr (by linarith))
  have hpL := owner_log_le_length hp
  have hm := mul_le_mul_of_nonneg_left hw.2 (by linarith only [hpL] :
    0≤SquarefreeVaughanLogSource.length u N-log p)
  have htotal := pair_total_log_lower hp hq hqp
  have hLhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  rw [original_pair_riesz_eq hu hU hN hp hq hqp]
  nlinarith only [hm,htotal,hLhi,hpl,hN0]

/-- The common ORIGINAL kernel, physical prime mask and sieve, before
either boundary coefficient is inserted. -/
def pairWeight (u : ℝ) (N p q : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)/(L*p)*
    (if q.Prime then ZetaRieszSmoothOwnerDiscrepancy.radial N (log p+log q)/(q : ℝ)*
      ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) q else 0)

theorem pairWeight_nonneg {u : ℝ} (hu : 0≤u) (N p q : ℕ) :
    0≤pairWeight u N p q := by
  unfold pairWeight ZetaRieszUnsignedDivisorError.sieve ZetaRieszSmoothOwnerDiscrepancy.radial
  split_ifs <;> positivity [SquarefreeVaughanLogSource.length_pos u N,
    log_natCast_nonneg p,log_natCast_nonneg q]

theorem originalPair_eq_weight (u y : ℝ) (N p q : ℕ) :
    originalPair u y N p q=
      ((pairWeight u N p q*(SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q)) : ℝ) : ℂ)*character y p q := by
  unfold originalPair rawAmount pairWeight
  push_cast
  ring

/-- The SUBTRACTED full semiprime term in the global completion ledger.
It is auxiliary; no new arithmetic carrier is being substituted here. -/
def semiprimeBoundary (u y : ℝ) (N p q : ℕ) : ℂ :=
  ((pairWeight u N p q*VaughanLogAverage.riesz
    (SquarefreeVaughanLogSource.length u N) (p*q) : ℝ) : ℂ)*character y p q

private theorem scalar_character_norm (a y : ℝ) (p q : ℕ) :
    ‖(a : ℂ)*character y p q‖=|a| := by
  rw [norm_mul,norm_character,mul_one,Complex.norm_real,Real.norm_eq_abs]

/-- This is a literal cancellation on identical labels, with every
factorial order and the entire product phase still coupled. -/
theorem boundary_sub_head_norm {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hqp : q.Prime) (y : ℝ) :
    ‖semiprimeBoundary u y N p q-originalPair u y N p q‖=
      ‖semiprimeBoundary u y N p q‖-‖originalPair u y N p q‖ := by
  have hb := pair_response_sub_head_lower hu hU hN hp hq hqp
  have hhead := (ZetaRieszOwnerCompletionAudit.allocated_head_le_boundary hu hU hN hp hq hqp).1
  have hgap : 0≤VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (p*q)-
      (SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q)) :=
    (by positivity : (0 : ℝ)≤(17/100 : ℝ)*N).trans hb
  have hresp : 0≤VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) (p*q) := by
    linarith only [hgap,hhead]
  have hw := pairWeight_nonneg (by linarith : 0≤u) N p q
  rw [originalPair_eq_weight,semiprimeBoundary,← sub_mul,← Complex.ofReal_sub]
  simp only [scalar_character_norm]
  rw [show pairWeight u N p q*VaughanLogAverage.riesz
      (SquarefreeVaughanLogSource.length u N) (p*q)-
      pairWeight u N p q*(SquarefreeVaughanLogSource.length u N-log p)*
        ownerWeight N (log q/(log p+log q))=
      pairWeight u N p q*(VaughanLogAverage.riesz
        (SquarefreeVaughanLogSource.length u N) (p*q)-
        (SquarefreeVaughanLogSource.length u N-log p)*
          ownerWeight N (log q/(log p+log q))) by ring,
    abs_of_nonneg (mul_nonneg hw hgap),
    abs_of_nonneg (mul_nonneg hw hresp),
    abs_of_nonneg (by simpa only [mul_assoc] using mul_nonneg hw hhead)]
  ring

/-- This boundary is the NEGATIVE original semiprime atom, with the
same physical kernel and prime sieve. No surrogate count weight occurs. -/
theorem boundary_re_eq_neg_literal (u y : ℝ) (N : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) :
    (semiprimeBoundary u y N p q).re=
      -(((u : ℂ)^(N+1)*SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) (p*q)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)).re)*
        ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) q := by
  have hcop := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hs := Nat.squarefree_mul_iff.mpr ⟨hcop,hp.squarefree,hq.squarefree⟩
  have hnp := Nat.not_prime_mul hp.ne_one hq.ne_one
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hk := ZetaRieszCosineCarrier.re_filterKernel_one N y (p*q : ℕ)
  have hk' : (zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)).re=
      exp (-(3/2 : ℝ)*log (p*q : ℕ))*log (p*q : ℕ)^N/N.factorial*
        cos (y*log (p*q : ℕ)) := by
    simpa only [zetaPrimeFilterKernel,ZetaRieszCosineCarrier.factorialPolynomial_one,
      zetaPrimeLogKernel,zetaPrimeFeature,neg_mul] using hk
  have he : exp (-(3/2 : ℝ)*log (p*q : ℕ))=
      exp (-log (p*q : ℕ)/2)/((p*q : ℕ) : ℝ) := by
    rw [show -(3/2 : ℝ)*log (p*q : ℕ)=
      -log (p*q : ℕ)/2+-log (p*q : ℕ) by ring,exp_add,exp_neg,
        exp_log (by exact_mod_cast Nat.mul_pos hp.pos hq.pos)]
    ring
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩]
  simp only [semiprimeBoundary,pairWeight,if_pos hq,
    ← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,character_re]
  rw [hk',he,hlog]
  simp only [ZetaRieszSmoothOwnerDiscrepancy.radial,Nat.cast_mul]
  ring

private theorem head_norm_eq_zero_height {u : ℝ} (hu : 1/2≤u)
    {N p q : ℕ} (hN : 64≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p) (y : ℝ) :
    ‖originalPair u y N p q‖=pairAmount u 0 N p q := by
  have hn := originalPair_norm hN hp hq y
  have hr := originalPair_re u 0 N p q
  have ha := (rawAmount_bounds (by linarith : 0≤u) hN hp hq (owner_log_le_length hp)).1
  rw [abs_of_nonneg ha] at hn
  rw [← hr]
  simp only [originalPair,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero,character_re,zero_mul,cos_zero,mul_one]
  exact hn

/-- Join the WHOLE original head population with its matched global
semiprime boundary. Composite cofactor slots are exactly zero. -/
theorem matched_boundary_norm_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) (y : ℝ) :
    ‖(∑ p∈owners u N,∑ q∈pairInterval N p,semiprimeBoundary u y N p q)-
      originalHead u y N‖≤
      (∑ p∈owners u N,∑ q∈pairInterval N p,‖semiprimeBoundary u y N p q‖)-
        ZetaRieszRoughPrimePairCancellation.nativeHead u 0 N := by
  rw [originalHead,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have he : (∑ p∈owners u N,∑ q∈pairInterval N p,
      ‖semiprimeBoundary u y N p q-originalPair u y N p q‖)=
      (∑ p∈owners u N,∑ q∈pairInterval N p,‖semiprimeBoundary u y N p q‖)-
        ZetaRieszRoughPrimePairCancellation.nativeHead u 0 N := by
    rw [nativeHead_eq_sum_pairAmount,← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqp : q.Prime
    · rw [boundary_sub_head_norm hu hU hN hp hq hqp y,
        head_norm_eq_zero_height hu (by omega : 64≤N) hp hq y]
    · simp [semiprimeBoundary,pairWeight,originalPair,rawAmount,pairAmount,hqp]
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => norm_sum_le _ _))).trans_eq he

/-- A concrete one-sided estimate for this JOINED auxiliary boundary.
It is not the whole floor: the prime and raw high-owner boundaries stay
outside this statement and have not been paid. -/
theorem matched_boundary_real_floor {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hN : 65536≤N) (y : ℝ) :
    ZetaRieszRoughPrimePairCancellation.nativeHead u 0 N-
      (∑ p∈owners u N,∑ q∈pairInterval N p,‖semiprimeBoundary u y N p q‖)≤
      ((∑ p∈owners u N,∑ q∈pairInterval N p,semiprimeBoundary u y N p q)-
        originalHead u y N).re := by
  have hh := matched_boundary_norm_bound hu hU hN y
  have hr := (Complex.abs_re_le_norm ((∑ p∈owners u N,∑ q∈pairInterval N p,
    semiprimeBoundary u y N p q)-originalHead u y N)).trans hh
  linarith only [(abs_le.mp hr).1]

end RiemannGaussian.ZetaRieszGlobalCompletionBoundary
