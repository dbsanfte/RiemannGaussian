/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedHeadCancellation
import RiemannGaussian.ZetaRieszPrefixCorrelation
import RiemannGaussian.ZetaRieszPairFloorAllMultiplicity

/-!
# The full factorial prime-cofactor head is not rectangle-cancelled

The old allocation requires a composite cofactor. Consequently its assigned
share is exactly zero on every product of two distinct ordinary primes,
regardless of the finite physical prime selection or the factorial order.
The rectangle-marked head vanishes, but its full-mass complement is the
entire nonzero semiprime response. Swapping the marked incidence does not
negate this response.

The separate, existing literal retained pair ledger has a nonzero source
at every exposed analytic multiplicity. No identification of that ledger
with an arbitrary completed cofactor series is assumed. These theorems
reject the proposed free head-completion shortcut; they prove no ceiling.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical

namespace RiemannGaussian.ZetaRieszCeilingHeadCompletionAudit
open ZetaRieszJointAllocation ZetaRieszJointOwnerTransfer

/-- Deleting any marked prime from a two-prime label leaves a prime,
so it fails the original COMPOSITE-cofactor eligibility condition. -/
theorem prime_pair_not_eligible {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : b ∈ (p*q).primeFactors) : ¬eligibleCofactor b (p*q/b) := by
  have hbp := Nat.prime_of_mem_primeFactors hb
  have hd := Nat.dvd_of_mem_primeFactors hb
  rcases hbp.dvd_mul.mp hd with hd | hd
  · have he := (Nat.prime_dvd_prime_iff_eq hbp hp).mp hd
    subst b
    rw [Nat.mul_div_cancel_left q hp.pos]
    exact fun h => h.2.2.1 hq
  · have he := (Nat.prime_dvd_prime_iff_eq hbp hq).mp hd
    subst b
    rw [mul_comm p q,Nat.mul_div_cancel_left p hq.pos]
    exact fun h => h.2.2.1 hp

/-- No upper/lower binomial tail is needed for this head: the exact
assigned amplitude is zero, including factorial orders zero and one. -/
theorem assignedAmplitude_prime_pair (A : Finset ℕ) (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    assignedAmplitude A N (p*q)=0 := by
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro k _
  exact if_neg (fun h => prime_pair_not_eligible hp hq hb h.2)

/-- The original old-allocation share vanishes on every semiprime.
This concerns `boundedShare`, not the unrelated marked rectangle weight. -/
theorem boundedShare_prime_pair (A : Finset ℕ) (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    boundedShare A N (p*q)=0 := by
  unfold boundedShare allocationShare
  rw [assignedAmplitude_prime_pair A N hp hq]
  simp

/-- Thus an ordinary-prime cofactor added by FULL factorial completion
keeps its entire original coefficient, at every physical selection. -/
theorem residualCoefficient_prime_pair (A : Finset ℕ) (L : ℝ) (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    residualCoefficient A L N (p*q)=SquarefreeVaughanLogSource.coefficient L (p*q) := by
  simp only [residualCoefficient,boundedShare_prime_pair A N hp hq,sub_zero,
    Complex.ofReal_one,one_mul]

/-- In the strict inner physical geometry, prime deletion gives the
same NEGATIVE response for each marked incidence. -/
theorem prime_cofactor_hinge_difference {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {L : ℝ} (hpL : log p ≤ L) (hqL : log q ≤ L)
    (hLT : L ≤ log (p*q : ℕ)) :
    VaughanLogAverage.riesz (L-log p) q-VaughanLogAverage.riesz L q=
      L-log (p*q : ℕ) := by
  have hpd : ¬p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hr := ZetaRieszPrefixCorrelation.riesz_semiprime_inner hq hp hpd hqL hpL hLT
  rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpd] at hr
  linarith only [hr]

/-- Incidence swapping cannot cancel this completed head: the two
literal translated responses agree, retaining the common product phase. -/
theorem marked_incidence_head_equal {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {L : ℝ} (hpL : log p ≤ L) (hqL : log q ≤ L)
    (hLT : L ≤ log (p*q : ℕ)) :
    VaughanLogAverage.riesz (L-log p) q-VaughanLogAverage.riesz L q=
      VaughanLogAverage.riesz (L-log q) p-VaughanLogAverage.riesz L p := by
  rw [prime_cofactor_hinge_difference hp hq hpq hpL hqL hLT,
    prime_cofactor_hinge_difference hq hp hpq.symm hqL hpL (by simpa [mul_comm] using hLT)]
  simp only [mul_comm]

/-- The arithmetic coefficient is strictly negative, independently of
height. Its complex atom still carries the original oscillating phase. -/
theorem residual_coefficient_negative (A : Finset ℕ) (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {L : ℝ} (hL : 0<L) (hpL : log p ≤ L) (hqL : log q ≤ L)
    (hLT : L<log (p*q : ℕ)) :
    (residualCoefficient A L N (p*q)).re<0 := by
  rw [residualCoefficient_prime_pair A L N hp hq,
    ZetaRieszPrefixCorrelation.coefficient_semiprime_inner hq hp
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)) hqL hpL hLT.le,
    Complex.ofReal_re]
  have ht : 0<log (p*q : ℕ) := hL.trans hLT
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ht)
    (sub_pos.mpr hLT)) hL

/-- Exact norm of the added full-factorial head. It is POSITIVE in the
strict inner geometry, with no relaxation of allocation or of the phase. -/
theorem residual_atom_norm (A : Finset ℕ) (N : ℕ) (y : ℝ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {L : ℝ} (hL : 0<L) (hpL : log p ≤ L) (hqL : log q ≤ L)
    (hLT : L<log (p*q : ℕ)) :
    ‖residualCoefficient A L N (p*q)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)‖=
      (log (p*q : ℕ)*(log (p*q : ℕ)-L)/L)*
        (log (p*q : ℕ)^N/(N.factorial : ℝ)*exp (-(3/2 : ℝ)*log (p*q : ℕ))) := by
  rw [norm_mul,residualCoefficient_prime_pair A L N hp hq,
    ZetaRieszPrefixCorrelation.coefficient_semiprime_inner hq hp
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)) hqL hpL hLT.le,
    Complex.norm_real,Real.norm_eq_abs]
  have ht : 0<log (p*q : ℕ) := hL.trans hLT
  rw [abs_of_neg (div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos ht) (sub_pos.mpr hLT)) hL),
    norm_zetaPrimeLogKernel]
  norm_num [zetaPrimeExpWeight]
  ring

/-- Removing the marked rectangle leaves the ENTIRE completed prime
head in its complement. Rectangle cancellation cannot be spent twice. -/
theorem rectangle_complement_keeps_full_head (A : Finset ℕ) (L y : ℝ) (N : ℕ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ((1-markedWeight N (p*q) p : ℝ) : ℂ)*
      (residualCoefficient A L N (p*q)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q))=
    SquarefreeVaughanLogSource.coefficient L (p*q)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q) := by
  rw [ZetaRieszJoinedHeadCancellation.markedWeight_prime_cofactor hp hq,
    residualCoefficient_prime_pair A L N hp hq]
  simp

/-- A nonzero prime head really exists for all factorial orders and
heights; this is an ACTUAL pair, not a synthetic mode or a native core
enumeration. Fixed finite labels are not claimed to carry a cofinal source. -/
theorem explicit_prime_head_nonzero (A : Finset ℕ) (N : ℕ) (y : ℝ) :
    residualCoefficient A (log (7 : ℝ)+log 5/2) N (7*5)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (7*5) ≠ 0 := by
  have h7 : Nat.Prime 7 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have hx : 0<log (7 : ℝ) := log_pos (by norm_num)
  have hz : 0<log (5 : ℝ) := log_pos (by norm_num)
  have hlog : log (7*5 : ℕ)=log (7 : ℝ)+log 5 := by
    rw [Nat.cast_mul,log_mul (by norm_num) (by norm_num)]
    norm_num
  have h57 : log (5 : ℝ) ≤ log 7 := log_le_log (by norm_num) (by norm_num)
  have hn := residual_atom_norm A N y h7 h5 (by norm_num)
    (by linarith : 0<log (7 : ℝ)+log 5/2)
    (by linarith) (by linarith) (by rw [hlog]; linarith)
  apply norm_ne_zero_iff.mp
  rw [hn,hlog]
  have ht : 0<log (7 : ℝ)+log 5 := by linarith
  have hd : 0<log (7 : ℝ)+log 5-(log 7+log 5/2) := by linarith
  have hden : 0<log (7 : ℝ)+log 5/2 := by linarith
  exact (by positivity : (log 7+log 5)*
    (log 7+log 5-(log 7+log 5/2))/(log 7+log 5/2)*
    ((log 7+log 5)^N/(N.factorial : ℝ)*exp (-(3/2 : ℝ)*(log 7+log 5)))>0).ne'

open ZetaRieszPairPrefixPayment ZetaRieszMaskSupport ZetaRieszWideOwnerAudit

/-- The previously retained literal pair correction has a strictly
positive cofinal real source. This does not identify an arbitrary
cofactor completion with that particular checked ledger. -/
theorem eventually_retained_pair_correction_gt (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤radiusCeiling) :
    ∀ᶠ N in atTop, (399/5000 : ℝ)<(prefixPairDefect (3/2-rho.1.re) rho.1.im N).re := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszPairFloorAllMultiplicity.tendsto_prefix_exact_source rho hrho hexposed hU)
  simp only [Complex.ofReal_re] at hs
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  exact hs.eventually_const_lt (ZetaRieszPairFloorAllMultiplicity.target_lt_multiple_source
    hu hU (analyticZetaZeroMultiplicity_positive rho))

/-- A double exposed zero leaves a head-correction real source above
319/1000. The upper geometric bound for omitted radial labels cannot pay
this retained source, even though those omitted labels are negligible. -/
theorem eventually_multiple_pair_correction_gt (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤radiusCeiling) (hm : 2≤analyticZetaZeroMultiplicity rho) :
    ∀ᶠ N in atTop, (319/1000 : ℝ)<(prefixPairDefect (3/2-rho.1.re) rho.1.im N).re := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszPairFloorAllMultiplicity.tendsto_prefix_exact_source rho hrho hexposed hU)
  simp only [Complex.ofReal_re] at hs
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  have hmR : (2 : ℝ)≤analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  have hsq : (4 : ℝ)≤(analyticZetaZeroMultiplicity rho : ℝ)^2 := by nlinarith only [hmR]
  have hh := mul_le_mul_of_nonneg_right hsq (by linarith : 0≤1-retainedCost (3/2-rho.1.re))
  exact hs.eventually_const_lt (by nlinarith only [hc,hh])

/-- In particular the SAME literal retained pair correction is not a
source-o(1) completion error. This is conditional on a candidate exposed
zero; it is not a zero existence or zero exclusion theorem. -/
theorem retained_pair_correction_not_tendsto_zero (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤radiusCeiling) :
    ¬Tendsto (prefixPairDefect (3/2-rho.1.re) rho.1.im) atTop (𝓝 0) := by
  intro hz
  have hr := Complex.continuous_re.tendsto _ |>.comp hz
  have he := eventually_retained_pair_correction_gt rho hrho hexposed hU
  have h := ge_of_tendsto hr (he.mono fun _ h => h.le)
  norm_num at h

end RiemannGaussian.ZetaRieszCeilingHeadCompletionAudit
