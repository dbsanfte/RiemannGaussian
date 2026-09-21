/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReflectedLinear
import RiemannGaussian.TripleRieszProfile

/-!
# Exact cutoff corrections for symmetric three-prime operators

The reflected-linear polynomial is not the coefficient of every balanced
triple. The pair-cutoff hinges stay explicit, including their complex
observation. No smallness of that correction is asserted.
-/

namespace RiemannGaussian.ZetaRieszSymmetricOperators
noncomputable section
open scoped BigOperators Classical
open ZetaRieszReflectedLinear ZetaRieszTriplePrime ZetaSquarefreeRieszWindows

/-- When all pair products are below the cutoff, the complete
three-prime profile is L-log(n), not log(n)-2L. -/
theorem tripleDifference_eq_lower_gap {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hab : a+b ≤ L) (hac : a+c ≤ L) (hbc : b+c ≤ L)
    (ht : L ≤ a+b+c) : tripleDifference a b c L = L-(a+b+c) := by
  simp only [tripleDifference, primePairTent, max_def]
  split_ifs <;> linarith

/-- The proposed reflected-linear coefficient on its actual class. -/
theorem linearCoefficient_three {L : ℝ} {n : ℕ} (hn : LinearClass L n)
    (hk : n.primeFactors.card = 3) :
    linearCoefficient L n = (Real.log n/L)*(2*L-Real.log n) := by
  rw [linearCoefficient, moebius_eq_primeCount hn.1, hk]
  norm_num

/-- The discrepancy from the reflected-linear formula is the sum of
three exact pair-cutoff hinges. No phase or sign is discarded. -/
theorem three_profile_with_pair_hinges {a b c L : ℝ}
    (ha : 0 ≤ a) (haL : a ≤ L) (hbL : b ≤ L) (hcL : c ≤ L)
    (ht : L ≤ a+b+c) :
    -tripleDifference a b c L = 2*L-(a+b+c) -
      (max 0 (L-a-b)+max 0 (L-a-c)+max 0 (L-b-c)) := by
  rw [TripleRieszProfile.tripleDifference_eq_pair_hinges ha haL hbL hcL ht]
  ring

private theorem product_data {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Squarefree (p*(q*r)) ∧ ¬(p*(q*r)).Prime := by
  have hqr' : q.Coprime r := hq.coprime_iff_not_dvd.mpr
    (fun h => hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp h))
  have hcop : p.Coprime (q*r) := hp.coprime_iff_not_dvd.mpr (by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h))
  exact ⟨Nat.squarefree_mul_iff.mpr ⟨hcop,hp.squarefree,
    Nat.squarefree_mul_iff.mpr ⟨hqr',hq.squarefree,hr.squarefree⟩⟩,
    Nat.not_prime_mul hp.ne_one (by nlinarith [hq.two_le,hr.two_le])⟩

private theorem log_product {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    Real.log (p*(q*r) : ℕ) = Real.log p+Real.log q+Real.log r := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
    (by exact_mod_cast (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)), Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
  ring

/-- The actual coefficient on the balanced pair-saturated class. -/
theorem coefficient_three_pair_saturated {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {L : ℝ}
    (hab : Real.log p+Real.log q ≤ L) (hac : Real.log p+Real.log r ≤ L)
    (hbc : Real.log q+Real.log r ≤ L) (ht : L ≤ Real.log (p*(q*r) : ℕ)) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*r)) =
      ((Real.log (p*(q*r) : ℕ)/L*(Real.log (p*(q*r) : ℕ)-L) : ℝ) : ℂ) := by
  rw [SquarefreeVaughanLogSource.coefficient, if_pos (product_data hp hq hr hpq hpr hqr),
    riesz_three_primes_eq_difference L hp hq hr hpq hpr hqr,
    tripleDifference_eq_lower_gap (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)
      (Real.log_natCast_nonneg r) hab hac hbc (by rwa [log_product hp hq hr] at ht),
    log_product hp hq hr]
  congr 1
  ring

/-- The linear and balanced polynomials differ at leading order;
the correction cannot be silently treated as a mask deletion. -/
theorem balanced_polynomial_defect (L t : ℝ) :
    (t/L)*(2*L-t) - (t/L)*(t-L) = (t/L)*(3*L-2*t) := by ring

/-- An integer formulation for the actual pair-saturated three-prime
class, using the reflected cutoff and the original prime factors. -/
theorem coefficient_three_reflected_unit {n : ℕ} (hn : Squarefree n)
    (hk : n.primeFactors.card = 3) {L : ℝ} (ht : L ≤ Real.log n)
    (hmin : ∀ p ∈ n.primeFactors, Real.log n-L ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L n =
      (((Real.log n/L)*(Real.log n-L) : ℝ) : ℂ) := by
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩ := exists_three_primes hn hk
  have hpf : (p*(q*r)).primeFactors = {p,q,r} := by
    simp [Nat.primeFactors_mul hp.ne_zero (Nat.mul_ne_zero hq.ne_zero hr.ne_zero),
      Nat.primeFactors_mul hq.ne_zero hr.ne_zero, hp.primeFactors, hq.primeFactors,
      hr.primeFactors, Finset.insert_comm]
  have hpa := hmin p (by simp [hpf])
  have hqa := hmin q (by simp [hpf])
  have hra := hmin r (by simp [hpf])
  rw [log_product hp hq hr] at hpa hqa hra
  exact coefficient_three_pair_saturated hp hq hr hpq hpr hqr
    (by linarith) (by linarith) (by linarith) ht

/-- The exact factorial operator for the reflected-linear three-prime
polynomial. L is frozen during differentiation. -/
theorem linear_three_kernel_operator {L : ℝ} (hL : L ≠ 0) (N n : ℕ) (s : ℂ) :
    (((Real.log n/L)*(2*L-Real.log n) : ℝ) : ℂ)*zetaPrimeLogKernel N s n =
      2*((N+1 : ℕ) : ℂ)*zetaPrimeLogKernel (N+1) s n -
        (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))*zetaPrimeLogKernel (N+2) s n := by
  have h1 := ZetaRieszHeadOrders.log_mul_kernel N n s
  have h2 := ZetaRieszHeadOrders.log_mul_kernel (N+1) n s
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]
  rw [show N+1+1 = N+2 by omega] at h2
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  field_simp [hLc]
  norm_num only [Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
  linear_combination (2*(L : ℂ)-(Real.log n : ℂ))*h1 - ((N : ℂ)+1)*h2

/-- The balanced class uses the opposite adjacent-moment combination. -/
theorem balanced_three_kernel_operator {L : ℝ} (hL : L ≠ 0) (N n : ℕ) (s : ℂ) :
    (((Real.log n/L)*(Real.log n-L) : ℝ) : ℂ)*zetaPrimeLogKernel N s n =
      (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))*zetaPrimeLogKernel (N+2) s n -
        ((N+1 : ℕ) : ℂ)*zetaPrimeLogKernel (N+1) s n := by
  have h1 := ZetaRieszHeadOrders.log_mul_kernel N n s
  have h2 := ZetaRieszHeadOrders.log_mul_kernel (N+1) n s
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub]
  rw [show N+1+1 = N+2 by omega] at h2
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  field_simp [hLc]
  norm_num only [Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
  linear_combination ((Real.log n : ℂ)-(L : ℂ))*h1 + ((N : ℂ)+1)*h2

end
end RiemannGaussian.ZetaRieszSymmetricOperators
