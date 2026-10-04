/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairPrefixPayment
import RiemannGaussian.ZetaRieszSkewFactorial

/-!
# Exact cancellation in the joined factorial-prefix convolution

The complete finite pair sum retains both prime phases and the single
repeated-prime diagonal. Its order-zero endpoints cancel algebraically,
before any real part or norm is taken. The literal radial support is not
completed by these identities, and the independent signed floor remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairPrefixConvolution
open ZetaRieszJointAllocation ZetaRieszOwnerMaximal
open ZetaRieszHeadOrders ZetaRieszPrimePairConvolution ZetaPrimeCofactorCompletion
open ZetaRieszPairPrefixPayment

/-- Both complementary orders exceed the exact lower-prefix endpoint. -/
def centralOrders (M K : ℕ) : Finset ℕ :=
  (Finset.range (M+1)).filter (fun k => K < k ∧ K < M-k)

/-- Reflection preserves every complex product in the upper prefix. -/
theorem reflected_prefix (v : ℕ → ℂ) (M K : ℕ) (hK : K ≤ M) :
    (∑ k ∈ (Finset.range (M+1)).filter (fun k => M-k ≤ K), v k*v (M-k)) =
      ∑ k ∈ Finset.range (K+1), v k*v (M-k) := by
  have href := Finset.sum_range_reflect
    (fun k => if k ≤ K then v k*v (M-k) else 0) (M+1)
  simp only [Nat.add_sub_cancel] at href
  have he : (∑ k ∈ (Finset.range (M+1)).filter (fun k => M-k ≤ K),
      v k*v (M-k)) = ∑ k ∈ Finset.range (M+1),
      if M-k ≤ K then v (M-k)*v (M-(M-k)) else 0 := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ M := by simpa using Finset.mem_range.mp hk
    simp only [Nat.sub_sub_self hkM, mul_comm]
  rw [he, href]
  have hset : (Finset.range (M+1)).filter (fun k => k ≤ K) = Finset.range (K+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hset]

/-- The two outer prefixes are exactly twice one prefix; no endpoint
is estimated or silently removed. -/
theorem full_convolution_eq_central_add_prefix (v : ℕ → ℂ) (M K : ℕ)
    (hMK : 2*K < M) :
    (∑ k ∈ Finset.range (M+1), v k*v (M-k)) =
      (∑ k ∈ centralOrders M K, v k*v (M-k)) +
        2*(∑ k ∈ Finset.range (K+1), v k*v (M-k)) := by
  have hK : K ≤ M := by omega
  have hlow : (∑ k ∈ (Finset.range (M+1)).filter (fun k => k ≤ K),
      v k*v (M-k)) = ∑ k ∈ Finset.range (K+1), v k*v (M-k) := by
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hp : (∑ k ∈ Finset.range (M+1), v k*v (M-k)) =
      (∑ k ∈ centralOrders M K, v k*v (M-k)) +
      (∑ k ∈ (Finset.range (M+1)).filter (fun k => k ≤ K), v k*v (M-k)) +
      (∑ k ∈ (Finset.range (M+1)).filter (fun k => M-k ≤ K), v k*v (M-k)) := by
    simp only [centralOrders, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ M := by simpa using Finset.mem_range.mp hk
    by_cases hl : k ≤ K
    · have hh : ¬M-k ≤ K := by omega
      simp [hl, hh]
    · by_cases hh : M-k ≤ K
      · simp [hl, hh]
      · simp [hl, hh]
  rw [hlow, reflected_prefix v M K hK] at hp
  rw [hp]
  ring

/-- The actual joined prefix removes both order-zero endpoints exactly.
The remaining low order has an explicit factor `k`; it is a logged leg. -/
theorem joined_convolution_cancel_endpoints (v : ℕ → ℂ) (M K : ℕ)
    (hMK : 2*K < M) (L : ℂ) (hL : L ≠ 0) :
    (M : ℂ)/2*(∑ k ∈ Finset.range (M+1), v k*v (M-k)) -
      (M : ℂ)*(M+1)/(2*L)*(∑ k ∈ Finset.range (M+2), v k*v (M+1-k)) -
      (M : ℂ)/L*(∑ k ∈ Finset.range (K+1),
        (L*v (M-k)-((M-k+1 : ℕ) : ℂ)*v (M-k+1))*v k) =
    (M : ℂ)/2*(∑ k ∈ centralOrders M K, v k*v (M-k)) -
      (M : ℂ)*(M+1)/(2*L)*(∑ k ∈ centralOrders (M+1) K, v k*v (M+1-k)) -
      (M : ℂ)/L*(∑ k ∈ (Finset.range (K+1)).filter (fun k => 0 < k),
        (k : ℂ)*v k*v (M+1-k)) := by
  have hnext : 2*K < M+1 := by omega
  rw [full_convolution_eq_central_add_prefix v M K hMK,
    show M+2 = (M+1)+1 by omega,
    full_convolution_eq_central_add_prefix v (M+1) K hnext]
  have hlog : (∑ k ∈ Finset.range (K+1),
      (L*v (M-k)-((M-k+1 : ℕ) : ℂ)*v (M-k+1))*v k) =
      L*(∑ k ∈ Finset.range (K+1), v k*v (M-k)) -
      (M+1 : ℂ)*(∑ k ∈ Finset.range (K+1), v k*v (M+1-k)) +
      (∑ k ∈ (Finset.range (K+1)).filter (fun k => 0 < k),
        (k : ℂ)*v k*v (M+1-k)) := by
    simp only [Finset.mul_sum, Finset.sum_filter,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ M := by have := Finset.mem_range.mp hk; omega
    have hc : ((M+1-k : ℕ) : ℂ) = (M+1 : ℂ)-(k : ℂ) := by
      rw [Nat.cast_sub (by omega : k ≤ M+1)]
      push_cast
      ring
    rw [show M-k+1 = M+1-k by omega, hc]
    by_cases hk0 : 0 < k
    · simp only [if_pos hk0]
      ring
    · have he : k = 0 := by omega
      subst k
      simp
      ring
  rw [hlog]
  field_simp [hL]
  ring

/-- Polarization retains the prime assigned to each factorial order.
Joining both swapped incidences cancels the same endpoints pointwise. -/
theorem mixed_convolution_cancel_endpoints (a b : ℕ → ℂ) (M K : ℕ)
    (hMK : 2*K < M) (L : ℂ) (hL : L ≠ 0) :
    (M : ℂ)/2*(∑ k ∈ Finset.range (M+1), (a k*b (M-k)+b k*a (M-k))) -
      (M : ℂ)*(M+1)/(2*L)*
        (∑ k ∈ Finset.range (M+2), (a k*b (M+1-k)+b k*a (M+1-k))) -
      (M : ℂ)/L*(∑ k ∈ Finset.range (K+1),
        ((L*a (M-k)-((M-k+1 : ℕ) : ℂ)*a (M-k+1))*b k+
        (L*b (M-k)-((M-k+1 : ℕ) : ℂ)*b (M-k+1))*a k)) =
    (M : ℂ)/2*(∑ k ∈ centralOrders M K, (a k*b (M-k)+b k*a (M-k))) -
      (M : ℂ)*(M+1)/(2*L)*
        (∑ k ∈ centralOrders (M+1) K, (a k*b (M+1-k)+b k*a (M+1-k))) -
      (M : ℂ)/L*(∑ k ∈ (Finset.range (K+1)).filter (fun k => 0 < k),
        (k : ℂ)*(a k*b (M+1-k)+b k*a (M+1-k))) := by
  have hab := joined_convolution_cancel_endpoints (fun k => a k+b k) M K hMK L hL
  have ha := joined_convolution_cancel_endpoints a M K hMK L hL
  have hb := joined_convolution_cancel_endpoints b M K hMK L hL
  simp only [add_mul, mul_add, sub_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc] at hab ha hb ⊢
  linear_combination hab-ha-hb

/-- The binomial prefix is exactly a prefix of the two factorial legs,
including order zero and the original complex product phase. -/
theorem prefix_mass_kernel (M K p q : ℕ) (hK : K ≤ M)
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p*q) (s : ℂ) :
    (lowerMass M K (Real.log q/Real.log (p*q : ℕ)) : ℂ)*
      zetaPrimeLogKernel M s (p*q) =
        ∑ k ∈ Finset.range (K+1),
          zetaPrimeLogKernel (M-k) s p*zetaPrimeLogKernel k s q := by
  simp only [lowerMass, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkM : k ≤ M := by have := Finset.mem_range.mp hk; omega
  have h := ZetaRieszSkewAllocation.split_mass_kernel M k q p hkM hq hp
    (by simpa [mul_comm] using hpq) s
  simpa only [mul_comm q p, mul_comm (zetaPrimeLogKernel k s q)] using h

/-- The product logarithm and its exact prefix become one shifted
factorial convolution, without a share-cutoff approximation. -/
theorem logged_prefix_kernel (N K p q : ℕ) (hK : K ≤ N+1)
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p*q) (s : ℂ) :
    (Real.log (p*q : ℕ) : ℂ)*
      (lowerMass (N+1) K (Real.log q/Real.log (p*q : ℕ)) : ℂ)*
      zetaPrimeLogKernel N s (p*q) =
        (N+1 : ℂ)*(∑ k ∈ Finset.range (K+1),
          zetaPrimeLogKernel (N+1-k) s p*zetaPrimeLogKernel k s q) := by
  calc
    _ = (lowerMass (N+1) K (Real.log q/Real.log (p*q : ℕ)) : ℂ)*
      ((Real.log (p*q : ℕ) : ℂ)*zetaPrimeLogKernel N s (p*q)) := by ring
    _ = _ := by
      rw [log_mul_kernel, mul_left_comm, prefix_mass_kernel _ _ _ _ hK hp hq hpq]
      push_cast
      rfl

/-- The finite factorial product law on two literal factors, with both
phases retained and no completion. -/
theorem pair_kernel_convolution (M p q : ℕ) (hp : 0 < p) (hq : 0 < q) (s : ℂ) :
    zetaPrimeLogKernel M s (p*q) = ∑ k ∈ Finset.range (M+1),
      zetaPrimeLogKernel k s p*zetaPrimeLogKernel (M-k) s q := by
  have h := ordered_kernel_eq_convolution {p} {q}
    (fun a ha => by have he := Finset.mem_singleton.mp ha; subst a; exact hp)
    (fun b hb => by have he := Finset.mem_singleton.mp hb; subst b; exact hq) M s
  simpa only [finiteMoment, Finset.sum_singleton] using h

/-- A single joined coefficient is exactly the full factorial pair
kernel minus its two logged prefixes. This holds before summing primes. -/
theorem prefix_atom_eq (N : ℕ) (L : ℝ) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p*q) (s : ℂ) :
    (prefixLogCoefficient N L (Real.log p) (Real.log q) : ℂ)*
      zetaPrimeLogKernel N s (p*q) =
    (N+1 : ℂ)*zetaPrimeLogKernel (N+1) s (p*q) -
      (N+1 : ℂ)*(N+2)/(L : ℂ)*zetaPrimeLogKernel (N+2) s (p*q) -
      (N+1 : ℂ)/(L : ℂ)*
        ((L-Real.log p : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
          zetaPrimeLogKernel (N+1-k) s p*zetaPrimeLogKernel k s q) +
         (L-Real.log q : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
          zetaPrimeLogKernel (N+1-k) s q*zetaPrimeLogKernel k s p)) := by
  have hK : 13*N/32 ≤ N+1 := by omega
  have hlog : Real.log p+Real.log q = Real.log (p*q : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have hpref := logged_prefix_kernel N (13*N/32) p q hK hp hq hpq s
  have hqref := logged_prefix_kernel N (13*N/32) q p hK hq hp
    (by simpa [mul_comm] using hpq) s
  rw [mul_comm q p] at hqref
  have hfull := log_mul_kernel N (p*q) s
  have hfull' := log_mul_kernel (N+1) (p*q) s
  simp only [Nat.cast_add, Nat.cast_one] at hfull hfull'
  simp only [prefixLogCoefficient, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, hlog]
  calc
    _ = (Real.log (p*q : ℕ) : ℂ)*zetaPrimeLogKernel N s (p*q) -
        (Real.log (p*q : ℕ) : ℂ)/(L : ℂ)*
          ((Real.log (p*q : ℕ) : ℂ)*zetaPrimeLogKernel N s (p*q)) -
        ((L-Real.log p : ℂ)/(L : ℂ))*
          ((Real.log (p*q : ℕ) : ℂ)*
            (lowerMass (N+1) (13*N/32) (Real.log q/Real.log (p*q : ℕ)) : ℂ)*
              zetaPrimeLogKernel N s (p*q)) -
        ((L-Real.log q : ℂ)/(L : ℂ))*
          ((Real.log (p*q : ℕ) : ℂ)*
            (lowerMass (N+1) (13*N/32) (Real.log p/Real.log (p*q : ℕ)) : ℂ)*
              zetaPrimeLogKernel N s (p*q)) := by ring
    _ = _ := by
      rw [hpref, hqref, hfull]
      have he : (Real.log (p*q : ℕ) : ℂ)/(L : ℂ)*
          ((N+1 : ℂ)*zetaPrimeLogKernel (N+1) s (p*q)) =
          (N+1 : ℂ)/(L : ℂ)*
          ((Real.log (p*q : ℕ) : ℂ)*zetaPrimeLogKernel (N+1) s (p*q)) := by ring
      rw [he, hfull']
      ring

/-- Cancellation already holds on one literal pair with both swapped
factorial incidences. ANY common radial/period/physical mask can multiply
this equality before summation; no prime support needs to be completed. -/
theorem prefix_atom_eq_central_logged (N : ℕ) (L : ℝ) (hL : L ≠ 0) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p*q) (s : ℂ) :
    (prefixLogCoefficient N L (Real.log p) (Real.log q) : ℂ)*
      zetaPrimeLogKernel N s (p*q) =
    (N+1 : ℂ)/2*(∑ k ∈ centralOrders (N+1) (13*N/32),
      (zetaPrimeLogKernel k s p*zetaPrimeLogKernel (N+1-k) s q+
       zetaPrimeLogKernel k s q*zetaPrimeLogKernel (N+1-k) s p)) -
      (N+1 : ℂ)*(N+2)/(2*(L : ℂ))*(∑ k ∈ centralOrders (N+2) (13*N/32),
        (zetaPrimeLogKernel k s p*zetaPrimeLogKernel (N+2-k) s q+
         zetaPrimeLogKernel k s q*zetaPrimeLogKernel (N+2-k) s p)) -
      (N+1 : ℂ)/(L : ℂ)*(∑ k ∈ (Finset.range (13*N/32+1)).filter (fun k => 0 < k),
        (k : ℂ)*(zetaPrimeLogKernel k s p*zetaPrimeLogKernel (N+2-k) s q+
          zetaPrimeLogKernel k s q*zetaPrimeLogKernel (N+2-k) s p)) := by
  have hMK : 2*(13*N/32) < N+1 := by omega
  have h := mixed_convolution_cancel_endpoints
    (fun k => zetaPrimeLogKernel k s p) (fun k => zetaPrimeLogKernel k s q)
    (N+1) (13*N/32) hMK (L : ℂ) (Complex.ofReal_ne_zero.mpr hL)
  have hproduct (M : ℕ) :
      (∑ k ∈ Finset.range (M+1),
        (zetaPrimeLogKernel k s p*zetaPrimeLogKernel (M-k) s q+
         zetaPrimeLogKernel k s q*zetaPrimeLogKernel (M-k) s p)) =
        2*zetaPrimeLogKernel M s (p*q) := by
    rw [Finset.sum_add_distrib, ← pair_kernel_convolution M p q hp hq s,
      ← pair_kernel_convolution M q p hq hp s, mul_comm q p]
    ring
  rw [hproduct, hproduct] at h
  have hprefix :
      (L-Real.log p : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
        zetaPrimeLogKernel (N+1-k) s p*zetaPrimeLogKernel k s q) +
      (L-Real.log q : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
        zetaPrimeLogKernel (N+1-k) s q*zetaPrimeLogKernel k s p) =
      ∑ k ∈ Finset.range (13*N/32+1),
        (((L : ℂ)*zetaPrimeLogKernel (N+1-k) s p-
            ((N+1-k+1 : ℕ) : ℂ)*zetaPrimeLogKernel (N+1-k+1) s p)*zetaPrimeLogKernel k s q+
         ((L : ℂ)*zetaPrimeLogKernel (N+1-k) s q-
            ((N+1-k+1 : ℕ) : ℂ)*zetaPrimeLogKernel (N+1-k+1) s q)*zetaPrimeLogKernel k s p) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hp' := log_mul_kernel (N+1-k) p s
    have hq' := log_mul_kernel (N+1-k) q s
    linear_combination -(zetaPrimeLogKernel k s q)*hp'-(zetaPrimeLogKernel k s p)*hq'
  rw [← hprefix] at h
  have ha := prefix_atom_eq N L p q hp hq hpq s
  simp only [Nat.cast_add, Nat.cast_one] at h
  linear_combination ha+h

/-- Summing one exact logged prefix keeps the two finite prime arrays
coupled. The logarithm is a factorial shift, not an absolute cost. -/
theorem ordered_logged_prefix (A : Finset ℕ) (M K : ℕ) (s L : ℂ) :
    (∑ p ∈ A, ∑ q ∈ A, (L-(Real.log p : ℂ))*
      (∑ k ∈ Finset.range (K+1),
        zetaPrimeLogKernel (M-k) s p*zetaPrimeLogKernel k s q)) =
    ∑ k ∈ Finset.range (K+1),
      (L*finiteMoment A (M-k) s-((M-k+1 : ℕ) : ℂ)*finiteMoment A (M-k+1) s)*
        finiteMoment A k s := by
  simp only [Finset.mul_sum]
  calc
    _ = ∑ p ∈ A, ∑ k ∈ Finset.range (K+1), ∑ q ∈ A,
        (L-(Real.log p : ℂ))*
          (zetaPrimeLogKernel (M-k) s p*zetaPrimeLogKernel k s q) := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.range (K+1), ∑ p ∈ A, ∑ q ∈ A,
        (L-(Real.log p : ℂ))*
          (zetaPrimeLogKernel (M-k) s p*zetaPrimeLogKernel k s q) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have hleg : L*finiteMoment A (M-k) s-
          ((M-k+1 : ℕ) : ℂ)*finiteMoment A (M-k+1) s =
          ∑ p ∈ A, (L-(Real.log p : ℂ))*zetaPrimeLogKernel (M-k) s p := by
        simp only [finiteMoment, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p _
        have hl := log_mul_kernel (M-k) p s
        linear_combination hl
      rw [hleg]
      simp only [finiteMoment, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm

/-- The full finite ordered pair sum of the current coefficient is
exactly its joined factorial convolution. No phase or diagonal is removed. -/
theorem ordered_prefix_eq_convolution (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (L : ℝ) (s : ℂ) :
    (∑ p ∈ A, ∑ q ∈ A,
      (prefixLogCoefficient N L (Real.log p) (Real.log q) : ℂ)*
        zetaPrimeLogKernel N s (p*q)) =
    (N+1 : ℂ)*(∑ k ∈ Finset.range (N+2),
      finiteMoment A k s*finiteMoment A (N+1-k) s) -
      (N+1 : ℂ)*(N+2)/(L : ℂ)*(∑ k ∈ Finset.range (N+3),
        finiteMoment A k s*finiteMoment A (N+2-k) s) -
      2*(N+1 : ℂ)/(L : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
        ((L : ℂ)*finiteMoment A (N+1-k) s-
          ((N+1-k+1 : ℕ) : ℂ)*finiteMoment A (N+1-k+1) s)*finiteMoment A k s) := by
  have hatom : (∑ p ∈ A, ∑ q ∈ A,
      (prefixLogCoefficient N L (Real.log p) (Real.log q) : ℂ)*
        zetaPrimeLogKernel N s (p*q)) =
      ∑ p ∈ A, ∑ q ∈ A, (
        (N+1 : ℂ)*zetaPrimeLogKernel (N+1) s (p*q) -
          (N+1 : ℂ)*(N+2)/(L : ℂ)*zetaPrimeLogKernel (N+2) s (p*q) -
          (N+1 : ℂ)/(L : ℂ)*
            ((L-Real.log p : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
              zetaPrimeLogKernel (N+1-k) s p*zetaPrimeLogKernel k s q) +
             (L-Real.log q : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
              zetaPrimeLogKernel (N+1-k) s q*zetaPrimeLogKernel k s p))) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact prefix_atom_eq N L p q (hA p hp).pos (hA q hq).pos
      (by have := (hA p hp).two_le; have := (hA q hq).two_le; nlinarith) s
  have hswap : (∑ p ∈ A, ∑ q ∈ A, (L-Real.log q : ℂ)*
      (∑ k ∈ Finset.range (13*N/32+1),
        zetaPrimeLogKernel (N+1-k) s q*zetaPrimeLogKernel k s p)) =
      ∑ k ∈ Finset.range (13*N/32+1),
        ((L : ℂ)*finiteMoment A (N+1-k) s-
          ((N+1-k+1 : ℕ) : ℂ)*finiteMoment A (N+1-k+1) s)*finiteMoment A k s := by
    rw [Finset.sum_comm]
    exact ordered_logged_prefix A (N+1) (13*N/32) s (L : ℂ)
  have hpull := ordered_logged_prefix A (N+1) (13*N/32) s (L : ℂ)
  simp only [← Finset.mul_sum] at hpull
  rw [hatom]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ordered_kernel_eq_convolution A A (fun p hp => (hA p hp).pos)
      (fun p hp => (hA p hp).pos),
    ordered_kernel_eq_convolution A A (fun p hp => (hA p hp).pos)
      (fun p hp => (hA p hp).pos),
    hpull, hswap]
  ring

/-- On the repo's exact integer prefix, the complete finite ordered
response has no order-zero leg after joining the correction. -/
theorem ordered_prefix_eq_central_logged (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (L : ℝ) (hL : L ≠ 0) (s : ℂ) :
    (∑ p ∈ A, ∑ q ∈ A,
      (prefixLogCoefficient N L (Real.log p) (Real.log q) : ℂ)*
        zetaPrimeLogKernel N s (p*q))/2 =
    (N+1 : ℂ)/2*(∑ k ∈ centralOrders (N+1) (13*N/32),
      finiteMoment A k s*finiteMoment A (N+1-k) s) -
      (N+1 : ℂ)*(N+2)/(2*(L : ℂ))*(∑ k ∈ centralOrders (N+2) (13*N/32),
        finiteMoment A k s*finiteMoment A (N+2-k) s) -
      (N+1 : ℂ)/(L : ℂ)*(∑ k ∈ (Finset.range (13*N/32+1)).filter (fun k => 0 < k),
        (k : ℂ)*finiteMoment A k s*finiteMoment A (N+2-k) s) := by
  rw [ordered_prefix_eq_convolution A hA]
  have hMK : 2*(13*N/32) < N+1 := by omega
  have h := joined_convolution_cancel_endpoints (fun k => finiteMoment A k s)
    (N+1) (13*N/32) hMK (L : ℂ) (Complex.ofReal_ne_zero.mpr hL)
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp only [Nat.cast_add, Nat.cast_one]
  convert h using 1 <;> ring

/-- Symmetry belongs to the exact prefix, rather than to an approximate
largest-prime mask. -/
theorem prefixLogCoefficient_symm (N : ℕ) (L x z : ℝ) :
    prefixLogCoefficient N L x z = prefixLogCoefficient N L z x := by
  unfold prefixLogCoefficient
  rw [add_comm z x]
  ring

/-- The canonical owner coordinates give the same symmetric coefficient
on either orientation, including a repeated-prime label. -/
theorem canonical_prefix_pair (N : ℕ) (L : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    prefixLogCoefficient N L (Real.log (ZetaRieszPrimeEndpoint.largestPrime (p*q)))
      (Real.log (ZetaRieszOwnedCells.ownerCofactor (p*q))) =
        prefixLogCoefficient N L (Real.log p) (Real.log q) := by
  have hmax : ZetaRieszPrimeEndpoint.largestPrime (p*q) = max p q := by
    apply ZetaRieszPrimeIntervals.largestPrime_eq_of_max
    · rcases le_total p q with h | h
      · rw [max_eq_right h]
        exact hq.mem_primeFactors (dvd_mul_left q p) (mul_ne_zero hp.ne_zero hq.ne_zero)
      · rw [max_eq_left h]
        exact hp.mem_primeFactors (dvd_mul_right p q) (mul_ne_zero hp.ne_zero hq.ne_zero)
    · intro r hr
      rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors,
        hq.primeFactors, Finset.mem_union] at hr
      simp only [Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
  rcases le_total p q with h | h
  · have hco : ZetaRieszOwnedCells.ownerCofactor (p*q) = p := by
      rw [ZetaRieszOwnedCells.ownerCofactor, hmax, max_eq_right h,
        Nat.mul_div_cancel p hq.pos]
    rw [hco, hmax, max_eq_right h, prefixLogCoefficient_symm]
  · have hco : ZetaRieszOwnedCells.ownerCofactor (p*q) = q := by
      rw [ZetaRieszOwnedCells.ownerCofactor, hmax, max_eq_left h]
      exact Nat.mul_div_cancel_left q hp.pos
    rw [hco, hmax, max_eq_left h]

/-- The actual unordered distinct-prime integer sum is the central
logged convolution minus its single WHOLE repeated-prime diagonal.
There is no hidden half or silently deleted square. -/
theorem unordered_prefix_eq_central_sub_diagonal
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (L : ℝ) (hL : L ≠ 0) (s : ℂ) :
    (∑ n ∈ ZetaRieszRemainingPrefix.pairedLabels A,
      (prefixLogCoefficient N L (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
        (Real.log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)*zetaPrimeLogKernel N s n) =
    (N+1 : ℂ)/2*(∑ k ∈ centralOrders (N+1) (13*N/32),
      finiteMoment A k s*finiteMoment A (N+1-k) s) -
      (N+1 : ℂ)*(N+2)/(2*(L : ℂ))*(∑ k ∈ centralOrders (N+2) (13*N/32),
        finiteMoment A k s*finiteMoment A (N+2-k) s) -
      (N+1 : ℂ)/(L : ℂ)*(∑ k ∈ (Finset.range (13*N/32+1)).filter (fun k => 0 < k),
        (k : ℂ)*finiteMoment A k s*finiteMoment A (N+2-k) s) -
      (1/2 : ℂ)*(∑ p ∈ A,
        (prefixLogCoefficient N L (Real.log p) (Real.log p) : ℂ)*
          zetaPrimeLogKernel N s (p^2)) := by
  let f := fun n : ℕ =>
    (prefixLogCoefficient N L (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
      (Real.log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)*zetaPrimeLogKernel N s n
  have ho := sum_ordered_eq_twice_labels_add_diagonal A hA f
  have hpair : (∑ p ∈ A, ∑ q ∈ A, f (p*q)) =
      ∑ p ∈ A, ∑ q ∈ A,
        (prefixLogCoefficient N L (Real.log p) (Real.log q) : ℂ)*
          zetaPrimeLogKernel N s (p*q) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only [f]
    rw [canonical_prefix_pair N L (hA p hp) (hA q hq)]
  have hdiag : (∑ p ∈ A, f (p^2)) = ∑ p ∈ A,
      (prefixLogCoefficient N L (Real.log p) (Real.log p) : ℂ)*
        zetaPrimeLogKernel N s (p^2) := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [f]
    rw [pow_two, canonical_prefix_pair N L (hA p hp) (hA p hp)]
  rw [hpair, hdiag] at ho
  have hc := ordered_prefix_eq_central_logged A hA N L hL s
  change _ = 2*(∑ n ∈ ZetaRieszRemainingPrefix.pairedLabels A,
    (prefixLogCoefficient N L (Real.log (ZetaRieszPrimeEndpoint.largestPrime n))
      (Real.log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)*zetaPrimeLogKernel N s n)+_ at ho
  linear_combination hc-(1/2 : ℂ)*ho

end RiemannGaussian.ZetaRieszPairPrefixConvolution
