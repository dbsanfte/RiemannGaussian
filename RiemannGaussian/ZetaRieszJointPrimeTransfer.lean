/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointBoundary

/-!
# Exact prime-factor transfer of the jointly weighted carrier

The identity is finite and arithmetic. Each correlated factorial allocation
becomes a product of its actual prime kernels, including zero orders.
The full residual coefficient and all label masks remain outside the product
but inside the finite sum. No completed-leg convergence is used here.
-/

namespace RiemannGaussian.ZetaRieszJointPrimeTransfer
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszJointBoundary
open ZetaRieszAnnulusJoint ZetaRieszParityPacket

theorem feature_product {n : ℕ} (hn : Squarefree n) (s : ℂ) :
    (∏ p ∈ n.primeFactors, zetaPrimeFeature s p) = zetaPrimeFeature s n := by
  unfold zetaPrimeFeature
  rw [← Complex.exp_sum, CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_neg_distrib]

/-- One exact multinomial atom with all ordinary-prime phases retained. -/
theorem allocation_kernel {n M : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    {d : ℕ → ℕ} (hd : d ∈ Finset.piAntidiag n.primeFactors M) (s : ℂ) :
    (allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d : ℂ)*
      zetaPrimeLogKernel M s n = ∏ p ∈ n.primeFactors, zetaPrimeLogKernel (d p) s p := by
  have hsum := (Finset.mem_piAntidiag.mp hd).1
  have hlog : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn1)).ne'
  have hf : (M.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hprod : (∏ p ∈ n.primeFactors, ((d p).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hmulti : (∏ p ∈ n.primeFactors, ((d p).factorial : ℂ))*
      (Nat.multinomial n.primeFactors d : ℂ) = (M.factorial : ℂ) := by
    have hh := Nat.multinomial_spec n.primeFactors d
    rw [hsum] at hh
    exact_mod_cast hh
  simp only [allocationWeight, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_div, div_pow,
    Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, zetaPrimeLogKernel,
    Finset.prod_mul_distrib]
  rw [feature_product hn s]
  field_simp
  linear_combination (∏ p ∈ n.primeFactors, (Real.log p : ℂ)^(d p))*
    zetaPrimeFeature s n*hmulti

/-- The rectangle has total base order N+1; the original kernel has
order N. This exact scalar is essential for the literal normalization. -/
theorem rectangle_kernel_atom {n N : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    {d : ℕ → ℕ} (hd : d ∈ rectangleAllocations N n) (s : ℂ) :
    (allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d : ℂ)*
      zetaPrimeLogKernel N s n = ((N+1 : ℕ) : ℂ)/(Real.log n : ℂ)*
        ∏ p ∈ n.primeFactors, zetaPrimeLogKernel (d p) s p := by
  have h := allocation_kernel hn hn1 (Finset.mem_filter.mp hd).1 s
  have hk := ZetaRieszHeadOrders.log_mul_kernel N n s
  have hlog : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn1)).ne'
  rw [← h]
  field_simp
  linear_combination (allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d : ℂ)*hk

/-- The correlated rectangle is transferred before any norm or phase
replacement. There is no independent product over unconstrained orders. -/
theorem weight_kernel {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n) (N : ℕ) (s : ℂ) :
    (weight N n : ℂ)*zetaPrimeLogKernel N s n =
      ((N+1 : ℕ) : ℂ)/(Real.log n : ℂ)*
        ∑ d ∈ rectangleAllocations N n,
          ∏ p ∈ n.primeFactors, zetaPrimeLogKernel (d p) s p := by
  rw [weight, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d hd => rectangle_kernel_atom hn hn1 hd s)

/-- Actual prime legs; every remaining arithmetic correlation is explicit
in the same summand, rather than an unestimated completion correction. -/
def primeAtom (u y : ℝ) (N n : ℕ) : ℂ :=
  (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
    (((N+1 : ℕ) : ℂ)/(Real.log n : ℂ)))*
    ∑ d ∈ rectangleAllocations N n,
      ∏ p ∈ n.primeFactors, zetaPrimeLogKernel (d p) (3/2+Complex.I*y) p

theorem atom_eq_primeAtom {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (u y : ℝ) (N : ℕ) : atom u y N n = primeAtom u y N n := by
  unfold atom primeAtom
  rw [show (weight N n : ℂ)*
      (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        ((weight N n : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n) by ring,
    weight_kernel hn hn1]
  ring

theorem packet_eq_prime_sum (u y : ℝ) (N K : ℕ) :
    packet u y N K = ∑ n ∈ band u N K, primeAtom u y N n := by
  exact Finset.sum_congr rfl (fun n hn => atom_eq_primeAtom
    (Finset.mem_filter.mp hn).2.1.squarefree (Finset.mem_filter.mp hn).2.1.nontrivial u y N)

/-- Joint cancellation is now an exact literal prime sum up to the
independently paid outer tails, uniformly in arbitrary phase height. -/
theorem joint_prime_transfer_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N K : ℕ) (hN : 1 ≤ N) :
    ‖(u : ℂ)^(N+1)*(fullParityPacket u y N K+neighbors u y N K-
      ∑ n ∈ (band u N K).filter interior, primeAtom u y N n)‖ ≤
      (2*ZetaRieszWideOwnerAudit.radiusCeiling)*exteriorRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have he : interiorPacket u y N K =
      ∑ n ∈ (band u N K).filter interior, primeAtom u y N n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
    exact atom_eq_primeAtom hb.squarefree hb.nontrivial u y N
  rw [← he]
  exact joint_transfer_bound hu hU y N K hN

end
end RiemannGaussian.ZetaRieszJointPrimeTransfer
