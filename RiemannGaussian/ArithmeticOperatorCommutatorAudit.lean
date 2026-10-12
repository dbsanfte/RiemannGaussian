/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFloorBoundaryAudit

/-!
# Cutoff-convolution and shared-prime successor audit

The cutoff/convolution identity is exact for arbitrary arrays. Its
Mangoldt/constant specialization is the literal factorial observation,
whose linear power source is already proved blind. A same-denominator
successor interaction is identically zero, while a fixed lag sees only
divisors of that lag. Cross-column shifted prime correlations are NOT
covered by these rejection theorems.
-/

namespace RiemannGaussian.ArithmeticOperatorCommutatorAudit
noncomputable section
open ArithmeticOperatorDilationAudit ArithmeticOperatorGcdAudit
open ArithmeticOperatorFactorialUniqueness SuzukiCarryCorrelation
open scoped BigOperators

/-- Literal finite convolution on the ordinary integer product lattice. -/
def divisorConvolution (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ n.divisorsAntidiagonal, f p.1*g p.2

/-- Complete cutoff with every divisor fiber kept. -/
def cutoffConvolution (f g : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, divisorConvolution f g n

/-- No prime property enters the finite quotient/convolution join. -/
theorem cutoffConvolution_eq_quotient (f g : ℕ → ℂ) (N : ℕ) :
    cutoffConvolution f g N =
      ∑ d ∈ Finset.Icc 1 N, f d*prefixSum g (N/d) := by
  unfold cutoffConvolution divisorConvolution prefixSum
  simpa only [Finset.mul_sum] using
    sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N (fun d n => f d*g n)

/-- The shift exposes precisely the next divisor fiber, for arbitrary
weights; reindexing alone supplies no independent estimate for that fiber. -/
theorem cutoffConvolution_increment (f g : ℕ → ℂ) (N : ℕ) :
    cutoffConvolution f g (N+1)-cutoffConvolution f g N =
      divisorConvolution f g (N+1) := by
  unfold cutoffConvolution
  rw [Finset.sum_Icc_succ_top (by omega),add_sub_cancel_left]

/-- Convolution with the constant array is exactly the integer-floor
operator whose entire finite Gamma data are invertible, not a new carrier. -/
theorem cutoffConvolution_const_one (f : ℕ → ℂ) (N : ℕ) :
    cutoffConvolution f (fun _ => 1) N = factorialPrefix f N := by
  rw [cutoffConvolution_eq_quotient]
  unfold factorialPrefix prefixSum
  apply Finset.sum_congr rfl
  intro d _
  simp [mul_comm]

/-- Actual integer primes give Gamma exactly only at the untwisted
weight; inserting a prime phase retains an unpaid twisted divisor sum. -/
theorem cutoffConvolution_mangoldt (N : ℕ) :
    cutoffConvolution (fun d => (ArithmeticFunction.vonMangoldt d : ℂ))
      (fun _ => 1) N = (Real.log (N.factorial : ℝ) : ℂ) := by
  rw [cutoffConvolution_const_one,factorialPrefix_mangoldt]

/-- A shared arithmetic-column correlation across a literal shift. -/
def sharedShift (w : ℕ → ℂ) (N h : ℕ) : ℂ := gcdKernel w N (N+h)

/-- The only possible shared denominators divide the lag itself. -/
theorem sharedShift_eq_lag_gcd (w : ℕ → ℂ) (N h : ℕ) :
    sharedShift w N h = gcdKernel w N h := by
  unfold sharedShift gcdKernel
  rw [Nat.gcd_self_add_right]

/-- Successor divisibility kills every shared source away from the
unit column, for arbitrary weights including all prime powers/phases. -/
theorem sharedShift_successor_zero {w : ℕ → ℂ} (hw : w 1 = 0) (N : ℕ) :
    sharedShift w N 1 = 0 := by
  rw [sharedShift_eq_lag_gcd]
  simp [gcdKernel,hw]

/-- A fixed lag cannot detect a source carried on denominators larger
than the lag. This exact support rejection precedes any norm estimate. -/
theorem sharedShift_zero_of_large_support {w : ℕ → ℂ} {h : ℕ}
    (hh : 0 < h) (hw : ∀ d ≤ h, w d = 0) (N : ℕ) : sharedShift w N h = 0 := by
  rw [sharedShift_eq_lag_gcd]
  unfold gcdKernel
  apply Finset.sum_eq_zero
  intro d hd
  have hdvd : d ∣ h := (Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right N h)
  exact hw d (Nat.le_of_dvd hh hdvd)

end
end RiemannGaussian.ArithmeticOperatorCommutatorAudit
