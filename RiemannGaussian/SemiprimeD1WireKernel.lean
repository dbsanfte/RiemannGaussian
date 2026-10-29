/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Original power-of-two grid content for the D.4 Cauchy wire kernel
The original grid is indexed by j<N, translated by -L with N=2L. Its derivative
product is acquired directly from integer differences, not a supplied inverse or
coefficient table. Polynomial and p-adic interpretations are specifications.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WireKernel
open scoped BigOperators

/-- Integer derivative product at the j-th point of the actual consecutive grid. -/
def derivativeProduct (N j : ℕ) : ℤ :=
  ∏ q∈Finset.range N, if q=j then 1 else (j:ℤ)-(q:ℤ)

/-- Legendre's recurrence uses an actual integer quotient, not a digit oracle. -/
theorem factorial_valuation_rec (n : ℕ) :
    padicValNat 2 n.factorial=padicValNat 2 (n/2).factorial+n/2 := by
  rw [← padicValNat_mul_div_factorial (p:=2) n,padicValNat_factorial_mul]

/-- Complementary factorials on a complete dyadic grid have the same total
2-content at EVERY point, including the two grid endpoints. -/
theorem complementary_factorial_content (k j : ℕ) (hj : j<2^k) :
    padicValNat 2 j.factorial+padicValNat 2 (2^k-1-j).factorial=
      padicValNat 2 (2^k-1).factorial := by
  induction k generalizing j with
  | zero =>
    have hj0 : j=0 := by simpa using hj
    subst j
    simp
  | succ k ih =>
    have hp : 0<2^k := by positivity
    have hn : 2^(k+1)=2*2^k := by rw [pow_succ];omega
    have hdiv : (2^(k+1)-1-j)/2=2^k-1-j/2 := by rw [hn] at *;omega
    have htop : (2^(k+1)-1)/2=2^k-1 := by rw [hn];omega
    have hsmall : j/2<2^k := by rw [hn] at hj;omega
    have hsum : j/2+(2^(k+1)-1-j)/2=2^k-1 := by rw [hn] at *;omega
    have hi := ih (j/2) hsmall
    have h1 := factorial_valuation_rec j
    have h2 := factorial_valuation_rec (2^(k+1)-1-j)
    have h3 := factorial_valuation_rec (2^(k+1)-1)
    rw [hdiv] at h2
    rw [htop] at h3
    omega

/-- Product at the final point is the acquired factorial, with no negative factors. -/
theorem derivativeProduct_last (N : ℕ) : derivativeProduct (N+1) N=(N.factorial:ℤ) := by
  simp only [derivativeProduct,Finset.prod_range_succ,ite_true,mul_one]
  have he : (∏ q∈Finset.range N, if q=N then (1:ℤ) else (N:ℤ)-(q:ℤ))=
      ∏ q∈Finset.range N, ((N:ℤ)-(q:ℤ)) := by
    apply Finset.prod_congr rfl
    intro q hq
    simp only [ne_of_lt (Finset.mem_range.mp hq),ite_false]
  rw [he,Finset.prod_range_natCast_sub,← Nat.descFactorial_eq_prod_range,Nat.descFactorial_self]

/-- Exact signed derivative of the original complete consecutive grid. -/
theorem derivativeProduct_formula (N j : ℕ) (hj : j<N) :
    derivativeProduct N j=(-1:ℤ)^(N-1-j)*(j.factorial:ℤ)*((N-1-j).factorial:ℤ) := by
  induction N generalizing j with
  | zero => omega
  | succ N ih =>
    by_cases he : j=N
    · subst j
      rw [derivativeProduct_last]
      simp
    · have hjN : j<N := by omega
      have hi := ih j hjN
      have hd : N-j=(N-1-j)+1 := by omega
      have hz : (j:ℤ)-(N:ℤ)=-((N-1-j:ℕ)+1:ℤ) := by omega
      have heN : N≠j := Ne.symm he
      simp only [derivativeProduct,Finset.prod_range_succ,heN,ite_false] at hi ⊢
      rw [hi]
      simp only [Nat.add_sub_cancel_right]
      rw [hd,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ,hz]
      ring

/-- Absolute derivative content is exactly the two acquired factorials. -/
theorem derivativeProduct_natAbs (N j : ℕ) (hj : j<N) :
    (derivativeProduct N j).natAbs=j.factorial*(N-1-j).factorial := by
  rw [derivativeProduct_formula N j hj]
  simp [Int.natAbs_mul,Int.natAbs_pow]

/-- The original grid derivative has constant 2-adic content, without assuming
integrality or an odd-binomial/normalizer oracle. -/
theorem derivativeProduct_content (k j : ℕ) (hj : j<2^k) :
    padicValInt 2 (derivativeProduct (2^k) j)=
      padicValNat 2 (2^k-1).factorial := by
  rw [padicValInt,derivativeProduct_natAbs _ _ hj,
    padicValNat.mul (Nat.factorial_ne_zero j) (Nat.factorial_ne_zero _)]
  exact complementary_factorial_content k j hj

end RiemannGaussian.SemiprimeD1WireKernel
