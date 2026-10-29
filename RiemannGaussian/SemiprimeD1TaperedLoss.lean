/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Finite tapered valuation estimate behind original D.10
This proves the finite level-count expression and its exact constant6 bound.
Identification of the original grid product valuation with that level expression
is a separate combinatorial obligation, not a precision hypothesis here.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TaperedLoss
open scoped BigOperators

/-- Original taper at valuation level i. -/
def multiplicity (h u i : ℕ) : ℕ := h*(u-i)

/-- The ORIGINAL h=ceil(3M/u), with native integer quotient acquisition. -/
def height (M u : ℕ) : ℕ := (3*M+u-1)/u

/-- Finite square-geometric numerator after clearing exactly2^n. -/
def squareSum (n : ℕ) : ℕ :=
  ∑ j∈Finset.range n,(j+1)^2*2^(n-(j+1))

/-- Executable finite sum recurrence, including its actual final level. -/
theorem squareSum_succ (n : ℕ) : squareSum (n+1)=2*squareSum n+(n+1)^2 := by
  unfold squareSum
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self,pow_zero,mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : n+1-(j+1)=n-(j+1)+1 := by have := Finset.mem_range.mp hj;omega
  rw [he,pow_succ]
  ring

/-- Exact finite identity underlying the universal constant6, no infinite sum oracle. -/
theorem squareSum_exact (n : ℕ) : squareSum n+n^2+4*n+6=6*2^n := by
  induction n with
  | zero => simp [squareSum]
  | succ n ih => rw [squareSum_succ,show (2:ℕ)^(n+1)=2^n*2 from pow_succ _ _];nlinarith

/-- Every finite taper loss is bounded using the same universal constant6. -/
theorem squareSum_le (n : ℕ) : squareSum n≤6*2^n := by
  have := squareSum_exact n
  omega

/-- The original taper changes by at most h per valuation level. -/
theorem taper_lipschitz (h u i j : ℕ) :
    -(h:ℤ)*(j:ℤ)≤(multiplicity h u (i+j):ℤ)-(multiplicity h u i:ℤ) := by
  have ha : u-i≤u-(i+j)+j := by omega
  have hb := Nat.mul_le_mul_left h ha
  have hc : multiplicity h u i≤ multiplicity h u (i+j)+h*j := by
    simpa only [multiplicity,Nat.mul_add] using hb
  have hc' : (multiplicity h u i:ℤ)≤(multiplicity h u (i+j):ℤ)+(h:ℤ)*(j:ℤ) := by
    exact_mod_cast hc
  linarith

/-- The actual finite D.10 level expression, D=2^n, with signed taper differences. -/
def levelValuation (h u i n : ℕ) : ℤ :=
  ∑ j∈Finset.range n,(j+1:ℤ)*(2:ℤ)^(n-(j+1))*
    ((multiplicity h u (i+(j+1)):ℤ)-(multiplicity h u i:ℤ))

/-- PIVOTAL D.10 numerical inequality for the ACTUAL taper, after exact grid
level regrouping. No desired valuation/precision lower bound is supplied. -/
theorem levelValuation_lower (h u i n : ℕ) :
    -(6:ℤ)*(2:ℤ)^n*(h:ℤ)≤levelValuation h u i n := by
  have hlocal : ∀ j∈Finset.range n,
      -(h:ℤ)*(j+1:ℤ)^2*(2:ℤ)^(n-(j+1))≤
        (j+1:ℤ)*(2:ℤ)^(n-(j+1))*
          ((multiplicity h u (i+(j+1)):ℤ)-(multiplicity h u i:ℤ)) := by
    intro j _
    have ht := taper_lipschitz h u i (j+1)
    have hm := mul_le_mul_of_nonneg_left ht
      (show 0≤(j+1:ℤ)*(2:ℤ)^(n-(j+1)) by positivity)
    push_cast at hm
    nlinarith
  have hs := Finset.sum_le_sum hlocal
  have he : (∑ j∈Finset.range n,-(h:ℤ)*(j+1:ℤ)^2*(2:ℤ)^(n-(j+1)))=
      -(h:ℤ)*(squareSum n:ℤ) := by
    unfold squareSum
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hs
  change -(h:ℤ)*(squareSum n:ℤ)≤levelValuation h u i n at hs
  have hsq : (squareSum n:ℤ)≤6*(2:ℤ)^n := by exact_mod_cast squareSum_le n
  have hm := mul_le_mul_of_nonneg_left hsq (show 0≤(h:ℤ) by positivity)
  nlinarith

/-- Original schedule specialization of the level expression, D_t=2^(a-i). -/
theorem original_level_lower (M u a i : ℕ) :
    -(6:ℤ)*(2:ℤ)^(a-i)*(height M u:ℤ)≤
      levelValuation (height M u) u i (a-i) := levelValuation_lower _ _ _ _

end RiemannGaussian.SemiprimeD1TaperedLoss
