/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.NatProductCollision
import RiemannGaussian.ChebyshevMoebiusCancellation
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Sqrt

/-!
# Joint divisor and factor scale in a least-common-multiple sum

The common divisor in an intersection is kept until its divided-cutoff
sum is estimated. This retains an explicit inverse-square-root factor
weight, including its complete divisor correction. All cutoffs are finite
and their integer endpoints are retained.
-/

open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The exact reciprocal-square-root mass on the multiples of a
positive divisor, with the original integer quotient cutoff. -/
theorem sum_Icc_dvd_inv_sqrt_eq {g : ℕ} (hg : 0 < g) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, if g ∣ d then 1 / Real.sqrt d else 0) =
      (1 / Real.sqrt g) * ∑ a ∈ Finset.Icc 1 (D / g), 1 / Real.sqrt a := by
  rw [sum_Icc_dvd_eq hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg g)]
  simp only [one_div, mul_inv]

/-- The reciprocal-square-root mass on a divisor progression retains
the full inverse divisor, after summing the divided prefix. -/
theorem sum_Icc_dvd_inv_sqrt_le {g : ℕ} (hg : 0 < g) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, if g ∣ d then 1 / Real.sqrt d else 0) ≤
      2 * Real.sqrt D / g := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hdiv : ((D / g : ℕ) : ℝ) ≤ (D : ℝ) / g := by
    apply (le_div_iff₀ hgR).mpr
    exact_mod_cast Nat.div_mul_le_self D g
  rw [sum_Icc_dvd_inv_sqrt_eq hg D]
  calc
    _ ≤ (1 / Real.sqrt g) * (2 * Real.sqrt (D / g : ℕ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le _) (by positivity)
    _ ≤ (1 / Real.sqrt g) * (2 * Real.sqrt ((D : ℝ) / g)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_div (Nat.cast_nonneg D)]
      have hs := Real.sq_sqrt hgR.le
      have hsg : Real.sqrt (g : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hgR).ne'
      field_simp
      rw [hs]
      ring

/-- The exact inverse-square-root intersection weight keeps both
outer factors and their common divisor. -/
theorem inv_sqrt_lcm_eq {d P : ℕ} (hd : 0 < d) (hP : 0 < P) :
    1 / Real.sqrt (Nat.lcm d P) =
      Real.sqrt (Nat.gcd d P) / (Real.sqrt d * Real.sqrt P) := by
  have he : Real.sqrt (Nat.gcd d P) * Real.sqrt (Nat.lcm d P) =
      Real.sqrt d * Real.sqrt P := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul,
      Nat.gcd_mul_lcm, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg d)]
  have hL : Real.sqrt (Nat.lcm d P : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.lcm_pos hd hP)).ne'
  have hdS : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hPS : Real.sqrt (P : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hP)).ne'
  field_simp
  nlinarith

/-- The factor's complete divisor correction, with its physical
inverse-square-root scale still present. -/
def lcmSqrtFactorMass (P : ℕ) : ℝ :=
  (1 / Real.sqrt P) * ∑ g ∈ P.divisors, 1 / Real.sqrt g

/-- The explicit factor mass is nonnegative at every integer. -/
theorem lcmSqrtFactorMass_nonneg (P : ℕ) : 0 ≤ lcmSqrtFactorMass P := by
  unfold lcmSqrtFactorMass
  positivity

/-- Summing the actual intersection weights retains the selected
factor size and every common-divisor correction, uniformly in the cutoff. -/
theorem sum_Icc_inv_sqrt_lcm_le (D : ℕ) {P : ℕ} (hP : 0 < P) :
    (∑ d ∈ Finset.Icc 1 D, 1 / Real.sqrt (Nat.lcm d P)) ≤
      2 * Real.sqrt D * lcmSqrtFactorMass P := by
  have hpoint (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      1 / Real.sqrt (Nat.lcm d P) ≤ (1 / Real.sqrt P) *
        ∑ g ∈ P.divisors, Real.sqrt g * (if g ∣ d then 1 / Real.sqrt d else 0) := by
    have hd0 := (Finset.mem_Icc.mp hd).1
    have hmem : Nat.gcd d P ∈ P.divisors := Nat.mem_divisors.mpr
      ⟨Nat.gcd_dvd_right d P, hP.ne'⟩
    have h := Finset.single_le_sum
      (f := fun g : ℕ ↦ Real.sqrt g * (if g ∣ d then 1 / Real.sqrt d else 0))
      (fun g _ ↦ by split_ifs <;> positivity) hmem
    rw [if_pos (Nat.gcd_dvd_left d P)] at h
    rw [inv_sqrt_lcm_eq hd0 hP]
    calc
      _ = (1 / Real.sqrt P) * (Real.sqrt (Nat.gcd d P) * (1 / Real.sqrt d)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (1 / Real.sqrt P) *
        ∑ g ∈ P.divisors, Real.sqrt g * (if g ∣ d then 1 / Real.sqrt d else 0) :=
      Finset.sum_le_sum hpoint
    _ = (1 / Real.sqrt P) * ∑ g ∈ P.divisors, Real.sqrt g *
        ∑ d ∈ Finset.Icc 1 D, if g ∣ d then 1 / Real.sqrt d else 0 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ (1 / Real.sqrt P) * ∑ g ∈ P.divisors,
        Real.sqrt g * (2 * Real.sqrt D / g) := by
      gcongr with g hg
      exact sum_Icc_dvd_inv_sqrt_le (Nat.pos_of_mem_divisors hg) D
    _ = _ := by
      unfold lcmSqrtFactorMass
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_mem_divisors hg
      have hs := Real.sq_sqrt hg0.le
      have hsg : Real.sqrt (g : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hg0).ne'
      field_simp
      rw [hs]
      ring

/-- The divisor correction factors exactly on coprime products. -/
theorem lcmSqrtFactorMass_mul {P Q : ℕ} (hcop : P.Coprime Q) :
    lcmSqrtFactorMass (P * Q) = lcmSqrtFactorMass P * lcmSqrtFactorMass Q := by
  unfold lcmSqrtFactorMass
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hcop.mul_injOn_divisors,
    Finset.sum_product, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg P)]
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), one_div, mul_inv,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- A prime factor has an explicit two-term divisor correction. -/
theorem lcmSqrtFactorMass_prime {p : ℕ} (hp : p.Prime) :
    lcmSqrtFactorMass p = (1 / Real.sqrt p) * (1 + 1 / Real.sqrt p) := by
  unfold lcmSqrtFactorMass
  rw [hp.sum_divisors]
  simp [add_comm]

/-- Every distinct-prime pair retains its full inverse product scale,
with a divisor correction bounded by four independently of both primes. -/
theorem lcmSqrtFactorMass_two_primes_le {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    lcmSqrtFactorMass (p * q) ≤ 4 / Real.sqrt (p * q : ℕ) := by
  rw [lcmSqrtFactorMass_mul ((Nat.coprime_primes hp hq).mpr hpq),
    lcmSqrtFactorMass_prime hp, lcmSqrtFactorMass_prime hq]
  have hb (n : ℕ) (hn : 1 ≤ n) : 1 / Real.sqrt n ≤ 1 := by
    have hs : (1 : ℝ) ≤ Real.sqrt n := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    exact (div_le_one (by positivity)).mpr hs
  calc
    _ ≤ ((1 / Real.sqrt p) * 2) * ((1 / Real.sqrt q) * 2) := by
      gcongr <;> linarith [hb p hp.one_lt.le, hb q hq.one_lt.le]
    _ = _ := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
      ring

/-- Pairing every divisor with its complementary divisor bounds the
complete reciprocal-square-root divisor sum by the fourth-root scale.
This holds for every positive integer, with no restriction on its primes. -/
theorem sum_divisors_inv_sqrt_le_four_mul_fourthRoot {P : ℕ} (hP : 0 < P) :
    (∑ d ∈ P.divisors, 1 / Real.sqrt d) ≤ 4 * Real.sqrt (Real.sqrt P) := by
  let R := Nat.sqrt P
  let f : ℕ → ℝ := fun d ↦ if d ≤ R then 1 / Real.sqrt d else 0
  have hf (d : ℕ) : 0 ≤ f d := by dsimp [f]; split_ifs <;> positivity
  have hpoint (d : ℕ) (hd : d ∈ P.divisors) : 1 / Real.sqrt d ≤ f d + f (P / d) := by
    by_cases hdR : d ≤ R
    · simpa only [f, if_pos hdR] using le_add_of_nonneg_right (hf (P / d))
    · have hprod : P = d * (P / d) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
      have hqR : P / d ≤ R := (Nat.le_sqrt_of_eq_mul hprod).resolve_left hdR
      have hqd : P / d ≤ d := by omega
      have hqpos : 0 < P / d := (Nat.one_le_div_iff (Nat.pos_of_mem_divisors hd)).mpr
        (Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors hd))
      simp only [f, if_neg hdR, if_pos hqR, zero_add]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hqpos))
        (Real.sqrt_le_sqrt (by exact_mod_cast hqd))
  have hsmall : (∑ d ∈ P.divisors, f d) ≤ ∑ d ∈ Finset.Icc 1 R, 1 / Real.sqrt d := by
    rw [show (∑ d ∈ P.divisors, f d) =
      ∑ d ∈ P.divisors.filter (fun d ↦ d ≤ R), 1 / Real.sqrt d by rw [Finset.sum_filter]]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdP, hdR⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdR⟩
    · intro d _ _
      positivity
  have hR : (R : ℝ) ≤ Real.sqrt P := by
    have hs : (R : ℝ) ^ 2 ≤ P := by exact_mod_cast Nat.sqrt_le' P
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg P), Real.sqrt_nonneg (P : ℝ), Nat.cast_nonneg (α := ℝ) R]
  calc
    _ ≤ ∑ d ∈ P.divisors, (f d + f (P / d)) := Finset.sum_le_sum hpoint
    _ = 2 * ∑ d ∈ P.divisors, f d := by rw [Finset.sum_add_distrib, Nat.sum_div_divisors]; ring
    _ ≤ 2 * ∑ d ∈ Finset.Icc 1 R, 1 / Real.sqrt d := mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ ≤ 2 * (2 * Real.sqrt R) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le R) (by norm_num)
    _ ≤ _ := by nlinarith [Real.sqrt_le_sqrt hR]

/-- Every positive factor has a fourth-root-decaying correction bound,
independently of its number of primes and their valuations. -/
theorem lcmSqrtFactorMass_le_four_div_fourthRoot {P : ℕ} (hP : 0 < P) :
    lcmSqrtFactorMass P ≤ 4 / Real.sqrt (Real.sqrt P) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hs : Real.sqrt (P : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hP0).ne'
  have hq : Real.sqrt (Real.sqrt (P : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hP0)).ne'
  apply (mul_le_mul_of_nonneg_left (sum_divisors_inv_sqrt_le_four_mul_fourthRoot hP)
    (show 0 ≤ 1 / Real.sqrt P by positivity)).trans_eq
  have he := Real.sq_sqrt (Real.sqrt_nonneg (P : ℝ))
  field_simp
  nlinarith

/-- A factor beyond the square of the divisor cutoff removes all
growth in the joint square-root mass, for every positive factor. -/
theorem sqrt_mul_lcmSqrtFactorMass_le_four {D P : ℕ} (hP : 0 < P) (hlarge : D ^ 2 ≤ P) :
    Real.sqrt D * lcmSqrtFactorMass P ≤ 4 := by
  have hD : (D : ℝ) ≤ Real.sqrt P := by
    have hs : (D : ℝ) ^ 2 ≤ P := by exact_mod_cast hlarge
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg P), Real.sqrt_nonneg (P : ℝ), Nat.cast_nonneg (α := ℝ) D]
  have hq : 0 < Real.sqrt (Real.sqrt (P : ℝ)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hP))
  calc
    _ ≤ Real.sqrt (Real.sqrt P) * (4 / Real.sqrt (Real.sqrt P)) :=
      mul_le_mul (Real.sqrt_le_sqrt hD) (lcmSqrtFactorMass_le_four_div_fourthRoot hP)
        (lcmSqrtFactorMass_nonneg P) hq.le
    _ = 4 := by field_simp

end
end RiemannGaussian
