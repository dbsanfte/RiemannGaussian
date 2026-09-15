/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWindowUnitDeletion

/-!
# The missing divisor-chain interactions

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszWindowOverlap
noncomputable section
open scoped BigOperators Classical
open ZetaRieszWindowGram

/-- Every nonunit divisor of a rough integer is at least its least
allowed prime. No squarefreeness assumption is needed here. -/
theorem rough_divisor_lower_bound {q m d : ℕ} (hm : m ≠ 0)
    (hrough : ∀ p ∈ m.primeFactors, q ≤ p) (hd : d ∣ m) (hd1 : 1 < d) : q ≤ d := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  exact (hrough p (hp.mem_primeFactors (dvd_trans hpd hd) hm)).trans
    (Nat.le_of_dvd (by omega) hpd)

/-- Comparable rough divisors are separated by at least one full
prime-window width on the logarithmic axis. -/
theorem log_ratio_ge_of_divisor_chain {q d e : ℕ} (hq : 0 < q) (hd : 0 < d) (he : 0 < e)
    (hde : d ∣ e) (hne : d ≠ e) (hrough : ∀ p ∈ e.primeFactors, q ≤ p) :
    Real.log q ≤ Real.log e - Real.log d := by
  let r := e / d
  have hrprod : r * d = e := Nat.div_mul_cancel hde
  have hlt : d < e := lt_of_le_of_ne (Nat.le_of_dvd he hde) hne
  have hr1 : 1 < r := by
    by_contra h
    have hh := Nat.mul_le_mul_right d (show r ≤ 1 by omega)
    rw [hrprod, one_mul] at hh
    omega
  have hqr : q ≤ r := rough_divisor_lower_bound he.ne' hrough (Nat.div_dvd_of_dvd hde) hr1
  have hlogr : Real.log q ≤ Real.log (r : ℝ) :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqr)
  have hlog : Real.log e = Real.log (r : ℝ) + Real.log d := by
    calc
      _ = Real.log ((r : ℝ) * d) := by congr 1; exact_mod_cast hrprod.symm
      _ = _ := Real.log_mul (by exact_mod_cast (show r ≠ 0 by omega))
        (by exact_mod_cast hd.ne')
  linarith

/-- Strictly comparable rough divisors have zero triangular Gram
entry, even when they belong to different original cofactors. -/
theorem triangular_kernel_zero_of_divisor_chain {q d e : ℕ} (hq : 0 < q)
    (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) (hne : d ≠ e)
    (hrough : ∀ p ∈ e.primeFactors, q ≤ p) :
    max (Real.log q - |Real.log d - Real.log e|) 0 = 0 := by
  have hh := log_ratio_ge_of_divisor_chain hq hd he hde hne hrough
  have hb : Real.log q ≤ |Real.log d - Real.log e| := by
    rw [abs_sub_comm]
    exact hh.trans (le_abs_self _)
  exact max_eq_right (sub_nonpos.mpr hb)

/-- The physical cutoff can only reduce interval overlap. Retain
this inequality alongside the exact cutoff-dependent kernel. -/
theorem clippedOverlap_le_triangular (a b x y : ℝ) :
    clippedOverlap a b x y ≤ max (b - |x - y|) 0 := by
  unfold clippedOverlap
  apply max_le_max _ le_rfl
  exact (sub_le_sub (min_le_left _ _) (le_max_left _ _)).trans_eq (overlap_eq_tent b x y)

/-- The literal finite-cutoff Gram kernel also vanishes on every
strict divisor chain. The cutoff is not removed to obtain this zero. -/
theorem clippedOverlap_zero_of_divisor_chain (a L : ℝ) {q d e : ℕ} (hq : 0 < q)
    (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) (hne : d ≠ e)
    (hrough : ∀ p ∈ e.primeFactors, q ≤ p) :
    clippedOverlap a (Real.log q) (L - Real.log d - Real.log q)
      (L - Real.log e - Real.log q) = 0 := by
  have hb := clippedOverlap_le_triangular a (Real.log q)
    (L - Real.log d - Real.log q) (L - Real.log e - Real.log q)
  have hdist : |(L - Real.log d - Real.log q) - (L - Real.log e - Real.log q)| =
      |Real.log d - Real.log e| := by
    rw [show (L - Real.log d - Real.log q) - (L - Real.log e - Real.log q) =
      -(Real.log d - Real.log e) by ring, abs_neg]
  rw [hdist, triangular_kernel_zero_of_divisor_chain hq hd he hde hne hrough] at hb
  exact le_antisymm hb (le_max_right _ _)

/-- The finite Gram kernel is symmetric in its actual window labels. -/
theorem clippedOverlap_comm (a b x y : ℝ) :
    clippedOverlap a b x y = clippedOverlap a b y x := by
  unfold clippedOverlap
  rw [min_comm (x + b) (y + b), max_comm x y]

/-- Nonzero off-diagonal interactions between rough divisors must
be incomparable. This restriction holds across different cofactors within
one fixed prime-pair family, before taking any amplitude norm. -/
theorem nonzero_clippedOverlap_incomparable (a L : ℝ) {q d e : ℕ} (hq : 0 < q)
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (hroughd : ∀ p ∈ d.primeFactors, q ≤ p)
    (hroughe : ∀ p ∈ e.primeFactors, q ≤ p)
    (hK : clippedOverlap a (Real.log q) (L - Real.log d - Real.log q)
      (L - Real.log e - Real.log q) ≠ 0) : ¬ d ∣ e ∧ ¬ e ∣ d := by
  constructor
  · intro hde
    exact hK (clippedOverlap_zero_of_divisor_chain a L hq hd he hde hne hroughe)
  · intro hed
    apply hK
    rw [clippedOverlap_comm]
    exact clippedOverlap_zero_of_divisor_chain a L hq he hd hed hne.symm hroughd

/-- The no-chain interaction theorem applies to the actual divisor
labels of any two rough cofactors, with all positivity and inherited
prime-support conditions discharged. -/
theorem actual_cofactor_chain_kernel_zero (a L : ℝ) {q m n d e : ℕ} (hq : q.Prime)
    (hd : d ∈ m.divisors) (he : e ∈ n.divisors)
    (hrough : ∀ p ∈ n.primeFactors, q ≤ p) (hde : d ∣ e) (hne : d ≠ e) :
    clippedOverlap a (Real.log q) (L - Real.log d - Real.log q)
      (L - Real.log e - Real.log q) = 0 := by
  have hrough' : ∀ p ∈ e.primeFactors, q ≤ p := by
    intro p hp
    apply hrough p
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (dvd_trans (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_divisors he))
      (Nat.mem_divisors.mp he).2
  exact clippedOverlap_zero_of_divisor_chain a L hq.pos (Nat.pos_of_mem_divisors hd)
    (Nat.pos_of_mem_divisors he) hde hne hrough'

/-- Incomparability forces a nonunit on both sides of the reduced
ratio. A surviving off-diagonal is not a single-prime insertion. -/
theorem one_lt_reduced_of_not_dvd {d e : ℕ} (hd : 0 < d) (hnot : ¬ d ∣ e) :
    1 < d / Nat.gcd d e := by
  have hg : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
  have hr : 0 < d / Nat.gcd d e := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left d e)) hg
  have hprod : Nat.gcd d e * (d / Nat.gcd d e) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  by_contra h
  have h1 : d / Nat.gcd d e = 1 := by omega
  rw [h1, mul_one] at hprod
  have hh := Nat.gcd_dvd_right d e
  rw [hprod] at hh
  exact hnot hh

/-- A negative Mobius interaction between two nonunits needs at
least three prime factors in total. Two ordinary prime factors give the
same Mobius sign, so their product cannot supply this cancellation. -/
theorem negative_moebius_pair_needs_three_factors {r s : ℕ}
    (hr : 1 < r) (hs : 1 < s)
    (hneg : (ArithmeticFunction.moebius r : ℤ) * ArithmeticFunction.moebius s < 0) :
    3 ≤ ArithmeticFunction.cardFactors (r * s) := by
  have hrp := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hr
  have hsp := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hs
  rw [ArithmeticFunction.cardFactors_mul (by omega : r ≠ 0) (by omega : s ≠ 0)]
  by_contra h
  have hr1 : ArithmeticFunction.cardFactors r = 1 := by omega
  have hs1 : ArithmeticFunction.cardFactors s = 1 := by omega
  rw [ArithmeticFunction.moebius_apply_prime (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hr1),
    ArithmeticFunction.moebius_apply_prime (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hs1)] at hneg
  norm_num at hneg

end
end RiemannGaussian.ZetaRieszWindowOverlap
