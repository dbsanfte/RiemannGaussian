/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWindowOverlap

/-!
# Second-prime transitions between original window families

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszCrossFamilyWindow
noncomputable section
open scoped Classical
open ZetaRieszWholeWindow ZetaRieszWindowOverlap

/-- Disjoint ordered intervals have exactly zero overlap inside
the common unit cutoff, regardless of their other endpoints. -/
theorem unitOverlap_zero_of_right_le_left {l r l' r' : ℝ} (h : r' ≤ l) :
    unitOverlap l r l' r' = 0 := by
  unfold unitOverlap
  apply max_eq_right
  have hu : min (min r r') 1 ≤ r' := (min_le_left _ _).trans (min_le_right _ _)
  have hl : l ≤ max (max l l') 0 := (le_max_left _ _).trans (le_max_left _ _)
  linarith

/-- Comparable divisors cannot interact when their first-prime scales
agree and the larger divisor has no prime below the smaller window's
second prime. The other second-prime family is kept arbitrary. -/
theorem primeWindow_overlap_zero_of_chain (L : ℝ) (p q : ℕ → ℕ) (n m : ℕ)
    (hp : (p n).Prime) (hq : (q n).Prime) (hfirst : p m = p n)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) (hne : d ≠ e)
    (hrough : ∀ r ∈ e.primeFactors, q n ≤ r) :
    unitOverlap (primeWindowLower L p q ⟨n, d⟩) (primeWindowUpper L p ⟨n, d⟩)
      (primeWindowLower L p q ⟨m, e⟩) (primeWindowUpper L p ⟨m, e⟩) = 0 := by
  apply unitOverlap_zero_of_right_le_left
  simp only [primeWindowLower, primeWindowUpper, hfirst]
  have hg := log_ratio_ge_of_divisor_chain hq.pos hd he hde hne hrough
  exact div_le_div_of_nonneg_right (by linarith)
    (Real.log_pos (by exact_mod_cast hp.one_lt)).le

/-- A surviving divisor-chain interaction across second-prime families
must move to a strictly smaller second prime. It cannot be internal to a
single family or move in the opposite prime-order direction. -/
theorem chain_overlap_forces_second_prime_drop (L : ℝ) (p q : ℕ → ℕ) (n m : ℕ)
    (hp : (p n).Prime) (hq : (q n).Prime) (hfirst : p m = p n)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) (hne : d ≠ e)
    (hrough : ∀ r ∈ e.primeFactors, q m ≤ r)
    (hK : unitOverlap (primeWindowLower L p q ⟨n, d⟩) (primeWindowUpper L p ⟨n, d⟩)
      (primeWindowLower L p q ⟨m, e⟩) (primeWindowUpper L p ⟨m, e⟩) ≠ 0) :
    q m < q n := by
  by_contra h
  have hqle : q n ≤ q m := le_of_not_gt h
  exact hK (primeWindow_overlap_zero_of_chain L p q n m hp hq hfirst hd he hde hne
    (fun r hr => hqle.trans (hrough r hr)))

/-- Nonzero clipped overlap forces the two strict intervals to
cross each other's endpoints, before any amplitude is estimated. -/
theorem unitOverlap_nonzero_cross {l r l' r' : ℝ} (hK : unitOverlap l r l' r' ≠ 0) :
    l < r' ∧ l' < r := by
  have hpos : 0 < unitOverlap l r l' r' := lt_of_le_of_ne (le_max_right _ _) hK.symm
  unfold unitOverlap at hpos
  have hinner := (lt_max_iff.mp hpos).resolve_right (lt_irrefl 0)
  have hl : l ≤ max (max l l') 0 := (le_max_left _ _).trans (le_max_left _ _)
  have hl' : l' ≤ max (max l l') 0 := (le_max_right _ _).trans (le_max_left _ _)
  have hr : min (min r r') 1 ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hr' : min (min r r') 1 ≤ r' := (min_le_left _ _).trans (min_le_right _ _)
  constructor <;> linarith

/-- Exact natural division keeps the actual logarithmic ratio,
with both integer positivity conditions explicit. -/
theorem log_quotient_of_dvd {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) :
    Real.log ((e / d : ℕ) : ℝ) = Real.log e - Real.log d := by
  have hr : 0 < e / d := Nat.div_pos (Nat.le_of_dvd he hde) hd
  have hprod := Nat.mul_div_cancel' hde
  have hh : Real.log e = Real.log d + Real.log ((e / d : ℕ) : ℝ) := by
    calc
      _ = Real.log ((d : ℝ) * (e / d : ℕ)) := by congr 1; exact_mod_cast hprod.symm
      _ = _ := Real.log_mul (by exact_mod_cast hd.ne') (by exact_mod_cast hr.ne')
  linarith

/-- A surviving comparable cross-family interaction must introduce
a new prime below the old second-prime threshold. Its exact allowed range
and its exclusion from the old divisor are proved, not assumed. -/
theorem chain_overlap_requires_new_small_prime (L : ℝ) (p q : ℕ → ℕ) (n m : ℕ)
    (hp : (p n).Prime) (hq : (q n).Prime) (hfirst : p m = p n)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) (hne : d ≠ e)
    (hroughd : ∀ r ∈ d.primeFactors, q n ≤ r)
    (hroughe : ∀ r ∈ e.primeFactors, q m ≤ r)
    (hK : unitOverlap (primeWindowLower L p q ⟨n, d⟩) (primeWindowUpper L p ⟨n, d⟩)
      (primeWindowLower L p q ⟨m, e⟩) (primeWindowUpper L p ⟨m, e⟩) ≠ 0) :
    ∃ r : ℕ, r.Prime ∧ r ∣ e / d ∧ ¬ r ∣ d ∧ q m ≤ r ∧ r < q n := by
  have hcross := (unitOverlap_nonzero_cross hK).1
  simp only [primeWindowLower, primeWindowUpper, hfirst] at hcross
  have hpLog : 0 < Real.log (p n) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hh := mul_lt_mul_of_pos_right hcross hpLog
  rw [div_mul_cancel₀ _ hpLog.ne', div_mul_cancel₀ _ hpLog.ne'] at hh
  have hgap : Real.log e - Real.log d < Real.log (q n) := by linarith
  have hquot : e / d < q n := by
    by_contra h
    have hqle : q n ≤ e / d := le_of_not_gt h
    have hg := Real.log_le_log (by exact_mod_cast hq.pos : (0 : ℝ) < q n)
      (by exact_mod_cast hqle : ((q n : ℕ) : ℝ) ≤ ((e / d : ℕ) : ℝ))
    rw [log_quotient_of_dvd hd he hde] at hg
    linarith
  have hprod : (e / d) * d = e := Nat.div_mul_cancel hde
  have hlt : d < e := lt_of_le_of_ne (Nat.le_of_dvd he hde) hne
  have hr1 : 1 < e / d := by
    by_contra h
    have hz := Nat.mul_le_mul_right d (show e / d ≤ 1 by omega)
    rw [hprod, one_mul] at hz
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega : e / d ≠ 1)
  have hre : r ∣ e := dvd_trans hrd (Nat.div_dvd_of_dvd hde)
  have hrlow := hroughe r (hr.mem_primeFactors hre he.ne')
  have hrhigh : r < q n := (Nat.le_of_dvd (by omega : 0 < e / d) hrd).trans_lt hquot
  refine ⟨r, hr, hrd, ?_, hrlow, hrhigh⟩
  intro hrd'
  have hrl := hroughd r (hr.mem_primeFactors hrd' hd.ne')
  omega

/-- A divisor of an actual selected cofactor inherits its second-prime
threshold. No new roughness hypothesis is needed downstream. -/
theorem divisor_rough_of_smallestPairFactorization {n p q m d : ℕ}
    (h : smallestPairFactorization n p q m) (hd : d ∈ m.divisors) :
    ∀ r ∈ d.primeFactors, q ≤ r := by
  obtain ⟨_, _, _, _, hm, _, _, _, hrough, _⟩ := h
  intro r hr
  apply hrough r
  exact (Nat.prime_of_mem_primeFactors hr).mem_primeFactors
    (dvd_trans (Nat.dvd_of_mem_primeFactors hr) (Nat.dvd_of_mem_divisors hd)) hm.ne_zero

/-- The full original factorization certificates discharge the prime,
positivity and roughness obligations in the cross-family restriction.
A comparable interaction can survive only by introducing a genuinely new
prime between the two selected second primes. -/
theorem actual_chain_overlap_requires_new_small_prime (L : ℝ) (p q c : ℕ → ℕ)
    {n m d e : ℕ} (hn : smallestPairFactorization n (p n) (q n) (c n))
    (hm : smallestPairFactorization m (p m) (q m) (c m))
    (hd : d ∈ (c n).divisors) (he : e ∈ (c m).divisors)
    (hfirst : p m = p n) (hde : d ∣ e) (hne : d ≠ e)
    (hK : unitOverlap (primeWindowLower L p q ⟨n, d⟩) (primeWindowUpper L p ⟨n, d⟩)
      (primeWindowLower L p q ⟨m, e⟩) (primeWindowUpper L p ⟨m, e⟩) ≠ 0) :
    ∃ r : ℕ, r.Prime ∧ r ∣ e / d ∧ ¬ r ∣ d ∧ q m ≤ r ∧ r < q n := by
  exact chain_overlap_requires_new_small_prime L p q n m hn.1 hn.2.1 hfirst
    (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he) hde hne
    (divisor_rough_of_smallestPairFactorization hn hd)
    (divisor_rough_of_smallestPairFactorization hm he) hK

end
end RiemannGaussian.ZetaRieszCrossFamilyWindow
