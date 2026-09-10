/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusGrowingSieve
import RiemannGaussian.ZetaMoebiusDistinctPrimeTail

/-!
# The surviving source has separated distinct-prime divisors

Simultaneous mixed-prime deletion commutes with the already proved
prime-power removal. The final arithmetic carrier has at least two
distinct prime divisors, every pair product is at least the cofinal sieve
threshold, and the original pole-jet response differs from it by an
independently proved geometric error. Its signed bound remains open.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The literal distinct-prime coefficient on the surviving products. -/
def zetaMoebiusSievedPrimeCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if ¬(∃ P ∈ S, P ∣ n) then zetaMoebiusDistinctPrimeCoefficient D n else 0

/-- No prime-power contribution is accidentally deleted: every selected
mixed-prime sector lies wholly inside the distinct-prime coefficient. -/
theorem zetaMoebiusDistinctPrimeCoefficient_eq_sieve_add_remainder (D : ℕ) (S : Finset ℕ)
    (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) (n : ℕ) :
    zetaMoebiusDistinctPrimeCoefficient D n = zetaMoebiusSieveCoefficient D S n +
      zetaMoebiusSievedPrimeCoefficient D S n := by
  by_cases hn : ∃ P ∈ S, P ∣ n
  · obtain ⟨P, hP, hPn⟩ := hn
    have hnprime : ¬IsPrimePow n := fun h ↦ (hS P hP).2.2 (h.dvd hPn (hS P hP).2.1)
    have he := zetaMoebiusLogTailCoefficient_eq_primePower_add_distinct D n
    have hn' : ∃ P ∈ S, P ∣ n := ⟨P, hP, hPn⟩
    simp only [zetaMoebiusSieveCoefficient, zetaMoebiusSievedPrimeCoefficient, hn',
      not_true_eq_false, if_true, if_false, add_zero]
    simpa only [zetaMoebiusTailPrimePowerCoefficient, if_neg hnprime, zero_add] using he.symm
  · simp [zetaMoebiusSieveCoefficient, zetaMoebiusSievedPrimeCoefficient, hn]

/-- The original filtered distinct-prime sum in its multiplicative kernel form. -/
theorem hasSum_zetaMoebiusDistinctPrimeFilter_kernel (p : Polynomial ℂ) (D N : ℕ)
    (hD : 1 ≤ D) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusDistinctPrimeCoefficient D n * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusDistinctPrimeFilter p D N s) := by
  apply (hasSum_zetaMoebiusDistinctPrimeFilter p D N hD hs).congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat]
  ring

/-- The final surviving arithmetic sum; its definition retains the
literal coefficient, support restriction, and complete complex kernel. -/
def zetaMoebiusSievedPrimeFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaMoebiusSievedPrimeCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- Genuine convergence identifies the final arithmetic sum with the
distinct-prime tail minus the independently controlled simultaneous deletion. -/
theorem hasSum_zetaMoebiusSievedPrimeFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusSievedPrimeCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusDistinctPrimeFilter p D N s - zetaMoebiusSieveFilter p D S N s) := by
  have h := (hasSum_zetaMoebiusDistinctPrimeFilter_kernel p D N hD hs).sub
    (summable_zetaMoebiusSieveKernel p D S N hs).hasSum
  apply h.congr_fun
  intro n
  rw [zetaMoebiusDistinctPrimeCoefficient_eq_sieve_add_remainder D S hS n]
  ring

/-- The exact filtered reconstruction preserves both arithmetic pieces. -/
theorem zetaMoebiusDistinctPrimeFilter_eq_sieve_add_remainder (p : Polynomial ℂ) (D N : ℕ)
    (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P)
    {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusDistinctPrimeFilter p D N s = zetaMoebiusSieveFilter p D S N s +
      zetaMoebiusSievedPrimeFilter p D S N s := by
  rw [zetaMoebiusSievedPrimeFilter, (hasSum_zetaMoebiusSievedPrimeFilter p D N hD S hS hs).tsum_eq]
  ring

/-- All removed terms, including the original finite head, prime powers,
and every sieve overlap, fit one proved geometric error allowance. -/
theorem exists_zetaRightHalfSievedPrimeTail_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaMoebiusSievedPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfMoebiusSieve rho N) N (3 / 2 + I * rho.1.im))‖ ≤
        C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_zetaRightHalfDistinctPrimeTail_error_bound rho hrho
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_zetaRightHalfMoebiusSieve_uniform_bound rho hrho
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro N
  obtain ⟨hS, hcost⟩ := zetaRightHalfMoebiusSieve_budget rho hrho N
  have h := hb₂ N (zetaRightHalfMoebiusSieve rho N) hS hcost
  have halg (a b c : ℂ) : a - (b - c) = a - b + c := by ring
  rw [zetaMoebiusSievedPrimeFilter,
    (hasSum_zetaMoebiusSievedPrimeFilter _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _ hS
      (by norm_num)).tsum_eq, halg, mul_add]
  exact (norm_add_le _ _).trans ((add_le_add (hb₁ N) h).trans_eq (by ring))

/-- The final distinct-prime arithmetic carrier retains the whole
negative multiplicity source after the explicit cofinal sieve. -/
theorem tendsto_zetaRightHalfSievedPrimeTail (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSievedPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfMoebiusSieve rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfDistinctPrimeTail rho hrho).sub
    (tendsto_zetaRightHalfMoebiusGrowingSieve rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaMoebiusSievedPrimeFilter,
    (hasSum_zetaMoebiusSievedPrimeFilter _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (zetaRightHalfMoebiusSieve_budget rho hrho N).1 (by norm_num)).tsum_eq, mul_sub]

/-- Every pair of distinct prime divisors in a surviving product has
product at least the sieve threshold. One individual prime can still be small. -/
theorem zetaMoebiusSieveHead_survivor_prime_pair {H n p q : ℕ}
    (hS : ¬∃ P ∈ zetaMoebiusSieveHead H, P ∣ n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpn : p ∣ n) (hqn : q ∣ n) : H ≤ p * q := by
  have hmix : ¬IsPrimePow (p * q) := by
    intro h
    obtain ⟨r, _, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    exact hpq ((hu p ⟨hp, Nat.dvd_mul_right p q⟩).trans (hu q ⟨hq, Nat.dvd_mul_left q p⟩).symm)
  have h1 : p * q ≠ 1 := fun h ↦ hp.ne_one (Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_mul_right p q))
  exact (zetaMoebiusSieveHead_survivor_iff H n).mp hS (p * q) (Nat.mul_pos hp.pos hq.pos) h1 hmix
    (((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpn hqn)

/-- A nonzero final coefficient has the original large-product support,
two distinct prime divisors, and separation for every such prime pair. -/
theorem zetaMoebiusSievedPrimeCoefficient_support (D H n : ℕ)
    (hn : zetaMoebiusSievedPrimeCoefficient D (zetaMoebiusSieveHead H) n ≠ 0) :
    2 * (D + 1) ≤ n ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n) ∧
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → p ∣ n → q ∣ n → H ≤ p * q := by
  have hS : ¬∃ P ∈ zetaMoebiusSieveHead H, P ∣ n := by
    by_contra h
    simp [zetaMoebiusSievedPrimeCoefficient, h] at hn
  have hd : zetaMoebiusDistinctPrimeCoefficient D n ≠ 0 := by
    simpa only [zetaMoebiusSievedPrimeCoefficient, if_pos hS] using hn
  obtain ⟨hlarge, hprimes⟩ := zetaMoebiusDistinctPrimeCoefficient_support D n hd
  exact ⟨hlarge, hprimes, fun _ _ hp hq hpq hpn hqn ↦
    zetaMoebiusSieveHead_survivor_prime_pair hS hp hq hpq hpn hqn⟩

end
end RiemannGaussian
