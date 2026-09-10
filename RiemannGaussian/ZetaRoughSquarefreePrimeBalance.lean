/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreeWindowSource

/-!
# The complete rough squarefree prefix and its ordinary-prime correction

Completing the proposed divisor--cofactor sum restores ordinary primes.
The complete prefix has an independent geometric normalized bound, with
every squarefree and prime-avoidance overlap included. The excluded primes
are therefore not an error term: they carry the full surviving source.
This tests the proposed bilinear completion without discarding its phase,
and identifies why a bound for the completed sum alone does not close RH.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The literal negative divisor prefix on all rough squarefree
integers, including ordinary primes. -/
def zetaRoughSquarefreePrefixCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if ∃ a ∈ S, a ∣ n then 0 else zetaSquarefreeDivisibilityPrefixCoefficient D ∅ n

/-- The ordinary-prime correction outside the selected prime family. -/
def zetaRoughPrimeCoefficient (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n.Prime ∧ n ∉ S then (Real.log n : ℂ) else 0

private theorem prime_selected_dvd_iff (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {n : ℕ} (hn : n.Prime) : (∃ a ∈ S, a ∣ n) ↔ n ∈ S := by
  constructor
  · rintro ⟨a, ha, han⟩
    rwa [Nat.prime_dvd_prime_iff_eq (hS a ha) hn |>.mp han] at ha
  · intro h
    exact ⟨n, h, dvd_rfl⟩

/-- Completing the rough squarefree divisor prefix requires exactly
the ordinary primes that the original composite carrier excludes. -/
theorem zetaRoughSquarefreeCoefficient_eq_prefix_add_prime (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    zetaRoughSquarefreeCoefficient D S n =
      zetaRoughSquarefreePrefixCoefficient D S n + zetaRoughPrimeCoefficient S n := by
  by_cases h : ∃ a ∈ S, a ∣ n
  · have hp : ¬(n.Prime ∧ n ∉ S) := by
      rintro ⟨hn, hnot⟩
      exact hnot ((prime_selected_dvd_iff S hS hn).mp h)
    simp [zetaRoughSquarefreeCoefficient, zetaRoughSquarefreePrefixCoefficient,
      zetaRoughPrimeCoefficient, h, hp]
  · have hcard : (S.filter (fun a ↦ a ∣ n)).card = 0 := by
      simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun a ha han ↦ h ⟨a, ha, han⟩
    have hpair : ¬∃ P ∈ primePairFactors S, P ∣ n := by
      intro hp
      have hc := (primePairSieve_card_iff S hS n).mpr hp
      omega
    have hp : (n.Prime ∧ n ∉ S) ↔ n.Prime := by
      refine ⟨And.left, fun hn ↦ ⟨hn, ?_⟩⟩
      exact fun hnS ↦ h ⟨n, hnS, dvd_rfl⟩
    simp only [zetaRoughSquarefreeCoefficient, zetaRoughSquarefreePrefixCoefficient,
      if_neg h, zetaSquarefreeCoefficient, zetaMoebiusSievedPrimeCoefficient, if_pos hpair,
      zetaRoughPrimeCoefficient, hp]
    exact zetaSquarefreeDistinctCoefficient_eq_prefix_add_prime D hD n

/-- On each retained ordinary prime the completed prefix is exactly
minus its logarithm, independently of the positive divisor cutoff. -/
theorem zetaRoughSquarefreePrefixCoefficient_prime (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hn : n.Prime) (hnS : n ∉ S) :
    zetaRoughSquarefreePrefixCoefficient D S n = -(Real.log n : ℂ) := by
  have h := zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS n
  have hz : zetaRoughSquarefreeCoefficient D S n = 0 := by
    simp [zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient,
      zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient, hn.primeFactors]
  rw [hz, zetaRoughPrimeCoefficient, if_pos ⟨hn, hnS⟩] at h
  linear_combination -h

/-- Every signed first-power intersection is retained in the exact
completed prefix, before applying any kernel or norm. -/
theorem zetaRoughSquarefreePrefixCoefficient_eq_subsets (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    zetaRoughSquarefreePrefixCoefficient D S n =
      ∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card * zetaSquarefreeDivisibilityPrefixCoefficient D W n := by
  calc
    _ = ∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        (if (∏ a ∈ W, a) ∣ n then zetaSquarefreeDivisibilityPrefixCoefficient D ∅ n else 0) :=
      (primeAvoidance_eq_signed_subsets S hS
        (zetaSquarefreeDivisibilityPrefixCoefficient D ∅) n).symm
    _ = _ := Finset.sum_congr rfl (fun W _ ↦ by
      rw [zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator D W n])

/-- The full complex filtered prefix, with no ordinary-prime exclusion. -/
def zetaRoughSquarefreePrefixFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaRoughSquarefreePrefixCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The actual filtered ordinary primes outside the selected family. -/
def zetaRoughPrimeFilter (p : Polynomial ℂ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaRoughPrimeCoefficient S n * zetaPrimeFilterKernel p N s n

/-- The complete prefix series genuinely converges and equals the
finite signed transform of the convergent squarefree intersections. -/
theorem hasSum_zetaRoughSquarefreePrefixFilter (p : Polynomial ℂ) (D N : ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaRoughSquarefreePrefixCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card * zetaSquarefreeDivisibilityPrefixFilter p D W N s) := by
  have h := hasSum_sum (s := S.powerset) (fun W hW ↦
    (summable_zetaSquarefreeDivisibilityPrefixFilter p D N W
      (fun a ha ↦ hS a (Finset.mem_powerset.mp hW ha)) hs).hasSum.mul_left ((-1 : ℂ) ^ W.card))
  apply h.congr_fun
  intro n
  rw [zetaRoughSquarefreePrefixCoefficient_eq_subsets D S hS n, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun W _ ↦ by ring)

/-- The prime correction is genuinely summable; this follows from
the exact difference of the original carrier and the completed prefix. -/
theorem summable_zetaRoughPrimeFilter (p : Polynomial ℂ) (N : ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaRoughPrimeCoefficient S n * zetaPrimeFilterKernel p N s n) := by
  have h := (summable_zetaRoughSquarefreeFilter p 1 N le_rfl S hS hs).sub
    (hasSum_zetaRoughSquarefreePrefixFilter p 1 N S hS hs).summable
  apply h.congr
  intro n
  rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime 1 le_rfl S hS n]
  ring

/-- The complete signed series splits exactly into its bounded
prefix and its ordinary-prime correction, retaining every complex phase. -/
theorem zetaRoughSquarefreeFilter_eq_prefix_add_prime (p : Polynomial ℂ) (D N : ℕ)
    (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    zetaRoughSquarefreeFilter p D S N s =
      zetaRoughSquarefreePrefixFilter p D S N s + zetaRoughPrimeFilter p S N s := by
  unfold zetaRoughSquarefreeFilter zetaRoughSquarefreePrefixFilter zetaRoughPrimeFilter
  simp_rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS, add_mul]
  exact (hasSum_zetaRoughSquarefreePrefixFilter p D N S hS hs).summable.tsum_add
    (summable_zetaRoughPrimeFilter p N S hS hs)

/-- The entire completed prefix has an independent product bound,
including every first-power and square overlap. No arithmetic cancellation
estimate for the remaining prime correction is assumed. -/
theorem exists_zetaRoughSquarefreePrefixFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖zetaRoughSquarefreePrefixFilter p D S N (3 / 2 + I * y)‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquarefreeDivisibilityPrefixFilter_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  let w := primeSquareCorrectedWeight τ
  refine ⟨C * Real.exp (2 * primeSquareWeightMass τ), by positivity, ?_⟩
  intro p D N R S hS
  let A := C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw : ∀ a, 0 ≤ w a := primeSquareCorrectedWeight_nonneg τ
  rw [zetaRoughSquarefreePrefixFilter,
    (hasSum_zetaRoughSquarefreePrefixFilter p D N S (fun a ha ↦ (hS a ha).1)
      (by norm_num)).tsum_eq]
  calc
    _ ≤ ∑ W ∈ S.powerset, A * ∏ a ∈ W, w a := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro W hW
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hb p D N W (fun a ha ↦ (hS a (Finset.mem_powerset.mp hW ha)).1)
    _ = A * ∏ a ∈ S, (1 + w a) := by rw [Finset.prod_one_add, Finset.mul_sum]
    _ ≤ A * ∏ a ∈ S, (1 + 2 * w a) := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun a _ ↦ by linarith [hw a])
        (fun a _ ↦ by linarith [hw a])) hA
    _ ≤ A * (Real.exp (2 * primeSquareWeightMass τ) * Real.exp (4 * Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left
        (prod_one_add_primeSquareCorrectedWeight_le S R hS (zetaSquareSieveExponent_gt_half hr1)) hA
    _ = _ := by dsimp [A]; ring

/-- At the actual moving cutoffs the completed signed prefix has
a geometric normalized bound, uniform in the moment order. -/
theorem exists_zetaRightHalfRoughSquarefreePrefix_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaRoughSquarefreePrefixFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * zetaRightHalfSquareSieveRate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := zetaRightHalfSquareSieveRadius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  obtain ⟨hr, hr1, _⟩ := zetaRightHalfSquareSieveRadius_bounds rho hrho
  have hq : 0 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le.trans' (by norm_num)
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_zetaRoughSquarefreePrefixFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B + 1, by positivity, fun N ↦ ?_⟩
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq N)
  have he := exp_primePatternCutoff_sqrt_le rho hrho N
  have hbound := hb p D N (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) *
        r⁻¹ ^ N * B) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * q ^ N * r⁻¹ ^ N * B) := by gcongr
    _ = (C * u * B) * ((u * q ^ 2) / r) ^ N := by
      rw [div_pow, mul_pow, pow_succ, show (q ^ 2) ^ N = (q ^ N) ^ 2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * zetaRightHalfSquareSieveRate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_rate hu]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (pow_nonneg (zetaRightHalfSquareSieveRate_bounds rho hrho).1.le N)

/-- The complete signed rough squarefree prefix decays after source
normalization. Its ordinary-prime terms remain part of this cancellation. -/
theorem tendsto_zetaRightHalfRoughSquarefreePrefixFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRoughSquarefreePrefixFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfRoughSquarefreePrefix_error_bound rho hrho
  obtain ⟨h0, h1⟩ := zetaRightHalfSquareSieveRate_bounds rho hrho
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul C

/-- Ordinary primes outside the moving quadratic cutoff carry the
full source. Thus controlling the completed divisor sum does not control
its composite restriction: the excluded prime correction is not small. -/
theorem tendsto_zetaRightHalfRoughPrimeFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRoughPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfRoughSquarefreeFilter rho hrho).sub
    (tendsto_zetaRightHalfRoughSquarefreePrefixFilter rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaRoughSquarefreeFilter_eq_prefix_add_prime _ _ N
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)]
  ring

/-- The ordinary-prime sum differs from the actual centered Fourier
carrier by a completely proved vanishing allowance. This compares the
full complex objects, without losing the ordinate or polynomial phases. -/
theorem exists_zetaRightHalfRoughPrime_fourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaRoughPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) -
            zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ ≤
        C * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfRoughSquarefreePrefix_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  let S := zetaRightHalfPrimePatternPrimes rho N
  let s : ℂ := 3 / 2 + I * rho.1.im
  let a := zetaRoughSquarefreeCoefficient D S
  let v : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hv : ‖v‖ ≤ 1 := by
    have hu : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [v]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    exact pow_le_one₀ hu (by linarith)
  have hid := zetaRoughSquarefreeFilter_eq_prefix_add_prime p D N
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) S
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (s := s) (by norm_num [s])
  have he : v * (zetaRoughPrimeFilter p S N s -
      zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N) =
      -(v * zetaRoughSquarefreePrefixFilter p D S N s) +
        v * (zetaRoughSquarefreeFilter p D S N s -
          zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N) := by rw [hid]; ring
  change ‖v * (zetaRoughPrimeFilter p S N s -
    zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfRoughSquarefreeWindowFourierCarrier,
    zetaRightHalfRoughSquarefreeWindowCoefficient, zetaRoughSquarefreeFilter,
    zetaArithmeticFilter, p, a, D, S, s] using
      norm_zetaArithmeticFilter_sub_averaged_window_le a
        (norm_zetaRoughSquarefreeCoefficient_le D S) p N rho.1.im hN

/-- The actual signed odd-reflection work equals the negative real
ordinary-prime contribution up to the proved complete finite allowance.
Neither completing the divisor sum nor deleting its restored primes is
an independent strict upper bound on this work. -/
theorem exists_zetaRightHalfRoughPrime_reflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaRoughPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤
        (C * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfRoughPrime_fourier_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let P := zetaRoughPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
    (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (P - zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (P.re + 2 * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * P.re / 2 - u * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤ _
  have he : -u * P.re / 2 - u * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N =
      -z.re / 2 := by rw [hz]; ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
