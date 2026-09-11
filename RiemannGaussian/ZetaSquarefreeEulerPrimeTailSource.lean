/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerFamilyDecay
import RiemannGaussian.ZetaRoughPrimeLogLcmBound

/-!
# The ordinary-prime tail after complete divisor-family decay

The complete logarithmic matrix and the small-prime insertion both have
independent decay at the current squared divisor cutoff. Their exact
arithmetic identity leaves the ordinary-prime correction explicit. The
remaining large-prime source is consequently the negative of that tail
up to a vanishing error. No independent bound on that tail is assumed or
claimed here.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

/-- The original ordinary-prime correction with the unchanged
complex polynomial filter and physical logarithmic kernel. -/
def primeLogResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The ordinary-prime correction is a genuinely summable part of
the complete logarithmic divisor correlation at every moment order. -/
theorem summable_primeLogResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_logResponse p S (Finset.Icc 1 D) hS
    (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) N hs).summable.indicator {n : ℕ | n.Prime}
  apply h.congr
  intro n
  by_cases hp : n.Prime
  · rw [Set.indicator_of_mem (show n ∈ {k : ℕ | k.Prime} from hp)]
    simp [primeCorrectionCoefficient, hp]
  · rw [Set.indicator_of_notMem (show n ∉ {k : ℕ | k.Prime} from hp)]
    simp [primeCorrectionCoefficient, hp]

/-- The correction is exactly the ordinary primes beyond the common
cutoff, with the original sieve, logarithm, and complex phase retained. -/
theorem primeLogResponse_eq_tail (p : Polynomial ℂ) {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (N : ℕ) (s : ℂ) :
    primeLogResponse p D S N s = ∑' n,
      if n.Prime ∧ D < n then RoughSquarefreeBare.coefficient S 1 n * (Real.log n : ℂ) *
        zetaPrimeFilterKernel p N s n else 0 := by
  apply tsum_congr
  intro n
  rw [primeCorrectionCoefficient_eq_tail hD]
  split_ifs <;> simp

/-- On an ordinary prime the full divisor mask has disappeared:
the remaining coefficient is its logarithm exactly when it lies beyond
the cutoff and was not among the excluded primes. -/
theorem primeCorrectionCoefficient_eq_prime_tail {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    primeCorrectionCoefficient D S n =
      if n.Prime ∧ D < n ∧ n ∉ S then (Real.log n : ℂ) else 0 := by
  by_cases hp : n.Prime
  · have hrough : (∃ a ∈ S, a ∣ n) ↔ n ∈ S := by
      constructor
      · rintro ⟨a, ha, han⟩
        exact (Nat.prime_dvd_prime_iff_eq (hS a ha) hp).mp han ▸ ha
      · exact fun hn ↦ ⟨n, hn, dvd_refl n⟩
    by_cases hcut : D < n <;> by_cases hnS : n ∈ S <;>
      simp [primeCorrectionCoefficient_eq_tail hD, RoughSquarefreeBare.coefficient,
        hp, hp.squarefree, hrough, hcut, hnS]
  · simp [primeCorrectionCoefficient, hp]

/-- The surviving correction is literally a sum over ordinary
primes, with no divisor matrix, Möbius mask, or squarefree weight left. -/
theorem primeLogResponse_eq_prime_sum (p : Polynomial ℂ) {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (N : ℕ) (s : ℂ) :
    primeLogResponse p D S N s = ∑' n,
      if n.Prime ∧ D < n ∧ n ∉ S then (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n else 0 := by
  apply tsum_congr
  intro n
  rw [primeCorrectionCoefficient_eq_prime_tail hD S hS]
  split_ifs <;> simp

/-- Adding back the ordinary primes to the original large-prime
source gives the complete logarithmic matrix minus the exact small-prime
insertion. Every equality is between convergent arithmetic series. -/
theorem large_add_prime_eq_log_sub_small (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    RoughPrimeLog.response p D S (N + 1) s + primeLogResponse p D S (N + 1) s =
      logResponse p S (Finset.Icc 1 D) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) (N + 1) s -
        RoughPrimeLog.smallResponse p D S (N + 1) s := by
  have hl := (RoughPrimeLog.hasSum_response p D hD S hS N hs).summable
  have hp := summable_primeLogResponse p D S hS (N + 1) hs
  have hf := (hasSum_logResponse p S (Finset.Icc 1 D) hS
    (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) (N + 1) hs).summable
  have hsml := (RoughPrimeLog.hasSum_smallResponse p D S hS N hs).summable
  rw [RoughPrimeLog.response, primeLogResponse, logResponse, RoughPrimeLog.smallResponse,
    ← hl.tsum_add hp, ← hf.tsum_sub hsml]
  apply tsum_congr
  intro n
  rw [RoughPrimeLog.coefficient_eq_square_sub_small, squareCoefficient_eq_log_sub_prime]
  ring

/-- The unchanged normalization of the literal ordinary-prime tail,
using exactly the current zero-isolating polynomial and sieve. -/
def normalizedPrimeLogResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    primeLogResponse (zetaRightHalfPoleJetFilter rho hrho) D
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The exact original normalized source is recovered before taking
any limit or discarding the ordinary-prime correction. -/
theorem normalized_large_add_prime_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    RoughPrimeLogLcm.normalizedLargeResponse rho hrho N D + normalizedPrimeLogResponse rho hrho N D =
      normalizedLogResponse rho (zetaRightHalfPoleJetFilter rho hrho) N D
        (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) -
          RoughPrimeLogLcm.normalizedSmallResponse rho hrho N D := by
  have h := large_add_prime_eq_log_sub_small (zetaRightHalfPoleJetFilter rho hrho) D hD
    (zetaRightHalfPrimePatternPrimes rho N)
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1)
    (N - 1) (by norm_num : (1 : ℝ) < (3 / 2 + I * rho.1.im : ℂ).re)
  rw [show N - 1 + 1 = N by omega] at h
  rw [RoughPrimeLogLcm.normalizedLargeResponse, normalizedPrimeLogResponse,
    normalizedLogResponse, RoughPrimeLogLcm.normalizedSmallResponse, ← mul_add, h, mul_sub]

/-- The full matrix-containing remainder now decays independently at
every moving cutoff through the squared schedule. The ordinary-prime
tail is kept explicitly; this theorem does not bound it separately. -/
theorem tendsto_large_add_primeCorrection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦ RoughPrimeLogLcm.normalizedLargeResponse rho hrho N (D N) +
      normalizedPrimeLogResponse rho hrho N (D N)) atTop (𝓝 0) := by
  have h := (tendsto_normalized_moebius_logResponse rho hrho D (hD.mono (fun _ h ↦ h.2))
    (zetaRightHalfPoleJetFilter rho hrho)).sub (RoughPrimeLogLcm.tendsto_square_cutoff rho hrho D hD)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hD, eventually_ge_atTop 1] with N hD hN
  exact (normalized_large_add_prime_eq rho hrho hN hD.1).symm

/-- Under the hypothetical right-half zero, the explicit ordinary-prime
tail carries the negative multiplicity source. This identifies the
remaining obstruction; it does not supply an independent upper bound. -/
theorem tendsto_normalizedPrimeLogResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦ normalizedPrimeLogResponse rho hrho N (D N)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_large_add_primeCorrection rho hrho D hD).sub
    (RoughPrimeLogLcm.tendsto_large_square_cutoff rho hrho D hD)
  simpa only [zero_sub, add_sub_cancel_left] using h

end
end RiemannGaussian.SquarefreeEulerQuadratic
