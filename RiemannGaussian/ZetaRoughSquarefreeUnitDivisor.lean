/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreePrimeBalance

/-!
# Independent control of all nonunit divisor rows

At divisor cutoff one, the rough squarefree coefficient is minus the
nonnegative logarithmic weight on composites. The entire difference at a
larger cutoff is the literal sum of the nonunit divisor rows. Its full
complex filtered response has an independent geometric normalized bound,
uniform over every cutoff below the original moving cutoff. Thus all
Möbius-prefix variation can be removed with a proved error. The remaining
signed kernel sum over rough squarefree composites still needs its own
strict upper bound; positivity of its arithmetic weights does not prove it.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

/-- A nonnegative logarithmic weight on rough squarefree composites.
The unit contributes zero, and zero is excluded by squarefreeness. -/
def zetaRoughSquarefreeCompositeLogWeight (S : Finset ℕ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ ¬n.Prime ∧ ¬∃ a ∈ S, a ∣ n then Real.log n else 0

/-- These replacement arithmetic weights have one sign at every integer. -/
theorem zetaRoughSquarefreeCompositeLogWeight_nonneg (S : Finset ℕ) (n : ℕ) :
    0 ≤ zetaRoughSquarefreeCompositeLogWeight S n := by
  unfold zetaRoughSquarefreeCompositeLogWeight
  split_ifs
  · exact Real.log_natCast_nonneg n
  · exact le_rfl

/-- The cutoff-one completed prefix is exactly the negative logarithm
on all rough squarefree integers, including ordinary primes. -/
theorem zetaRoughSquarefreePrefixCoefficient_one (S : Finset ℕ) (n : ℕ) :
    zetaRoughSquarefreePrefixCoefficient 1 S n =
      if Squarefree n ∧ ¬∃ a ∈ S, a ∣ n then -(Real.log n : ℂ) else 0 := by
  by_cases hS : ∃ a ∈ S, a ∣ n <;> by_cases hn : Squarefree n <;>
    simp [zetaRoughSquarefreePrefixCoefficient, zetaSquarefreeDivisibilityPrefixCoefficient,
      zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient, hS, hn]

/-- The original composite carrier at divisor cutoff one is precisely
minus the nonnegative composite logarithmic weight. No prime is restored. -/
theorem zetaRoughSquarefreeCoefficient_one (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    zetaRoughSquarefreeCoefficient 1 S n =
      -(zetaRoughSquarefreeCompositeLogWeight S n : ℂ) := by
  rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime 1 le_rfl S hS n,
    zetaRoughSquarefreePrefixCoefficient_one]
  by_cases hp : n.Prime
  · have he : (∃ a ∈ S, a ∣ n) ↔ n ∈ S := by
      refine ⟨?_, fun hn ↦ ⟨n, hn, dvd_rfl⟩⟩
      rintro ⟨a, ha, han⟩
      rwa [(Nat.prime_dvd_prime_iff_eq (hS a ha) hp).mp han] at ha
    by_cases hnS : n ∈ S <;>
      simp [zetaRoughPrimeCoefficient, zetaRoughSquarefreeCompositeLogWeight,
        hp, hp.squarefree, he, hnS]
  · by_cases hn : Squarefree n <;> by_cases hs : ∃ a ∈ S, a ∣ n <;>
      simp [zetaRoughPrimeCoefficient, zetaRoughSquarefreeCompositeLogWeight, hp, hn, hs]

/-- The replacement weights satisfy the original genuine summable
arithmetic majorant, without an added analytic hypothesis. -/
theorem zetaRoughSquarefreeCompositeLogWeight_le_majorant (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    zetaRoughSquarefreeCompositeLogWeight S n ≤ zetaMoebiusLogMajorant n := by
  have h := norm_zetaRoughSquarefreeCoefficient_le 1 S n
  rw [zetaRoughSquarefreeCoefficient_one S hS n, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (zetaRoughSquarefreeCompositeLogWeight_nonneg S n)] at h
  exact h

/-- All cutoff dependence is exactly the original finite signed sum
over nonunit divisors. The squarefree, roughness and cofactor masks remain
inside this identity, and the logarithm at cofactor one is retained. -/
theorem zetaRoughSquarefreeCoefficient_add_compositeLog_eq_nonunit
    (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    zetaRoughSquarefreeCoefficient D S n + (zetaRoughSquarefreeCompositeLogWeight S n : ℂ) =
      if Squarefree n ∧ ¬∃ a ∈ S, a ∣ n then
        -(∑ d ∈ Finset.Ioc 1 D,
          if d ∣ n then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) else 0 := by
  have h1 := zetaRoughSquarefreeCoefficient_eq_prefix_add_prime 1 le_rfl S hS n
  rw [zetaRoughSquarefreeCoefficient_one S hS n] at h1
  rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS n]
  have he : zetaRoughSquarefreePrefixCoefficient D S n + zetaRoughPrimeCoefficient S n +
      (zetaRoughSquarefreeCompositeLogWeight S n : ℂ) =
        zetaRoughSquarefreePrefixCoefficient D S n - zetaRoughSquarefreePrefixCoefficient 1 S n := by
    linear_combination -h1
  rw [he, zetaRoughSquarefreePrefixCoefficient_one]
  by_cases hs : ∃ a ∈ S, a ∣ n
  · simp [zetaRoughSquarefreePrefixCoefficient, hs]
  · by_cases hn : Squarefree n
    · have hsum := Finset.sum_Ioc_add_eq_sum_Icc (f := fun d : ℕ ↦
        if d ∣ n then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) hD
      simp only [one_dvd, if_true, ArithmeticFunction.moebius_apply_one,
        Int.cast_one, one_mul, Nat.div_one] at hsum
      simp [zetaRoughSquarefreePrefixCoefficient, zetaSquarefreeDivisibilityPrefixCoefficient,
        zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient, hs, hn,
        mul_ite] at hsum ⊢
      linear_combination hsum
    · simp [zetaRoughSquarefreePrefixCoefficient, zetaSquarefreeDivisibilityPrefixCoefficient, hs, hn]

/-- The full complex kernel sum with the nonnegative composite weights. -/
def zetaRoughSquarefreeCompositeLogFilter (p : Polynomial ℂ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, (zetaRoughSquarefreeCompositeLogWeight S n : ℂ) * zetaPrimeFilterKernel p N s n

/-- The replacement series genuinely converges in the Euler half-plane. -/
theorem summable_zetaRoughSquarefreeCompositeLogFilter (p : Polynomial ℂ) (N : ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ (zetaRoughSquarefreeCompositeLogWeight S n : ℂ) *
      zetaPrimeFilterKernel p N s n) := by
  have h := (summable_zetaRoughSquarefreeFilter p 1 N le_rfl S hS hs).neg
  apply h.congr
  intro n
  rw [zetaRoughSquarefreeCoefficient_one S hS n]
  ring

/-- The unit-divisor carrier is exactly the negative composite log sum,
with the full original complex polynomial and ordinate unchanged. -/
theorem zetaRoughSquarefreeFilter_one (p : Polynomial ℂ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) (s : ℂ) :
    zetaRoughSquarefreeFilter p 1 S N s = -zetaRoughSquarefreeCompositeLogFilter p S N s := by
  simp only [zetaRoughSquarefreeFilter, zetaRoughSquarefreeCompositeLogFilter,
    zetaRoughSquarefreeCoefficient_one S hS, neg_mul, tsum_neg]

/-- The full nonunit-divisor response is a difference of two completed
prefixes. Their ordinary-prime corrections cancel exactly before a norm
is taken, so the composite restriction does not require a new premise. -/
theorem zetaRoughSquarefreeFilter_add_compositeLog_eq_prefix_sub
    (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    zetaRoughSquarefreeFilter p D S N s + zetaRoughSquarefreeCompositeLogFilter p S N s =
      zetaRoughSquarefreePrefixFilter p D S N s - zetaRoughSquarefreePrefixFilter p 1 S N s := by
  have h1 := zetaRoughSquarefreeFilter_eq_prefix_add_prime p 1 N le_rfl S hS hs
  rw [zetaRoughSquarefreeFilter_one p S hS N s] at h1
  rw [zetaRoughSquarefreeFilter_eq_prefix_add_prime p D N hD S hS hs]
  linear_combination -h1

/-- A single independent geometric bound controls every completed
prefix below the original divisor schedule, uniformly in the order and
the choice of cutoff. No source convergence is used in this estimate. -/
theorem exists_zetaRightHalfRoughSquarefreePrefix_uniform_cutoff_bound
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D : ℕ,
      D ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaRoughSquarefreePrefixFilter (zetaRightHalfPoleJetFilter rho hrho) D
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
  refine ⟨C * u * B + 1, by positivity, fun N D hD ↦ ?_⟩
  have hDR : (D : ℝ) ≤ q ^ N :=
    (show (D : ℝ) ≤ zetaMoebiusGeometricCutoff q N by exact_mod_cast hD).trans
      (Nat.floor_le (pow_nonneg hq N))
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

/-- All nonunit divisor rows together have an independent geometric
normalized bound, for every cutoff up to the actual moving schedule. -/
theorem exists_zetaRightHalfRoughSquarefree_nonunit_error_bound
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D : ℕ, 1 ≤ D →
      D ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho) D
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) +
        zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))‖ ≤
        C * zetaRightHalfSquareSieveRate rho ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfRoughSquarefreePrefix_uniform_cutoff_bound rho hrho
  refine ⟨2 * C, by positivity, fun N D hD hDtop ↦ ?_⟩
  rw [zetaRoughSquarefreeFilter_add_compositeLog_eq_prefix_sub _ _ _ hD _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num), mul_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (hb N D hDtop)
    (hb N 1 (hD.trans hDtop))).trans_eq (by ring))

/-- At the original moving cutoff, the entire signed nonunit-divisor
response tends to zero at the selected-zero normalization. -/
theorem tendsto_zetaRightHalfRoughSquarefree_nonunit (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) +
      zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfRoughSquarefree_nonunit_error_bound rho hrho
  obtain ⟨h0, h1⟩ := zetaRightHalfSquareSieveRate_bounds rho hrho
  apply squeeze_zero_norm (fun N ↦ hb N _ (zetaRightHalfPoleJetCutoff_pos rho hrho N) le_rfl)
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul C

/-- The original multiplicity source survives on the nonnegative
logarithmic composite weights. The kernel and its phases are unchanged;
the sign change records that the removed unit-divisor row was negative. -/
theorem tendsto_zetaRightHalfRoughSquarefreeCompositeLogFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have h := (tendsto_zetaRightHalfRoughSquarefree_nonunit rho hrho).sub
    (tendsto_zetaRightHalfRoughSquarefreeFilter rho hrho)
  simp only [zero_sub, neg_neg] at h
  convert h using 1
  funext N
  ring

/-- The composite logarithmic sum and the original Fourier carrier
have opposite signs up to a completely proved finite vanishing error.
All physical localization and complementary-frequency costs are included. -/
theorem exists_zetaRightHalfRoughSquarefreeCompositeLog_fourier_error_bound
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) +
            zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ ≤
        C * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfRoughSquarefree_nonunit_error_bound rho hrho
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
  have he : v * (zetaRoughSquarefreeCompositeLogFilter p S N s +
      zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N) =
      v * (zetaRoughSquarefreeFilter p D S N s + zetaRoughSquarefreeCompositeLogFilter p S N s) -
        v * (zetaRoughSquarefreeFilter p D S N s -
          zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N) := by ring
  change ‖v * (zetaRoughSquarefreeCompositeLogFilter p S N s +
    zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add (hb N D (zetaRightHalfPoleJetCutoff_pos rho hrho N) le_rfl)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfRoughSquarefreeWindowFourierCarrier,
    zetaRightHalfRoughSquarefreeWindowCoefficient, zetaRoughSquarefreeFilter,
    zetaArithmeticFilter, p, a, D, S, s] using
      norm_zetaArithmeticFilter_sub_averaged_window_le a
        (norm_zetaRoughSquarefreeCoefficient_le D S) p N rho.1.im hN

/-- The new logarithmic composite sum controls the original signed
reflection target with an explicit vanishing allowance. An independent
strict upper bound for its real part would still be needed to close RH. -/
theorem exists_zetaRightHalfRoughSquarefreeCompositeLog_reflection_error_bound
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤
        (C * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfRoughSquarefreeCompositeLog_fourier_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let L := zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
    (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L + zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re - 2 * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.add_re,
      zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection]
    ring
  change |u * L.re / 2 - u * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤ _
  have he : u * L.re / 2 - u * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N =
      z.re / 2 := by rw [hz]; ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
