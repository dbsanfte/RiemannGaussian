/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerLogDecay
import RiemannGaussian.ZetaSquarefreeEulerQuadratic
import RiemannGaussian.ZetaRoughDivisorLinearBound

/-!
# Complete logarithmic decay for growing complex divisor families

The exact marked expansion is retained before paying the total mass of
both complex coefficient families. The full quadratic prime sieve is
allowed. At the squared divisor cutoff, the existing source normalization
pays even the complete pair count, leaving the logarithmic subexponential
saving. Ordinary primes remain part of these complete arithmetic series.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The complete squarefree arithmetic response with its physical
logarithm and both original complex divisor families. -/
def logResponse (p : Polynomial ℂ) (S T : Finset ℕ) (w v : ℕ → ℂ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, coefficient S T w v n * (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n

/-- Every ordered pair of marks remains in an exact identity of
genuinely convergent logarithmic series, including incompatible marks. -/
theorem hasSum_logResponse (p : Polynomial ℂ) (S T : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient S T w v n * (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n)
      (∑ d ∈ T, ∑ e ∈ T, (w d * v e) * SquarefreeEulerLog.response p S (Nat.lcm d e) N s) := by
  have h := hasSum_sum (s := T) (fun d _ ↦ hasSum_sum (s := T) (fun e _ ↦
    (SquarefreeEulerLog.summable_response p S hS (Nat.lcm d e) N hs).hasSum.mul_left (w d * v e)))
  apply h.congr_fun
  intro n
  rw [coefficient_eq_lcm_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun d _ ↦ Finset.sum_congr rfl (fun e _ ↦ by ring))

/-- The complete logarithmic response equals the full complex lcm
sum before taking norms or restricting the divisor families. -/
theorem logResponse_eq_lcm_sum (p : Polynomial ℂ) (S T : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    logResponse p S T w v N s =
      ∑ d ∈ T, ∑ e ∈ T, (w d * v e) * SquarefreeEulerLog.response p S (Nat.lcm d e) N s :=
  (hasSum_logResponse p S T hS w v N hs).tsum_eq

/-- The physical logarithm also commutes with the exact complex
Selberg diagonalization, keeping its raised polynomial explicit. -/
theorem logResponse_eq_cutoff_diagonal (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    logResponse p S (Finset.Icc 1 D) w v N s =
      zetaMomentSequenceFilter (Polynomial.X * SquarefreeEulerLog.raisedPolynomial p N)
        (fun k ↦ signedTaylorMoment k (diagonal D S w v) s) N := by
  have h := hasSum_cutoff_filter D S hS w v
    (Polynomial.X * SquarefreeEulerLog.raisedPolynomial p N) N hs
  convert h.tsum_eq using 1
  apply tsum_congr
  intro n
  rw [mul_assoc, SquarefreeEulerLog.log_mul_kernel]
  simp only [zetaPrimeFilterKernel, zetaFactorialPolynomial_X_mul]

/-- The entire logarithmic correlation has one uniform independent
bound. Both total coefficient masses are paid, with no restriction on
the locations or sizes of the finite divisor marks. -/
theorem exists_logResponse_quadratic_sieve_bound (y : ℝ) (hy : 1 < |y|)
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop,
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime ∧ a ≤ R N) →
      ∀ (T : Finset ℕ) (w v : ℕ → ℂ) (p : Polynomial ℂ),
        ‖logResponse p S T w v N (3 / 2 + I * y)‖ ≤
          C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
            (∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖) *
              (∑ d ∈ T, ‖w d‖) * (∑ e ∈ T, ‖v e‖) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeEulerLog.exists_quadratic_sieve_bound y hy R hR hcut
  refine ⟨C, hC, hb.mono ?_⟩
  intro N hN S hS T w v p
  let A := C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
    ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖
  rw [logResponse_eq_lcm_sum p S T (fun a ha ↦ (hS a ha).1) w v N (by norm_num)]
  calc
    _ ≤ ∑ d ∈ T, ∑ e ∈ T, ‖w d‖ * ‖v e‖ * A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hN S hS (Nat.lcm d e) p) (by positivity)
    _ = ∑ d ∈ T, ‖w d‖ * ((∑ e ∈ T, ‖v e‖) * A) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ ↦ by ring)
    _ = (∑ d ∈ T, ‖w d‖) * ((∑ e ∈ T, ‖v e‖) * A) := (Finset.sum_mul ..).symm
    _ = _ := by dsimp [A]; ring

/-- Every moving pair of finite complex divisor families has decay
when the chosen normalization keeps their total mass product bounded.
The theorem covers arbitrary mark locations and retains both families. -/
theorem tendsto_logResponse_of_mass_budget (y : ℝ) (hy : 1 < |y|)
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40)
    (S T : ℕ → Finset ℕ) (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ R N)
    (w v : ℕ → ℕ → ℂ) (scale : ℕ → ℂ) (B : ℝ)
    (hbudget : ∀ᶠ N in atTop,
      ‖scale N‖ * (∑ d ∈ T N, ‖w N d‖) * (∑ e ∈ T N, ‖v N e‖) ≤ B)
    (p : Polynomial ℂ) :
    Tendsto (fun N ↦ scale N * logResponse p (S N) (T N) (w N) (v N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_logResponse_quadratic_sieve_bound y hy R hR hcut
  let E := ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖scale N * logResponse p (S N) (T N) (w N) (v N) N (3 / 2 + I * y)‖ ≤
        (C * E * B) * ((N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ)))) := by
    filter_upwards [hb, hbudget] with N hN hbudget
    rw [norm_mul]
    calc
      _ ≤ ‖scale N‖ * (C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
          E * (∑ d ∈ T N, ‖w N d‖) * (∑ e ∈ T N, ‖v N e‖)) :=
        mul_le_mul_of_nonneg_left (hN (S N) (hS N) (T N) (w N) (v N) p) (norm_nonneg _)
      _ = (C * E * ((N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))))) *
          (‖scale N‖ * (∑ d ∈ T N, ‖w N d‖) * (∑ e ∈ T N, ‖v N e‖)) := by ring
      _ ≤ (C * E * ((N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))))) * B :=
        mul_le_mul_of_nonneg_left hbudget (by dsimp [E]; positivity)
      _ = _ := by ring
  apply squeeze_zero_norm' hbound
  simpa using (SquarefreeEulerLog.tendsto_quadratic_sieve_log_allowance R hcut).const_mul (C * E * B)

/-- The existing source normalization exactly pays the full number
of ordered pairs through the squared geometric divisor cutoff. -/
theorem source_pair_count_bound {u : ℝ} (hu : 0 < u) (N D : ℕ)
    (hD : D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N) ^ 2) :
    u ^ (N + 1) * (D : ℝ) ^ 2 ≤ u := by
  let q := zetaMoebiusHeadGrowth u
  have hq : 0 < q := by dsimp [q, zetaMoebiusHeadGrowth]; positivity
  have hq4 : u * q ^ 4 = 1 := by
    apply (mul_left_cancel₀ hu.ne')
    calc
      u * (u * q ^ 4) = (u * q ^ 2) ^ 2 := by ring
      _ = (Real.sqrt u) ^ 2 := by rw [zetaMoebiusHeadGrowth_rate hu]
      _ = u * 1 := by rw [Real.sq_sqrt hu.le, mul_one]
  have hf : (zetaMoebiusGeometricCutoff q N : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have hcut : (D : ℝ) ≤ (q ^ N) ^ 2 := by
    have h : (D : ℝ) ≤ (zetaMoebiusGeometricCutoff q N : ℝ) ^ 2 := by exact_mod_cast hD
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2)
  have hpair : (D : ℝ) ^ 2 ≤ (q ^ 4) ^ N := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hcut 2).trans_eq
    simp only [← pow_mul]
    congr 1
    omega
  calc
    _ ≤ u ^ (N + 1) * (q ^ 4) ^ N := mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = u * (u * q ^ 4) ^ N := by rw [pow_succ, mul_pow]; ring
    _ = u := by rw [hq4, one_pow, mul_one]

/-- The original zero-source normalization and full prime sieve,
with a complete logarithmic divisor correlation and an arbitrary filter. -/
def normalizedLogResponse (rho : NontrivialZetaZero) (p : Polynomial ℂ)
    (N D : ℕ) (w v : ℕ → ℂ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    logResponse p (zetaRightHalfPrimePatternPrimes rho N) (Finset.Icc 1 D)
      w v N (3 / 2 + I * rho.1.im)

/-- The complete normalized logarithmic sum decays for every moving
pair of bounded complex divisor families through the squared cutoff.
All ordered pairs and the actual quadratic prime sieve are included. -/
theorem tendsto_normalizedLogResponse_square_cutoff (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (w v : ℕ → ℕ → ℂ)
    (hD : ∀ᶠ N in atTop,
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2 ∧
        (∀ d ∈ Finset.Icc 1 (D N), ‖w N d‖ ≤ 1) ∧
        (∀ e ∈ Finset.Icc 1 (D N), ‖v N e‖ ≤ 1))
    (p : Polynomial ℂ) :
    Tendsto (fun N ↦ normalizedLogResponse rho p N (D N) (w N) (v N)) atTop (𝓝 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hbudget : ∀ᶠ N in atTop,
      ‖(u : ℂ) ^ (N + 1)‖ * (∑ d ∈ Finset.Icc 1 (D N), ‖w N d‖) *
        (∑ e ∈ Finset.Icc 1 (D N), ‖v N e‖) ≤ u := by
    filter_upwards [hD] with N hD
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, mul_assoc]
    exact (mul_le_mul_of_nonneg_left
      (RoughDivisorCorrelation.mass_budget_of_norm_le_one (D N) (w N) (v N) hD.2.1 hD.2.2)
      (by positivity)).trans (source_pair_count_bound hu N (D N) hD.1)
  exact tendsto_logResponse_of_mass_budget rho.1.im (nontrivialZetaZero_one_lt_abs_im rho)
    (zetaRightHalfPrimePatternCutoff rho) (tendsto_zetaRightHalfPrimePatternCutoff rho hrho)
    (Eventually.of_forall (sqrt_zetaRightHalfPrimePatternCutoff_le rho hrho))
    (zetaRightHalfPrimePatternPrimes rho) (fun N ↦ Finset.Icc 1 (D N))
    (zetaRightHalfPrimePatternPrimes_eligible rho) w v (fun N ↦ (u : ℂ) ^ (N + 1)) u hbudget p

/-- The full original Möbius square, with ordinary primes included,
has independently proved normalized logarithmic decay through the
squared divisor cutoff. No coefficient-family premise remains. -/
theorem tendsto_normalized_moebius_logResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop,
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2)
    (p : Polynomial ℂ) :
    Tendsto (fun N ↦ normalizedLogResponse rho p N (D N)
      (fun d ↦ (ArithmeticFunction.moebius d : ℂ)) (fun d ↦ (ArithmeticFunction.moebius d : ℂ)))
      atTop (𝓝 0) := by
  have hm (d : ℕ) : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  exact tendsto_normalizedLogResponse_square_cutoff rho hrho D
    (fun _ d ↦ (ArithmeticFunction.moebius d : ℂ)) (fun _ d ↦ (ArithmeticFunction.moebius d : ℂ))
    (hD.mono (fun N hN ↦ ⟨hN, fun d _ ↦ hm d, fun d _ ↦ hm d⟩)) p

end
end RiemannGaussian.SquarefreeEulerQuadratic
