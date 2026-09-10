/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreeBareFilter
import RiemannGaussian.ZetaRoughMoebiusIncidenceSource
import RiemannGaussian.ZetaRoughSquarefreeUnitDivisor

/-!
# Independent decay of the exact mixed Möbius logarithmic term

The mixed term expands over every ordered divisor pair with its literal
least-common-multiple mark. A uniform bound for the complete marked bare
squarefree response controls this family without using source convergence.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.RoughMoebiusMixed
noncomputable section
open RoughMoebiusIncidence

/-- The full mixed logarithmic coefficient on rough squarefree
integers. Its vanishing on ordinary primes is proved separately. -/
def coefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  RoughSquarefreeBare.coefficient S 1 n * mask D n * logMask D n

/-- Every ordered divisor pair retains its exact lcm mark and sign. -/
theorem coefficient_eq_lcm_sum (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    coefficient D S n = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      ((μ d : ℂ) * (μ e : ℂ) * (Real.log e : ℂ)) *
        RoughSquarefreeBare.coefficient S (Nat.lcm d e) n := by
  unfold coefficient mask logMask
  conv_lhs => arg 1; rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hsf : Squarefree n <;> by_cases hs : ∃ a ∈ S, a ∣ n <;>
    by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
      simp [RoughSquarefreeBare.coefficient, Nat.lcm_dvd_iff, hsf, hs, hd, he]
  all_goals ring

/-- The mixed kernel response as its original complete arithmetic series. -/
def response (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, coefficient D S n * zetaPrimeFilterKernel p N s n

/-- The double lcm expansion is an equality of genuinely convergent
series, with all complex coefficients retained before estimating them. -/
theorem hasSum_response (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient D S n * zetaPrimeFilterKernel p (N + 1) s n)
      (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((μ d : ℂ) * (μ e : ℂ) * (Real.log e : ℂ)) *
          RoughSquarefreeBare.response p S (Nat.lcm d e) (N + 1) s) := by
  have h := hasSum_sum (s := Finset.Icc 1 D) (fun d _ ↦
    hasSum_sum (s := Finset.Icc 1 D) (fun e _ ↦
      (RoughSquarefreeBare.summable_response p S hS (Nat.lcm d e) N hs).hasSum.mul_left
        ((μ d : ℂ) * (μ e : ℂ) * (Real.log e : ℂ))))
  apply h.congr_fun
  intro n
  rw [coefficient_eq_lcm_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun e _ ↦ by ring)

private theorem norm_moebius_le_one (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- The entire mixed term has an independent quadratic divisor cost.
Every lcm coincidence is included; no prime-cancellation premise is used. -/
theorem exists_response_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖response p D S (N + 1) (3 / 2 + I * y)‖ ≤
        C * D ^ 2 * Real.log D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := by
  obtain ⟨C, hC, hb⟩ := RoughSquarefreeBare.exists_response_bound y hy hr hr1
  refine ⟨C, hC, ?_⟩
  intro p D N R S hS
  let A := C * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
    (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [response, (hasSum_response p D S (fun a ha ↦ (hS a ha).1) N (by norm_num)).tsum_eq]
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, ∑ _e ∈ Finset.Icc 1 D, Real.log D * A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg e)]
      have hlog : Real.log e ≤ Real.log D := Real.log_le_log
        (by exact_mod_cast (Finset.mem_Icc.mp he).1)
        (by exact_mod_cast (Finset.mem_Icc.mp he).2)
      have hm : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ ≤ 1 := by
        simpa using mul_le_mul (norm_moebius_le_one d) (norm_moebius_le_one e)
          (norm_nonneg _) (by norm_num)
      have hc : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ * Real.log e ≤ Real.log D :=
        (mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg e)).trans
          (by simpa using hlog)
      exact mul_le_mul hc (hb p N R S (Nat.lcm d e) hS) (norm_nonneg _)
        (Real.log_natCast_nonneg D)
    _ = _ := by simp [A]; ring

/-- The original zero-adapted normalization of the exact mixed term. -/
def actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    response (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The full mixed logarithmic term has a geometrically vanishing
allowance at the literal zero-source normalization. This estimate uses
the independent marked-series bound, not the source limit. -/
theorem exists_actual_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖actualResponse rho hrho N‖ ≤ C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := RoughPrimeIncidence.radius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq1 : 1 < q := one_lt_zetaMoebiusHeadGrowth hu hu1
  have hq : 0 < q := zero_lt_one.trans hq1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  have hrate : 0 ≤ RoughPrimeIncidence.rate rho := (RoughPrimeIncidence.rate_bounds rho hrho).1.le
  obtain ⟨hr, hr1, _⟩ := RoughPrimeIncidence.radius_bounds rho hrho
  have hri : 1 ≤ r⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hr).mpr (by simpa using hr1.le)
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_response_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B * (1 + 4 * Real.log q) + 1, by positivity, ?_⟩
  intro N hN
  let D := zetaMoebiusGeometricCutoff q N
  have hDpos : 1 ≤ D := zetaRightHalfPoleJetCutoff_pos rho hrho N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have he := RoughPrimeIncidence.exp_sqrt_cutoff_bound rho hrho N
  have hlog : Real.log D ≤ 1 + 4 * (N : ℝ) * Real.log q := by
    have h := Real.log_le_log (show (0 : ℝ) < D by exact_mod_cast hDpos) hD
    rw [Real.log_pow] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hD3 : (D : ℝ) ^ 2 ≤ q ^ N * (q ^ N) ^ 2 := by
    have hDn : (1 : ℝ) ≤ D := by exact_mod_cast hDpos
    have hqN : (1 : ℝ) ≤ q ^ N := one_le_pow₀ hq1.le
    exact (pow_le_pow_left₀ (by positivity) hD 2).trans
      (by nlinarith [sq_nonneg (q ^ N)])
  have hpred : N - 1 + 1 = N := by omega
  have hbN := hb p D (N - 1) (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [hpred] at hbN
  have hpow : r⁻¹ ^ (N - 1) ≤ r⁻¹ ^ N := pow_le_pow_right₀ hri (by omega)
  rw [actualResponse, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D ^ 2 * Real.log D *
        Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ (N - 1) * B) :=
      mul_le_mul_of_nonneg_left hbN (by positivity)
    _ ≤ u ^ (N + 1) * (C * (q ^ N * (q ^ N) ^ 2) *
        (1 + 4 * (N : ℝ) * Real.log q) * (Real.sqrt q) ^ N * r⁻¹ ^ N * B) := by
      gcongr
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) *
        ((u * Real.sqrt q * q ^ 3) / r) ^ N := by
      rw [div_pow, mul_pow, mul_pow, pow_succ,
        show (q ^ 3) ^ N = (q ^ N) ^ 3 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) * RoughPrimeIncidence.rate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
      rfl
    _ ≤ (C * u * B) * ((1 + 4 * Real.log q) * (1 + (N : ℝ))) * RoughPrimeIncidence.rate rho ^ N := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ _ := by
      have h0 : 0 ≤ (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by positivity
      calc
        _ = (C * u * B * (1 + 4 * Real.log q)) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) := by ring
        _ ≤ (C * u * B * (1 + 4 * Real.log q) + 1) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
        _ = _ := by ring

/-- The refined mixed arithmetic residual itself tends to zero in
complex norm at the original normalization, with no missing premise. -/
theorem tendsto_actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualResponse rho hrho) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actual_bound rho hrho
  exact squeeze_zero_norm' ((eventually_ge_atTop 1).mono (fun N hN ↦ hb N hN))
    (RoughPrimeIncidence.tendsto_allowance rho hrho C)

/-- The mixed mask vanishes on every ordinary prime: below the
cutoff the Möbius mask is zero, and above it the logarithmic mask is zero. -/
theorem mask_mul_logMask_prime (D : ℕ) {p : ℕ} (hp : p.Prime) :
    mask D p * logMask D p = 0 := by
  by_cases hpD : p ≤ D
  · simp [mask_eq_unit hp.pos hpD, hp.ne_one]
  · have hz : logMask D p = 0 := by
      unfold logMask
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hdp : d ∣ p
      · rcases hp.eq_one_or_self_of_dvd d hdp with h | h
        · subst d
          simp
        · subst d
          exact (hpD (Finset.mem_Icc.mp hd).2).elim
      · simp [hdp]
    rw [hz, mul_zero]

/-- Completing the mixed term to all squarefree integers restores
no ordinary-prime contribution. This is exact pointwise cancellation. -/
theorem coefficient_prime (D : ℕ) (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    coefficient D S p = 0 := by
  rw [coefficient, mul_assoc, mask_mul_logMask_prime D hp, mul_zero]

/-- The exact squared Möbius coefficient on the original rough
squarefree composite support. Its full complex kernel is kept downstream. -/
def squareCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  mask D n ^ 2 * (zetaRoughSquarefreeCompositeLogWeight S n : ℂ)

/-- The remaining squared coefficient is nonnegative in its real
channel, independently of the oscillatory kernel. -/
theorem squareCoefficient_re_nonneg (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    0 ≤ (squareCoefficient D S n).re := by
  rw [squareCoefficient, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_nonneg (mask_square_re_nonneg D n) (zetaRoughSquarefreeCompositeLogWeight_nonneg S n)

/-- The square coefficient has no hidden imaginary part before
multiplication by the literal complex filter. -/
theorem squareCoefficient_im (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    (squareCoefficient D S n).im = 0 := by
  simp [squareCoefficient, pow_two, Complex.mul_im, mask_im]

/-- The full compensated coefficient is exactly minus the square
plus the mixed term, including primes, zero and excluded sieve indices. -/
theorem compensatedCoefficient_eq_neg_square_add_mixed (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    RoughMoebiusIncidence.coefficient D D S n = -squareCoefficient D S n + coefficient D S n := by
  by_cases hp : n.Prime
  · rw [coefficient_prime D S hp]
    have hz : zetaRoughSquarefreeCoefficient D S n = 0 := by
      simp [zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient,
        zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient, hp.primeFactors]
    simp [RoughMoebiusIncidence.coefficient, hz, squareCoefficient,
      zetaRoughSquarefreeCompositeLogWeight, hp]
  by_cases hsf : Squarefree n
  · by_cases hs : ∃ a ∈ S, a ∣ n
    · simp [RoughMoebiusIncidence.coefficient, zetaRoughSquarefreeCoefficient,
        coefficient, RoughSquarefreeBare.coefficient, squareCoefficient,
        zetaRoughSquarefreeCompositeLogWeight, hs]
    · rw [coefficient_eq_square_add_mixed D hD S hS hsf hp hs]
      simp [coefficient, RoughSquarefreeBare.coefficient, squareCoefficient,
        zetaRoughSquarefreeCompositeLogWeight, hsf, hp, hs]
  · simp [RoughMoebiusIncidence.coefficient, zetaRoughSquarefreeCoefficient,
      zetaSquarefreeCoefficient, coefficient, RoughSquarefreeBare.coefficient,
      squareCoefficient, zetaRoughSquarefreeCompositeLogWeight, hsf]

/-- The complete square response with the same polynomial and moment order. -/
def squareResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, squareCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The squared arithmetic series genuinely converges and keeps the
exact signed difference between mixed and compensated responses. -/
theorem hasSum_squareResponse (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ squareCoefficient D S n * zetaPrimeFilterKernel p (N + 1) s n)
      (response p D S (N + 1) s - ∑' n,
        RoughMoebiusIncidence.coefficient D D S n * zetaPrimeFilterKernel p (N + 1) s n) := by
  have hm := (hasSum_response p D S hS N hs).summable.hasSum
  have hc := (RoughMoebiusIncidence.hasSum_coefficient p D D (N + 1) hD hD S hS hs).summable.hasSum
  apply (hm.sub hc).congr_fun
  intro n
  rw [compensatedCoefficient_eq_neg_square_add_mixed D hD S hS n]
  ring

/-- The source-normalized response with the exact squared Möbius coefficient. -/
def actualSquareResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    squareResponse (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The complete source comparison preserves its sign and every
correction before using the independent mixed-term estimate. -/
theorem actualSquareResponse_eq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) (hN : 1 ≤ N) :
    actualSquareResponse rho hrho N = actualResponse rho hrho N -
      RoughMoebiusIncidence.response rho hrho N
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) := by
  have h := (hasSum_squareResponse (zetaRightHalfPoleJetFilter rho hrho) _
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1)
    (N - 1) (s := 3 / 2 + I * rho.1.im) (by norm_num)).tsum_eq
  rw [show N - 1 + 1 = N by omega] at h
  unfold actualSquareResponse squareResponse
  rw [h, mul_sub]
  rfl

/-- Both errors in transferring the full original source to the
squared coefficient have one explicit independently vanishing allowance. -/
theorem exists_actualSquare_source_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖actualSquareResponse rho hrho N +
        ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by
  obtain ⟨C₁, hC₁, hm⟩ := exists_actual_bound rho hrho
  obtain ⟨C₂, hC₂, hc⟩ := RoughMoebiusIncidence.exists_response_error_bound rho hrho
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  have hD : 1 ≤ D := zetaRightHalfPoleJetCutoff_pos rho hrho N
  have hD4 : D ≤ D ^ 4 := by simpa using pow_le_pow_right₀ hD (by norm_num : 1 ≤ 4)
  have hb := add_le_add (hm N hN) (hc N D hD hD4)
  rw [actualSquareResponse_eq rho hrho N hN]
  have he (a b c : ℂ) : a - b + c = a - (b - c) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (hb.trans_eq (by ring))

/-- After independently controlling the mixed term, the full
positive-multiplicity source remains in the nonnegative square coefficient
with its oscillatory complex kernel. No upper bound on this response is asserted. -/
theorem tendsto_actualSquareResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualSquareResponse rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have hc := RoughMoebiusIncidence.tendsto_response rho hrho
    (fun N ↦ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (Eventually.of_forall (fun N ↦ by
      have hD := zetaRightHalfPoleJetCutoff_pos rho hrho N
      exact ⟨hD, by simpa using pow_le_pow_right₀ hD (by norm_num : 1 ≤ 4)⟩))
  have h := (tendsto_actualResponse rho hrho).sub hc
  simp only [zero_sub, neg_neg] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (actualSquareResponse_eq rho hrho N hN).symm

/-- A cofinal strict upper bound below the unit source suffices for
contradiction. Its arithmetic premise remains the open obligation. -/
theorem false_of_cofinal_square_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∃ᶠ N in atTop, (actualSquareResponse rho hrho N).re ≤ 1 - ε) : False := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_actualSquareResponse rho hrho)
  have hb := le_of_tendsto_of_frequently h hbound
  simp only [Complex.natCast_re] at hb
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

end
end RiemannGaussian.RoughMoebiusMixed
