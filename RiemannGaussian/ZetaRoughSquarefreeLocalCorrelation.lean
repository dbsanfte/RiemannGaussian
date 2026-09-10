/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArithmeticLocalEnergy
import RiemannGaussian.ZetaRoughSquarefreeWindowSource

/-!
# Vanishing local correlations and the full distant-pair source

The actual rough squarefree samples use the unchanged complex pole-jet
kernel and the original source normalization. All ordered pairs separated
by at most the fourth power of the moving divisor cutoff have an independent
geometric bound, including their cross terms. The exact complementary pair
sum therefore retains the full squared source of a hypothetical right-half
zero. Its upper bound, and the original signed upper bound, remain open.

Distance here is additive distance between integer indices. It is not a
separation of logarithmic phases or a claim of decorrelation at a fixed
ratio of indices.
-/

open Complex ComplexConjugate Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The literal physical sample with the full complex filter and
the original zero-source normalization. -/
def zetaRightHalfRoughSquarefreeNormalizedSample (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N n : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (zetaRightHalfRoughSquarefreeWindowCoefficient rho N n *
      zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
        (3 / 2 + I * rho.1.im) n)

/-- The local correlation keeps all ordered pairs through the fourth
power of the actual divisor cutoff, with both complex orientations. -/
def zetaRightHalfRoughSquarefreeLocalCorrelation (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  finiteLocalCorrelation (zetaPrimeLogBand N)
    (zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 4)

/-- The complementary physical pairs retain exactly the same
arithmetic coefficients, normalization and complex filter. -/
def zetaRightHalfRoughSquarefreeFarCorrelation (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  finiteFarCorrelation (zetaPrimeLogBand N)
    (zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 4)

/-- The controlled additive neighbourhood grows beyond every fixed
integer separation; its width is not a fixed finite band. -/
theorem tendsto_zetaRightHalfRoughSquarefreeCorrelationWidth (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 4)
      atTop atTop := by
  have hq := one_lt_zetaMoebiusHeadGrowth
    (by linarith [NontrivialZetaZero.re_lt_one rho] : 0 < 3 / 2 - rho.1.re)
    (by linarith : 3 / 2 - rho.1.re < 1)
  apply tendsto_atTop_mono _ (tendsto_zetaMoebiusGeometricCutoff hq)
  intro N
  by_cases hz : zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N = 0
  · simp [hz]
  · exact le_self_pow₀ (Nat.one_le_iff_ne_zero.mpr hz) (by decide)

/-- The actual local and distant correlations retain every cross
term in the squared physical sum, before any estimate is applied. -/
theorem zetaRightHalfRoughSquarefreeLocal_add_far (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    zetaRightHalfRoughSquarefreeLocalCorrelation rho hrho N +
      zetaRightHalfRoughSquarefreeFarCorrelation rho hrho N =
        (∑ n ∈ zetaPrimeLogBand N, zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n) *
          conj (∑ n ∈ zetaPrimeLogBand N, zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n) :=
  finiteLocalCorrelation_add_far _ _ _

private theorem actual_coefficient_bound (rho : NontrivialZetaZero) (N n : ℕ) :
    ‖zetaRightHalfRoughSquarefreeWindowCoefficient rho N n‖ ≤ zetaMoebiusLogMajorant n :=
  norm_zetaLogWindowCoefficient_le _ (norm_zetaRoughSquarefreeCoefficient_le _ _) N n

/-- A finite error connects these same normalized samples to the
original retained Fourier carrier. The old physical and Fourier allowances
are retained explicitly and both are already proved to vanish. -/
theorem norm_sum_zetaRightHalfRoughSquarefreeNormalizedSample_sub_fourier_le
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) (hN : 2 ≤ N) :
    ‖(∑ n ∈ zetaPrimeLogBand N, zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n) -
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N‖ ≤
      zetaLogWindowError (zetaRightHalfPoleJetFilter rho hrho) N +
        zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  let a := zetaRoughSquarefreeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfPrimePatternPrimes rho N)
  let p := zetaRightHalfPoleJetFilter rho hrho
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  let F := zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)
  let G := zetaArithmeticFilter (zetaLogWindowCoefficient a N) p N (3 / 2 + I * rho.1.im)
  let Q := zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N
  have ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n := norm_zetaRoughSquarefreeCoefficient_le _ _
  have hG : ‖F - G‖ ≤ zetaLogWindowError p N :=
    norm_zetaArithmeticFilter_sub_window_le a ha p N rho.1.im
  have hQ : ‖F - Q‖ ≤ zetaAveragedWindowError p N rho.1.im :=
    norm_zetaArithmeticFilter_sub_averaged_window_le a ha p N rho.1.im hN
  have hu : ‖u‖ ≤ 1 := by
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg
      (by linarith [NontrivialZetaZero.re_lt_one rho])]
    exact pow_le_one₀ (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)
  have he : (∑ n ∈ zetaPrimeLogBand N,
      zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n) = u * G := by
    dsimp [G]
    rw [zetaArithmeticFilter_window_eq_band _ _ _ _ (by omega)]
    simp only [zetaRightHalfRoughSquarefreeNormalizedSample, ← Finset.mul_sum]
    rfl
  rw [he, ← mul_sub, norm_mul]
  calc
    _ ≤ ‖G - Q‖ := by simpa using mul_le_mul_of_nonneg_right hu (norm_nonneg (G - Q))
    _ ≤ ‖G - F‖ + ‖F - Q‖ := norm_sub_le_norm_sub_add_norm_sub G F Q
    _ ≤ _ := by rw [norm_sub_rev G F]; exact add_le_add hG hQ

/-- The complete local band of correlations has an independently
vanishing bound. The constant depends on the fixed zero and filter, but
not on the order, divisor cutoff, or number of retained pairs. -/
theorem exists_zetaRightHalfRoughSquarefreeLocalCorrelation_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖zetaRightHalfRoughSquarefreeLocalCorrelation rho hrho N‖ ≤
        C * (zetaRightHalfSquareSieveRate rho ^ 2) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := zetaRightHalfSquareSieveRadius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let A := zetaArithmeticEnergyConstant p r
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  obtain ⟨hr, hr1, _⟩ := zetaRightHalfSquareSieveRadius_bounds rho hrho
  have hA : 0 ≤ A := zetaArithmeticEnergyConstant_nonneg p r
  refine ⟨3 * A * u ^ 2 + 1, by positivity, fun N ↦ ?_⟩
  let D := zetaMoebiusGeometricCutoff q N
  let f := zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (by positivity)
  have hE : (∑ n ∈ zetaPrimeLogBand N, ‖f n‖ ^ 2) ≤
      (u ^ (N + 1)) ^ 2 * (A * (r⁻¹ ^ N) ^ 2) := by
    dsimp [f, zetaRightHalfRoughSquarefreeNormalizedSample]
    simp only [norm_mul, norm_pow, Complex.norm_real, mul_pow]
    rw [show ‖(3 / 2 - rho.1.re : ℝ)‖ = u from Real.norm_of_nonneg hu.le]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [norm_mul, mul_pow] using sum_norm_zetaArithmeticKernel_sq_le
      (zetaRightHalfRoughSquarefreeWindowCoefficient rho N) (actual_coefficient_bound rho N)
      p N rho.1.im (zetaPrimeLogBand N) hr hr1
  have hdegree : (2 * (D ^ 4 : ℕ) + 1 : ℝ) ≤ 3 * (q ^ N) ^ 4 := by
    have hd4 := pow_le_pow_left₀ (Nat.cast_nonneg D) hD 4
    have hqN : (1 : ℝ) ≤ (q ^ N) ^ 4 := one_le_pow₀ (one_le_pow₀ hq)
    push_cast
    nlinarith
  have hrate : q ^ 4 * u ^ 2 * r⁻¹ ^ 2 = zetaRightHalfSquareSieveRate rho ^ 2 := by
    have he : u * q ^ 2 = Real.sqrt u := zetaMoebiusHeadGrowth_rate hu
    change _ = (Real.sqrt u / r) ^ 2
    rw [div_pow, div_eq_mul_inv, inv_pow]
    linear_combination (r ^ 2)⁻¹ * congrArg (fun x : ℝ ↦ x ^ 2) he
  change ‖finiteLocalCorrelation (zetaPrimeLogBand N) f (D ^ 4)‖ ≤ _
  calc
    _ ≤ (2 * (D ^ 4 : ℕ) + 1 : ℝ) * ∑ n ∈ zetaPrimeLogBand N, ‖f n‖ ^ 2 :=
      norm_finiteLocalCorrelation_le _ _ _
    _ ≤ (3 * (q ^ N) ^ 4) * ((u ^ (N + 1)) ^ 2 * (A * (r⁻¹ ^ N) ^ 2)) :=
      mul_le_mul hdegree hE (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (by positivity)
    _ = (3 * A * u ^ 2) * (zetaRightHalfSquareSieveRate rho ^ 2) ^ N := by
      rw [← hrate, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
        Nat.mul_comm N 4, Nat.mul_comm N 2, pow_succ]
      ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The sum of all nearby signed cross terms, including the diagonal,
vanishes in the actual source normalization at the moving exponential width. -/
theorem tendsto_zetaRightHalfRoughSquarefreeLocalCorrelation (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (zetaRightHalfRoughSquarefreeLocalCorrelation rho hrho) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfRoughSquarefreeLocalCorrelation_bound rho hrho
  obtain ⟨h0, h1⟩ := zetaRightHalfSquareSieveRate_bounds rho hrho
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) (by nlinarith :
      zetaRightHalfSquareSieveRate rho ^ 2 < 1)).const_mul C

/-- The finite physical sample sum retains the full complex source.
Only the previously bounded physical outer shells are removed here. -/
theorem tendsto_sum_zetaRightHalfRoughSquarefreeNormalizedSample (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ∑ n ∈ zetaPrimeLogBand N,
      zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let a := fun N ↦ zetaRoughSquarefreeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfPrimePatternPrimes rho N)
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_window a
    (fun N ↦ norm_zetaRoughSquarefreeCoefficient_le _ _) p rho.1.im
  have h := (tendsto_zetaRightHalfRoughSquarefreeFilter rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [zetaArithmeticFilter_window_eq_band _ _ _ _ hN]
  simp only [zetaRightHalfRoughSquarefreeNormalizedSample, ← Finset.mul_sum]
  dsimp [a, p, zetaRoughSquarefreeFilter, zetaArithmeticFilter, zetaArithmeticBand,
    zetaRightHalfRoughSquarefreeWindowCoefficient]
  ring

/-- After removing the entire bounded local band, the literal
remaining ordered pairs retain the squared multiplicity source. This
is a localization of the obstruction, not an upper bound for those pairs. -/
theorem tendsto_zetaRightHalfRoughSquarefreeFarCorrelation (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (zetaRightHalfRoughSquarefreeFarCorrelation rho hrho) atTop
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)) := by
  have hsum := tendsto_sum_zetaRightHalfRoughSquarefreeNormalizedSample rho hrho
  have h := (hsum.mul (Complex.continuous_conj.continuousAt.tendsto.comp hsum)).sub
    (tendsto_zetaRightHalfRoughSquarefreeLocalCorrelation rho hrho)
  have he (N : ℕ) := zetaRightHalfRoughSquarefreeLocal_add_far rho hrho N
  convert h using 1
  · funext N
    dsimp only [Function.comp_def]
    linear_combination he N
  · simp [sq]

end
end RiemannGaussian
