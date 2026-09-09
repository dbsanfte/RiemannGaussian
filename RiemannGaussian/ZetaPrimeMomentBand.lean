/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimePowerMoments

/-!
# Independent arithmetic bounds outside a finite logarithmic prime band

Elementary exponential tilts make both tails of the factorial log kernel
geometrically small, uniformly in the ordinate. The retained band is finite
and consists of actual ordinary primes. No bound for its signed sum is
assumed; this is the remaining arithmetic carrier.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The positive real-axis arithmetic mass controlling the omitted tails. -/
def zetaPrimeExpMass (σ : ℝ) : ℝ :=
  ∑' m, ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight σ m

/-- This arithmetic mass converges absolutely beyond one. -/
theorem summable_zetaPrimeExpMass {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun m ↦ ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight σ m) :=
  summable_zetaPrimeExpWeight_mul _ (by simp)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ))

/-- The tail-controlling arithmetic mass is nonnegative. -/
theorem zetaPrimeExpMass_nonneg (σ : ℝ) : 0 ≤ zetaPrimeExpMass σ :=
  tsum_nonneg (fun _ ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)

/-- Below the lower logarithmic endpoint the complete moment kernel has
a geometric bound, uniform in the ordinate and in the prime index. -/
theorem norm_zetaPrimeLogKernel_le_lower_band (N k m : ℕ) (s : ℂ)
    (hm : Real.log m ≤ (N : ℝ) * Real.log 2 / 4) :
    ‖zetaPrimeLogKernel (N + k) s m‖ ≤
      (1 / 2 : ℝ) ^ N * (1 / 4 : ℝ) ^ k * zetaPrimeExpWeight s.re m := by
  have he : zetaPrimeExpWeight (s.re - 4) m =
      Real.exp (4 * Real.log m) * zetaPrimeExpWeight s.re m := by
    rw [zetaPrimeExpWeight, zetaPrimeExpWeight, ← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp (4 * Real.log m) ≤ (2 : ℝ) ^ N := by
    calc
      _ ≤ Real.exp ((N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hpow : (1 / 4 : ℝ) ^ N * 2 ^ N = (1 / 2 : ℝ) ^ N := by
    rw [← mul_pow]
    norm_num
  calc
    _ ≤ (1 / 4 : ℝ) ^ (N + k) *
        (Real.exp (4 * Real.log m) * zetaPrimeExpWeight s.re m) := by
      simpa only [he, one_div] using norm_zetaPrimeLogKernel_le (N + k) s m (by norm_num : (0 : ℝ) < 4)
    _ ≤ (1 / 4 : ℝ) ^ (N + k) * (2 ^ N * zetaPrimeExpWeight s.re m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le) (by positivity)
    _ = ((1 / 4 : ℝ) ^ N * 2 ^ N) * ((1 / 4 : ℝ) ^ k * zetaPrimeExpWeight s.re m) := by
      rw [pow_add]
      ring
    _ = _ := by rw [hpow]; ring

/-- Above the upper logarithmic endpoint an independent exponential tilt
also gives geometric decay, using only the Euler mass at real part `5/4`. -/
theorem norm_zetaPrimeLogKernel_le_upper_band (N k m : ℕ) (y : ℝ)
    (hm : 32 * (N : ℝ) * Real.log 2 ≤ Real.log m) :
    ‖zetaPrimeLogKernel (N + k) (3 / 2 + I * y) m‖ ≤
      (1 / 2 : ℝ) ^ N * (8 : ℝ) ^ k * zetaPrimeExpWeight (5 / 4) m := by
  have hs : (3 / 2 + I * (y : ℂ)).re - 1 / 8 = 11 / 8 := by norm_num
  have he : zetaPrimeExpWeight (11 / 8) m =
      Real.exp (-Real.log m / 8) * zetaPrimeExpWeight (5 / 4) m := by
    rw [zetaPrimeExpWeight, zetaPrimeExpWeight, ← Real.exp_add]
    congr 1
    ring
  have hx : Real.exp (-4 * Real.log 2) = (1 / 16 : ℝ) := by
    have h4 := Real.exp_nat_mul (Real.log 2) 4
    norm_num only [Nat.cast_ofNat] at h4
    rw [neg_mul, Real.exp_neg, h4, Real.exp_log (by norm_num)]
    norm_num
  have hb : Real.exp (-Real.log m / 8) ≤ (1 / 16 : ℝ) ^ N := by
    calc
      _ ≤ Real.exp ((N : ℝ) * (-4 * Real.log 2)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_nat_mul, hx]
  have hpow : (8 : ℝ) ^ N * (1 / 16 : ℝ) ^ N = (1 / 2 : ℝ) ^ N := by
    rw [← mul_pow]
    norm_num
  calc
    _ ≤ (8 : ℝ) ^ (N + k) * (Real.exp (-Real.log m / 8) * zetaPrimeExpWeight (5 / 4) m) := by
      have h := norm_zetaPrimeLogKernel_le (N + k) (3 / 2 + I * y) m (by norm_num : (0 : ℝ) < 1 / 8)
      rw [hs, he] at h
      norm_num only [one_div, inv_inv] at h
      exact h
    _ ≤ (8 : ℝ) ^ (N + k) * ((1 / 16 : ℝ) ^ N * zetaPrimeExpWeight (5 / 4) m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le) (by positivity)
    _ = ((8 : ℝ) ^ N * (1 / 16 : ℝ) ^ N) * ((8 : ℝ) ^ k * zetaPrimeExpWeight (5 / 4) m) := by
      rw [pow_add]
      ring
    _ = _ := by rw [hpow]; ring

/-- A finite logarithmic band. Its upper endpoint is the exact integer
`2^(32 N)` and its lower endpoint is specified before rounding. -/
def zetaPrimeLogBand (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 ^ (32 * N))).filter (fun m ↦ (N : ℝ) * Real.log 2 / 4 < Real.log m)

/-- Every omitted positive integer lies in one of the two controlled tails. -/
theorem zetaPrimeLogBand_complement (N : ℕ) {m : ℕ} (hm0 : m ≠ 0)
    (hm : m ∉ zetaPrimeLogBand N) :
    Real.log m ≤ (N : ℝ) * Real.log 2 / 4 ∨ 32 * (N : ℝ) * Real.log 2 ≤ Real.log m := by
  by_cases hl : Real.log m ≤ (N : ℝ) * Real.log 2 / 4
  · exact Or.inl hl
  · right
    have hu : 2 ^ (32 * N) < m := by
      by_contra! h
      apply hm
      simp only [zetaPrimeLogBand, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, h⟩, lt_of_not_ge hl⟩
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (32 * N))
      (show (2 : ℝ) ^ (32 * N) ≤ (m : ℝ) by exact_mod_cast hu.le)
    simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using hlog

/-- The retained finite ordinary-prime moment. -/
def zetaOrdinaryPrimeBandMoment (N k : ℕ) (y : ℝ) : ℂ :=
  ∑ m ∈ zetaPrimeLogBand N, if m.Prime then
    (ArithmeticFunction.vonMangoldt m : ℂ) * zetaPrimeLogKernel (N + k) (3 / 2 + I * y) m else 0

private theorem ordinary_atom_norm_le_outside (N k m : ℕ) (y : ℝ)
    (hm : m ∉ zetaPrimeLogBand N) :
    ‖if m.Prime then (ArithmeticFunction.vonMangoldt m : ℂ) *
      zetaPrimeLogKernel (N + k) (3 / 2 + I * y) m else 0‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * (ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight (3 / 2) m) +
          (8 : ℝ) ^ k * (ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight (5 / 4) m)) := by
  have hw (σ : ℝ) : 0 ≤ ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight σ m :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  by_cases hp : m.Prime
  · rw [if_pos hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rcases zetaPrimeLogBand_complement N hp.ne_zero hm with hl | hu
    · have h := mul_le_mul_of_nonneg_left
        (norm_zetaPrimeLogKernel_le_lower_band N k m (3 / 2 + I * y) hl)
        (ArithmeticFunction.vonMangoldt_nonneg (n := m))
      have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
      simp only [hs] at h
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ N * 8 ^ k by positivity) (hw (5 / 4))]
    · have h := mul_le_mul_of_nonneg_left (norm_zetaPrimeLogKernel_le_upper_band N k m y hu)
        (ArithmeticFunction.vonMangoldt_nonneg (n := m))
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ N * (1 / 4) ^ k by positivity) (hw (3 / 2))]
  · rw [if_neg hp, norm_zero]
    exact mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg (by positivity) (hw (3 / 2))) (mul_nonneg (by positivity) (hw (5 / 4))))

private theorem tsum_sub_sum_eq_complement {f : ℕ → ℂ} (hf : Summable f) (S : Finset ℕ) :
    (∑' m, f m) - ∑ m ∈ S, f m = ∑' m, if m ∈ S then 0 else f m := by
  have h := hf.sum_add_tsum_compl (s := S)
  rw [tsum_subtype] at h
  have he : ((S : Set ℕ)ᶜ).indicator f = (fun m ↦ if m ∈ S then 0 else f m) := by
    funext m
    by_cases hm : m ∈ S <;> simp [hm]
  rw [he] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

/-- Both omitted arithmetic tails have an explicit geometric bound.
The retained finite sum is over ordinary primes, with full phases. -/
theorem norm_zetaOrdinaryPrimeLogMoment_sub_band_le (N k : ℕ) (y : ℝ) :
    ‖zetaOrdinaryPrimeLogMoment (N + k) (3 / 2 + I * y) - zetaOrdinaryPrimeBandMoment N k y‖ ≤
      (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * zetaPrimeExpMass (3 / 2) + (8 : ℝ) ^ k * zetaPrimeExpMass (5 / 4)) := by
  let f (m : ℕ) : ℂ := if m.Prime then (ArithmeticFunction.vonMangoldt m : ℂ) *
    zetaPrimeLogKernel (N + k) (3 / 2 + I * y) m else 0
  have hf : Summable f := summable_zetaOrdinaryPrimeLogMoment (N + k) (by norm_num)
  have ht : Summable (fun m ↦ if m ∈ zetaPrimeLogBand N then 0 else f m) := by
    apply (hf.indicator ((zetaPrimeLogBand N : Set ℕ)ᶜ)).congr
    intro m
    by_cases hm : m ∈ zetaPrimeLogBand N <;> simp [hm]
  have h1 := summable_zetaPrimeExpMass (by norm_num : (1 : ℝ) < 3 / 2)
  have h2 := summable_zetaPrimeExpMass (by norm_num : (1 : ℝ) < 5 / 4)
  have hmajor := ((h1.mul_left ((1 / 4 : ℝ) ^ k)).add (h2.mul_left ((8 : ℝ) ^ k))).mul_left ((1 / 2 : ℝ) ^ N)
  change ‖(∑' m, f m) - ∑ m ∈ zetaPrimeLogBand N, f m‖ ≤ _
  rw [tsum_sub_sum_eq_complement hf]
  calc
    _ ≤ ∑' m, (1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * (ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight (3 / 2) m) +
          (8 : ℝ) ^ k * (ArithmeticFunction.vonMangoldt m * zetaPrimeExpWeight (5 / 4) m)) := by
      apply (norm_tsum_le_tsum_norm ht.norm).trans
      apply Summable.tsum_le_tsum _ ht.norm hmajor
      intro m
      by_cases hm : m ∈ zetaPrimeLogBand N
      · rw [if_pos hm, norm_zero]
        exact mul_nonneg (by positivity) (add_nonneg
          (mul_nonneg (by positivity) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le))
          (mul_nonneg (by positivity) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)))
      · rw [if_neg hm]
        exact ordinary_atom_norm_le_outside N k m y hm
    _ = _ := by
      rw [tsum_mul_left, (h1.mul_left _).tsum_add (h2.mul_left _), tsum_mul_left, tsum_mul_left]
      rfl

/-- The exact finite ordinary-prime carrier left after both tails are removed. -/
def zetaOrdinaryPrimeBandFilter (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * zetaOrdinaryPrimeBandMoment N k y

/-- The retained carrier is one literal finite sum over ordinary primes.
The factorial log polynomial and the complex oscillatory phase are explicit. -/
theorem zetaOrdinaryPrimeBandFilter_eq_prime_sum (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaOrdinaryPrimeBandFilter p N y =
      ∑ m ∈ (zetaPrimeLogBand N).filter Nat.Prime,
        (Real.log m : ℂ) * zetaPrimeFeature (3 / 2 + I * y) m *
          ∑ k ∈ p.support, p.coeff k * ((Real.log m : ℂ) ^ (N + k) / ((N + k).factorial : ℂ)) := by
  rw [zetaOrdinaryPrimeBandFilter]
  simp only [zetaOrdinaryPrimeBandMoment, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.Prime
  · simp only [if_pos hm, ArithmeticFunction.vonMangoldt_apply_prime hm,
      zetaPrimeLogKernel]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [if_neg hm, mul_zero, Finset.sum_const_zero]

/-- The filter's fixed arithmetic tail constant, independent of the ordinate. -/
def zetaPrimeBandTailConstant (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ *
    ((1 / 4 : ℝ) ^ k * zetaPrimeExpMass (3 / 2) + (8 : ℝ) ^ k * zetaPrimeExpMass (5 / 4))

/-- The whole omitted filtered tail is geometrically small, uniformly in
height, using positive arithmetic estimates only on the discarded tails. -/
theorem norm_zetaOrdinaryPrimeLogFilter_sub_band_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖zetaOrdinaryPrimeLogFilter p N (3 / 2 + I * y) - zetaOrdinaryPrimeBandFilter p N y‖ ≤
      (1 / 2 : ℝ) ^ N * zetaPrimeBandTailConstant p := by
  rw [zetaOrdinaryPrimeLogFilter, zetaOrdinaryPrimeBandFilter, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((1 / 2 : ℝ) ^ N *
        ((1 / 4 : ℝ) ^ k * zetaPrimeExpMass (3 / 2) + (8 : ℝ) ^ k * zetaPrimeExpMass (5 / 4))) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_zetaOrdinaryPrimeLogMoment_sub_band_le N k y) (norm_nonneg _)
    _ = _ := by
      rw [zetaPrimeBandTailConstant, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The actual omitted arithmetic tail tends to zero even before
normalization by the selected zero's exponentially growing source. -/
theorem tendsto_zetaOrdinaryPrimeLogFilter_sub_band (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N : ℕ ↦ zetaOrdinaryPrimeLogFilter p N (3 / 2 + I * y) -
      zetaOrdinaryPrimeBandFilter p N y) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaOrdinaryPrimeLogFilter_sub_band_le p N y)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (zetaPrimeBandTailConstant p)

/-- Every hypothetical right-half zero forces its full negative
multiplicity signal into a finite band of ordinary primes. All omitted
analytic and arithmetic terms have now been proved negligible. -/
theorem tendsto_zetaRightHalfOrdinaryPrimeBandFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaOrdinaryPrimeBandFilter (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have ha : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha).comp (tendsto_add_atTop_nat 1)
  have htail := hpow.mul (tendsto_zetaOrdinaryPrimeLogFilter_sub_band
    (zetaRightHalfZeroModeFilter rho hrho) rho.1.im)
  have h := (tendsto_zetaRightHalfOrdinaryPrimeLogFilter rho hrho).sub htail
  simp only [zero_mul, sub_zero, Function.comp_apply] at h
  convert h using 1
  funext N
  ring

/-- The real part of the literal finite prime band retains the full
negative multiplicity limit. -/
theorem tendsto_zetaRightHalfOrdinaryPrimeBandFilter_re (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      (zetaOrdinaryPrimeBandFilter (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im).re)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℝ))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfOrdinaryPrimeBandFilter rho hrho)
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.neg_re, Complex.natCast_re] using h

/-- Every sufficiently late finite prime band must have a negative
source at least half as large as the selected zero's exact multiplicity
scale. The opposite independent arithmetic estimate remains unproved. -/
theorem zetaRightHalfOrdinaryPrimeBandFilter_eventually_negative (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      (zetaOrdinaryPrimeBandFilter (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im).re <
        -(analyticZetaZeroMultiplicity rho : ℝ) / (2 * (3 / 2 - rho.1.re) ^ (N + 1)) := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_zetaRightHalfOrdinaryPrimeBandFilter_re rho hrho).eventually
    (gt_mem_nhds (by linarith : -(analyticZetaZeroMultiplicity rho : ℝ) <
      -(analyticZetaZeroMultiplicity rho : ℝ) / 2))
  filter_upwards [h] with N hN
  rw [lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hu _))]
  nlinarith

end

end RiemannGaussian
