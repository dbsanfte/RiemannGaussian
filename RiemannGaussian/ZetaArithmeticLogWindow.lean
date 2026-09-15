/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogMomentTilt

/-!
# Summed arithmetic bounds in a narrower logarithmic window

The existing Chernoff kernel machinery now bounds arbitrary finite masks
of actual divisor-majorized coefficients, including coefficients and
supports varying with moment order. Every fixed polynomial filter keeps
its full factorial shifts and finite tilt cost. Both outer pieces of
2*N/5 < log(n) <= 8*N*log(2) have explicit geometric allowances.
The upper rate has cube 125/128. Exact signed partitions are retained
before norms, and a general source-adapted tilt criterion stays available.
-/

namespace RiemannGaussian.ZetaArithmeticLogWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- Every finite selection of dominated coefficients has a uniform tilted
moment bound. All arithmetic coefficients remain in the original sum. -/
theorem norm_sum_moment_of_log_bound (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (N k : ℕ) (y σ q B : ℝ) (hσ : 1 < σ) (hq : 0 < q)
    (hlog : ∀ n ∈ S, (σ - 3 / 2 + q) * Real.log n ≤ (N : ℝ) * B) :
    ‖∑ n ∈ S, a n * zetaPrimeLogKernel (N + k) (3 / 2 + Complex.I * y) n‖ ≤
      (q⁻¹ * Real.exp B) ^ N * q⁻¹ ^ k * zetaMoebiusLogMajorantMass σ := by
  have hn (n : ℕ) : 0 ≤ zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n :=
    mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le
  calc
    _ ≤ ∑ n ∈ S, ‖a n * zetaPrimeLogKernel (N + k) (3 / 2 + Complex.I * y) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ((q⁻¹ * Real.exp B) ^ N * q⁻¹ ^ k) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n) := by
      apply Finset.sum_le_sum
      intro n hnS
      rw [norm_mul]
      exact (mul_le_mul (ha n hnS)
        (norm_zetaPrimeLogKernel_le_tilt N k n (3 / 2 + Complex.I * y) (q := q) (τ := σ) (A := B) hq (by
          have hh := hlog n hnS
          have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
          rw [hs]
          nlinarith))
        (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)).trans_eq (by ring)
    _ = ((q⁻¹ * Real.exp B) ^ N * q⁻¹ ^ k) *
        ∑ n ∈ S, zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum S (fun n _ => hn n) (summable_zetaMoebiusLogMajorant hσ))
      (by positivity)

/-- Fixed polynomial shifts pay a finite and explicit tilt cost. -/
def tiltConstant (P : Polynomial ℂ) (q σ : ℝ) : ℝ :=
  (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) * zetaMoebiusLogMajorantMass σ

/-- A finite arithmetic filter is exactly the sum of its shifted moments,
with every original coefficient and complex phase retained. -/
theorem sum_filter_eq_moments (S : Finset ℕ) (a : ℕ → ℂ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (∑ n ∈ S, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ k ∈ P.support, P.coeff k *
        ∑ n ∈ S, a n * zetaPrimeLogKernel (N + k) (3 / 2 + Complex.I * y) n := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold zetaPrimeLogKernel
  ring

/-- The same outer-label bound holds for every fixed polynomial filter
and every finite dominated coefficient family, uniformly in the ordinate. -/
theorem norm_sum_filter_of_log_bound (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y σ q B : ℝ) (hσ : 1 < σ) (hq : 0 < q)
    (hlog : ∀ n ∈ S, (σ - 3 / 2 + q) * Real.log n ≤ (N : ℝ) * B) :
    ‖∑ n ∈ S, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (q⁻¹ * Real.exp B) ^ N * tiltConstant P q σ := by
  rw [sum_filter_eq_moments]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ P.support, ‖P.coeff k‖ *
        ((q⁻¹ * Real.exp B) ^ N * q⁻¹ ^ k * zetaMoebiusLogMajorantMass σ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_sum_moment_of_log_bound S a ha N k y σ q B hσ hq hlog) (norm_nonneg _)
    _ = _ := by
      simp only [tiltConstant, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The upper-tail tilt has an explicit geometric rate. -/
def upperRate : ℝ := 5 * Real.exp (-(7 / 3 : ℝ) * Real.log 2)

/-- The upper rate is strictly positive. -/
theorem upperRate_pos : 0 < upperRate := by unfold upperRate; positivity

/-- An exact rational cube certifies the upper-tail rate without decimal
estimates of an exponential or logarithm. -/
theorem upperRate_cube : upperRate ^ 3 = (125 / 128 : ℝ) := by
  have h7 : Real.exp (7 * Real.log 2) = (128 : ℝ) := by
    have h := Real.exp_nat_mul (Real.log 2) 7
    norm_num only [Nat.cast_ofNat] at h
    rw [h, Real.exp_log (by norm_num)]
    norm_num
  rw [upperRate, mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (3 : ℝ) * (-(7 / 3 : ℝ) * Real.log 2) = -(7 * Real.log 2) by ring,
    Real.exp_neg, h7]
  norm_num

/-- The upper-tail rate is strictly below one, uniformly in height and
in the hypothetical source radius. -/
theorem upperRate_lt_one : upperRate < 1 := by
  by_contra! h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 3
  rw [one_pow, upperRate_cube] at hp
  norm_num at hp

/-- The lower-tail rate also stays strictly below one. -/
def lowerRate : ℝ := (1 / 2) * Real.exp (5 / 8)

/-- Positivity of the lower rate. -/
theorem lowerRate_pos : 0 < lowerRate := by unfold lowerRate; positivity

/-- The elementary logarithm bound makes the lower-tail rate strict. -/
theorem lowerRate_lt_one : lowerRate < 1 := by
  have hh : (5 / 8 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he := Real.exp_lt_exp.mpr hh
  rw [Real.exp_log (by norm_num)] at he
  dsimp [lowerRate]
  linarith

/-- Every selected term below exp(2*N/5) has a geometric bound before
source normalization, retaining all fixed factorial filter shifts. -/
theorem norm_lower_sum_le (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hS : ∀ n ∈ S, Real.log n ≤ (2 / 5 : ℝ) * N) :
    ‖∑ n ∈ S, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      lowerRate ^ N * tiltConstant P 2 (17 / 16) := by
  have h := norm_sum_filter_of_log_bound S a ha P N y (17 / 16) 2 (5 / 8)
    (by norm_num) (by norm_num) (by
      intro n hn
      have hh := hS n hn
      nlinarith)
  simpa only [lowerRate, one_div] using h

/-- Every selected term above the reduced upper endpoint decays at the
explicit rate whose cube is 125/128, before source normalization. -/
theorem norm_upper_sum_le (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hS : ∀ n ∈ S, 8 * (N : ℝ) * Real.log 2 ≤ Real.log n) :
    ‖∑ n ∈ S, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      upperRate ^ N * tiltConstant P (1 / 5) (121 / 120) := by
  have h := norm_sum_filter_of_log_bound S a ha P N y (121 / 120) (1 / 5)
    (-(7 / 3 : ℝ) * Real.log 2) (by norm_num) (by norm_num) (by
      intro n hn
      have hh := hS n hn
      nlinarith)
  simpa only [one_div, inv_inv, upperRate] using h

/-- Every positive tilt has a nonnegative finite cost. -/
theorem tiltConstant_nonneg (P : Polynomial ℂ) {q σ : ℝ} (hq : 0 < q) :
    0 ≤ tiltConstant P q σ := by
  apply mul_nonneg
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (by positivity))
  · exact tsum_nonneg (fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)

/-- A source-adapted tilt pays any selected family whenever its complete
normalized geometric rate is below one. The coefficients may vary with N. -/
theorem tendsto_normalized_tilted_sum (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, n ∈ S N → ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y σ q B u : ℝ) (hσ : 1 < σ) (hq : 0 < q) (hu : 0 < u)
    (hrate : u * (q⁻¹ * Real.exp B) < 1)
    (hlog : ∀ N n, n ∈ S N → (σ - 3 / 2 + q) * Real.log n ≤ (N : ℝ) * B) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ S N, a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => ?_)
    (show Tendsto (fun N : ℕ => (u * (q⁻¹ * Real.exp B)) ^ N *
      (u * tiltConstant P q σ)) atTop (𝓝 0) from by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hrate).mul_const
          (u * tiltConstant P q σ))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  exact (mul_le_mul_of_nonneg_left
    (norm_sum_filter_of_log_bound (S N) (a N) (ha N) P N y σ q B hσ hq (hlog N))
    (by positivity)).trans_eq (by rw [pow_succ, mul_pow]; ring)

/-- The smaller actual logarithmic window inside any existing finite
support. Arithmetic restrictions are intersected, never replaced. -/
def narrowBand (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter (fun (n : ℕ) => (2 / 5 : ℝ) * N < Real.log n ∧ Real.log n ≤ 8 * (N : ℝ) * Real.log 2)

/-- The lower and upper endpoints are correctly ordered for every N. -/
theorem endpoints_ordered (N : ℕ) :
    (2 / 5 : ℝ) * N ≤ 8 * (N : ℝ) * Real.log 2 := by
  have hlog : (2 / 5 : ℝ) ≤ 8 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) N)]

/-- Exact signed partition into the retained window and its two outer
pieces. All original atoms, signs and phases remain unchanged. -/
theorem sum_sub_narrowBand (S : Finset ℕ) (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ S, f n) - (∑ n ∈ narrowBand S N, f n) =
      (∑ n ∈ S.filter (fun (n : ℕ) => Real.log n ≤ (2 / 5 : ℝ) * N), f n) +
      (∑ n ∈ S.filter (fun (n : ℕ) => 8 * (N : ℝ) * Real.log 2 < Real.log n), f n) := by
  simp only [narrowBand, Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hl : (2 / 5 : ℝ) * N < Real.log n
  · by_cases hu : Real.log n ≤ 8 * (N : ℝ) * Real.log 2
    · simp [hl, hu, not_le.mpr hl, not_lt.mpr hu]
    · simp [hl, hu, not_le.mpr hl, lt_of_not_ge hu]
  · have hu : Real.log n ≤ 8 * (N : ℝ) * Real.log 2 := (le_of_not_gt hl).trans (endpoints_ordered N)
    simp [hl, le_of_not_gt hl, not_lt.mpr hu]

/-- The complete discarded outer contribution has an explicit sum of
two geometric allowances, for arbitrary dominated actual coefficients. -/
theorem norm_sub_narrowBand_le (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖(∑ n ∈ S, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
      (∑ n ∈ narrowBand S N, a n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)‖ ≤
      lowerRate ^ N * tiltConstant P 2 (17 / 16) +
        upperRate ^ N * tiltConstant P (1 / 5) (121 / 120) := by
  rw [sum_sub_narrowBand]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact norm_lower_sum_le _ a (fun n hn => ha n (Finset.mem_filter.mp hn).1) P N y
      (fun _ hn => (Finset.mem_filter.mp hn).2)
  · exact norm_upper_sum_le _ a (fun n hn => ha n (Finset.mem_filter.mp hn).1) P N y
      (fun _ hn => (Finset.mem_filter.mp hn).2.le)

/-- The two outer pieces vanish for arbitrarily changing finite
supports and coefficients, with the original source normalization. -/
theorem tendsto_sub_narrowBand (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, n ∈ S N → ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ((∑ n ∈ S N, a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
        (∑ n ∈ narrowBand (S N) N, a N n * zetaPrimeFilterKernel P N
          (3 / 2 + Complex.I * y) n))) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun N : ℕ =>
      lowerRate ^ N * tiltConstant P 2 (17 / 16) +
        upperRate ^ N * tiltConstant P (1 / 5) (121 / 120)) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one lowerRate_pos.le lowerRate_lt_one).mul_const
        (tiltConstant P 2 (17 / 16))).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one upperRate_pos.le upperRate_lt_one).mul_const
        (tiltConstant P (1 / 5) (121 / 120)))
  have he : Tendsto (fun N : ℕ =>
      (∑ n ∈ S N, a N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
        ∑ n ∈ narrowBand (S N) N, a N n * zetaPrimeFilterKernel P N
          (3 / 2 + Complex.I * y) n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => norm_sub_narrowBand_le (S N) (a N) (ha N) P N y) hdecay
  have hp : Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1)) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] using hu1) |>.comp
    exact tendsto_add_atTop_nat 1
  simpa only [mul_zero] using hp.mul he

end
end RiemannGaussian.ZetaArithmeticLogWindow
