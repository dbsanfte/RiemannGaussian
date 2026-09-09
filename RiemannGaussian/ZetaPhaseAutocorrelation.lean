/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseWeightedRecurrence
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Phase-return bounds with the complete autocorrelation

An arbitrary real test vector retains its entire phase Gram, including
every return multiplicity. Grouping by the distance of the two indices
allows each lag to be compared directly with its actual prime-power
amplitude. The resulting arithmetic lower bound holds for every summable
nonnegative real-frequency spectrum with nonnegative phase kernel.

Binomial test vectors come from `(1 + exp(i * theta)) ^ N`; no fitted
phase coefficients are used. This strengthens an independent arithmetic
floor, while the global signed inequality needed for RH remains open.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian
noncomputable section

/-- The full ordered autocorrelation at one nonnegative index distance.
Real test coefficients may have either sign. -/
def zetaPhaseReturnCorrelation {N : ℕ} (c : Fin (N + 1) → ℝ) (k : ℕ) : ℝ :=
  ∑ i, ∑ j, if Nat.dist i.val j.val = k then c i * c j else 0

/-- The zero-lag coefficient is exactly the squared size of the test. -/
theorem zetaPhaseReturnCorrelation_zero {N : ℕ} (c : Fin (N + 1) → ℝ) :
    zetaPhaseReturnCorrelation c 0 = ∑ i, c i ^ 2 := by
  have he (i j : Fin (N + 1)) : Nat.dist i.val j.val = 0 ↔ i = j :=
    ⟨fun h ↦ Fin.ext (Nat.eq_of_dist_eq_zero h), fun h ↦ by simp [h, Nat.dist_self]⟩
  simp only [zetaPhaseReturnCorrelation, he, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, ← pow_two]

/-- Exact grouping of a phase Gram by lag, before any bounds are taken. -/
theorem zetaPhase_gram_eq_returnCorrelation (a ω : ℕ → ℝ) {N : ℕ}
    (c : Fin (N + 1) → ℝ) (θ : ℝ) :
    (∑ i, ∑ j, c i * c j *
      zetaPhaseKernel a ω ((j.val : ℝ) * θ - (i.val : ℝ) * θ)) =
      ∑ k ∈ Finset.range (N + 1),
        zetaPhaseReturnCorrelation c k * zetaPhaseKernel a ω ((k : ℝ) * θ) := by
  have hdist (i j : Fin (N + 1)) : Nat.dist i.val j.val < N + 1 := by
    unfold Nat.dist
    omega
  have hphase (i j : Fin (N + 1)) :
      zetaPhaseKernel a ω ((j.val : ℝ) * θ - (i.val : ℝ) * θ) =
        zetaPhaseKernel a ω ((Nat.dist i.val j.val : ℝ) * θ) := by
    by_cases hij : i.val ≤ j.val
    · rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij, sub_mul]
    · have hji : j.val ≤ i.val := by omega
      rw [Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji]
      rw [show ((i.val : ℝ) - (j.val : ℝ)) * θ =
        -((j.val : ℝ) * θ - (i.val : ℝ) * θ) by ring, zetaPhaseKernel_neg]
  simp_rw [hphase, zetaPhaseReturnCorrelation, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.range (N + 1))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := Finset.range (N + 1))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  simp [Finset.sum_ite_eq, Finset.mem_range, hdist]

/-- The zero frequency forces the entire autocorrelation-weighted
return sum. No sign assumption on the test vector is needed. -/
theorem zetaPhase_returnCorrelation_source {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (r : ℕ) (hr : ω r = 0)
    {N : ℕ} (c : Fin (N + 1) → ℝ) (θ : ℝ) :
    a r * (∑ i, c i) ^ 2 - (∑' n, a n) * (∑ i, c i ^ 2) ≤
      ∑ k ∈ Finset.range N, zetaPhaseReturnCorrelation c (k + 1) *
        zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ) := by
  have h := zetaPhase_gramEnergy_zeroFrequency_le ha hs r hr
    (fun i : Fin (N + 1) ↦ (i.val : ℝ) * θ) c
  rw [zetaPhase_gram_eq_returnCorrelation, Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, zero_mul, zetaPhaseKernel_zero,
    zetaPhaseReturnCorrelation_zero] at h
  linarith

/-- The entire weighted return sum lies below the arithmetic work
when its individual lag costs fit the actual prime amplitudes. No
frequency source or nonzero-frequency energy has yet been discarded. -/
theorem zetaPhase_returnCorrelation_primePower_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime)
    {N : ℕ} (c : Fin (N + 1) → ℝ) (v : ℝ)
    (hcost : ∀ k ∈ Finset.range N,
      v * zetaPhaseReturnCorrelation c (k + 1) ≤ zetaPhasePrimeWeight σ (p ^ (k + 1)))
    (y : ℝ) :
    v * (∑ k ∈ Finset.range N, zetaPhaseReturnCorrelation c (k + 1) *
      zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * (y * Real.log p))) ≤
      ∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  have hf := zetaPhase_finite_primeWork_le ha hs hP hσ y
    ((Finset.range N).image (fun k ↦ p ^ (k + 1)))
  rw [Finset.sum_image (fun i _ j _ hij ↦
    Nat.add_right_cancel (Nat.pow_right_injective hp.two_le hij))] at hf
  refine le_trans ?_ hf
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have he : y * Real.log (p ^ (k + 1) : ℕ) =
      ((k + 1 : ℕ) : ℝ) * (y * Real.log p) := by
    rw [Nat.cast_pow, Real.log_pow]
    ring
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hcost k hk) (hP _)

/-- Any finite test whose actual lag costs fit the prime amplitudes
gives a proved arithmetic floor for every admissible phase family. The
prime, all its retained powers, and the height remain unchanged. -/
theorem zetaPhase_returnCorrelation_primePower_floor {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0)
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime)
    {N : ℕ} (c : Fin (N + 1) → ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hcost : ∀ k ∈ Finset.range N,
      v * zetaPhaseReturnCorrelation c (k + 1) ≤ zetaPhasePrimeWeight σ (p ^ (k + 1)))
    (y : ℝ) :
    v * (a r * (∑ i, c i) ^ 2 - (∑' n, a n) * (∑ i, c i ^ 2)) ≤
      ∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  exact (mul_le_mul_of_nonneg_left
    (zetaPhase_returnCorrelation_source ha hs r hr c (y * Real.log p)) hv).trans
    (zetaPhase_returnCorrelation_primePower_le ha hs hP hσ hp c v hcost y)

/-- The exact binomial test, available at every degree. -/
def zetaPhaseBinomialTest (N : ℕ) (i : Fin (N + 1)) : ℝ := N.choose i.val

/-- The full coefficient mass of a binomial test is explicit. -/
theorem zetaPhaseBinomialTest_sum (N : ℕ) :
    (∑ i, zetaPhaseBinomialTest N i) = (2 : ℝ) ^ N := by
  simpa only [zetaPhaseBinomialTest, Finset.sum_range, Nat.cast_sum, Nat.cast_pow,
    Nat.cast_ofNat] using congrArg (fun n : ℕ ↦ (n : ℝ)) (Nat.sum_range_choose N)

/-- Vandermonde's identity evaluates the zero-lag mass at every degree. -/
theorem zetaPhaseBinomialTest_sum_sq (N : ℕ) :
    (∑ i, zetaPhaseBinomialTest N i ^ 2) = ((2 * N).choose N : ℝ) := by
  simpa only [zetaPhaseBinomialTest, Finset.sum_range, Nat.cast_sum, Nat.cast_pow]
    using congrArg (fun n : ℕ ↦ (n : ℝ)) (Nat.sum_range_choose_sq N)

/-- The binomial test is the exact complex trigonometric power; its
phase is retained before any real or norm projection. -/
theorem zetaPhaseBinomialTest_complex_sum (N : ℕ) (θ : ℝ) :
    (∑ i, (zetaPhaseBinomialTest N i : ℂ) *
      Complex.exp (((i.val : ℝ) * θ : ℝ) * I)) =
        (1 + Complex.exp ((θ : ℂ) * I)) ^ N := by
  rw [add_comm (1 : ℂ) (Complex.exp ((θ : ℂ) * I)), add_pow]
  simp only [one_pow, mul_one, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.exp_nat_mul]
  simp only [zetaPhaseBinomialTest, Complex.ofReal_natCast, Complex.ofReal_mul]
  rw [mul_comm (N.choose i.val : ℂ)]
  congr 2
  ring

/-- The same test is exactly a nonnegative trigonometric power after
forming its whole Gram. Both sine and cosine channels contribute. -/
theorem zetaPhaseBinomialTest_energy (N : ℕ) (θ : ℝ) :
    finiteCosinePhaseEnergy (fun i : Fin (N + 1) ↦ (i.val : ℝ) * θ)
      (zetaPhaseBinomialTest N) = (2 + 2 * Real.cos θ) ^ N := by
  have h := congrArg Complex.normSq (zetaPhaseBinomialTest_complex_sum N θ)
  rw [map_pow] at h
  have hn : Complex.normSq (1 + Complex.exp ((θ : ℂ) * I)) = 2 + 2 * Real.cos θ := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_add]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hn] at h
  rw [finiteCosinePhaseEnergy_eq_squares]
  convert h using 1
  simp [Complex.normSq_apply, pow_two, Complex.exp_re, Complex.exp_im]

/-- Every frequency contributes its full binomial trigonometric energy.
The series converges for every summable nonnegative spectrum, including
infinite spectra with arbitrary real frequencies. -/
theorem hasSum_zetaPhase_binomial_energy {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (N : ℕ) (θ : ℝ) :
    HasSum (fun n ↦ a n * (2 + 2 * Real.cos (ω n * θ)) ^ N)
      (∑ k ∈ Finset.range (N + 1),
        zetaPhaseReturnCorrelation (zetaPhaseBinomialTest N) k *
          zetaPhaseKernel a ω ((k : ℝ) * θ)) := by
  have h := hasSum_zetaPhase_gramEnergy (ω := ω) ha hs
    (fun i : Fin (N + 1) ↦ (i.val : ℝ) * θ) (zetaPhaseBinomialTest N)
  rw [zetaPhase_gram_eq_returnCorrelation] at h
  apply h.congr_fun
  intro n
  have he : (fun i : Fin (N + 1) ↦ ω n * ((i.val : ℝ) * θ)) =
      (fun i : Fin (N + 1) ↦ (i.val : ℝ) * (ω n * θ)) := by
    funext i
    ring
  rw [he, zetaPhaseBinomialTest_energy]

/-- The exact return identity keeps all nonzero-frequency energy,
rather than keeping only the zero-frequency lower bound. -/
theorem zetaPhase_binomial_return_identity {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (N : ℕ) (θ : ℝ) :
    (∑ k ∈ Finset.range N,
      zetaPhaseReturnCorrelation (zetaPhaseBinomialTest N) (k + 1) *
        zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ)) =
      (∑' n, a n * (2 + 2 * Real.cos (ω n * θ)) ^ N) -
        ((2 * N).choose N : ℝ) * (∑' n, a n) := by
  have h := (hasSum_zetaPhase_binomial_energy (ω := ω) ha hs N θ).tsum_eq
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, zero_mul, zetaPhaseKernel_zero,
    zetaPhaseReturnCorrelation_zero, zetaPhaseBinomialTest_sum_sq] at h
  linarith

/-- Any selected collection of frequencies supplies a joint return
source. This keeps their actual linked angles and applies to every degree
and every summable nonnegative real-frequency family. -/
theorem zetaPhase_binomial_selected_source {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (N : ℕ) (θ : ℝ) (F : Finset ℕ) :
    (∑ n ∈ F, a n * (2 + 2 * Real.cos (ω n * θ)) ^ N) -
        ((2 * N).choose N : ℝ) * (∑' n, a n) ≤
      ∑ k ∈ Finset.range N,
        zetaPhaseReturnCorrelation (zetaPhaseBinomialTest N) (k + 1) *
          zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ) := by
  rw [zetaPhase_binomial_return_identity ha hs]
  apply sub_le_sub_right
  apply Summable.sum_le_tsum F _
    (hasSum_zetaPhase_binomial_energy (ω := ω) ha hs N θ).summable
  intro n _
  exact mul_nonneg (ha n) (pow_nonneg (by linarith [Real.neg_one_le_cos (ω n * θ)]) _)

/-- An angle and its double cannot both avoid the binomial energy.
The bound is independent of the degree and keeps both frequency weights. -/
theorem binomial_trig_double_reserve {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (N : ℕ) (θ : ℝ) :
    min u v ≤ u * (2 + 2 * Real.cos θ) ^ N +
      v * (2 + 2 * Real.cos (2 * θ)) ^ N := by
  by_cases hc : -(1 / 2 : ℝ) ≤ Real.cos θ
  · have hp : 1 ≤ (2 + 2 * Real.cos θ) ^ N := one_le_pow₀ (by linarith)
    have h0 : 0 ≤ v * (2 + 2 * Real.cos (2 * θ)) ^ N :=
      mul_nonneg hv (pow_nonneg (by linarith [Real.neg_one_le_cos (2 * θ)]) _)
    exact (min_le_left u v).trans ((le_mul_of_one_le_right hu hp).trans (le_add_of_nonneg_right h0))
  · have hp : 1 ≤ (2 + 2 * Real.cos (2 * θ)) ^ N := by
      apply one_le_pow₀
      rw [Real.cos_two_mul]
      nlinarith [sq_nonneg (Real.cos θ + 1 / 2)]
    have h0 : 0 ≤ u * (2 + 2 * Real.cos θ) ^ N :=
      mul_nonneg hu (pow_nonneg (by linarith [Real.neg_one_le_cos θ]) _)
    exact (min_le_right u v).trans ((le_mul_of_one_le_right hv hp).trans (le_add_of_nonneg_left h0))

/-- Any two distinct frequencies related by doubling contribute an
additional uniform source beyond the zero frequency. This is a theorem
for all summable nonnegative real-frequency spectra, not a fitted family. -/
theorem zetaPhase_binomial_doubled_source {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (r i j : ℕ)
    (hri : r ≠ i) (hrj : r ≠ j) (hij : i ≠ j)
    (hr : ω r = 0) (hω : ω j = 2 * ω i) (N : ℕ) (θ : ℝ) :
    (4 : ℝ) ^ N * a r + min (a i) (a j) -
        ((2 * N).choose N : ℝ) * (∑' n, a n) ≤
      ∑ k ∈ Finset.range N,
        zetaPhaseReturnCorrelation (zetaPhaseBinomialTest N) (k + 1) *
          zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ) := by
  have h := zetaPhase_binomial_selected_source (ω := ω) ha hs N θ {r, i, j}
  rw [Finset.sum_insert (by simp [hri, hrj]), Finset.sum_pair hij, hr, zero_mul,
    Real.cos_zero, hω, show (2 * ω i) * θ = 2 * (ω i * θ) by ring] at h
  norm_num only [mul_one, show (2 : ℝ) + 2 = 4 by norm_num] at h
  have ht := binomial_trig_double_reserve (ha i) (ha j) N (ω i * θ)
  nlinarith only [h, ht]

/-- Actual arithmetic work retains the complete trigonometric energy
at every frequency. The prime amplitudes are compared before any source
selection, so later arguments can use the remainder and its linked phases. -/
theorem zetaPhase_binomial_primePower_energy_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime) (N : ℕ) (v : ℝ)
    (hcost : ∀ k ∈ Finset.range N,
      v * zetaPhaseReturnCorrelation (zetaPhaseBinomialTest N) (k + 1) ≤
        zetaPhasePrimeWeight σ (p ^ (k + 1))) (y : ℝ) :
    v * ((∑' n, a n * (2 + 2 * Real.cos (ω n * (y * Real.log p))) ^ N) -
        ((2 * N).choose N : ℝ) * (∑' n, a n)) ≤
      ∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  rw [← zetaPhase_binomial_return_identity ha hs N]
  exact zetaPhase_returnCorrelation_primePower_le ha hs hP hσ hp
    (zetaPhaseBinomialTest N) v hcost y

/-- Every binomial degree gives a uniform return constraint on every
admissible spectrum. The source and diagonal cost are both exact. -/
theorem zetaPhase_binomial_return_source {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (r : ℕ) (hr : ω r = 0)
    (N : ℕ) (θ : ℝ) :
    (4 : ℝ) ^ N * a r - ((2 * N).choose N : ℝ) * (∑' n, a n) ≤
      ∑ k ∈ Finset.range N, zetaPhaseReturnCorrelation (zetaPhaseBinomialTest N) (k + 1) *
        zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ) := by
  have h := zetaPhase_returnCorrelation_source ha hs r hr (zetaPhaseBinomialTest N) θ
  rw [zetaPhaseBinomialTest_sum, zetaPhaseBinomialTest_sum_sq] at h
  have he : ((2 : ℝ) ^ N) ^ 2 = (4 : ℝ) ^ N := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul]
    norm_num
  rw [he] at h
  nlinarith only [h]

end
end RiemannGaussian
