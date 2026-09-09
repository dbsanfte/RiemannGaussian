/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaBilinearCurvature
import RiemannGaussian.EtaDivisorGcdBound

/-!
# Gaussian control of the bare eta curvature

The Gaussian transform of the full bilinear gap sum retains every signed
pair. The oscillation is at the sum of the logarithmic frequencies. The
only zero-frequency pair is killed by its zero gap. These statements
concern the bare curvature, before multiplication by the eta numerator,
reflection weight, completion correction, and smoothing denominator.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

variable {ι : Type*}

private lemma gaussian_gap_atom (c d : ℂ) (a b sigma tau x t : ℝ) :
    (translatedGaussian tau x t : ℂ) *
      (c * d * exp (-((sigma : ℂ) + (t : ℂ) * I) * ((a : ℂ) + (b : ℂ))) *
        ((a : ℂ) - (b : ℂ)) ^ 2) =
      (c * d * exp (-(sigma : ℂ) * ((a : ℂ) + (b : ℂ))) *
        ((a : ℂ) - (b : ℂ)) ^ 2) *
          complexTranslatedGaussianOscillation tau x (-(a + b)) t := by
  unfold translatedGaussian complexTranslatedGaussianOscillation
  rw [Complex.ofReal_exp]
  have he : -((sigma : ℂ) + (t : ℂ) * I) * ((a : ℂ) + (b : ℂ)) =
      -(sigma : ℂ) * ((a : ℂ) + (b : ℂ)) + I * ((-(a + b) * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_add]
  push_cast
  ring

private lemma gaussian_gap_sum (S : Finset ι) (c : ι → ℂ) (l : ι → ℝ)
    (sigma tau x t : ℝ) :
    (translatedGaussian tau x t : ℂ) *
      finiteLaplaceGapSum S c l ((sigma : ℂ) + (t : ℂ) * I) =
      ∑ j ∈ S, ∑ k ∈ S,
        (c j * c k * exp (-(sigma : ℂ) * ((l j : ℂ) + (l k : ℂ))) *
          ((l j : ℂ) - (l k : ℂ)) ^ 2) *
            complexTranslatedGaussianOscillation tau x (-(l j + l k)) t := by
  simp only [finiteLaplaceGapSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact gaussian_gap_atom (c j) (c k) (l j) (l k) sigma tau x t

/-- The full Gaussian-weighted bilinear curvature sum is genuinely
integrable for every finite family at positive Gaussian time. -/
theorem integrable_finiteLaplaceGapSum_gaussian (S : Finset ι) (c : ι → ℂ)
    (l : ι → ℝ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    Integrable (fun t : ℝ => (translatedGaussian tau x t : ℂ) *
      finiteLaplaceGapSum S c l ((sigma : ℂ) + (t : ℂ) * I)) := by
  simp_rw [gaussian_gap_sum]
  apply integrable_finsetSum S
  intro j _
  apply integrable_finsetSum S
  intro k _
  exact (integrable_complexTranslatedGaussianOscillation htau x (-(l j + l k))).const_mul _

/-- Exact Gaussian evaluation retains the sum-frequency oscillation and
the squared difference-frequency amplitude for every coefficient family. -/
theorem integral_finiteLaplaceGapSum_gaussian (S : Finset ι) (c : ι → ℂ)
    (l : ι → ℝ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    (∫ t : ℝ, (translatedGaussian tau x t : ℂ) *
      finiteLaplaceGapSum S c l ((sigma : ℂ) + (t : ℂ) * I)) =
      (Real.sqrt (Real.pi / tau) : ℂ) *
        ∑ j ∈ S, ∑ k ∈ S,
          (c j * c k * exp (-(sigma : ℂ) * ((l j : ℂ) + (l k : ℂ))) *
            ((l j : ℂ) - (l k : ℂ)) ^ 2) *
              exp (((-(-(l j + l k)) ^ 2 / (4 * tau) : ℝ) : ℂ) + I * (x * (-(l j + l k)))) := by
  simp_rw [gaussian_gap_sum]
  have ht (j k : ι) : Integrable (fun t : ℝ =>
      (c j * c k * exp (-(sigma : ℂ) * ((l j : ℂ) + (l k : ℂ))) *
        ((l j : ℂ) - (l k : ℂ)) ^ 2) *
          complexTranslatedGaussianOscillation tau x (-(l j + l k)) t) :=
    (integrable_complexTranslatedGaussianOscillation htau x (-(l j + l k))).const_mul _
  rw [integral_finsetSum S (fun j _ => integrable_finsetSum S (fun k _ => ht j k)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum S (fun k _ => ht j k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, integral_complexTranslatedGaussianOscillation htau]
  push_cast
  ring

/-- A positive sum-frequency gap gives Gaussian decay with a summable
exponential majorant. The difference-frequency amplitude is included. -/
theorem logGap_gaussian_le {a b c tau : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hgap : c ≤ a + b) (htau : 0 < tau) (htime : tau ≤ c / 32) :
    (a - b) ^ 2 * Real.exp (-(a + b) ^ 2 / (4 * tau)) ≤
      Real.exp (-2 * (a + b)) * Real.exp (-c ^ 2 / (8 * tau)) := by
  let L := a + b
  have hL : 0 ≤ L := add_nonneg ha hb
  have hgapSq : (a - b) ^ 2 ≤ L ^ 2 := by dsimp [L]; nlinarith [mul_nonneg ha hb]
  have hcSq : c ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hc.le hL).2 hgap
  have htL : 32 * tau * L ≤ L ^ 2 := by
    have h : 32 * tau ≤ L := by dsimp [L]; linarith
    have hp := mul_le_mul_of_nonneg_right h hL
    nlinarith
  have hexp : L ^ 2 ≤ Real.exp (2 * L) := by
    have hp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hs := (sq_le_sq₀ hL (Real.exp_pos L).le).2 hp
    simpa only [two_mul, Real.exp_add, sq] using hs
  have hden : 0 < 8 * tau := by positivity
  have ht0 : tau ≠ 0 := htau.ne'
  have hpower : 2 * L - L ^ 2 / (4 * tau) ≤ -2 * L - c ^ 2 / (8 * tau) := by
    apply (mul_le_mul_iff_right₀ hden).mp
    calc
      (8 * tau) * (2 * L - L ^ 2 / (4 * tau)) = 16 * tau * L - 2 * L ^ 2 := by
        field_simp
        ring
      _ ≤ -16 * tau * L - c ^ 2 := by nlinarith
      _ = (8 * tau) * (-2 * L - c ^ 2 / (8 * tau)) := by
        field_simp
        ring
  calc
    (a - b) ^ 2 * Real.exp (-(a + b) ^ 2 / (4 * tau)) ≤
        Real.exp (2 * L) * Real.exp (-L ^ 2 / (4 * tau)) :=
      mul_le_mul_of_nonneg_right (hgapSq.trans hexp) (Real.exp_pos _).le
    _ = Real.exp (2 * L - L ^ 2 / (4 * tau)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-2 * L - c ^ 2 / (8 * tau)) := Real.exp_le_exp.mpr hpower
    _ = Real.exp (-2 * (a + b)) * Real.exp (-c ^ 2 / (8 * tau)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [L]
      ring

private lemma gaussian_log_atom_norm {c d : ℂ} {a b sigma tau : ℝ}
    (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsigma : 0 ≤ sigma) (x : ℝ) :
    ‖(c * d * exp (-(sigma : ℂ) * ((a : ℂ) + (b : ℂ))) *
      ((a : ℂ) - (b : ℂ)) ^ 2) *
        exp (((-(-(a + b)) ^ 2 / (4 * tau) : ℝ) : ℂ) + I * (x * (-(a + b))))‖ ≤
      (a - b) ^ 2 * Real.exp (-(a + b) ^ 2 / (4 * tau)) := by
  have he : Real.exp (-sigma * (a + b)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hsigma (add_nonneg ha hb)])
  have hscale : ‖c‖ * ‖d‖ * Real.exp (-sigma * (a + b)) ≤ 1 := by
    calc
      ‖c‖ * ‖d‖ * Real.exp (-sigma * (a + b)) ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  calc
    _ = (‖c‖ * ‖d‖ * Real.exp (-sigma * (a + b))) *
        ((a - b) ^ 2 * Real.exp (-(a + b) ^ 2 / (4 * tau))) := by
      rw [← Complex.ofReal_sub]
      simp only [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.mul_im, Complex.neg_im, zero_mul, mul_zero, sub_zero, add_zero, neg_sq,
        neg_zero]
      ring
    _ ≤ 1 * ((a - b) ^ 2 * Real.exp (-(a + b) ^ 2 / (4 * tau))) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = _ := one_mul _

private lemma exp_neg_two_log (y : ℝ) (hy : 0 < y) :
    Real.exp (-2 * Real.log y) = (1 / y) ^ 2 := by
  rw [show -2 * Real.log y = -(Real.log y + Real.log y) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log hy]
  field_simp

/-- A uniform Gaussian bound for every bounded complex coefficient
family on the positive integer logarithmic frequencies. The constant
does not depend on the cutoff, coefficients, nonnegative tilt, or center. -/
theorem norm_integral_finiteDirichletGapSum_gaussian_le (M : ℕ) (c : ℕ → ℂ)
    (hc : ∀ n ∈ Finset.Icc 1 M, ‖c n‖ ≤ 1) {sigma tau : ℝ}
    (hsigma : 0 ≤ sigma) (htau : 0 < tau) (htime : tau ≤ Real.log 2 / 32) (x : ℝ) :
    ‖∫ t : ℝ, (translatedGaussian tau x t : ℂ) *
      finiteLaplaceGapSum (Finset.Icc 1 M) c (fun n => Real.log n)
        ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      4 * Real.sqrt (Real.pi / tau) * Real.exp (-(Real.log 2) ^ 2 / (8 * tau)) := by
  let E := Real.exp (-(Real.log 2) ^ 2 / (8 * tau))
  let A (m n : ℕ) : ℂ :=
    (c m * c n * exp (-(sigma : ℂ) * ((Real.log m : ℂ) + (Real.log n : ℂ))) *
      ((Real.log m : ℂ) - (Real.log n : ℂ)) ^ 2) *
        exp (((-(-(Real.log m + Real.log n)) ^ 2 / (4 * tau) : ℝ) : ℂ) +
          I * (x * (-(Real.log m + Real.log n))))
  have hterm (m n : ℕ) (hm : m ∈ Finset.Icc 1 M) (hn : n ∈ Finset.Icc 1 M) :
      ‖A m n‖ ≤ (1 / (m : ℝ)) ^ 2 * (1 / (n : ℝ)) ^ 2 * E := by
    by_cases hmn : m = n
    · subst n
      simp only [A, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, norm_zero]
      positivity
    have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hmp : 0 < (m : ℝ) := by linarith
    have hnp : 0 < (n : ℝ) := by linarith
    have hp : 2 ≤ (m : ℝ) * (n : ℝ) := by
      have hmn2 : 2 ≤ m * n := by
        have hmnat := (Finset.mem_Icc.mp hm).1
        have hnnat := (Finset.mem_Icc.mp hn).1
        by_cases hmone : m = 1
        · subst m
          simp only [one_mul]
          omega
        · have : 2 ≤ m := by omega
          nlinarith
      exact_mod_cast hmn2
    have hgap : Real.log 2 ≤ Real.log (m : ℝ) + Real.log (n : ℝ) := by
      rw [← Real.log_mul hmp.ne' hnp.ne']
      exact Real.log_le_log (by norm_num) hp
    calc
      ‖A m n‖ ≤ (Real.log m - Real.log n) ^ 2 *
          Real.exp (-(Real.log m + Real.log n) ^ 2 / (4 * tau)) :=
        gaussian_log_atom_norm (hc m hm) (hc n hn) (Real.log_nonneg hm1) (Real.log_nonneg hn1) hsigma x
      _ ≤ Real.exp (-2 * (Real.log m + Real.log n)) * E :=
        logGap_gaussian_le (Real.log_nonneg hm1) (Real.log_nonneg hn1)
          (Real.log_pos (by norm_num)) hgap htau htime
      _ = _ := by
        rw [mul_add, Real.exp_add, exp_neg_two_log _ hmp, exp_neg_two_log _ hnp]
  have hsum : ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, A m n‖ ≤ 4 * E := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, ‖A m n‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          (1 / (m : ℝ)) ^ 2 * (1 / (n : ℝ)) ^ 2 * E :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hterm m n hm hn
      _ = (∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) ^ 2) ^ 2 * E := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
      _ ≤ 4 * E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hh := sum_Icc_inv_sq_le_two M
        have hp : 0 ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) ^ 2 := by positivity
        nlinarith
  rw [integral_finiteLaplaceGapSum_gaussian _ _ _ sigma htau x, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (Real.pi / tau) * (4 * E) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = _ := by dsimp [E]; ring

/-- The Gaussian-weighted bare curvature of every literal eta prefix is
integrable, with its full complex value retained. -/
theorem integrable_pairedEtaCorePartialSum_curvature_gaussian
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    Integrable (fun t : ℝ => (translatedGaussian tau x t : ℂ) *
      (deriv (pairedEtaCorePartialSum N) ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCorePartialSum N ((sigma : ℂ) + (t : ℂ) * I) *
          deriv (deriv (pairedEtaCorePartialSum N)) ((sigma : ℂ) + (t : ℂ) * I))) := by
  have h := (integrable_finiteLaplaceGapSum_gaussian (Finset.Icc 1 (2 * N))
    (fun n => (pairedEtaDirichletSign n : ℂ)) (fun n => Real.log n) sigma htau x).const_mul (-(1 / 2 : ℂ))
  apply h.congr
  filter_upwards with t
  rw [pairedEtaCorePartialSum_curvature_eq_logGap]
  unfold pairedEtaFiniteLogGapSum
  ring

/-- The bare eta curvature has a Gaussian bound uniform in every finite
prefix, every nonnegative real tilt, and every center. It does not bound
the reflection-weighted normalized source or exchange an infinite-prefix
limit with the integral. -/
theorem norm_integral_pairedEtaCorePartialSum_curvature_gaussian_le
    (N : ℕ) {sigma tau : ℝ} (hsigma : 0 ≤ sigma) (htau : 0 < tau)
    (htime : tau ≤ Real.log 2 / 32) (x : ℝ) :
    ‖∫ t : ℝ, (translatedGaussian tau x t : ℂ) *
      (deriv (pairedEtaCorePartialSum N) ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCorePartialSum N ((sigma : ℂ) + (t : ℂ) * I) *
          deriv (deriv (pairedEtaCorePartialSum N)) ((sigma : ℂ) + (t : ℂ) * I))‖ ≤
      2 * Real.sqrt (Real.pi / tau) * Real.exp (-(Real.log 2) ^ 2 / (8 * tau)) := by
  have hc (n : ℕ) (_ : n ∈ Finset.Icc 1 (2 * N)) : ‖(pairedEtaDirichletSign n : ℂ)‖ ≤ 1 := by
    unfold pairedEtaDirichletSign
    split_ifs <;> norm_num
  have h := norm_integral_finiteDirichletGapSum_gaussian_le (2 * N)
    (fun n => (pairedEtaDirichletSign n : ℂ)) hc hsigma htau htime x
  have he (t : ℝ) : (translatedGaussian tau x t : ℂ) *
      (deriv (pairedEtaCorePartialSum N) ((sigma : ℂ) + (t : ℂ) * I) ^ 2 -
        pairedEtaCorePartialSum N ((sigma : ℂ) + (t : ℂ) * I) *
          deriv (deriv (pairedEtaCorePartialSum N)) ((sigma : ℂ) + (t : ℂ) * I)) =
      -(1 / 2 : ℂ) * ((translatedGaussian tau x t : ℂ) *
        finiteLaplaceGapSum (Finset.Icc 1 (2 * N))
          (fun n => (pairedEtaDirichletSign n : ℂ)) (fun n => Real.log n)
            ((sigma : ℂ) + (t : ℂ) * I)) := by
    rw [pairedEtaCorePartialSum_curvature_eq_logGap]
    unfold pairedEtaFiniteLogGapSum
    ring
  simp_rw [he]
  rw [integral_const_mul, norm_mul]
  norm_num only [norm_neg, norm_div, norm_one, norm_ofNat]
  nlinarith

end
end RiemannGaussian
