/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierFractionalBudget
import RiemannGaussian.ZetaMoebiusCenteredResonance
import RiemannGaussian.ZetaPrimeKernelLaplace

/-!
# Independent physical tests of the quarter-kernel Fourier budget

A uniform first-derivative bound connects every positive real sample to
the actual finite cyclic samples. The already controlled upper tail extends
this comparison globally. Exact Laplace moments then give lower tests of
the complete fractional Fourier absolute mass, with no arithmetic or
zero-source asymptotic used to obtain the tests.
-/

open Complex Filter MeasureTheory Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A fixed allowance for interpolating positive samples and for the
entire part beyond the finite cyclic endpoint. -/
def zetaQuarterKernelInterpolationConstant (p : Polynomial ℂ) (y : ℝ) : ℝ :=
  (1 + ‖1 / 4 + I * (y : ℂ)‖) * (∑ k ∈ p.support, ‖p.coeff k‖) +
    2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k

/-- The interpolation allowance is nonnegative and independent of moment order. -/
theorem zetaQuarterKernelInterpolationConstant_nonneg (p : Polynomial ℂ) (y : ℝ) :
    0 ≤ zetaQuarterKernelInterpolationConstant p y := by
  unfold zetaQuarterKernelInterpolationConstant
  positivity

/-- The complete first derivative is uniformly bounded at every
positive sample at least one, for all moment orders. -/
theorem norm_zetaQuarterKernel_first_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖(zetaPrimeFilterKernel p N (1 / 4 + I * y) x -
      (1 / 4 + I * y) * zetaPrimeFilterKernel p (N + 1) (1 / 4 + I * y) x) / (x : ℂ)‖ ≤
      (1 + ‖1 / 4 + I * (y : ℂ)‖) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  let s : ℂ := 1 / 4 + I * y
  have hb (n : ℕ) : ‖zetaPrimeFilterKernel p n s x / (x : ℂ)‖ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ := by
    rw [← pow_one (x : ℂ), zetaPrimeFilterKernel_div_pow p n 1 s (zero_lt_one.trans_le hx)]
    have h := norm_zetaPrimeFilterKernel_le_tilt p n (s + 1) hx (by norm_num : (0 : ℝ) < 1)
    norm_num [s] at h ⊢
    apply h.trans
    have he : Real.exp (-(1 / 4 : ℝ) * Real.log x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.log_nonneg hx])
    simpa only [one_mul, neg_mul] using mul_le_mul_of_nonneg_right he
      (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  have he : (zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ) =
      zetaPrimeFilterKernel p N s x / (x : ℂ) - s * (zetaPrimeFilterKernel p (N + 1) s x / (x : ℂ)) := by ring
  change ‖(zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ)‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  calc
    _ ≤ (∑ k ∈ p.support, ‖p.coeff k‖) + ‖s‖ * ∑ k ∈ p.support, ‖p.coeff k‖ := by gcongr <;> apply hb
    _ = _ := by ring

/-- Rounding down a positive real sample loses only a fixed allowance;
the large cyclic endpoint does not enter the interpolation error. -/
theorem norm_zetaQuarterKernel_sub_floor_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hN : 1 ≤ N) {x : ℝ} (hx : 1 ≤ x) :
    ‖zetaPrimeFilterKernel p N (1 / 4 + I * y) x -
      zetaPrimeFilterKernel p N (1 / 4 + I * y) (⌊x⌋₊ : ℕ)‖ ≤
      (1 + ‖1 / 4 + I * (y : ℂ)‖) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  let A := (1 + ‖1 / 4 + I * (y : ℂ)‖) * ∑ k ∈ p.support, ‖p.coeff k‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hnr : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (⌊x⌋₊ : ℝ) x) :
      HasDerivAt (zetaPrimeFilterKernel p N (1 / 4 + I * y))
        ((zetaPrimeFilterKernel p (N - 1) (1 / 4 + I * y) t -
          (1 / 4 + I * y) * zetaPrimeFilterKernel p N (1 / 4 + I * y) t) / (t : ℂ)) t := by
    simpa only [Nat.sub_add_cancel hN] using hasDerivAt_zetaPrimeFilterKernel p (N - 1)
      (1 / 4 + I * y) (by linarith [ht.1])
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht ↦ (hd t ht).hasDerivWithinAt)
    (C := A) (fun t ht ↦ by
      simpa only [Nat.sub_add_cancel hN] using
        norm_zetaQuarterKernel_first_le p (N - 1) y (hnr.trans ht.1)) x ⟨hnx, le_rfl⟩
  apply hh.trans
  have hxl := Nat.lt_floor_add_one x
  nlinarith

/-- Every real kernel sample is bounded by the complete fractional
Fourier mass of the actual finite samples and a fixed interpolation cost. -/
theorem norm_zetaQuarterKernel_le_fractionalFourierMass (p : Polynomial ℂ) (N : ℕ)
    (y : ℝ) (hN : 1 ≤ N) {τ x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : 1 ≤ x) :
    ‖zetaPrimeFilterKernel p N (1 / 4 + I * y) x‖ ≤
      2 * x ^ τ * fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ +
        zetaQuarterKernelInterpolationConstant p y := by
  have hW := fractionalFourierMass_nonneg τ (zetaQuarterKernelSamples p N y) Finset.univ
  by_cases hM : x ≤ ((2 ^ (32 * N) : ℕ) : ℝ)
  · have hn : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
    have hnM : ⌊x⌋₊ < 2 ^ (32 * N) + 1 := by
      have hh : (⌊x⌋₊ : ℝ) ≤ ((2 ^ (32 * N) : ℕ) : ℝ) := (Nat.floor_le (by linarith)).trans hM
      exact_mod_cast (show (⌊x⌋₊ : ℝ) < ((2 ^ (32 * N) : ℕ) : ℝ) + 1 by linarith)
    have hs := norm_sub_zero_le_fractionalFourierMass (zetaQuarterKernelSamples p N y)
      (⌊x⌋₊ : ZMod (2 ^ (32 * N) + 1)) hτ0 hτ1
    rw [zetaQuarterKernelSamples_nat p N y (by omega) hnM,
      show zetaQuarterKernelSamples p N y 0 = 0 by simp [zetaQuarterKernelSamples], sub_zero,
      ZMod.val_natCast_of_lt hnM] at hs
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg ⌊x⌋₊) (Nat.floor_le (by linarith)) hτ0
    have hn' := hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hW)
    have hr := norm_zetaQuarterKernel_sub_floor_le p N y hN hx
    have ht := norm_le_insert' (zetaPrimeFilterKernel p N (1 / 4 + I * y) x)
      (zetaPrimeFilterKernel p N (1 / 4 + I * y) (⌊x⌋₊ : ℕ))
    unfold zetaQuarterKernelInterpolationConstant
    linarith [Finset.sum_nonneg (s := p.support) (fun k _ ↦
      mul_nonneg (norm_nonneg (p.coeff k)) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) k))]
  · have ht := norm_zetaQuarterKernel_near_upper_le p N y hx (by linarith)
    have hp : (1 / 2 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hs : 0 ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by positivity
    have ha : 0 ≤ (1 + ‖1 / 4 + I * (y : ℂ)‖) * ∑ k ∈ p.support, ‖p.coeff k‖ := by positivity
    unfold zetaQuarterKernelInterpolationConstant
    have h0 : 0 ≤ 2 * x ^ τ * fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ := by positivity
    nlinarith

/-- A damped logarithmic kernel has a global integrable majorant in
terms of the actual finite Fourier budget. The exponent gap is explicit. -/
theorem norm_zetaFactorialPolynomial_exp_le_fourier (p : Polynomial ℂ) (N : ℕ)
    (y : ℝ) (hN : 1 ≤ N) {τ d t : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (ht : 0 ≤ t) :
    ‖zetaFactorialPolynomial p N t * Complex.exp (-(d : ℂ) * t)‖ ≤
      (2 * fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ) *
        Real.exp (-(d - 1 / 4 - τ) * t) +
      zetaQuarterKernelInterpolationConstant p y * Real.exp (-(d - 1 / 4) * t) := by
  have he : ‖zetaFactorialPolynomial p N t * Complex.exp (-(d : ℂ) * t)‖ =
      ‖zetaPrimeFilterKernel p N (1 / 4 + I * y) (Real.exp t)‖ *
        Real.exp (-(d - 1 / 4) * t) := by
    simp only [zetaPrimeFilterKernel, Real.log_exp, norm_mul, Complex.norm_exp]
    norm_num
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_right
    (norm_zetaQuarterKernel_le_fractionalFourierMass p N y hN hτ0 hτ1 (Real.one_le_exp ht))
    (Real.exp_pos (-(d - 1 / 4) * t)).le
  apply h.trans_eq
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, add_mul]
  have hexp : Real.exp (t * τ) * Real.exp (-(d - 1 / 4) * t) =
      Real.exp (-(d - 1 / 4 - τ) * t) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (2 * fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ) *
        (Real.exp (t * τ) * Real.exp (-(d - 1 / 4) * t)) +
      zetaQuarterKernelInterpolationConstant p y * Real.exp (-(d - 1 / 4) * t) := by ring
    _ = _ := by rw [hexp]

/-- Every positive Laplace test supplies an independent lower test of
the finite absolute Fourier budget. The full polynomial evaluation, rather
than the separate coefficient norms, appears on the left. -/
theorem zetaQuarterKernel_laplace_le_fractionalFourierMass (p : Polynomial ℂ) (N : ℕ)
    (y : ℝ) (hN : 1 ≤ N) {τ d : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hd : 1 / 4 + τ < d) :
    d⁻¹ ^ (N + 1) * ‖p.eval (d : ℂ)⁻¹‖ ≤
      (2 / (d - 1 / 4 - τ)) * fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ +
        zetaQuarterKernelInterpolationConstant p y / (d - 1 / 4) := by
  have hd0 : 0 < d := by linarith
  have hi1 := (integrableOn_exp_mul_Ioi (a := -(d - 1 / 4 - τ)) (by linarith) 0).const_mul
    (2 * fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ)
  have hi2 := (integrableOn_exp_mul_Ioi (a := -(d - 1 / 4)) (by linarith) 0).const_mul
    (zetaQuarterKernelInterpolationConstant p y)
  have h := norm_integral_le_of_norm_le (hi1.add hi2) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_zetaFactorialPolynomial_exp_le_fourier p N y hN hτ0 hτ1 ht.le)
  rw [integral_zetaFactorialPolynomial_exp p N hd0, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hd0.le] at h
  have he (r : ℝ) (hr : 0 < r) : (∫ t : ℝ in Set.Ioi 0, Real.exp (-r * t)) = r⁻¹ := by
    simpa using integral_exp_mul_Ioi (neg_neg_of_pos hr) 0
  simp only [Pi.add_apply] at h
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    he _ (by linarith), he _ (by linarith)] at h
  apply h.trans_eq
  ring

end
end RiemannGaussian
