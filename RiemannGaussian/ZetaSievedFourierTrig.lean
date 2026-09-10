/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSievedFourierCarrier

/-!
# Signed half-angle identities for the retained arithmetic interaction

The real part needed for the contradiction has an exact sine-square and
mixed sine-cosine expansion. The arithmetic coefficients are real, but
the kernel's imaginary Fourier component contributes a signed mixed term
that cannot be dropped. The source transfers to this single real work;
controlling the full complex norm or proving its decay is unnecessary.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The unwrapped additive phase at an original natural arithmetic index. -/
def cyclicPhaseAngle {q : ℕ} (k : ZMod q) (n : ℕ) : ℝ :=
  (n : ℝ) * (2 * Real.pi * (k.val : ℝ) / q)

/-- The cyclic character retains its full original-index phase,
including every turn around the circle. -/
theorem stdAddChar_pow_eq_exp_phase {q : ℕ} [NeZero q] (k : ZMod q) (n : ℕ) :
    ZMod.stdAddChar k ^ n = Complex.exp ((cyclicPhaseAngle k n : ℂ) * I) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp, ← Complex.exp_nat_mul]
  congr 1
  unfold cyclicPhaseAngle
  push_cast
  ring

/-- The exact signed half-angle split of one complete Fourier product.
The sine-square term and the mixed sine-cosine term both contribute to
the real part relevant to the contradiction. -/
theorem re_cyclicPhaseAtom {q : ℕ} [NeZero q] (k : ZMod q) (n : ℕ) (z : ℂ) :
    ((ZMod.stdAddChar k ^ n - 1) * z).re =
      -2 * (Real.sin (cyclicPhaseAngle k n / 2) ^ 2 * z.re +
        Real.sin (cyclicPhaseAngle k n / 2) * Real.cos (cyclicPhaseAngle k n / 2) * z.im) := by
  rw [stdAddChar_pow_eq_exp_phase]
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    Complex.exp_re, Complex.exp_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero,
    Real.exp_zero, one_mul]
  have hc : Real.cos (cyclicPhaseAngle k n) =
      1 - 2 * Real.sin (cyclicPhaseAngle k n / 2) ^ 2 := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      Real.cos_two_mul_eq_one_sub (cyclicPhaseAngle k n / 2)
  have hs : Real.sin (cyclicPhaseAngle k n) =
      2 * Real.sin (cyclicPhaseAngle k n / 2) * Real.cos (cyclicPhaseAngle k n / 2) := by
    convert Real.sin_two_mul (cyclicPhaseAngle k n / 2) using 1
    congr 1
    ring
  rw [hc, hs]
  ring

/-- The literal divisor signs and logarithms form a real coefficient,
before multiplication by either analytic or Fourier phases. -/
theorem zetaMoebiusLogTailCoefficient_im (D n : ℕ) :
    (zetaMoebiusLogTailCoefficient D n).im = 0 := by
  rw [zetaMoebiusLogTailCoefficient_eq]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs
  · simp only [Complex.mul_im, Complex.intCast_im, Complex.ofReal_im,
      mul_zero, zero_mul, zero_add]
  · rfl

/-- The exact arithmetic sieve preserves the real nature of every
coefficient without replacing any coefficient by its absolute value. -/
theorem zetaMoebiusSievedPrimeCoefficient_im (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    (zetaMoebiusSievedPrimeCoefficient D S n).im = 0 := by
  unfold zetaMoebiusSievedPrimeCoefficient zetaMoebiusDistinctPrimeCoefficient
  split_ifs <;> simp [zetaMoebiusLogTailCoefficient_im]

private theorem feature_real (n : ℕ) :
    zetaPrimeFeature (5 / 4) n = (zetaPrimeExpWeight (5 / 4) n : ℂ) := by
  unfold zetaPrimeFeature zetaPrimeExpWeight
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The single signed real work left by the half-angle identity.
The mixed kernel component stays coupled to the sine-square component
inside each original arithmetic and frequency product. -/
def zetaArithmeticTrigWork (a : ℕ → ℝ) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) : ℝ :=
  ((2 ^ (32 * N) + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ S, ∑ n ∈ zetaPrimeLogBand N,
    (a n * zetaPrimeExpWeight (5 / 4) n) *
      (Real.sin (cyclicPhaseAngle k n / 2) ^ 2 * (ZMod.dft (zetaQuarterKernelSamples p N y) k).re +
        Real.sin (cyclicPhaseAngle k n / 2) * Real.cos (cyclicPhaseAngle k n / 2) *
          (ZMod.dft (zetaQuarterKernelSamples p N y) k).im)

/-- Every real arithmetic family has an exact scalar trigonometric
representation of the required real part. This identity imposes no
summability or positivity assumptions on the finite retained interaction. -/
theorem zetaArithmeticCenteredPart_re_eq_trig (a : ℕ → ℂ)
    (ha : ∀ n, (a n).im = 0) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    (zetaArithmeticCenteredPart a p N y S).re =
      -2 * zetaArithmeticTrigWork (fun n ↦ (a n).re) p N y S := by
  unfold zetaArithmeticCenteredPart centeredFourierPart
  simp_rw [zetaArithmeticWeightedDFT_sub_zero_eq]
  have hq : (((2 ^ (32 * N) + 1 : ℕ) : ℂ)⁻¹) =
      ((((2 ^ (32 * N) + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hq, Complex.re_ofReal_mul]
  simp only [Finset.sum_mul, Complex.re_sum]
  unfold zetaArithmeticTrigWork
  rw [mul_left_comm (-2) (((2 ^ (32 * N) + 1 : ℕ) : ℝ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc, feature_real]
  have hn : a n = ((a n).re : ℂ) := by
    apply Complex.ext <;> simp [ha n]
  rw [hn, ← Complex.ofReal_mul, Complex.re_ofReal_mul, re_cyclicPhaseAtom]
  ring

/-- The actual selected-zero work in the smaller region, with the
entire cofinal arithmetic sieve and both trigonometric channels retained. -/
def zetaRightHalfSievedTrigWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticTrigWork (fun n ↦ (zetaMoebiusSievedPrimeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfMoebiusSieve rho N) n).re) (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))

/-- The real part of the original retained carrier is exactly minus
twice the signed trigonometric work; no imaginary-kernel contribution is lost. -/
theorem zetaRightHalfSievedFourierCarrier_re_eq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfSievedFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfSievedTrigWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_trig _
    (zetaMoebiusSievedPrimeCoefficient_im _ _) _ _ _ _

/-- The retained real trigonometric work has half the positive
multiplicity source. A strict one-sided upper bound below this source
would suffice; neither complex norm control nor decay is required. -/
theorem tendsto_zetaRightHalfSievedTrigWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfSievedTrigWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfSievedFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfSievedFourierCarrier_re_eq] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

end
end RiemannGaussian
