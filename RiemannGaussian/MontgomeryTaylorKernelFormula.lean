/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorInverseSampling

/-!
# An entire identity for the Montgomery--Taylor kernel

The identity is valid even at the two removable singularities. Numerical
enclosures may use the quotient only after checking its denominator. The
small-frequency estimate handles a full neighborhood of both singularities.
-/

namespace RiemannGaussian.MontgomeryTaylorKernelFormula
noncomputable section

/-- The single transcendental coefficient remaining after normalization. -/
def eta : ℝ := Real.cos montgomeryTaylorTheta / Real.sinc montgomeryTaylorTheta

private lemma mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

private lemma sinc_theta_eq :
    Real.sinc montgomeryTaylorTheta = Real.sqrt 2 * Real.sin montgomeryTaylorTheta := by
  have hr : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [Real.sinc_of_ne_zero montgomeryTaylorTheta_pos.ne']
  unfold montgomeryTaylorTheta
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A closed formula for the normalized coefficient, with a positive
denominator, suitable for an independent rational enclosure. -/
theorem eta_eq_cos_div : eta =
    Real.cos (Real.sqrt 2 / 2) /
      (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)) := by
  rw [eta, sinc_theta_eq]
  rfl

/-- Multiplying by the apparent denominator gives a global identity; no
division by a possibly vanishing kernel factor occurs. -/
theorem denominator_mul_kernel (x : ℝ) :
    (x ^ 2 - 2) * montgomeryTaylorKernel x =
      2 * (eta * x * Real.sin (x / 2) - Real.cos (x / 2)) := by
  let u := (x - Real.sqrt 2) / 2
  let v := (x + Real.sqrt 2) / 2
  have hfac : x ^ 2 - 2 = 4 * (u * v) := by
    dsimp [u, v]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hu : u = x / 2 - montgomeryTaylorTheta := by
    dsimp [u, montgomeryTaylorTheta]; ring
  have hv : v = x / 2 + montgomeryTaylorTheta := by
    dsimp [v, montgomeryTaylorTheta]; ring
  have hprod : (x ^ 2 - 2) * (Real.sinc u + Real.sinc v) =
      4 * montgomeryTaylorNumerator x := by
    calc
      _ = 4 * (v * (u * Real.sinc u) + u * (v * Real.sinc v)) := by rw [hfac]; ring
      _ = 4 * (v * Real.sin u + u * Real.sin v) := by rw [mul_sinc, mul_sinc]
      _ = _ := by
        rw [hu, hv, Real.sin_sub, Real.sin_add]
        dsimp [montgomeryTaylorNumerator, montgomeryTaylorTheta]
        ring
  have hden := sinc_montgomeryTaylorTheta_pos.ne'
  change (x ^ 2 - 2) * ((Real.sinc u + Real.sinc v) /
    (2 * Real.sinc montgomeryTaylorTheta)) = _
  rw [← mul_div_assoc, hprod]
  unfold eta montgomeryTaylorNumerator
  rw [← sinc_theta_eq]
  field_simp
  ring

/-- The normalized cycles variable used in finite certificate tables. -/
theorem cycles_identity (x : ℝ) :
    (2 * Real.pi ^ 2 * x ^ 2 - 1) * montgomeryTaylorKernel (2 * Real.pi * x) =
      2 * Real.pi * eta * x * Real.sin (Real.pi * x) - Real.cos (Real.pi * x) := by
  have h := denominator_mul_kernel (2 * Real.pi * x)
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring] at h
  nlinarith

/-- Away from the removable denominator zeros, the cycles formula is a
legitimate quotient and can be passed to a checked interval evaluator. -/
theorem cycles_quotient {x : ℝ} (hx : 2 * Real.pi ^ 2 * x ^ 2 - 1 ≠ 0) :
    montgomeryTaylorKernel (2 * Real.pi * x) =
      (2 * Real.pi * eta * x * Real.sin (Real.pi * x) - Real.cos (Real.pi * x)) /
        (2 * Real.pi ^ 2 * x ^ 2 - 1) := by
  apply (eq_div_iff hx).mpr
  simpa only [mul_comm] using cycles_identity x

/-- A global cubic sine bound supplies a quadratic lower bound for sinc. -/
theorem sinc_lower (x : ℝ) : 1 - x ^ 2 / 6 ≤ Real.sinc x := by
  suffices ∀ y : ℝ, 0 ≤ y → 1 - y ^ 2 / 6 ≤ Real.sinc y by
    have h := this |x| (abs_nonneg x)
    rcases le_total 0 x with hx | hx
    · simpa only [abs_of_nonneg hx] using h
    · simpa only [abs_of_nonpos hx, neg_sq, Real.sinc_neg] using h
  intro y hy
  rcases eq_or_lt_of_le hy with rfl | hy
  · simp
  · rw [Real.sinc_of_ne_zero hy.ne', le_div_iff₀ hy]
    nlinarith [Real.sin_ge_sub_cube hy.le]

/-- The complete small-frequency interval has a fixed positive kernel
floor, including both apparent poles of the quotient formula. -/
theorem small_cycles_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (1 : ℝ) / 3) :
    (1 : ℝ) / 3 ≤ montgomeryTaylorKernel (2 * Real.pi * x) := by
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hr : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpx0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0
  have hpx : Real.pi * x ≤ (11 : ℝ) / 10 := by
    have h := mul_le_mul_of_nonneg_left hx1 Real.pi_pos.le
    linarith [Real.pi_lt_d2]
  have hleft : ((2 * Real.pi * x - Real.sqrt 2) / 2) ^ 2 ≤ 4 := by
    nlinarith
  have hright : ((2 * Real.pi * x + Real.sqrt 2) / 2) ^ 2 ≤ 4 := by
    nlinarith
  have hl := sinc_lower ((2 * Real.pi * x - Real.sqrt 2) / 2)
  have hh := sinc_lower ((2 * Real.pi * x + Real.sqrt 2) / 2)
  have hsinc : Real.sinc montgomeryTaylorTheta ≤ 1 := Real.sinc_le_one _
  unfold montgomeryTaylorKernel
  apply (le_div_iff₀ (mul_pos (by norm_num) sinc_montgomeryTaylorTheta_pos)).mpr
  linarith

end
end RiemannGaussian.MontgomeryTaylorKernelFormula
