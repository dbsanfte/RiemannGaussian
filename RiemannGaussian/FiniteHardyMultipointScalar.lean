import RiemannGaussian.FiniteHardySchwarzPick

/-!
# Scalar geometry for the finite multipoint Pick argument

This file formalizes the disk-automorphism algebra needed to turn a
multiplicity-aware zero-product estimate into the sharp Cayley-radius bound.
The reduction deliberately keeps the zero-product estimate as a separate
hypothesis; proving that estimate is the next analytic Pick step.
-/

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

/-- The standard automorphism of the complex unit disk taking `a` to zero. -/
def unitDiskAutomorphism (a w : ℂ) : ℂ :=
  (w - a) / (1 - starRingEnd ℂ a * w)

@[simp] theorem unitDiskAutomorphism_zero (a : ℂ) :
    unitDiskAutomorphism a 0 = -a := by
  simp [unitDiskAutomorphism]

/-- A disk automorphism denominator cannot vanish when its center is in the
open unit disk and its argument is in the closed unit disk. -/
theorem unitDiskAutomorphism_denominator_ne_zero
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - starRingEnd ℂ a * w ≠ 0 := by
  intro hzero
  have hone' : (1 : ℂ) = starRingEnd ℂ a * w := sub_eq_zero.mp hzero
  have hone : starRingEnd ℂ a * w = 1 := hone'.symm
  have hnorm := congrArg norm hone
  rw [norm_mul, Complex.norm_conj, norm_one] at hnorm
  have hprod : ‖a‖ * ‖w‖ < 1 := by
    calc
      ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = ‖a‖ := mul_one _
      _ < 1 := ha
  linarith

/-- A disk automorphism preserves the closed unit disk. -/
theorem norm_unitDiskAutomorphism_le_one
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖unitDiskAutomorphism a w‖ ≤ 1 := by
  have hden := unitDiskAutomorphism_denominator_ne_zero ha hw
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hwSq : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hid := normSq_one_sub_mul_conj_sub_normSq_sub w a
  have hsq : Complex.normSq (w - a) ≤
      Complex.normSq (1 - starRingEnd ℂ a * w) := by
    calc
      Complex.normSq (w - a) ≤
          Complex.normSq (1 - w * starRingEnd ℂ a) := by nlinarith
      _ = Complex.normSq (1 - starRingEnd ℂ a * w) := by
        rw [mul_comm w (starRingEnd ℂ a)]
  unfold unitDiskAutomorphism
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr hden)).2
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm]
  exact hsq

/-- A disk automorphism is holomorphic on the open unit disk. -/
theorem unitDiskAutomorphism_differentiableOn
    {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (unitDiskAutomorphism a) (Metric.ball 0 1) := by
  intro w hw
  unfold unitDiskAutomorphism
  have hden : 1 - starRingEnd ℂ a * w ≠ 0 :=
    unitDiskAutomorphism_denominator_ne_zero
      ha (mem_ball_zero_iff.mp hw).le
  fun_prop

/-- Subtracting the image of zero exposes the positive radial factor of a
disk automorphism. -/
theorem unitDiskAutomorphism_sub_zero
    {a s : ℂ} (hden : 1 - starRingEnd ℂ a * s ≠ 0) :
    unitDiskAutomorphism a s - unitDiskAutomorphism a 0 =
      ((1 - Complex.normSq a : ℝ) : ℂ) * s /
        (1 - starRingEnd ℂ a * s) := by
  rw [unitDiskAutomorphism_zero]
  unfold unitDiskAutomorphism
  rw [show (((1 - Complex.normSq a : ℝ) : ℂ)) =
      1 - starRingEnd ℂ a * a by
    rw [← Complex.normSq_eq_conj_mul_self]
    norm_cast]
  have hden' : 1 - s * starRingEnd ℂ a ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hden, hden']
  ring

/-- The point of radius `r` lying on the ray through `s`; totalized division
makes it zero when `s = 0`. -/
def radialDiskPoint (r : ℝ) (s : ℂ) : ℂ :=
  ((r / ‖s‖ : ℝ) : ℂ) * s

theorem norm_radialDiskPoint
    {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : s ≠ 0) :
    ‖radialDiskPoint r s‖ = r := by
  unfold radialDiskPoint
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr (norm_nonneg _)),
    div_mul_cancel₀ r (norm_ne_zero_iff.mpr hs)]

theorem conj_radialDiskPoint_mul
    {r : ℝ} {s : ℂ} (hs : s ≠ 0) :
    starRingEnd ℂ (radialDiskPoint r s) * s = (r * ‖s‖ : ℝ) := by
  unfold radialDiskPoint
  simp only [map_mul, Complex.conj_ofReal]
  rw [mul_assoc, Complex.normSq_eq_conj_mul_self.symm,
    Complex.normSq_eq_norm_sq]
  norm_cast
  field_simp [norm_ne_zero_iff.mpr hs]

/-- Exact scalar terminal step for the multipoint argument.  If the images
of `s` and zero under the radial automorphism at radius `r` are at most
`2*r` apart, then `s` obeys the sharp Cayley-radius bound. -/
theorem norm_le_two_mul_div_one_add_sq_of_radialAutomorphism_sub
    {s : ℂ} {r : ℝ} (hr : 0 ≤ r) (hrone : r < 1)
    (hsone : ‖s‖ ≤ 1)
    (hbound :
      ‖unitDiskAutomorphism (radialDiskPoint r s) s -
          unitDiskAutomorphism (radialDiskPoint r s) 0‖ ≤ 2 * r) :
    ‖s‖ ≤ 2 * r / (1 + r ^ 2) := by
  by_cases hs : s = 0
  · rw [hs, norm_zero]
    positivity
  let x := ‖s‖
  let a := radialDiskPoint r s
  have hx : 0 < x := norm_pos_iff.mpr hs
  have hxa : x ≤ 1 := hsone
  have haNorm : ‖a‖ = r := norm_radialDiskPoint hr hs
  have hconj : starRingEnd ℂ a * s = (r * x : ℝ) := by
    exact conj_radialDiskPoint_mul hs
  have hrx : r * x < 1 := by
    exact (mul_le_mul_of_nonneg_left hxa hr).trans_lt (by simpa using hrone)
  have hden : 1 - starRingEnd ℂ a * s ≠ 0 := by
    rw [hconj]
    exact sub_ne_zero.mpr (by exact_mod_cast hrx.ne')
  rw [unitDiskAutomorphism_sub_zero hden, norm_div, norm_mul,
    hconj] at hbound
  norm_cast at hbound
  have hnormSq : Complex.normSq a = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, haNorm]
  rw [hnormSq] at hbound
  have hcoeff : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hdenReal : 0 < 1 - r * x := sub_pos.mpr hrx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcoeff,
    abs_of_pos hdenReal] at hbound
  apply (le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)).2
  change x * (1 + r ^ 2) ≤ 2 * r
  rw [div_le_iff₀ hdenReal] at hbound
  nlinarith

/-- Function-level wrapper for the scalar terminal step.  It isolates the
remaining multipoint task: bound the difference of the two commonly
transformed Schur values by twice the complete zero-radius product. -/
theorem norm_apply_le_two_mul_div_one_add_sq_of_radialCommonTransform_sub
    {f g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hrone : r < 1) (hf : ‖f z‖ ≤ 1)
    (hgz : g z = 0)
    (hbound :
      ‖unitDiskAutomorphism (radialDiskPoint r (f z)) (f z) -
          unitDiskAutomorphism (radialDiskPoint r (f z)) (g z)‖ ≤ 2 * r) :
    ‖f z‖ ≤ 2 * r / (1 + r ^ 2) := by
  apply norm_le_two_mul_div_one_add_sq_of_radialAutomorphism_sub
    hr hrone hf
  simpa [hgz] using hbound

end

end RiemannGaussian
