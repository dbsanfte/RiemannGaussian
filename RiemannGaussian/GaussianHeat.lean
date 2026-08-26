import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian heat convolution

This file formalizes the exact positive convolution identity used to propagate
Gaussian-Weil positivity from one endpoint `a` to every `0 < ε < a`.

It is independent of the Weil functional: the theorem is a pointwise identity
for a translated Gaussian.  Passing a Weil functional through this integral
will be a separate theorem once that functional has been defined on a suitable
topological test-function space.
-/

open MeasureTheory

namespace RiemannGaussian

noncomputable section

/-- A translated, unnormalised real Gaussian. -/
def translatedGaussian (ε t r : ℝ) : ℝ :=
  Real.exp (-ε * (r - t) ^ 2)

/-- The additional heat parameter needed to broaden an `a`-Gaussian to an
`ε`-Gaussian, where `0 < ε < a`. -/
def heatParameter (a ε : ℝ) : ℝ :=
  a * ε / (a - ε)

/-- A normalization chosen as the reciprocal of the Gaussian integral. -/
def heatNormalization (a b : ℝ) : ℝ :=
  (Real.sqrt (Real.pi / (a + b)))⁻¹

lemma heatParameter_pos {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    0 < heatParameter a ε := by
  exact div_pos (mul_pos (hε.trans hεa) hε) (sub_pos.mpr hεa)

lemma heatParameter_add_pos {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    0 < a + heatParameter a ε := by
  exact add_pos (hε.trans hεa) (heatParameter_pos hε hεa)

lemma heatParameter_effective {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    a * heatParameter a ε / (a + heatParameter a ε) = ε := by
  have ha_pos : 0 < a := hε.trans hεa
  have haε : a - ε ≠ 0 := ne_of_gt (sub_pos.mpr hεa)
  have ha : a ≠ 0 := ne_of_gt ha_pos
  simp only [heatParameter]
  field_simp [haε, ha]
  ring

lemma gaussian_complete_square {a b : ℝ} (hab : a + b ≠ 0) (r t s : ℝ) :
    b * (t - s) ^ 2 + a * (r - s) ^ 2 =
      (a + b) * (s - (a * r + b * t) / (a + b)) ^ 2
        + (a * b / (a + b)) * (r - t) ^ 2 := by
  field_simp
  ring

lemma translatedGaussian_product_eq
    {a b : ℝ} (hab : a + b ≠ 0) (r t s : ℝ) :
    Real.exp (-b * (t - s) ^ 2) * translatedGaussian a s r =
      Real.exp (-(a * b / (a + b)) * (r - t) ^ 2) *
        Real.exp (-(a + b) *
          (s - (a * r + b * t) / (a + b)) ^ 2) := by
  simp only [translatedGaussian, ← Real.exp_add]
  apply congrArg Real.exp
  calc
    -b * (t - s) ^ 2 + -a * (r - s) ^ 2 =
        -(b * (t - s) ^ 2 + a * (r - s) ^ 2) := by ring
    _ = -((a + b) * (s - (a * r + b * t) / (a + b)) ^ 2
        + (a * b / (a + b)) * (r - t) ^ 2) := by
          rw [gaussian_complete_square hab]
    _ = -(a * b / (a + b)) * (r - t) ^ 2
        + -(a + b) * (s - (a * r + b * t) / (a + b)) ^ 2 := by ring

lemma integrable_translatedGaussian_product
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r t : ℝ) :
    Integrable (fun s : ℝ =>
      Real.exp (-b * (t - s) ^ 2) * translatedGaussian a s r) := by
  have hab_pos : 0 < a + b := add_pos ha hb
  have hab : a + b ≠ 0 := ne_of_gt hab_pos
  let m : ℝ := (a * r + b * t) / (a + b)
  let c : ℝ := Real.exp (-(a * b / (a + b)) * (r - t) ^ 2)
  have hgauss : Integrable (fun s : ℝ =>
      Real.exp (-(a + b) * (s - m) ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq hab_pos).comp_sub_right m
  have hscaled : Integrable (fun s : ℝ =>
      c * Real.exp (-(a + b) * (s - m) ^ 2)) := hgauss.const_mul c
  refine hscaled.congr (Filter.Eventually.of_forall fun s => ?_)
  exact (translatedGaussian_product_eq hab r t s).symm

/-- Integral of the product of two translated Gaussians. -/
theorem integral_translatedGaussian_mul_translatedGaussian
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r t : ℝ) :
    (∫ s : ℝ,
        Real.exp (-b * (t - s) ^ 2) * translatedGaussian a s r) =
      Real.exp (-(a * b / (a + b)) * (r - t) ^ 2) *
        Real.sqrt (Real.pi / (a + b)) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  let m : ℝ := (a * r + b * t) / (a + b)
  have hpoint (s : ℝ) :
      Real.exp (-b * (t - s) ^ 2) * translatedGaussian a s r =
        Real.exp (-(a * b / (a + b)) * (r - t) ^ 2) *
          Real.exp (-(a + b) * (s - m) ^ 2) := by
    simpa only [m] using translatedGaussian_product_eq hab r t s
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul]
  have hshift :
      (∫ s : ℝ, Real.exp (-(a + b) * (s - m) ^ 2)) =
        Real.sqrt (Real.pi / (a + b)) := by
    calc
      _ = ∫ x : ℝ, Real.exp (-(a + b) * x ^ 2) := by
        simpa using MeasureTheory.integral_sub_right_eq_self
          (fun x : ℝ => Real.exp (-(a + b) * x ^ 2)) m
      _ = Real.sqrt (Real.pi / (a + b)) := integral_gaussian (a + b)
  rw [hshift]

/-- Exact broadening of a translated Gaussian by positive Gaussian
convolution in its center variable. -/
theorem translatedGaussian_heat_convolution
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t r : ℝ) :
    translatedGaussian ε t r =
      heatNormalization a (heatParameter a ε) *
        ∫ s : ℝ,
          Real.exp (-heatParameter a ε * (t - s) ^ 2) *
            translatedGaussian a s r := by
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < heatParameter a ε := heatParameter_pos hε hεa
  have hab : 0 < a + heatParameter a ε := add_pos ha hb
  rw [integral_translatedGaussian_mul_translatedGaussian ha hb]
  rw [heatParameter_effective hε hεa]
  simp only [translatedGaussian, heatNormalization]
  have hsqrt : Real.sqrt (Real.pi / (a + heatParameter a ε)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos Real.pi_pos hab)
  field_simp

lemma heatNormalization_pos {a b : ℝ} (hab : 0 < a + b) :
    0 < heatNormalization a b := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (div_pos Real.pi_pos hab))

/-- The even pair used by the Gaussian-Weil program.  The second summand is
`exp (-ε (r+t)^2)`, written by reflecting `r`. -/
def symmetricGaussian (ε t r : ℝ) : ℝ :=
  translatedGaussian ε t r + translatedGaussian ε t (-r)

lemma symmetricGaussian_pos (ε t r : ℝ) :
    0 < symmetricGaussian ε t r := by
  exact add_pos (Real.exp_pos _) (Real.exp_pos _)

lemma symmetricGaussian_even (ε t r : ℝ) :
    symmetricGaussian ε t (-r) = symmetricGaussian ε t r := by
  simp [symmetricGaussian, add_comm]

/-- The exact heat identity for the symmetric Gaussian test function. -/
theorem symmetricGaussian_heat_convolution
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t r : ℝ) :
    symmetricGaussian ε t r =
      heatNormalization a (heatParameter a ε) *
        ∫ s : ℝ,
          Real.exp (-heatParameter a ε * (t - s) ^ 2) *
            symmetricGaussian a s r := by
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < heatParameter a ε := heatParameter_pos hε hεa
  have h₁ := integrable_translatedGaussian_product ha hb r t
  have h₂ := integrable_translatedGaussian_product ha hb (-r) t
  have hfirst := translatedGaussian_heat_convolution hε hεa t r
  have hsecond := translatedGaussian_heat_convolution hε hεa t (-r)
  simp only [symmetricGaussian, mul_add]
  rw [integral_add h₁ h₂, mul_add]
  exact congrArg₂ (· + ·) hfirst hsecond

/-- Positive Gaussian convolution of a real-valued function. -/
def heatConvolution (a b : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  heatNormalization a b *
    ∫ s : ℝ, Real.exp (-b * (t - s) ^ 2) * f s

/-- A continuous, everywhere-positive function remains strictly positive
after normalized Gaussian convolution, provided the product is integrable. -/
theorem heatConvolution_pos
    {a b : ℝ} (hab : 0 < a + b)
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_pos : ∀ s, 0 < f s)
    (t : ℝ)
    (hf_int : Integrable (fun s : ℝ =>
      Real.exp (-b * (t - s) ^ 2) * f s)) :
    0 < heatConvolution a b f t := by
  have hcont : Continuous (fun s : ℝ =>
      Real.exp (-b * (t - s) ^ 2) * f s) := by
    fun_prop
  have hnonneg : 0 ≤ (fun s : ℝ =>
      Real.exp (-b * (t - s) ^ 2) * f s) := fun s =>
    mul_nonneg (Real.exp_pos _).le (hf_pos s).le
  have hnonzero :
      Real.exp (-b * (t - t) ^ 2) * f t ≠ 0 :=
    ne_of_gt (mul_pos (Real.exp_pos _) (hf_pos t))
  exact mul_pos (heatNormalization_pos hab)
    (integral_pos_of_integrable_nonneg_nonzero hcont hf_int hnonneg hnonzero)

end

end RiemannGaussian
