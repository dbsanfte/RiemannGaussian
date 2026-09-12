/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiLaplaceOrder

/-!
# Positive cosine modulation with exact coupled frequencies

Multiplying a window by `(1+cos(delta*t))/2` preserves its pointwise
nonnegativity, every absolute exponential moment, and the positivity of
its reflected Fermi pair. The latter follows from an exact positive
combination of the original pair at three coupled frequencies. The real
Laplace comparison keeps the modulated window itself, so its source and
constant-pole costs can be compared without separating the three phases.
-/

namespace RiemannGaussian.FermiCosineModulation
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open FermiLaplaceReflection

/-- The nonnegative cosine factor, with value one at the origin. -/
def factor (δ t : ℝ) : ℝ := (1 + Real.cos (δ * t)) / 2

/-- The original window with its coupled cosine modulation. -/
def modulate (δ : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := g t * factor δ t

/-- The modulation lies in the closed unit interval at every argument. -/
theorem factor_bounds (δ t : ℝ) : 0 ≤ factor δ t ∧ factor δ t ≤ 1 := by
  unfold factor
  constructor <;> linarith [Real.neg_one_le_cos (δ * t), Real.cos_le_one (δ * t)]

/-- Every nonnegative original window stays nonnegative. -/
theorem modulate_nonneg (δ : ℝ) {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (t : ℝ) :
    0 ≤ modulate δ g t := mul_nonneg (hg t) (factor_bounds δ t).1

/-- Modulation does not change the endpoint normalization. -/
theorem modulate_zero (δ : ℝ) (g : ℝ → ℝ) : modulate δ g 0 = g 0 := by
  simp [modulate, factor]

/-- Continuity survives multiplication by the cosine factor. -/
theorem continuous_modulate (δ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (modulate δ g) := by
  unfold modulate factor
  fun_prop

/-- Every absolute exponential moment survives, including negative damping. -/
theorem integrable_modulate_exp (δ : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (x : ℝ) (hi : Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) :
    Integrable (fun t : ℝ ↦ modulate δ g t * Real.exp (-x * t)) := by
  apply hi.norm.mono' (by have := continuous_modulate δ hg; fun_prop)
  filter_upwards with t
  simp only [modulate, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (factor_bounds δ t).1]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg _) (factor_bounds δ t).2) (abs_nonneg _)

/-- The complex modulation is an exact positive combination of three
exponentials, retaining both shifted phases. -/
theorem factor_mul_exp (δ t : ℝ) (z : ℂ) :
    (factor δ t : ℂ) * Complex.exp (-z * (t : ℂ)) =
      Complex.exp (-z * (t : ℂ)) / 2 +
      Complex.exp (-(z + I * δ) * (t : ℂ)) / 4 +
      Complex.exp (-(z - I * δ) * (t : ℂ)) / 4 := by
  have hc := Complex.two_cos ((δ * t : ℝ) : ℂ)
  rw [← Complex.ofReal_cos] at hc
  have hp : -(z + I * δ) * (t : ℂ) = -z * (t : ℂ) + -((δ * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hm : -(z - I * δ) * (t : ℂ) = -z * (t : ℂ) + ((δ * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hp, hm, Complex.exp_add, Complex.exp_add]
  unfold factor
  push_cast at hc ⊢
  linear_combination Complex.exp (-z * (t : ℂ)) * hc / 4

/-- The complete Fermi transform has the identical three-frequency
decomposition. All three integrals genuinely converge. -/
theorem transform_modulate (δ a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) (z : ℂ) :
    transform a (modulate δ g) z = transform a g z / 2 +
      transform a g (z + I * δ) / 4 + transform a g (z - I * δ) / 4 := by
  have hint (w : ℂ) : IntegrableOn
      (fun t : ℝ ↦ (weight a g t : ℂ) * Complex.exp (-w * (t : ℂ))) (Ioi 0) :=
    (integrable_transform_integrand a hg (hi w.re)).integrableOn
  have hsum : IntegrableOn (fun t : ℝ ↦
      (weight a g t : ℂ) * Complex.exp (-z * (t : ℂ)) / 2 +
      (weight a g t : ℂ) * Complex.exp (-(z + I * δ) * (t : ℂ)) / 4) (Ioi 0) :=
    ((hint z).div_const 2).add ((hint (z + I * δ)).div_const 4)
  unfold transform
  rw [← integral_div, ← integral_div, ← integral_div,
    ← integral_add ((hint z).div_const 2) ((hint (z + I * δ)).div_const 4),
    ← integral_add hsum ((hint (z - I * δ)).div_const 4)]
  apply integral_congr_ae
  filter_upwards with t
  have he : (weight a (modulate δ g) t : ℂ) =
      (weight a g t : ℂ) * (factor δ t : ℂ) := by
    unfold weight modulate
    push_cast
    ring
  rw [he, mul_assoc, factor_mul_exp]
  ring

/-- The reflected pairs remain coupled at each shifted frequency;
the horizontal-reflection coordinate is unchanged. -/
theorem reflected_pair_modulate (δ a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) (z : ℂ) :
    transform a (modulate δ g) z +
      transform a (modulate δ g) ((a : ℂ) - starRingEnd ℂ z) =
      (transform a g z + transform a g ((a : ℂ) - starRingEnd ℂ z)) / 2 +
      (transform a g (z + I * δ) +
        transform a g ((a : ℂ) - starRingEnd ℂ (z + I * δ))) / 4 +
      (transform a g (z - I * δ) +
        transform a g ((a : ℂ) - starRingEnd ℂ (z - I * δ))) / 4 := by
  rw [transform_modulate δ a hg hi, transform_modulate δ a hg hi]
  simp only [map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hp : (a : ℂ) - (starRingEnd ℂ z + -(I * δ)) =
      (a : ℂ) - starRingEnd ℂ z + I * δ := by ring
  have hm : (a : ℂ) - (starRingEnd ℂ z - -(I * δ)) =
      (a : ℂ) - starRingEnd ℂ z - I * δ := by ring
  rw [hp, hm]
  ring

/-- Positivity of every original reflected pair transfers to the whole
modulated pair; no sign is assigned to an individual transform. -/
theorem reflected_pair_nonneg (δ : ℝ) {a : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t)))
    (hpair : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ a →
      0 ≤ (transform a g z + transform a g ((a : ℂ) - starRingEnd ℂ z)).re)
    {z : ℂ} (hz : 0 ≤ z.re) (hza : z.re ≤ a) :
    0 ≤ (transform a (modulate δ g) z +
      transform a (modulate δ g) ((a : ℂ) - starRingEnd ℂ z)).re := by
  rw [reflected_pair_modulate δ a hg hi]
  have hp := hpair (z + I * δ) (by simpa using hz) (by simpa using hza)
  have hm := hpair (z - I * δ) (by simpa using hz) (by simpa using hza)
  have h0 := hpair z hz hza
  simp only [Complex.add_re, Complex.div_ofNat_re] at hp hm h0 ⊢
  linarith

/-- In particular every positive Gaussian width admits the new window
on the entire original reflection strip and at every modulation frequency. -/
theorem gaussian_reflected_pair_nonneg (δ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re) (hza : z.re ≤ a) :
    0 ≤ (transform a (modulate δ (GaussianFermiZeroPair.window b)) z +
      transform a (modulate δ (GaussianFermiZeroPair.window b))
        ((a : ℂ) - starRingEnd ℂ z)).re :=
  reflected_pair_nonneg δ (GaussianFermiZeroPair.continuous_window b)
    (GaussianFermiZeroPair.integrable_window_exp hb)
    (fun _ hz hza ↦ GaussianFermiZeroPair.reflected_pair_re_nonneg ha hb hz hza) hz hza

/-- The one-sided real Laplace integral of the entire retained window. -/
def halfLaplace (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), g t * Real.exp (-x * t)

/-- At a real argument, the original complex Fermi transform is its
genuine real weighted Laplace integral. -/
theorem transform_real_re (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (x : ℝ) (hi : Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) :
    (transform a g (x : ℂ)).re =
      ∫ t in Ioi (0 : ℝ), weight a g t * Real.exp (-x * t) := by
  have hint := (integrable_transform_integrand a hg (z := (x : ℂ)) (by simpa using hi)).integrableOn
    (s := Ioi 0)
  have h : (∫ t in Ioi (0 : ℝ), ((weight a g t : ℂ) * Complex.exp (-(x : ℂ) * (t : ℂ))).re) =
      (∫ t in Ioi (0 : ℝ), (weight a g t : ℂ) * Complex.exp (-(x : ℂ) * (t : ℂ))).re :=
    integral_re hint
  unfold transform
  rw [← h]
  apply integral_congr_ae
  filter_upwards with t
  simp [Complex.mul_re, Complex.exp_re]

/-- Nonnegative time windows give monotone real Fermi transforms;
the modulation is kept inside the integral throughout the comparison. -/
theorem transform_real_antitone (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgn : ∀ t, 0 ≤ g t)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) :
    Antitone (fun x : ℝ ↦ (transform a g (x : ℂ)).re) := by
  intro x y hxy
  dsimp only
  rw [transform_real_re a hg y (hi y), transform_real_re a hg x (hi x)]
  apply integral_mono_ae (integrable_weight_exp a hg (hi y)).integrableOn
    (integrable_weight_exp a hg (hi x)).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have ht0 : 0 < t := ht
    nlinarith
  · exact mul_nonneg (hgn t) (EtaGammaSmoothing.fermi_bounds _).1.le

/-- The exact real partition reconstructs the original window before
any source or pole reserve is estimated. -/
theorem real_partition (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) (x : ℝ) :
    (transform a g (x : ℂ)).re + (transform a g ((a + x : ℝ) : ℂ)).re = halfLaplace g x := by
  rw [transform_real_re a hg x (hi x), transform_real_re a hg (a + x) (hi (a + x))]
  rw [← integral_add (integrable_weight_exp a hg (hi x)).integrableOn
    (integrable_weight_exp a hg (hi (a + x))).integrableOn]
  unfold halfLaplace
  apply integral_congr_ae
  filter_upwards with t
  have he : Real.exp (-(a + x) * t) = Real.exp (-a * t) * Real.exp (-x * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  linear_combination (Real.exp (-x * t)) * (weight_partition a g t)

/-- The full resonant source has its exact signed Fermi reserve beside
the Laplace transform of the retained window. -/
theorem real_pair_eq_halfLaplace_add_reserve (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t))) (x : ℝ) :
    (transform a g (x : ℂ)).re + (transform a g ((a - x : ℝ) : ℂ)).re =
      halfLaplace g x + ((transform a g ((a - x : ℝ) : ℂ)).re -
        (transform a g ((a + x : ℝ) : ℂ)).re) := by
  linarith [real_partition a hg hi x]

/-- For nonnegative resonant displacement, the exact reserve has a
favorable sign for every nonnegative window with all exponential moments. -/
theorem halfLaplace_le_real_pair (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgn : ∀ t, 0 ≤ g t)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t)))
    {x : ℝ} (hx : 0 ≤ x) :
    halfLaplace g x ≤
      (transform a g (x : ℂ)).re + (transform a g ((a - x : ℝ) : ℂ)).re := by
  rw [real_pair_eq_halfLaplace_add_reserve a hg hi]
  have h := transform_real_antitone a hg hgn hi (show a - x ≤ a + x by linarith)
  linarith

/-- At an interior evaluation line, the complete constant-frequency
pole is bounded by the Laplace transform of the same retained window. -/
theorem real_pole_pair_le_halfLaplace {g : ℝ → ℝ} (hg : Continuous g)
    (hgn : ∀ t, 0 ≤ g t)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ ↦ g t * Real.exp (-x * t)))
    {σ : ℝ} (hσ : σ ≤ 1) :
    (transform (2 * σ - 1) g ((σ - 1 : ℝ) : ℂ)).re +
      (transform (2 * σ - 1) g (σ : ℂ)).re ≤ halfLaplace g (σ - 1) := by
  have h := real_partition (2 * σ - 1) hg hi (σ - 1)
  rw [show 2 * σ - 1 + (σ - 1) = 3 * σ - 2 by ring] at h
  have hm := transform_real_antitone (2 * σ - 1) hg hgn hi
    (show 3 * σ - 2 ≤ σ by linarith)
  linarith

end
end RiemannGaussian.FermiCosineModulation
