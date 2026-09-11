/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPrimeFormula

/-!
# Exact pole terms in the Fermi explicit formula

The elementary Gaussian pole average evaluates to the original reflected
Fermi pair. Unit mass fixes the constant term exactly. The remaining gamma
term is an explicitly integrable average of the original digamma integral.
Combining these identities gives the full zero formula with a literal
prime series, explicit pole pair, and separated gamma term.
-/

namespace RiemannGaussian.GaussianFermiPoleFormula

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiSpectralWeight
open GaussianFermiGaussianMixture GaussianFermiPrimeFormula GaussianFermiZeroTail

/-- The elementary pole term in the existing Gaussian normalization. -/
def gaussianPole (ε t : ℝ) : ℝ :=
  4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)

/-- The literal reflected Fermi pole pair, before any upper estimate. -/
def polePair (B σ t : ℝ) : ℝ :=
  (transform (2 * σ - 1) (window B) ((σ : ℂ) + (t : ℂ) * I) +
    transform (2 * σ - 1) (window B) (((2 * σ - 1 : ℝ) : ℂ) -
      ((σ : ℂ) + (t : ℂ) * I))).re

/-- The gamma contribution is the actual spectral average of the existing
digamma integral, with its explicit normalization. -/
def digammaAverage (a b c t : ℝ) : ℝ :=
  (Real.sqrt (Real.pi / b) / 8) *
    ∫ y : ℝ, density a c y * gaussianDigammaIntegral (1 / (4 * b)) (t - y)

/-- The elementary pole has a uniform vertical bound. -/
theorem abs_gaussianPole_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    |gaussianPole ε t| ≤ 4 * Real.exp (ε / 4) := by
  unfold gaussianPole
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.exp (ε / 4 - ε * t ^ 2))]
  calc
    _ ≤ 4 * Real.exp (ε / 4 - ε * t ^ 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (by positivity : 0 ≤ 4 * Real.exp (ε / 4 - ε * t ^ 2))
    _ ≤ _ := by
      gcongr
      exact sub_le_self _ (mul_nonneg hε (sq_nonneg t))

/-- The pole average is absolutely integrable at every real center. -/
theorem integrable_density_pole {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hε : 0 ≤ ε) (t : ℝ) :
    Integrable (fun y : ℝ => density a c y * gaussianPole ε (t - y)) := by
  have hd := continuous_density hc a
  apply ((integrable_density ha hc).abs.mul_const (4 * Real.exp (ε / 4))).mono'
    (by unfold gaussianPole; fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_gaussianPole_le hε (t - y)) (abs_nonneg _)

/-- The real part of the complex Gaussian pole atom, including its
oscillatory phase. -/
theorem gaussianAtom_pole_re (b v : ℝ) :
    (gaussianAtom b ((1 / 2 : ℂ) + (v : ℂ) * I)).re =
      (Real.sqrt (Real.pi / b) / 4) * gaussianPole (1 / (4 * b)) v := by
  unfold gaussianAtom gaussianPole
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  have hreal : (((1 / 2 : ℂ) + (v : ℂ) * I) ^ 2).re = 1 / 4 - v ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  have himag : (((1 / 2 : ℂ) + (v : ℂ) * I) ^ 2).im = v := by
    norm_num [pow_two, Complex.mul_im]
    ring
  have hr : (1 / 4 - v ^ 2) / (4 * b) = 1 / (4 * b) / 4 - 1 / (4 * b) * v ^ 2 := by ring
  have hi : v / (4 * b) = 1 / (4 * b) * v := by ring
  rw [hreal, himag, hr, hi]
  ring

private theorem pole_argument (σ t y : ℝ) :
    ((σ : ℂ) + (t : ℂ) * I) - ((2 * σ - 1) / 2 : ℝ) - (y : ℂ) * I =
      (1 / 2 : ℂ) + ((t - y : ℝ) : ℂ) * I := by
  push_cast
  ring

/-- The normalized pole average is exactly the original reflected Fermi
pair. This evaluates the pole rather than bounding it. -/
theorem normalized_pole_average {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (Real.sqrt (Real.pi / b) / 8) *
      (∫ y : ℝ, density (2 * σ - 1) c y * gaussianPole (1 / (4 * b)) (t - y)) =
      polePair (b + c) σ t := by
  have ha : 0 ≤ 2 * σ - 1 := by linarith
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hi := integrable_density_gaussianAtom ha hb hc (z - ((2 * σ - 1) / 2 : ℝ))
  have hre : (∫ y : ℝ, ((density (2 * σ - 1) c y : ℂ) *
      gaussianAtom b (z - ((2 * σ - 1) / 2 : ℝ) - (y : ℂ) * I)).re) =
      (∫ y : ℝ, (density (2 * σ - 1) c y : ℂ) *
        gaussianAtom b (z - ((2 * σ - 1) / 2 : ℝ) - (y : ℂ) * I)).re := integral_re hi
  have hint : (∫ y : ℝ, (density (2 * σ - 1) c y : ℂ) *
      gaussianAtom b (z - ((2 * σ - 1) / 2 : ℝ) - (y : ℂ) * I)).re =
      (Real.sqrt (Real.pi / b) / 4) *
        ∫ y : ℝ, density (2 * σ - 1) c y * gaussianPole (1 / (4 * b)) (t - y) := by
    rw [← hre, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [z]
    rw [pole_argument, Complex.mul_re, gaussianAtom_pole_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have he := congrArg Complex.re (integral_density_gaussianAtom_eq_pair ha hb hc z)
  rw [hint] at he
  have htwo (q : ℂ) : (2 * q).re = 2 * q.re := by simp
  rw [htwo] at he
  change _ = 2 * polePair (b + c) σ t at he
  linarith

/-- The analytic and physical pole displays have exactly the same real
value. Conjugation, rather than a complex equality of the pairs, is used. -/
theorem polePair_eq_physical (B σ t : ℝ) :
    polePair B σ t =
      (transform (2 * σ - 1) (window B) ((σ : ℂ) + (t : ℂ) * I)).re +
      (transform (2 * σ - 1) (window B) (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I)).re := by
  have he : (((2 * σ - 1 : ℝ) : ℂ) - ((σ : ℂ) + (t : ℂ) * I)) =
      starRingEnd ℂ (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I) := by
    push_cast
    simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one]
    ring
  unfold polePair
  rw [he, transform_conj]
  simp

/-- Unit mass and the scale ratio evaluate every constant contribution
with its exact coefficient. -/
theorem normalized_constant_average {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (k : ℝ) :
    (Real.sqrt (Real.pi / b) / 8) *
      (∫ y : ℝ, density a c y * (k / Real.sqrt (Real.pi * (1 / (4 * b))))) = k / 4 := by
  have hr : Real.sqrt (Real.pi * (1 / (4 * b))) ≠ 0 := by positivity
  rw [integral_mul_const, integral_density ha hc, one_mul, sqrt_scale_ratio b]
  field_simp
  ring

/-- The separated digamma average has genuine absolute integrability. -/
theorem integrable_density_digamma {a c ε : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => density a c y * gaussianDigammaIntegral ε (t - y)) := by
  apply (((integrable_density_archimedean ha hc hε t).sub
    (integrable_density_pole ha hc hε.le t)).add
    ((integrable_density ha hc).mul_const (Real.log Real.pi / Real.sqrt (Real.pi * ε)))).congr
  filter_upwards with y
  dsimp only [Pi.add_apply, Pi.sub_apply]
  unfold gaussianArchimedeanContribution gaussianPole
  ring

/-- The actual Archimedean average separates into the exact Fermi poles,
the constant `-log(pi)/4`, and the explicit integrable digamma average. -/
theorem normalized_archimedean_average {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (Real.sqrt (Real.pi / b) / 8) *
      (∫ y : ℝ, density (2 * σ - 1) c y *
        gaussianArchimedeanContribution (1 / (4 * b)) (t - y)) =
      polePair (b + c) σ t - Real.log Real.pi / 4 +
        digammaAverage (2 * σ - 1) b c t := by
  have ha : 0 ≤ 2 * σ - 1 := by linarith
  have hε : 0 < 1 / (4 * b) := by positivity
  have he (v : ℝ) : gaussianArchimedeanContribution (1 / (4 * b)) v =
      gaussianPole (1 / (4 * b)) v -
        Real.log Real.pi / Real.sqrt (Real.pi * (1 / (4 * b))) +
          gaussianDigammaIntegral (1 / (4 * b)) v := rfl
  have hconst : Integrable (fun y : ℝ => density (2 * σ - 1) c y *
      (Real.log Real.pi / Real.sqrt (Real.pi * (1 / (4 * b))))) :=
    (integrable_density ha hc).mul_const _
  have hsub : Integrable (fun y : ℝ =>
      density (2 * σ - 1) c y * gaussianPole (1 / (4 * b)) (t - y) -
      density (2 * σ - 1) c y * (Real.log Real.pi / Real.sqrt (Real.pi * (1 / (4 * b))))) :=
    (integrable_density_pole ha hc hε.le t).sub hconst
  simp_rw [he, mul_add, mul_sub]
  rw [integral_add hsub (integrable_density_digamma ha hc hε t),
    integral_sub (integrable_density_pole ha hc hε.le t) hconst, mul_add, mul_sub,
    normalized_pole_average hb hc hσ, normalized_constant_average ha hb hc]
  rfl

/-- The full actual Fermi zero formula, with every pole, constant,
gamma term and convergent prime-power term explicitly separated. -/
theorem zero_side_eq_poles_digamma_sub_prime {b c σ : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (∑' ρ : NontrivialZetaZero, contribution (b + c) σ t ρ) =
      polePair (b + c) σ t - Real.log Real.pi / 4 + digammaAverage (2 * σ - 1) b c t -
        primeSum (2 * σ - 1) (b + c) t := by
  rw [zero_side_eq_archimedean_sub_prime hb hc hσ, normalized_archimedean_average hb hc hσ]

/-- The gamma average depends only on the total time-Gaussian scale.
Every auxiliary positive split gives the same actual value. -/
theorem digammaAverage_eq_of_add_eq {a b c d e : ℝ} (ha : 0 ≤ a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hscale : b + c = d + e) (t : ℝ) :
    digammaAverage a b c t = digammaAverage a d e t := by
  have hσ : 1 / 2 ≤ (a + 1) / 2 := by linarith
  have hpar : 2 * ((a + 1) / 2) - 1 = a := by ring
  have hfirst := zero_side_eq_poles_digamma_sub_prime hb hc hσ t
  have hsecond := zero_side_eq_poles_digamma_sub_prime hd he hσ t
  rw [hpar, hscale] at hfirst
  rw [hpar] at hsecond
  linarith

/-- The known zero-free width gives a uniform literal-prime upper budget
with explicit poles, gamma average and the vanishing height allowance. -/
theorem exists_uniform_prime_pole_digamma_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (H b c t : ℝ), 1 ≤ H → 0 < b → 0 < c →
      zetaPoleReserveZeroMargin H ^ 2 ≤ b + c → b + c ≤ 1 → 2 * |t| ≤ H →
      primeSum (2 * (1 - zetaPoleReserveZeroMargin H) - 1) (b + c) t ≤
        polePair (b + c) (1 - zetaPoleReserveZeroMargin H) t - Real.log Real.pi / 4 +
          digammaAverage (2 * (1 - zetaPoleReserveZeroMargin H) - 1) b c t +
          K * (Real.log (H + 2) / Real.sqrt H) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_prime_archimedean_bound
  refine ⟨K, hK, ?_⟩
  intro H b c t hH hb hc hscale hsum ht
  have hσ : 1 / 2 ≤ 1 - zetaPoleReserveZeroMargin H := by
    linarith [(zetaPoleReserveZeroMargin_bounds H).2]
  have h := hbound H b c t hH hb hc hscale hsum ht
  rwa [normalized_archimedean_average hb hc hσ] at h

end
end RiemannGaussian.GaussianFermiPoleFormula
