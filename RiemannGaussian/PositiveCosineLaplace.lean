/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FermiLaplaceReflection

/-!
# Positive real Laplace transforms from complete cosine data

For every continuous real window with all exponential moments and
nonnegative boundary cosine transform, the original half-line Laplace
transform has nonnegative real part on the closed right half-plane.
The proof exhausts the already checked Fermi reflection strips. Genuine
dominated convergence removes the reflected partner, and the exact
partition recovers the original transform before its real part is taken.
No choice of coefficients or particular Gaussian scale is involved.
-/

namespace RiemannGaussian.PositiveCosineLaplace
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open EtaGammaSmoothing

/-- The original complex half-line Laplace transform, before Fermi smoothing. -/
def laplace (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-z * (t : ℂ))

private theorem norm_shifted_atom_le (g : ℝ → ℝ) (a : ℝ) (z : ℂ) (t : ℝ) :
    ‖(FermiLaplaceReflection.weight a g t : ℂ) *
      Complex.exp (-((a : ℂ) + z) * (t : ℂ))‖ ≤
      |g t| * Real.exp (-(a + z.re) * t) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, FermiLaplaceReflection.weight,
    abs_of_pos (fermi_bounds _).1, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  calc
    _ ≤ |g t| * 1 * Real.exp (-(a + z.re) * t) := by
      gcongr
      exact (fermi_bounds _).2.le
    _ = _ := by ring

/-- The moving reflected transform disappears as the Fermi strip grows,
with genuine complex dominated convergence at every fixed argument. -/
theorem tendsto_shifted_transform_zero {g : ℝ → ℝ} (hg : Continuous g) (z : ℂ)
    (hi : Integrable (fun t : ℝ => g t * Real.exp (-z.re * t))) :
    Tendsto (fun a : ℝ => FermiLaplaceReflection.transform a g ((a : ℂ) + z))
      atTop (𝓝 0) := by
  have hb : IntegrableOn (fun t : ℝ => |g t| * Real.exp (-z.re * t)) (Ioi 0) := by
    simpa only [Real.norm_eq_abs, abs_mul, Real.abs_exp] using hi.norm.integrableOn
  have hm (a : ℝ) : AEStronglyMeasurable (fun t : ℝ =>
      (FermiLaplaceReflection.weight a g t : ℂ) *
        Complex.exp (-((a : ℂ) + z) * (t : ℂ))) (volume.restrict (Ioi (0 : ℝ))) := by
    have hw : Continuous (FermiLaplaceReflection.weight a g) :=
      hg.mul (continuous_fermi.comp (continuous_const.mul continuous_id))
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (FermiLaplaceReflection.weight a g t : ℂ) *
        Complex.exp (-((a : ℂ) + z) * (t : ℂ)))).aestronglyMeasurable
  have hd : ∀ᶠ a : ℝ in atTop, ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ‖(FermiLaplaceReflection.weight a g t : ℂ) *
        Complex.exp (-((a : ℂ) + z) * (t : ℂ))‖ ≤
        |g t| * Real.exp (-z.re * t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply (norm_shifted_atom_le g a z t).trans
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have ht0 : 0 < t := ht
    nlinarith
  have hp : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      Tendsto (fun a : ℝ => (FermiLaplaceReflection.weight a g t : ℂ) *
        Complex.exp (-((a : ℂ) + z) * (t : ℂ))) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have ha : Tendsto (fun a : ℝ => -(a + z.re) * t) atTop atBot := by
      have h := (tendsto_atTop_add_const_right atTop z.re tendsto_id).atTop_mul_const_of_neg
        (neg_lt_zero.mpr ht0)
      simpa only [id_eq, mul_neg, neg_mul] using h
    have he := (Real.tendsto_exp_atBot.comp ha).const_mul |g t|
    simp only [mul_zero] at he
    exact squeeze_zero_norm (norm_shifted_atom_le g · z t) he
  simpa only [FermiLaplaceReflection.transform, integral_zero] using
    tendsto_integral_filter_of_dominated_convergence
      (F := fun a t : ℝ => (FermiLaplaceReflection.weight a g t : ℂ) *
        Complex.exp (-((a : ℂ) + z) * (t : ℂ)))
      (f := fun _ : ℝ => (0 : ℂ)) (fun t : ℝ => |g t| * Real.exp (-z.re * t))
      (Eventually.of_forall hm) hd hb hp

/-- The exact Fermi partition converges back to the complete original
complex transform, so no endpoint normalization is left behind. -/
theorem tendsto_transform {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t))) (z : ℂ) :
    Tendsto (fun a : ℝ => FermiLaplaceReflection.transform a g z) atTop (𝓝 (laplace g z)) := by
  have h := (tendsto_const_nhds (x := laplace g z)).sub
    (tendsto_shifted_transform_zero hg z (hi z.re))
  simp only [sub_zero] at h
  apply h.congr
  intro a
  have he := FermiLaplaceReflection.transform_partition a hg hi z
  change FermiLaplaceReflection.transform a g z +
    FermiLaplaceReflection.transform a g ((a : ℂ) + z) = laplace g z at he
  exact (eq_sub_iff_add_eq.mpr he).symm

/-- The complete analytic reflected pair converges in the complex plane
to the original unpaired transform as its strip becomes the half-plane. -/
theorem tendsto_reflected_pair {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t))) (z : ℂ) :
    Tendsto (fun a : ℝ => FermiLaplaceReflection.transform a g z +
      FermiLaplaceReflection.transform a g ((a : ℂ) - z)) atTop (𝓝 (laplace g z)) := by
  simpa only [sub_eq_add_neg, add_zero] using
    (tendsto_transform hg hi z).add (tendsto_shifted_transform_zero hg (-z) (hi (-z).re))

/-- Nonnegative complete cosine data imply a nonnegative real Laplace
transform throughout the closed right half-plane, for every eligible window. -/
theorem laplace_re_nonneg {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t)))
    (hpos : ∀ z : ℂ, z.re = 0 → 0 ≤ (laplace g z).re)
    {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (laplace g z).re := by
  apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (tendsto_reflected_pair hg hi z))
  filter_upwards [eventually_ge_atTop (max z.re 1)] with a ha
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans ha)
  exact FermiLaplaceReflection.transform_pair_re_nonneg ha0 hg hi hpos hz
    ((le_max_left _ _).trans ha)

end
end RiemannGaussian.PositiveCosineLaplace
