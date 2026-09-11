/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaGammaKernel
import RiemannGaussian.SignedLaplaceMoments
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Exact Fermi smoothing and reflected Laplace pairs

The ideal multiplier in Bellotti--Trudgian--Yang, *Zero-free regions inspired
by work of Heath-Brown* (arXiv:2603.21490v1, Section 3), is the eta Fermi
kernel with a rescaled argument. We retain this exact multiplier and the
complex reflected pair. Positivity is asserted only on the closed strip
`0 ≤ re z ≤ a`, with all convergence hypotheses explicit.
-/

namespace RiemannGaussian.FermiLaplaceReflection

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open EtaGammaSmoothing

/-- The exact ideal Fermi multiplier applied to a real window. -/
def weight (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := g t * fermi (-a * t)

/-- The genuine one-sided Laplace integral of the Fermi-weighted window. -/
def transform (a : ℝ) (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (weight a g t : ℂ) * Complex.exp (-z * (t : ℂ))

/-- The ideal multiplier splits the window without approximation. -/
theorem weight_partition (a : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    weight a g t + Real.exp (-a * t) * weight a g t = g t := by
  have he : 1 + Real.exp (-a * t) ≠ 0 := by positivity
  dsimp [weight, fermi]
  field_simp

/-- Even windows obey an exact detailed-balance identity. -/
theorem weight_reflection (a : ℝ) {g : ℝ → ℝ}
    (hg : Function.Even g) (t : ℝ) :
    weight a g (-t) = Real.exp (-a * t) * weight a g t := by
  have he : Real.exp (-a * t) ≠ 0 := Real.exp_ne_zero _
  have hd : 1 + Real.exp (-a * t) ≠ 0 := by positivity
  dsimp only [weight, fermi]
  rw [hg, show -a * -t = -(-a * t) by ring, Real.exp_neg]
  field_simp
  ring

/-- No endpoint value is lost when the ideal multiplier is introduced. -/
theorem weight_zero (a : ℝ) (g : ℝ → ℝ) : weight a g 0 = g 0 / 2 := by
  norm_num [weight, fermi, div_eq_mul_inv]

/-- A window stationary at zero acquires a nonzero first endpoint derivative. -/
theorem hasDerivAt_weight_zero (a : ℝ) {g : ℝ → ℝ}
    (hg : HasDerivAt g 0 0) : HasDerivAt (weight a g) (a * g 0 / 4) 0 := by
  have hf := (hasDerivAt_fermi (-a * 0)).comp (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).const_mul (-a))
  apply (hg.mul hf).congr_deriv
  norm_num [fermiOne, fermi]
  ring

/-- The leading paired endpoint coefficient cancels exactly. -/
theorem paired_endpoint_cancel (a : ℝ) {g : ℝ → ℝ}
    (hg : HasDerivAt g 0 0) :
    2 * deriv (weight a g) 0 - a * weight a g 0 = 0 := by
  rw [(hasDerivAt_weight_zero a hg).deriv, weight_zero]
  ring

/-- Multiplication by the ideal Fermi factor preserves each exponential moment. -/
theorem integrable_weight_exp (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    {x : ℝ} (hi : Integrable (fun t : ℝ => g t * Real.exp (-x * t))) :
    Integrable (fun t : ℝ => weight a g t * Real.exp (-x * t)) := by
  apply hi.norm.mono' (by
    have hf : Continuous (fun t : ℝ => fermi (-a * t)) :=
      continuous_fermi.comp (continuous_const.mul continuous_id)
    unfold weight
    fun_prop)
  filter_upwards with t
  simp only [weight, Real.norm_eq_abs, abs_mul, Real.abs_exp,
    abs_of_pos (fermi_bounds _).1]
  calc
    _ ≤ |g t| * 1 * Real.exp (-x * t) := by
      gcongr
      exact (fermi_bounds _).2.le
    _ = _ := by ring

/-- Complex Laplace integrability is proved for the original weighted signal. -/
theorem integrable_transform_integrand (a : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) {z : ℂ}
    (hi : Integrable (fun t : ℝ => g t * Real.exp (-z.re * t))) :
    Integrable (fun t : ℝ => (weight a g t : ℂ) * Complex.exp (-z * (t : ℂ))) := by
  apply (integrable_weight_exp a hg hi).norm.mono' (by
    have hf : Continuous (fun t : ℝ => fermi (-a * t)) :=
      continuous_fermi.comp (continuous_const.mul continuous_id)
    unfold weight
    fun_prop)
  filter_upwards with t
  simp [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs,
    Complex.mul_re]

/-- All real exponential moments give genuine analytic continuation of this
integral to every complex argument. -/
theorem analyticAt_transform (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t))) (z : ℂ) :
    AnalyticAt ℂ (transform a g) z := by
  have hf : Continuous (weight a g) := by
    exact hg.mul (continuous_fermi.comp (continuous_const.mul continuous_id))
  exact (signed_real_laplace_moments (μ := volume.restrict (Ioi (0 : ℝ)))
    (b := z.re - 1) hf.aemeasurable
    (fun x _ => (integrable_weight_exp a hg (hi x)).integrableOn) (by linarith)).1

/-- The two shifted complex transforms reconstruct the original window,
before taking real parts or norms. -/
theorem transform_partition (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t))) (z : ℂ) :
    transform a g z + transform a g ((a : ℂ) + z) =
      ∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
  unfold transform
  rw [← integral_add (integrable_transform_integrand a hg (hi _)).integrableOn
    (integrable_transform_integrand a hg (hi _)).integrableOn]
  apply integral_congr_ae
  filter_upwards with t
  have he : -((a : ℂ) + z) * (t : ℂ) = ((-a * t : ℝ) : ℂ) + -z * (t : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  have hw := congrArg (fun r : ℝ => (r : ℂ)) (weight_partition a g t)
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at hw
  calc
    _ = ((weight a g t : ℂ) + (Real.exp (-a * t) : ℂ) * (weight a g t : ℂ)) *
        Complex.exp (-z * (t : ℂ)) := by ring
    _ = _ := by rw [hw]

/-- Reality of the original time signal gives exact conjugate symmetry. -/
theorem transform_conj (a : ℝ) (g : ℝ → ℝ) (z : ℂ) :
    transform a g (starRingEnd ℂ z) = starRingEnd ℂ (transform a g z) := by
  unfold transform
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  congr 2
  simp

/-- Coupling the reflected phases turns the half-line transforms into one
bilateral integral, with no artificial endpoint left in the signal. -/
theorem transform_pair_eq_bilateral (a : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) (he : Function.Even g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t))) (z : ℂ) :
    transform a g z + transform a g ((a : ℂ) - z) =
      ∫ t : ℝ, (weight a g t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
  have hint := integrable_transform_integrand a hg (hi z.re)
  rw [← intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hint.integrableOn hint.integrableOn, add_comm]
  congr 1
  have hn : (∫ t in Ioi (0 : ℝ),
      (weight a g (-t) : ℂ) * Complex.exp (-z * ((-t : ℝ) : ℂ))) =
      ∫ t in Iic (0 : ℝ), (weight a g t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
    simpa only [neg_zero] using integral_comp_neg_Ioi (0 : ℝ)
      (fun t : ℝ => (weight a g t : ℂ) * Complex.exp (-z * (t : ℂ)))
  rw [← hn]
  unfold transform
  apply integral_congr_ae
  filter_upwards with t
  rw [weight_reflection a he, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [mul_comm (Real.exp (-a * t) : ℂ), mul_assoc, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- In the right half-plane the ideal transform has a uniform vertical
bound supplied by the original window's absolute integral. -/
theorem norm_transform_le (a : ℝ) {g : ℝ → ℝ} (hi : Integrable g)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ‖transform a g z‖ ≤ ∫ t in Ioi (0 : ℝ), |g t| := by
  apply norm_integral_le_of_norm_le hi.abs.integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, weight,
    abs_of_pos (fermi_bounds _).1, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
  have hexp : Real.exp (-z.re * t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) (show 0 < t from ht).le)
  calc
    _ ≤ |g t| * 1 * 1 := by
      gcongr
      exact (fermi_bounds _).2.le
    _ = _ := by ring

/-- On the left edge, the reflected real part is exactly the original
window's cosine transform. -/
theorem transform_pair_re_boundary (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t)))
    {z : ℂ} (hz : z.re = 0) :
    (transform a g z + transform a g ((a : ℂ) - z)).re =
      (∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-z * (t : ℂ))).re := by
  have he : (a : ℂ) - z = starRingEnd ℂ ((a : ℂ) + z) := by
    apply Complex.ext <;> simp [hz]
  rw [he, transform_conj]
  simpa only [Complex.add_re, Complex.conj_re] using
    congrArg Complex.re (transform_partition a hg hi z)

private theorem re_nonneg_of_strip_boundary {a : ℝ} (ha : 0 < a)
    {H : ℂ → ℂ} (hd : Differentiable ℂ H) {C : ℝ}
    (hb : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ a → ‖H z‖ ≤ C)
    (hleft : ∀ z : ℂ, z.re = 0 → 0 ≤ (H z).re)
    (hright : ∀ z : ℂ, z.re = a → 0 ≤ (H z).re)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a) : 0 ≤ (H z).re := by
  have he := PhragmenLindelof.vertical_strip
    (f := fun w : ℂ => Complex.exp (-H w)) (a := 0) (b := a) (C := 1) (z := z)
    (Complex.differentiable_exp.comp hd.neg).diffContOnCl
  have hgrowth : ∃ c < Real.pi / (a - 0), ∃ B,
      (fun w : ℂ => Complex.exp (-H w)) =O[
        comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo 0 a)]
        fun w => Real.exp (B * Real.exp (c * |w.im|)) := by
    refine ⟨0, by simpa using div_pos Real.pi_pos ha, 0, ?_⟩
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨Real.exp C, ?_⟩
    apply Filter.Eventually.filter_mono inf_le_right
    rw [Filter.eventually_principal]
    intro w hw
    simp only [Complex.norm_exp, Complex.neg_re, zero_mul, Real.exp_zero,
      norm_one, mul_one]
    exact Real.exp_le_exp.mpr ((neg_le_abs (H w).re).trans
      ((Complex.abs_re_le_norm _).trans (hb w hw.1.le hw.2.le)))
  have hbound := he hgrowth (fun w hw => by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (hleft w hw)) (fun w hw => by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (hright w hw)) hz0 hza
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at hbound
  linarith

/-- Every real window with all exponential moments and nonnegative boundary
cosine transform yields a nonnegative ideal reflected pair throughout the
closed strip. This is an all-window statement, with no fitted coefficients. -/
theorem transform_pair_re_nonneg {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t)))
    (hpos : ∀ z : ℂ, z.re = 0 →
      0 ≤ (∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-z * (t : ℂ))).re)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a) :
    0 ≤ (transform a g z + transform a g ((a : ℂ) - z)).re := by
  have hd : Differentiable ℂ (transform a g) :=
    fun w => (analyticAt_transform a hg hi w).differentiableAt
  have hi0 : Integrable g := by simpa using hi 0
  apply re_nonneg_of_strip_boundary ha
    (hd.add (hd.comp (differentiable_const (a : ℂ) |>.sub differentiable_id)))
    (C := 2 * ∫ t in Ioi (0 : ℝ), |g t|) ?_ ?_ ?_ hz0 hza
  · intro w hw0 hwa
    change ‖transform a g w + transform a g ((a : ℂ) - w)‖ ≤ _
    have hwr : 0 ≤ ((a : ℂ) - w).re := by simpa using sub_nonneg.mpr hwa
    exact (norm_add_le _ _).trans (by
      linarith [norm_transform_le a hi0 hw0, norm_transform_le a hi0 hwr])
  · intro w hw
    change 0 ≤ (transform a g w + transform a g ((a : ℂ) - w)).re
    rw [transform_pair_re_boundary a hg hi hw]
    exact hpos w hw
  · intro w hw
    change 0 ≤ (transform a g w + transform a g ((a : ℂ) - w)).re
    have hwr : ((a : ℂ) - w).re = 0 := by simp [hw]
    have hp := hpos ((a : ℂ) - w) hwr
    rw [← transform_pair_re_boundary a hg hi hwr] at hp
    simpa only [sub_sub_cancel, add_comm] using hp

/-- The actual reflected-zero partner retains the same imaginary phase.
Its transform is the conjugate of the analytic reflection used above. -/
theorem transform_reflected_partner (a : ℝ) (g : ℝ → ℝ) (z : ℂ) :
    transform a g ((a : ℂ) - starRingEnd ℂ z) =
      starRingEnd ℂ (transform a g ((a : ℂ) - z)) := by
  rw [← transform_conj]
  congr 1
  simp

/-- Positivity also holds for the same-phase partner appearing in the zeta
explicit formula; the preceding identity records the required conjugation. -/
theorem transform_reflected_pair_re_nonneg {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun t : ℝ => g t * Real.exp (-x * t)))
    (hpos : ∀ z : ℂ, z.re = 0 →
      0 ≤ (∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-z * (t : ℂ))).re)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a) :
    0 ≤ (transform a g z + transform a g ((a : ℂ) - starRingEnd ℂ z)).re := by
  rw [transform_reflected_partner]
  simpa only [Complex.add_re, Complex.conj_re] using
    transform_pair_re_nonneg ha hg hi hpos hz0 hza

end
end RiemannGaussian.FermiLaplaceReflection
