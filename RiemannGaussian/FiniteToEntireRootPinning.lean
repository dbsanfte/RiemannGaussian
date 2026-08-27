import RiemannGaussian.FiniteToEntireHomotopy

/-!
# Exact root pinning for finite real-polynomial approximants

Suppose real polynomials converge locally uniformly to an entire function
`f`, and `z` is a zero of `f + i * eta * f'`.  This file constructs an
explicit real affine correction to every polynomial.  When
`z.im + eta ≠ 0`, the corrected finite homotopy has the *same exact root*
`z`.  The correction tends to zero, so the corrected polynomials still
converge locally uniformly to `f`.

This avoids a root-selection or Hurwitz argument at this stage.  It does not
prove that the corrected polynomials are separable; that remains a distinct
finite-model obligation.
-/

open Filter Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- Slope of the real affine correction which cancels the imaginary part of
the finite homotopy residual at `z`. -/
def finiteERootPinSlope (A : ℝ[X]) (eta : ℝ) (z : ℂ) : ℝ :=
  -((finiteEPolynomial A eta).eval z).im / (z.im + eta)

/-- Intercept of the real affine correction after its slope has cancelled
the imaginary part of the residual. -/
def finiteERootPinIntercept (A : ℝ[X]) (eta : ℝ) (z : ℂ) : ℝ :=
  -((finiteEPolynomial A eta).eval z).re -
    finiteERootPinSlope A eta z * z.re

/-- A real polynomial obtained by adding the root-pinning affine correction
to `A`. -/
def finiteERootPinnedPolynomial (A : ℝ[X]) (eta : ℝ) (z : ℂ) : ℝ[X] :=
  A + C (finiteERootPinIntercept A eta z) +
    C (finiteERootPinSlope A eta z) * X

/-- Evaluation of the pinned polynomial is evaluation of `A` plus its
explicit affine correction. -/
@[simp] theorem finiteERootPinnedPolynomial_map_eval
    (A : ℝ[X]) (eta : ℝ) (z w : ℂ) :
    ((finiteERootPinnedPolynomial A eta z).map Complex.ofRealHom).eval w =
      (A.map Complex.ofRealHom).eval w +
        (finiteERootPinIntercept A eta z : ℂ) +
          (finiteERootPinSlope A eta z : ℂ) * w := by
  simp [finiteERootPinnedPolynomial]

/-- If `z.im + eta` is nonzero, the pinned finite homotopy vanishes exactly
at `z`. -/
theorem finiteERootPinnedPolynomial_isRoot
    (A : ℝ[X]) (eta : ℝ) {z : ℂ} (hz : z.im + eta ≠ 0) :
    (finiteEPolynomial (finiteERootPinnedPolynomial A eta z) eta).eval z = 0 := by
  let r : ℂ := (finiteEPolynomial A eta).eval z
  let d : ℝ := finiteERootPinSlope A eta z
  let c : ℝ := finiteERootPinIntercept A eta z
  have hd : d = -r.im / (z.im + eta) := by
    simp [d, r, finiteERootPinSlope]
  have hc : c = -r.re - d * z.re := by
    simp [c, d, r, finiteERootPinIntercept]
  have hform :
      (finiteEPolynomial (finiteERootPinnedPolynomial A eta z) eta).eval z =
        r + (c : ℂ) + (d : ℂ) * z +
          Complex.I * (eta : ℂ) * (d : ℂ) := by
    rw [finiteEPolynomial_eval]
    dsimp only [r]
    rw [finiteEPolynomial_eval]
    simp [finiteERootPinnedPolynomial, c, d]
    ring
  rw [hform]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, sub_zero,
      mul_zero, add_zero, Complex.zero_re]
    rw [hc]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, one_mul, add_zero, zero_add, Complex.zero_im]
    rw [hd]
    field_simp
    ring

/-- Along a locally uniform approximation to a limiting homotopy root, the
root-pinning slopes tend to zero. -/
theorem finiteERootPinSlope_tendsto_zero
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) {f : ℂ → ℂ}
    (eta : ℝ) {z : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f φ Set.univ)
    (hroot : analyticEValue f eta z = 0) :
    Tendsto (fun n ↦ finiteERootPinSlope (A n) eta z) φ (nhds 0) := by
  have hE := analyticEValue_tendstoLocallyUniformlyOn hA
    (Eventually.of_forall fun n ↦ ((A n).map Complex.ofRealHom).differentiableOn)
    isOpen_univ eta
  have hres :
      Tendsto (fun n ↦ (finiteEPolynomial (A n) eta).eval z) φ (nhds 0) := by
    simpa only [analyticEValue_realPolynomial, hroot] using
      hE.tendsto_at (mem_univ z)
  simpa [finiteERootPinSlope] using
    (((Complex.continuous_im.tendsto 0).comp hres).neg.div_const
      (z.im + eta))

/-- Along a locally uniform approximation to a limiting homotopy root, the
root-pinning intercepts tend to zero. -/
theorem finiteERootPinIntercept_tendsto_zero
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) {f : ℂ → ℂ}
    (eta : ℝ) {z : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f φ Set.univ)
    (hroot : analyticEValue f eta z = 0) :
    Tendsto (fun n ↦ finiteERootPinIntercept (A n) eta z) φ (nhds 0) := by
  have hE := analyticEValue_tendstoLocallyUniformlyOn hA
    (Eventually.of_forall fun n ↦ ((A n).map Complex.ofRealHom).differentiableOn)
    isOpen_univ eta
  have hres :
      Tendsto (fun n ↦ (finiteEPolynomial (A n) eta).eval z) φ (nhds 0) := by
    simpa only [analyticEValue_realPolynomial, hroot] using
      hE.tendsto_at (mem_univ z)
  have hslope := finiteERootPinSlope_tendsto_zero A eta hA hroot
  have hre := (Complex.continuous_re.tendsto 0).comp hres
  simpa [finiteERootPinIntercept] using
    hre.neg.sub (hslope.mul (tendsto_const_nhds :
      Tendsto (fun _ : ι ↦ z.re) φ (nhds z.re)))

/-- A sequence which is constant in its index converges locally uniformly to
that same function. -/
theorem tendstoLocallyUniformlyOn_const_index
    {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {φ : Filter ι} {s : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ι ↦ g) g φ s := by
  intro u hu x hx
  exact ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ ↦
    refl_mem_uniformity hu⟩

/-- The pinned real polynomials retain the locally uniform limit because
both correction coefficients tend to zero. -/
theorem finiteERootPinnedPolynomial_tendstoLocallyUniformlyOn
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) {f : ℂ → ℂ}
    (eta : ℝ) {z : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f φ Set.univ)
    (hroot : analyticEValue f eta z = 0) :
    TendstoLocallyUniformlyOn
      (fun n w ↦
        ((finiteERootPinnedPolynomial (A n) eta z).map
          Complex.ofRealHom).eval w)
      f φ Set.univ := by
  have hslope := (finiteERootPinSlope_tendsto_zero A eta hA hroot).ofReal
  have hintercept := (finiteERootPinIntercept_tendsto_zero A eta hA hroot).ofReal
  have hslopeConst :=
    (hslope.tendstoUniformlyOn_const (Set.univ : Set ℂ)).tendstoLocallyUniformlyOn
  have hinterceptConst :=
    (hintercept.tendstoUniformlyOn_const (Set.univ : Set ℂ)).tendstoLocallyUniformlyOn
  have hid : TendstoLocallyUniformlyOn
      (fun _ : ι ↦ id) id φ (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_const_index id
  have hlinear := hslopeConst.mul₀ hid continuousOn_const continuous_id.continuousOn
  have hcorrection := hinterceptConst.add hlinear
  refine ((hA.add hcorrection).congr
    (G := fun n w ↦
      ((finiteERootPinnedPolynomial (A n) eta z).map
        Complex.ofRealHom).eval w) ?_).congr_right ?_
  · intro n w _
    simp [add_assoc]
  · intro w _
    simp

/-- Complete generic pinning specification: the corrected real polynomials
retain the same locally uniform limit and every corrected finite homotopy has
the prescribed exact root. -/
theorem finiteERootPinnedPolynomial_spec
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) {f : ℂ → ℂ}
    (eta : ℝ) {z : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f φ Set.univ)
    (hroot : analyticEValue f eta z = 0) (hz : z.im + eta ≠ 0) :
    TendstoLocallyUniformlyOn
        (fun n w ↦
          ((finiteERootPinnedPolynomial (A n) eta z).map
            Complex.ofRealHom).eval w)
        f φ Set.univ ∧
      ∀ n, (finiteEPolynomial
        (finiteERootPinnedPolynomial (A n) eta z) eta).eval z = 0 := by
  exact ⟨finiteERootPinnedPolynomial_tendstoLocallyUniformlyOn
    A eta hA hroot, fun n ↦ finiteERootPinnedPolynomial_isRoot (A n) eta hz⟩

/-- The root-pinning specification specialized to the spectral xi function.
The only approximation premise is displayed explicitly. -/
theorem riemannXiSpectral_pinnedPolynomial_spec
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) (eta : ℝ) {z : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral φ Set.univ)
    (hroot : analyticEValue riemannXiSpectral eta z = 0)
    (hz : z.im + eta ≠ 0) :
    TendstoLocallyUniformlyOn
        (fun n w ↦
          ((finiteERootPinnedPolynomial (A n) eta z).map
            Complex.ofRealHom).eval w)
        riemannXiSpectral φ Set.univ ∧
      ∀ n, (finiteEPolynomial
        (finiteERootPinnedPolynomial (A n) eta z) eta).eval z = 0 :=
  finiteERootPinnedPolynomial_spec A eta hA hroot hz

end

end RiemannGaussian
