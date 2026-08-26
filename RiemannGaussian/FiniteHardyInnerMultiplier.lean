import RiemannGaussian.FiniteHardyBoundary

/-!
# The finite residual-inner multiplier on the Hardy boundary

The rational residual inner function has unit modulus at every real boundary
point.  This file upgrades that pointwise fact to a genuine complex-linear
isometry of `L²(ℝ, ℂ)` and records the resulting weighted Gram identity.

This is one analytic half of the proposed two-node metric bridge.  The
orthogonality theorem identifying the relevant shifted Cauchy vectors with
orthogonal-projection residuals is separate and is not assumed here.
-/

open MeasureTheory Polynomial
open scoped ENNReal

namespace RiemannGaussian

noncomputable section

/-- Boundary value of the residual rational inner function associated to a
complex polynomial. -/
def lowerRootInnerBoundaryValue (p : ℂ[X]) (x : ℝ) : ℂ :=
  lowerRootInnerValue p (x : ℂ)

theorem lowerRootInnerBoundaryValue_continuous (p : ℂ[X]) :
    Continuous (lowerRootInnerBoundaryValue p) := by
  change Continuous (fun x : ℝ ↦
    (conjugatePolynomial (lowerRootFactor p)).eval (x : ℂ) /
      (lowerRootFactor p).eval (x : ℂ))
  exact polynomialBoundaryQuotient_continuous
    (lowerRootFactor_eval_real_ne_zero p)

@[simp] theorem norm_lowerRootInnerBoundaryValue
    (p : ℂ[X]) (x : ℝ) :
    ‖lowerRootInnerBoundaryValue p x‖ = 1 := by
  exact norm_lowerRootInnerValue_real p x

/-- Multiplication by the residual inner boundary value preserves every
`MemLp` class. -/
theorem lowerRootInnerBoundaryValue_mul_memLp
    {q : ℝ≥0∞} (p : ℂ[X]) {f : ℝ → ℂ} (hf : MemLp f q) :
    MemLp (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x) q := by
  apply hf.congr_norm
  · exact (lowerRootInnerBoundaryValue_continuous p).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      simp

/-- Multiplication by the residual rational inner boundary value, defined on
actual `L²` equivalence classes. -/
noncomputable def lowerRootInnerBoundaryLpLinearMap (p : ℂ[X]) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) where
  toFun f :=
    (lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp f)).toLp
      (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x)
  map_add' f g := by
    let hf := lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp f)
    let hg := lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp g)
    calc
      (lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp (f + g))).toLp
          (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * (f + g) x) =
          (hf.add hg).toLp
            ((fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x) +
              fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * g x) := by
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [Pi.add_apply]
        rw [hx]
        simp only [Pi.add_apply]
        ring
      _ = hf.toLp
            (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x) +
          hg.toLp
            (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * g x) :=
        MemLp.toLp_add hf hg
  map_smul' c f := by
    let hf := lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp f)
    calc
      (lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp (c • f))).toLp
          (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * (c • f) x) =
          (hf.const_smul c).toLp
            (c • fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x) := by
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [Pi.smul_apply]
        rw [hx]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = c • hf.toLp
          (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x) :=
        MemLp.toLp_const_smul c hf

theorem lowerRootInnerBoundaryLpLinearMap_ae
    (p : ℂ[X]) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    lowerRootInnerBoundaryLpLinearMap p f =ᵐ[volume]
      fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x :=
  MemLp.coeFn_toLp
    (lowerRootInnerBoundaryValue_mul_memLp p (Lp.memLp f))

theorem lowerRootInnerBoundaryLpLinearMap_norm
    (p : ℂ[X]) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lowerRootInnerBoundaryLpLinearMap p f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    eLpNorm (lowerRootInnerBoundaryLpLinearMap p f) 2 volume =
        eLpNorm
          (fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * f x)
          2 volume :=
      eLpNorm_congr_ae (lowerRootInnerBoundaryLpLinearMap_ae p f)
    _ = eLpNorm f 2 volume := by
      apply eLpNorm_congr_norm_ae
      exact Filter.Eventually.of_forall fun x => by
        simp

/-- The finite residual inner function acts isometrically on the genuine
Hardy boundary ambient space. -/
noncomputable def lowerRootInnerBoundaryLpLinearIsometry (p : ℂ[X]) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) where
  toLinearMap := lowerRootInnerBoundaryLpLinearMap p
  norm_map' := lowerRootInnerBoundaryLpLinearMap_norm p

@[simp] theorem lowerRootInnerBoundaryLpLinearIsometry_apply
    (p : ℂ[X]) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    lowerRootInnerBoundaryLpLinearIsometry p f =
      lowerRootInnerBoundaryLpLinearMap p f :=
  rfl

/-- Exact weighted-Gram identity after residual-inner multiplication. -/
theorem lowerRootInnerBoundaryLp_weighted_inner
    (p : ℂ[X]) (s₀ s₁ : ℂ)
    (f₀ f₁ : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ
        (s₀ • lowerRootInnerBoundaryLpLinearIsometry p f₀)
        (s₁ • lowerRootInnerBoundaryLpLinearIsometry p f₁) =
      starRingEnd ℂ s₀ * s₁ * inner ℂ f₀ f₁ := by
  rw [inner_smul_left, inner_smul_right,
    (lowerRootInnerBoundaryLpLinearIsometry p).inner_map_map]
  ring

end

end RiemannGaussian
