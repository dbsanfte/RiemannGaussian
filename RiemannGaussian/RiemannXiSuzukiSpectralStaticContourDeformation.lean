import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannGaussian.RiemannXiSuzukiSpectralSignedContourTimeDerivative

/-!
# Static spectral-xi contour deformation to the real boundary

The directly differentiated Suzuki contour gives a static signed contour of
the genuine spectral `-xi'/xi` Cauchy kernel.  This file moves its inner
horizontal lines toward the real spectral axis at fixed finite window.

Admissible inner heights are downward closed, so every finite window has an
explicit positive sequence approaching zero on which the complete signed
contour is exactly constant.  We then separate the inner horizontal pair,
the fixed safe outer pair, and the vertical remainder.  The vertical term is
continuous at height zero because its two lines are zero-free.  Consequently
the *paired* upper/lower horizontal trace has a finite rigorous boundary
limit even when individual horizontal integrals encounter critical-line
poles.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## Downward deformation of admissible heights -/

/-- Once an inner height separates the selected upper poles, every smaller
positive height does as well. -/
theorem SuzukiXiUpperContourBottomAdmissible.mono
    {T eta eta' : ℝ}
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (heta' : 0 < eta') (hle : eta' ≤ eta) :
    SuzukiXiUpperContourBottomAdmissible T eta' := by
  refine ⟨heta', hle.trans_lt heta.2.1, ?_⟩
  intro rho hrho hupper
  exact hle.trans_lt (heta.2.2 rho hrho hupper)

/-- The canonical reciprocal subdivision of an admissible height remains
strictly positive and admissible at every stage. -/
theorem upperContourBottomAdmissible_div_nat_succ
    {T eta : ℝ} (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (n : ℕ) :
    SuzukiXiUpperContourBottomAdmissible T
      (eta / ((n : ℝ) + 1)) := by
  apply heta.mono
  · exact div_pos heta.1 (by positivity)
  · exact div_le_self heta.1.le (by norm_num)

/-- The canonical admissible inner heights converge to the real spectral
axis through positive values. -/
theorem tendsto_upperContourBottom_div_nat_succ_zero
    {T eta : ℝ} (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    Tendsto (fun n : ℕ ↦ eta / ((n : ℝ) + 1)) atTop
      (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
  · simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := eta)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  · exact div_pos heta.1 (by positivity)

/-- At a fixed zero-free spectral cutoff, the complete static signed contour
is independent of the chosen admissible positive inner height. -/
theorem xiSpectralBlaschkeSignedContourWindow_eq_of_admissible
    {z : ℂ} (hz : 1 < z.im)
    {T eta eta' : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (heta' : SuzukiXiUpperContourBottomAdmissible T eta') :
    xiSpectralBlaschkeSignedContourWindow T eta z =
      xiSpectralBlaschkeSignedContourWindow T eta' z := by
  rw [xiSpectralBlaschkeSignedContourWindow_eq_blaschke
      hz hT hboundary heta,
    xiSpectralBlaschkeSignedContourWindow_eq_blaschke
      hz hT hboundary heta']

/-- Along the canonical decreasing inner heights, the whole static contour
converges—indeed is identically equal—to the finite Blaschke detector. -/
theorem tendsto_xiSpectralBlaschkeSignedContourWindow_div_nat_succ
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    Tendsto
      (fun n : ℕ ↦ xiSpectralBlaschkeSignedContourWindow T
        (eta / ((n : ℝ) + 1)) z)
      atTop
      (𝓝 (-(((2 * Real.pi : ℝ) : ℂ)) *
        riemannXiUpperBlaschkeLogDerivativeWindow z T)) := by
  apply tendsto_const_nhds.congr'
  exact Eventually.of_forall fun n ↦
    (xiSpectralBlaschkeSignedContourWindow_eq_blaschke
      hz hT hboundary
        (upperContourBottomAdmissible_div_nat_succ heta n)).symm

/-! ## Horizontal and vertical pieces of the static contour -/

/-- Static Cauchy kernel on the right vertical line. -/
def xiSpectralBlaschkeRightVerticalKernel
    (T : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  xiSpectralBlaschkeContourKernel z
    ((T : ℂ) + (y : ℂ) * Complex.I)

/-- Static Cauchy kernel on the left vertical line. -/
def xiSpectralBlaschkeLeftVerticalKernel
    (T : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  xiSpectralBlaschkeContourKernel z
    (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- Sum of the horizontal traces immediately above and below the real
spectral axis.  Pairing is essential at critical-line poles. -/
def xiSpectralBlaschkeInnerHorizontalPairWindow
    (T eta : ℝ) (z : ℂ) : ℂ :=
  (∫ x : ℝ in (-T)..T, xiSpectralBlaschkeContourKernel z
      ((x : ℂ) + (eta : ℂ) * Complex.I)) +
    ∫ x : ℝ in (-T)..T, xiSpectralBlaschkeContourKernel z
      ((x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I)

/-- Fixed pair of arithmetic safe-line horizontal traces at heights `1`
and `-1`. -/
def xiSpectralBlaschkeOuterHorizontalPairWindow
    (T : ℝ) (z : ℂ) : ℂ :=
  (∫ x : ℝ in (-T)..T, xiSpectralBlaschkeContourKernel z
      ((x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I)) +
    ∫ x : ℝ in (-T)..T, xiSpectralBlaschkeContourKernel z
      ((x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I)

/-- The oriented vertical contribution left after subtracting the reflected
lower rectangle from the upper rectangle. -/
def xiSpectralBlaschkeSignedVerticalRemainderWindow
    (T eta : ℝ) (z : ℂ) : ℂ :=
  Complex.I * (∫ y : ℝ in eta..1,
      xiSpectralBlaschkeRightVerticalKernel T z y) -
    Complex.I * (∫ y : ℝ in eta..1,
      xiSpectralBlaschkeLeftVerticalKernel T z y) -
    Complex.I * (∫ y : ℝ in (-1)..(-eta),
      xiSpectralBlaschkeRightVerticalKernel T z y) +
    Complex.I * (∫ y : ℝ in (-1)..(-eta),
      xiSpectralBlaschkeLeftVerticalKernel T z y)

/-- Exact side decomposition of the complete static signed contour. -/
theorem xiSpectralBlaschkeSignedContourWindow_decomposition
    (T eta : ℝ) (z : ℂ) :
    xiSpectralBlaschkeSignedContourWindow T eta z =
      xiSpectralBlaschkeInnerHorizontalPairWindow T eta z -
        xiSpectralBlaschkeOuterHorizontalPairWindow T z +
          xiSpectralBlaschkeSignedVerticalRemainderWindow T eta z := by
  unfold xiSpectralBlaschkeSignedContourWindow
    xiSpectralBlaschkeInnerHorizontalPairWindow
    xiSpectralBlaschkeOuterHorizontalPairWindow
    xiSpectralBlaschkeSignedVerticalRemainderWindow
    xiSpectralBlaschkeRightVerticalKernel
    xiSpectralBlaschkeLeftVerticalKernel
    rectangularBoundaryIntegral
  ring

/-- For every admissible height, the moving inner horizontal pair plus its
vertical remainder is exactly the finite Blaschke detector plus the fixed
safe outer pair. -/
theorem xiSpectralBlaschkeInnerHorizontalPair_add_vertical_eq
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    xiSpectralBlaschkeInnerHorizontalPairWindow T eta z +
        xiSpectralBlaschkeSignedVerticalRemainderWindow T eta z =
      -(((2 * Real.pi : ℝ) : ℂ)) *
          riemannXiUpperBlaschkeLogDerivativeWindow z T +
        xiSpectralBlaschkeOuterHorizontalPairWindow T z := by
  rw [← xiSpectralBlaschkeSignedContourWindow_eq_blaschke
      hz hT hboundary heta,
    xiSpectralBlaschkeSignedContourWindow_decomposition]
  ring

/-! ## Zero-free vertical integrability -/

/-- The static Cauchy kernel is integrable on the full right vertical segment
of a zero-free spectral cutoff. -/
theorem intervalIntegrable_xiSpectralBlaschkeRightVerticalKernel
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    IntervalIntegrable (xiSpectralBlaschkeRightVerticalKernel T z)
      volume (-1) 1 := by
  have hderiv :=
    intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      0 (-1) 1 z
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I) (by fun_prop) (by
        intro y hy
        rw [uIcc_of_le (by norm_num)] at hy
        constructor
        · intro heq
          have him := congrArg Complex.im heq
          simp at him
          linarith [hy.2]
        · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
          simp [abs_of_nonneg hT])
  have hscaled := hderiv.const_mul Complex.I
  apply hscaled.congr
  intro y _hy
  unfold xiSpectralBlaschkeRightVerticalKernel
  change Complex.I *
      suzukiXiWeilSpectralIntegrandTimeDerivative 0 z
        ((T : ℂ) + (y : ℂ) * Complex.I) = _
  rw [suzukiXiWeilSpectralIntegrandTimeDerivative_zero]
  calc
    Complex.I *
        (-Complex.I * xiSpectralBlaschkeContourKernel z
          ((T : ℂ) + (y : ℂ) * Complex.I)) =
      -(Complex.I ^ 2 * xiSpectralBlaschkeContourKernel z
          ((T : ℂ) + (y : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The static Cauchy kernel is integrable on the full left vertical segment
of the same zero-free spectral cutoff. -/
theorem intervalIntegrable_xiSpectralBlaschkeLeftVerticalKernel
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    IntervalIntegrable (xiSpectralBlaschkeLeftVerticalKernel T z)
      volume (-1) 1 := by
  have hderiv :=
    intervalIntegrable_suzukiXiWeilSpectralIntegrandTimeDerivative_comp
      0 (-1) 1 z
      (fun y : ℝ ↦ (((-T : ℝ) : ℂ)) +
        (y : ℂ) * Complex.I) (by fun_prop) (by
        intro y hy
        rw [uIcc_of_le (by norm_num)] at hy
        constructor
        · intro heq
          have him := congrArg Complex.im heq
          simp at him
          linarith [hy.2]
        · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
          simp [abs_of_nonneg hT])
  have hscaled := hderiv.const_mul Complex.I
  apply hscaled.congr
  intro y _hy
  unfold xiSpectralBlaschkeLeftVerticalKernel
  change Complex.I *
      suzukiXiWeilSpectralIntegrandTimeDerivative 0 z
        (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I) = _
  rw [suzukiXiWeilSpectralIntegrandTimeDerivative_zero]
  calc
    Complex.I *
        (-Complex.I * xiSpectralBlaschkeContourKernel z
          (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      -(Complex.I ^ 2 * xiSpectralBlaschkeContourKernel z
          (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-! ## Continuity of the vertical remainder at the real axis -/

/-- At a zero-free cutoff, the signed vertical remainder is continuous as
the inner height crosses zero. -/
theorem continuousAt_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    ContinuousAt
      (fun eta : ℝ ↦
        xiSpectralBlaschkeSignedVerticalRemainderWindow T eta z) 0 := by
  let R : ℝ → ℂ := xiSpectralBlaschkeRightVerticalKernel T z
  let L : ℝ → ℂ := xiSpectralBlaschkeLeftVerticalKernel T z
  have hRint : IntervalIntegrable R volume (-1) 1 := by
    simpa [R] using
      intervalIntegrable_xiSpectralBlaschkeRightVerticalKernel
        hz hT hboundary
  have hLint : IntervalIntegrable L volume (-1) 1 := by
    simpa [L] using
      intervalIntegrable_xiSpectralBlaschkeLeftVerticalKernel
        hz hT hboundary
  have hRicc : IntegrableOn R (Icc (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hRint
  have hLicc : IntegrableOn L (Icc (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hLint
  have hRucc : IntegrableOn R (uIcc (-1 : ℝ) 1) volume := by
    rw [uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    exact hRicc
  have hLucc : IntegrableOn L (uIcc (-1 : ℝ) 1) volume := by
    rw [uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    exact hLicc
  have hRupper : ContinuousAt (fun eta : ℝ ↦
      ∫ y : ℝ in eta..1, R y) 0 :=
    ((intervalIntegral.continuousOn_primitive_interval_left hRucc)
      0 (show (0 : ℝ) ∈ uIcc (-1) 1 by norm_num)).continuousAt
        (Icc_mem_nhds (by norm_num) (by norm_num))
  have hLupper : ContinuousAt (fun eta : ℝ ↦
      ∫ y : ℝ in eta..1, L y) 0 :=
    ((intervalIntegral.continuousOn_primitive_interval_left hLucc)
      0 (show (0 : ℝ) ∈ uIcc (-1) 1 by norm_num)).continuousAt
        (Icc_mem_nhds (by norm_num) (by norm_num))
  have hRlowerBase : ContinuousAt (fun q : ℝ ↦
      ∫ y : ℝ in (-1)..q, R y) 0 :=
    ((intervalIntegral.continuousOn_primitive_interval hRucc)
      0 (show (0 : ℝ) ∈ uIcc (-1) 1 by norm_num)).continuousAt
        (Icc_mem_nhds (by norm_num) (by norm_num))
  have hLlowerBase : ContinuousAt (fun q : ℝ ↦
      ∫ y : ℝ in (-1)..q, L y) 0 :=
    ((intervalIntegral.continuousOn_primitive_interval hLucc)
      0 (show (0 : ℝ) ∈ uIcc (-1) 1 by norm_num)).continuousAt
        (Icc_mem_nhds (by norm_num) (by norm_num))
  have hneg : ContinuousAt (fun eta : ℝ ↦ -eta) 0 := by fun_prop
  have hRlower : ContinuousAt (fun eta : ℝ ↦
      ∫ y : ℝ in (-1)..(-eta), R y) 0 := by
    simpa only [Function.comp_def, neg_zero] using
      hRlowerBase.comp_of_eq hneg (by simp)
  have hLlower : ContinuousAt (fun eta : ℝ ↦
      ∫ y : ℝ in (-1)..(-eta), L y) 0 := by
    simpa only [Function.comp_def, neg_zero] using
      hLlowerBase.comp_of_eq hneg (by simp)
  have hcombined :=
    (((hRupper.const_mul Complex.I).sub
      (hLupper.const_mul Complex.I)).sub
        (hRlower.const_mul Complex.I)).add
          (hLlower.const_mul Complex.I)
  apply hcombined.congr_of_eventuallyEq
  exact Eventually.of_forall fun eta ↦ by
    simp [xiSpectralBlaschkeSignedVerticalRemainderWindow, R, L]

/-- Any family of inner heights tending to zero carries the signed vertical
remainder to its exact zero-height value. -/
theorem tendsto_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero
    {alpha : Type*} {l : Filter alpha} {eta : alpha → ℝ}
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : Tendsto eta l (𝓝 0)) :
    Tendsto
      (fun a ↦ xiSpectralBlaschkeSignedVerticalRemainderWindow
        T (eta a) z)
      l
      (𝓝 (xiSpectralBlaschkeSignedVerticalRemainderWindow T 0 z)) :=
  (continuousAt_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero
    hz hT hboundary).tendsto.comp heta

/-! ## The paired horizontal boundary value -/

/-- The exact finite value approached by the paired upper/lower horizontal
traces. -/
def xiSpectralBlaschkePairedHorizontalBoundaryValueWindow
    (T : ℝ) (z : ℂ) : ℂ :=
  -(((2 * Real.pi : ℝ) : ℂ)) *
      riemannXiUpperBlaschkeLogDerivativeWindow z T +
    xiSpectralBlaschkeOuterHorizontalPairWindow T z -
      xiSpectralBlaschkeSignedVerticalRemainderWindow T 0 z

/-- Along any admissible family of inner heights tending to zero, the paired
horizontal traces converge to the explicit finite boundary value.  The two
horizontal sides are kept paired, so this remains valid in the presence of
critical-line poles. -/
theorem tendsto_xiSpectralBlaschkeInnerHorizontalPairWindow
    {alpha : Type*} {l : Filter alpha} {eta : alpha → ℝ}
    {z : ℂ} (hz : 1 < z.im)
    {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (hetaAdmissible : ∀ a,
      SuzukiXiUpperContourBottomAdmissible T (eta a))
    (heta : Tendsto eta l (𝓝 0)) :
    Tendsto
      (fun a ↦ xiSpectralBlaschkeInnerHorizontalPairWindow
        T (eta a) z)
      l
      (𝓝 (xiSpectralBlaschkePairedHorizontalBoundaryValueWindow T z)) := by
  have hvertical :=
    tendsto_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero
      hz hT hboundary heta
  have hsub :=
    (tendsto_const_nhds : Tendsto
      (fun _ : alpha ↦
        -(((2 * Real.pi : ℝ) : ℂ)) *
            riemannXiUpperBlaschkeLogDerivativeWindow z T +
          xiSpectralBlaschkeOuterHorizontalPairWindow T z)
      l
      (𝓝 (-(((2 * Real.pi : ℝ) : ℂ)) *
            riemannXiUpperBlaschkeLogDerivativeWindow z T +
          xiSpectralBlaschkeOuterHorizontalPairWindow T z))).sub hvertical
  apply hsub.congr'
  exact Eventually.of_forall fun a ↦ by
    have hidentity :=
      xiSpectralBlaschkeInnerHorizontalPair_add_vertical_eq
        hz hT hboundary (hetaAdmissible a)
    rw [← hidentity]
    ring

/-- In particular, reciprocal subdivisions of any one admissible height give
a canonical paired approach to the real spectral boundary. -/
theorem tendsto_xiSpectralBlaschkeInnerHorizontalPairWindow_div_nat_succ
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    Tendsto
      (fun n : ℕ ↦ xiSpectralBlaschkeInnerHorizontalPairWindow T
        (eta / ((n : ℝ) + 1)) z)
      atTop
      (𝓝 (xiSpectralBlaschkePairedHorizontalBoundaryValueWindow T z)) := by
  apply tendsto_xiSpectralBlaschkeInnerHorizontalPairWindow
    hz hT hboundary
  · exact upperContourBottomAdmissible_div_nat_succ heta
  · exact (tendsto_nhdsWithin_iff.mp
      (tendsto_upperContourBottom_div_nat_succ_zero heta)).1

end

end RiemannGaussian
