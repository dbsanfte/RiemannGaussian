import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vanishing real-line integrals from upper-half-plane analyticity

We isolate the rectangle-contour argument needed for the finite Hardy
orthogonality calculation.  An integrable boundary function that is
holomorphic on the closed upper half-plane and decays quadratically on large
upper semicircles has zero real-line integral.
-/

open Filter MeasureTheory Polynomial Set
open scoped Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A polynomial quotient whose numerator is at least two degrees below its
denominator has a uniform `C / T²` bound in the closed upper half-plane,
provided the denominator has no zero there. -/
theorem polynomialQuotient_upperHalfPlane_quadraticDecay
    {q P : ℂ[X]} (hdegree : q.natDegree + 2 ≤ P.natDegree)
    (hupper : ∀ z : ℂ, 0 ≤ z.im → P.eval z ≠ 0) :
    ∃ C R : ℝ, 0 < C ∧ 0 ≤ R ∧
      ∀ T : ℝ, R ≤ T → 0 < T → ∀ z : ℂ, 0 ≤ z.im →
        T ≤ ‖z‖ → ‖q.eval z / P.eval z‖ ≤ C / T ^ 2 := by
  have hP : P ≠ 0 := by
    intro hzero
    exact hupper 0 (by simp) (by simp [hzero])
  by_cases hq : q = 0
  · refine ⟨1, 0, by norm_num, le_rfl, ?_⟩
    intro T _hT hTpos z _hz _hTz
    simp [hq]
    positivity
  have hXq : X ^ 2 * q ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 X_ne_zero) hq
  have hdegreePoly : (X ^ 2 * q).degree ≤ P.degree := by
    rw [degree_eq_natDegree hXq, degree_eq_natDegree hP]
    exact_mod_cast (by
      rw [natDegree_X_pow_mul 2 hq]
      exact hdegree)
  have hbigO :
      (X ^ 2 * q).eval =O[Bornology.cobounded ℂ] P.eval :=
    Polynomial.isBigO_cobounded_of_degree_le hdegreePoly
  obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp hbigO
  obtain ⟨R, _hRtrivial, hR⟩ :=
    Filter.hasBasis_cobounded_norm.eventually_iff.mp hbound
  refine ⟨C, max R 0, hC, le_max_right _ _, ?_⟩
  intro T hRT hTpos z hz hTz
  have hRz : R ≤ ‖z‖ :=
    le_trans (le_max_left R 0) (hRT.trans hTz)
  have hpolyBound := hR hRz
  have hPz : P.eval z ≠ 0 := hupper z hz
  have hPnorm : 0 < ‖P.eval z‖ := norm_pos_iff.mpr hPz
  have hznorm : 0 < ‖z‖ := hTpos.trans_le hTz
  rw [eval_mul, eval_pow, eval_X, norm_mul, norm_pow] at hpolyBound
  rw [norm_div]
  calc
    ‖q.eval z‖ / ‖P.eval z‖ ≤ C / ‖z‖ ^ 2 := by
      rw [div_le_div_iff₀ hPnorm (sq_pos_of_pos hznorm)]
      simpa [mul_comm] using hpolyBound
    _ ≤ C / T ^ 2 := by
      apply div_le_div_of_nonneg_left hC.le (sq_pos_of_pos hTpos)
      nlinarith [sq_nonneg (‖z‖ - T)]

/-- A rectangle-contour version of the elementary Hardy fact that an
upper-half-plane holomorphic function with `O(1 / |z|²)` decay has zero
integral on the real boundary.  The decay hypothesis is phrased as the exact
uniform estimate used on the three moving sides of the rectangle. -/
theorem integral_realLine_eq_zero_of_upperHalfPlane_decay
    (f : ℂ → ℂ)
    (hdiff : DifferentiableOn ℂ f {z : ℂ | 0 ≤ z.im})
    (hint : Integrable (fun x : ℝ ↦ f (x : ℂ)))
    {C R : ℝ}
    (hdecay : ∀ T : ℝ, R ≤ T → 0 < T →
      ∀ z : ℂ, 0 ≤ z.im → T ≤ ‖z‖ → ‖f z‖ ≤ C / T ^ 2) :
    (∫ x : ℝ, f (x : ℂ)) = 0 := by
  let topEdge : ℝ → ℂ := fun T ↦
    ∫ x : ℝ in -T..T, f ((x : ℂ) + (T : ℂ) * Complex.I)
  let rightEdge : ℝ → ℂ := fun T ↦
    ∫ y : ℝ in 0..T, f ((T : ℂ) + (y : ℂ) * Complex.I)
  let leftEdge : ℝ → ℂ := fun T ↦
    ∫ y : ℝ in 0..T, f ((-T : ℂ) + (y : ℂ) * Complex.I)
  have htop : Tendsto topEdge atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun T => norm_nonneg (topEdge T)
    · filter_upwards [eventually_ge_atTop (max R 1)] with T hT
      have hRT : R ≤ T := le_trans (le_max_left _ _) hT
      have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) <|
        le_trans (le_max_right R 1) hT
      change ‖∫ x : ℝ in -T..T,
        f ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ (2 * C) * T⁻¹
      calc
        ‖∫ x : ℝ in -T..T,
            f ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
            (C / T ^ 2) * |T - (-T)| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x _hx
          have him :
              (((x : ℂ) + (T : ℂ) * Complex.I)).im = T := by simp
          apply hdecay T hRT hTpos
          · rw [him]
            exact hTpos.le
          calc
            T = |(((x : ℂ) + (T : ℂ) * Complex.I)).im| := by
              rw [him, abs_of_pos hTpos]
            _ ≤ ‖(x : ℂ) + (T : ℂ) * Complex.I‖ :=
              Complex.abs_im_le_norm _
        _ = (2 * C) * T⁻¹ := by
          rw [show |T - (-T)| = 2 * T by
            rw [sub_neg_eq_add, abs_of_pos (add_pos hTpos hTpos)]
            ring]
          field_simp [hTpos.ne']
    · simpa using tendsto_inv_atTop_zero.const_mul (2 * C)
  have hright : Tendsto rightEdge atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun T => norm_nonneg (rightEdge T)
    · filter_upwards [eventually_ge_atTop (max R 1)] with T hT
      have hRT : R ≤ T := le_trans (le_max_left _ _) hT
      have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) <|
        le_trans (le_max_right R 1) hT
      change ‖∫ y : ℝ in 0..T,
        f ((T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * T⁻¹
      calc
        ‖∫ y : ℝ in 0..T,
            f ((T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
            (C / T ^ 2) * |T - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro y hy
          rw [uIoc_of_le hTpos.le] at hy
          apply hdecay T hRT hTpos
          · simpa using hy.1.le
          calc
            T = |(((T : ℂ) + (y : ℂ) * Complex.I)).re| := by
              simp [abs_of_pos hTpos]
            _ ≤ ‖(T : ℂ) + (y : ℂ) * Complex.I‖ :=
              Complex.abs_re_le_norm _
        _ = C * T⁻¹ := by
          rw [sub_zero, abs_of_pos hTpos]
          field_simp [hTpos.ne']
    · simpa using tendsto_inv_atTop_zero.const_mul C
  have hleft : Tendsto leftEdge atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun T => norm_nonneg (leftEdge T)
    · filter_upwards [eventually_ge_atTop (max R 1)] with T hT
      have hRT : R ≤ T := le_trans (le_max_left _ _) hT
      have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) <|
        le_trans (le_max_right R 1) hT
      change ‖∫ y : ℝ in 0..T,
        f ((-T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * T⁻¹
      calc
        ‖∫ y : ℝ in 0..T,
            f ((-T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
            (C / T ^ 2) * |T - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro y hy
          rw [uIoc_of_le hTpos.le] at hy
          apply hdecay T hRT hTpos
          · simpa using hy.1.le
          calc
            T = |(((-T : ℂ) + (y : ℂ) * Complex.I)).re| := by
              simp [abs_of_pos hTpos]
            _ ≤ ‖(-T : ℂ) + (y : ℂ) * Complex.I‖ :=
              Complex.abs_re_le_norm _
        _ = C * T⁻¹ := by
          rw [sub_zero, abs_of_pos hTpos]
          field_simp [hTpos.ne']
    · simpa using tendsto_inv_atTop_zero.const_mul C
  have hbottom : Tendsto
      (fun T : ℝ ↦ ∫ x : ℝ in -T..T, f (x : ℂ))
      atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hrect : ∀ T : ℝ, 0 ≤ T →
      (∫ x : ℝ in -T..T, f (x : ℂ)) - topEdge T +
          Complex.I * rightEdge T - Complex.I * leftEdge T = 0 := by
    intro T hT
    have hdRect : DifferentiableOn ℂ f
        (Complex.Rectangle (-T : ℂ)
          ((T : ℂ) + (T : ℂ) * Complex.I)) := by
      apply hdiff.mono
      intro z hz
      change 0 ≤ z.im
      rw [Complex.Rectangle] at hz
      have hzIm : 0 ≤ z.im ∧ z.im ≤ T := by
        simpa [uIcc_of_le hT] using hz.2
      exact hzIm.1
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (-T : ℂ) ((T : ℂ) + (T : ℂ) * Complex.I) hdRect
    simpa [topEdge, rightEdge, leftEdge, smul_eq_mul] using h
  have hboundary : Tendsto
      (fun T : ℝ ↦
        (∫ x : ℝ in -T..T, f (x : ℂ)) - topEdge T +
          Complex.I * rightEdge T - Complex.I * leftEdge T)
      atTop (𝓝 ((∫ x : ℝ, f (x : ℂ)) - 0 +
        Complex.I * 0 - Complex.I * 0)) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hright)).sub
      (tendsto_const_nhds.mul hleft)
  have hzero : Tendsto
      (fun _T : ℝ ↦ (0 : ℂ)) atTop
      (𝓝 ((∫ x : ℝ, f (x : ℂ)) - 0 +
        Complex.I * 0 - Complex.I * 0)) := by
    refine hboundary.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact hrect T hT
  have : (0 : ℂ) = (∫ x : ℝ, f (x : ℂ)) := by
    simpa using tendsto_nhds_unique tendsto_const_nhds hzero
  exact this.symm

/-- A degree-gap-two polynomial quotient with all denominator zeros strictly
below the real axis has vanishing real-line integral.  Integrability is kept
as an explicit hypothesis so applications may obtain it directly from the
two `L²` factors whose inner product is being computed. -/
theorem integral_polynomialQuotient_eq_zero_of_upperHalfPlane
    {q P : ℂ[X]} (hdegree : q.natDegree + 2 ≤ P.natDegree)
    (hupper : ∀ z : ℂ, 0 ≤ z.im → P.eval z ≠ 0)
    (hint : Integrable
      (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ))) :
    (∫ x : ℝ, q.eval (x : ℂ) / P.eval (x : ℂ)) = 0 := by
  obtain ⟨C, R, _hC, _hR, hdecay⟩ :=
    polynomialQuotient_upperHalfPlane_quadraticDecay hdegree hupper
  apply integral_realLine_eq_zero_of_upperHalfPlane_decay
    (f := fun z : ℂ ↦ q.eval z / P.eval z)
    (C := C) (R := R)
  · intro z hz
    exact (q.differentiableAt.div P.differentiableAt
      (hupper z hz)).differentiableWithinAt
  · exact hint
  · exact hdecay

end

end RiemannGaussian
