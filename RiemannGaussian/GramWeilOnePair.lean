import RiemannGaussian.GramWeilMetricPencil

/-!
# The scalar one-pair block model

This is the fully algebraic one-dimensional sanity model for the checked
Gram--Weil metric pencil.  For a scalar cross-angle `0 < c < 1`, it proves
that the generalized eigenvalues are exactly

`+sqrt (1 - c^2)` and `-sqrt (1 - c^2)`.

This file does **not** assume or claim the still-unformalized analytic
identity that the polynomial `A(z) = z^2 + a^2` has a particular `L^2` Gram
matrix.  It proves only the scalar block theorem to which that identity would
later connect.
-/

namespace RiemannGaussian

noncomputable section

/-- Multiplication by the real scalar `c`, regarded as the one-dimensional
cross-angle map. -/
def gramWeilScalarCrossAngle (c : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun x := c * x
  map_add' x y := by ring
  map_smul' a x := by
    simp
    ring

@[simp] theorem gramWeilScalarCrossAngle_apply (c x : ℝ) :
    gramWeilScalarCrossAngle c x = c * x := rfl

theorem gramWeilScalarCrossAngle_adjoint (c : ℝ) :
    (gramWeilScalarCrossAngle c).adjoint =
      gramWeilScalarCrossAngle c := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp [gramWeilScalarCrossAngle]
  ring

theorem gramWeilScalarCrossAngle_injective {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (gramWeilScalarCrossAngle c) := by
  intro x y hxy
  apply (mul_left_cancel₀ hc)
  exact hxy

theorem gramWeilScalarCrossAngle_strictContraction
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    GramWeilPointwiseStrictContraction (gramWeilScalarCrossAngle c) := by
  intro x hx
  change |c * x| < |x|
  rw [abs_mul, abs_of_nonneg hc0]
  have hxabs : 0 < |x| := abs_pos.mpr hx
  nlinarith

theorem gramWeilScalar_pencilEigenvalue_sq
    {c lambda : ℝ} {x : ℝ × ℝ}
    (hlambda : lambda ≠ 1) (hx : x ≠ 0)
    (hpencil :
      gramWeilGramOperator (gramWeilScalarCrossAngle c) x =
        lambda • gramWeilSignatureOperator
          (𝕜 := ℝ) (P := ℝ) (N := ℝ) x) :
    lambda ^ 2 = 1 - c ^ 2 := by
  have hright : x.2 ≠ 0 :=
    gramWeil_pencilEquation_right_ne_zero hlambda hx hpencil
  have hmode := gramWeil_pencilEquation_implies_adjoint_comp hpencil
  rw [gramWeilScalarCrossAngle_adjoint] at hmode
  change c * (c * x.2) = (1 - lambda ^ 2) * x.2 at hmode
  have hfactor : c ^ 2 = 1 - lambda ^ 2 := by
    apply mul_right_cancel₀ hright
    simpa [pow_two, mul_assoc] using hmode
  linarith

/-- The exceptional value `lambda = 1` has no nonzero scalar pencil mode
when `c ≠ 0`. -/
theorem gramWeilScalar_no_pencilEigenvector_one
    {c : ℝ} (hc : c ≠ 0) {x : ℝ × ℝ} (hx : x ≠ 0) :
    ¬(gramWeilGramOperator (gramWeilScalarCrossAngle c) x =
      (1 : ℝ) • gramWeilSignatureOperator
        (𝕜 := ℝ) (P := ℝ) (N := ℝ) x) := by
  intro hpencil
  have hpair := gramWeil_pencilEquation_one_iff
    (gramWeilScalarCrossAngle_injective hc) x |>.mp hpencil
  have hleft : x.1 = 0 := by
    have hadjoint : (gramWeilScalarCrossAngle c).adjoint x.1 = 0 := hpair.2
    rw [gramWeilScalarCrossAngle_adjoint] at hadjoint
    exact (mul_eq_zero.mp hadjoint).resolve_left hc
  apply hx
  apply Prod.ext
  · simpa using hleft
  · simpa using hpair.1

/-- A scalar squared-singular-value identity lifts to an explicit pencil
mode. -/
theorem gramWeilScalar_lift_mode
    {c lambda : ℝ} (hlambda : lambda ≠ 1)
    (hsquare : lambda ^ 2 = 1 - c ^ 2) :
    gramWeilGramOperator (gramWeilScalarCrossAngle c)
        (((1 - lambda)⁻¹ * c), 1) =
      lambda • gramWeilSignatureOperator
        (𝕜 := ℝ) (P := ℝ) (N := ℝ)
        (((1 - lambda)⁻¹ * c), 1) := by
  have hmode :
      (gramWeilScalarCrossAngle c).adjoint
          (gramWeilScalarCrossAngle c 1) =
        (1 - lambda ^ 2) • (1 : ℝ) := by
    rw [gramWeilScalarCrossAngle_adjoint]
    change c * (c * 1) = (1 - lambda ^ 2) * 1
    nlinarith
  simpa [gramWeilScalarCrossAngle] using
    (gramWeil_lift_adjointComp_eigenvector
      (gramWeilScalarCrossAngle c) hlambda hmode)

theorem gramWeilScalar_radicand_nonnegative
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ 1 - c ^ 2 := by
  nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1.le)]

theorem gramWeilScalar_sqrt_lt_one
    {c : ℝ} (hc0 : 0 < c) :
    Real.sqrt (1 - c ^ 2) < 1 := by
  rw [Real.sqrt_lt' zero_lt_one]
  nlinarith [sq_pos_of_pos hc0]

/-- Complete scalar spectral classification, expressed only as existence of
nonzero generalized eigenvectors and proved without appealing to a matrix
eigenvalue package. -/
theorem gramWeilScalar_pencilEigenvalue_iff
    {c lambda : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (∃ x : ℝ × ℝ, x ≠ 0 ∧
      gramWeilGramOperator (gramWeilScalarCrossAngle c) x =
        lambda • gramWeilSignatureOperator
          (𝕜 := ℝ) (P := ℝ) (N := ℝ) x) ↔
      lambda = Real.sqrt (1 - c ^ 2) ∨
        lambda = -Real.sqrt (1 - c ^ 2) := by
  let sigma : ℝ := Real.sqrt (1 - c ^ 2)
  have hrad : 0 ≤ 1 - c ^ 2 :=
    gramWeilScalar_radicand_nonnegative hc0.le hc1
  have hsigmaSq : sigma ^ 2 = 1 - c ^ 2 := by
    exact Real.sq_sqrt hrad
  have hsigmaNonneg : 0 ≤ sigma := Real.sqrt_nonneg _
  have hsigmaLt : sigma < 1 := gramWeilScalar_sqrt_lt_one hc0
  constructor
  · rintro ⟨x, hx, hpencil⟩
    have hlambda : lambda ≠ 1 := by
      intro hlambda
      subst lambda
      exact gramWeilScalar_no_pencilEigenvector_one hc0.ne' hx hpencil
    have hlambdaSq :=
      gramWeilScalar_pencilEigenvalue_sq hlambda hx hpencil
    have heqSq : lambda ^ 2 = sigma ^ 2 := by
      rw [hlambdaSq, hsigmaSq]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp heqSq)
  · intro hlambda
    rcases hlambda with rfl | rfl
    · refine ⟨(((1 - sigma)⁻¹ * c), 1), ?_, ?_⟩
      · intro hzero
        have := congrArg Prod.snd hzero
        norm_num at this
      · exact gramWeilScalar_lift_mode (ne_of_lt hsigmaLt) hsigmaSq
    · refine ⟨(((1 - (-sigma))⁻¹ * c), 1), ?_, ?_⟩
      · intro hzero
        have := congrArg Prod.snd hzero
        norm_num at this
      · apply gramWeilScalar_lift_mode
        · nlinarith
        · nlinarith

end

end RiemannGaussian
