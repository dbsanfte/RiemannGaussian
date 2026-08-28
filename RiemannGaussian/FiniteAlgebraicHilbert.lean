import RiemannGaussian.FiniteModelGeometry
import RiemannGaussian.GramWeilMetricPencil
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# A finite algebraic Hilbert realization

This file equips the finite polynomial model with an explicit Euclidean
Hilbert structure.  The common numerator space is transported through its
Sylvester decomposition and given the `L²` product norm.  The first factor is
the residual coordinate and the second is the Blaschke coordinate.

This construction is entirely finite-dimensional and algebraic.  It does not
identify this Euclidean coefficient norm with a Hardy boundary norm; that is
a separate analytic obligation.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- Euclidean coefficients for the residual numerator in the Sylvester
decomposition. -/
abbrev finiteResidualCoefficientHilbert (A : ℝ[X]) (tau : ℝ) :=
  EuclideanSpace ℂ
    (Fin (conjugatePolynomial
      (lowerRootFactor (finiteEPolynomial A tau))).natDegree)

/-- Euclidean coefficients for the Blaschke numerator. -/
abbrev finiteBlaschkeCoefficientHilbert (A : ℝ[X]) (tau : ℝ) :=
  EuclideanSpace ℂ
    (Fin (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau))).natDegree)

/-- The `L²` product Hilbert space carrying residual and Blaschke
coefficients, in that order. -/
abbrev finiteAlgebraicAmbient (A : ℝ[X]) (tau : ℝ) :=
  WithLp 2
    (finiteResidualCoefficientHilbert A tau ×
      finiteBlaschkeCoefficientHilbert A tau)

/-- Coefficients identify every algebraic model space with a Euclidean
space of the same dimension. -/
noncomputable def finiteModelCoefficientLinearEquiv (P : ℂ[X]) :
    finiteModelSpace P ≃ₗ[ℂ] EuclideanSpace ℂ (Fin P.natDegree) :=
  (Polynomial.degreeLTEquiv ℂ P.natDegree).trans
    (WithLp.linearEquiv 2 ℂ (Fin P.natDegree → ℂ)).symm

/-- Transport the common numerator through the exact Sylvester
decomposition, put its residual coordinate first, and equip the pair with
the `L²` product norm. -/
noncomputable def finiteCommonNumeratorAmbientLinearEquiv
    (A : ℝ[X]) (tau : ℝ) :
    finiteCommonNumeratorSpace A tau ≃ₗ[ℂ]
      finiteAlgebraicAmbient A tau :=
  (finiteModelSylvesterLinearEquiv A tau).symm |>.trans
    ((finiteModelCoefficientLinearEquiv
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))).prodCongr
      (finiteModelCoefficientLinearEquiv
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))))) |>.trans
    (LinearEquiv.prodComm ℂ
      (finiteBlaschkeCoefficientHilbert A tau)
      (finiteResidualCoefficientHilbert A tau)) |>.trans
    (WithLp.linearEquiv 2 ℂ
      (finiteResidualCoefficientHilbert A tau ×
        finiteBlaschkeCoefficientHilbert A tau)).symm

@[simp] theorem finiteCommonNumeratorAmbientLinearEquiv_fst
    (A : ℝ[X]) (tau : ℝ) (q : finiteCommonNumeratorSpace A tau) :
    (finiteCommonNumeratorAmbientLinearEquiv A tau q).fst =
      finiteModelCoefficientLinearEquiv
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau)))
        ((finiteModelSylvesterLinearEquiv A tau).symm q).2 := by
  rfl

@[simp] theorem finiteCommonNumeratorAmbientLinearEquiv_snd
    (A : ℝ[X]) (tau : ℝ) (q : finiteCommonNumeratorSpace A tau) :
    (finiteCommonNumeratorAmbientLinearEquiv A tau q).snd =
      finiteModelCoefficientLinearEquiv
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        ((finiteModelSylvesterLinearEquiv A tau).symm q).1 := by
  rfl

/-- Put a Blaschke numerator over the common denominator by multiplying it
by the lower root factor. -/
def finiteNegativeCommonNumeratorLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau →ₗ[ℂ]
      finiteCommonNumeratorSpace A tau where
  toFun q := ⟨(q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau), by
    rw [Polynomial.mem_degreeLT]
    refine (degree_mul_le _ _).trans_lt ?_
    simpa only [Nat.cast_add, conjugatePolynomial_natDegree] using
      WithBot.add_lt_add_of_lt_of_le
        (degree_ne_bot.mpr
          (lowerRootFactor_ne_zero (finiteEPolynomial A tau)))
        (by
          simpa [finiteNegativeModelSpace, finiteModelSpace] using
            (Polynomial.mem_degreeLT.mp q.property))
        (by
          simpa using
            (degree_le_natDegree
              (p := lowerRootFactor (finiteEPolynomial A tau))))
    ⟩
  map_add' q r := by
    apply Subtype.ext
    simp
    ring
  map_smul' c q := by
    apply Subtype.ext
    simp [smul_eq_C_mul]
    ring

@[simp] theorem coe_finiteNegativeCommonNumeratorLinearMap
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    ((finiteNegativeCommonNumeratorLinearMap A tau q :
        finiteCommonNumeratorSpace A tau) : ℂ[X]) =
      (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) :=
  rfl

theorem finiteNegativeCommonNumeratorLinearMap_injective
    (A : ℝ[X]) (tau : ℝ) :
    Function.Injective (finiteNegativeCommonNumeratorLinearMap A tau) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  apply Subtype.ext
  have hpoly :
      (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) = 0 := by
    exact congrArg Subtype.val hq
  exact (mul_eq_zero.mp hpoly).resolve_right
    (lowerRootFactor_ne_zero (finiteEPolynomial A tau))

/-- The Blaschke numerator embedded in the Euclidean common-numerator
ambient. -/
noncomputable def finiteNegativeAmbientLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau →ₗ[ℂ]
      finiteAlgebraicAmbient A tau :=
  (finiteCommonNumeratorAmbientLinearEquiv A tau).toLinearMap.comp
    (finiteNegativeCommonNumeratorLinearMap A tau)

theorem finiteNegativeAmbientLinearMap_injective
    (A : ℝ[X]) (tau : ℝ) :
    Function.Injective (finiteNegativeAmbientLinearMap A tau) :=
  (finiteCommonNumeratorAmbientLinearEquiv A tau).injective.comp
    (finiteNegativeCommonNumeratorLinearMap_injective A tau)

@[simp] theorem finiteNegativeAmbientLinearMap_fst
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    (finiteNegativeAmbientLinearMap A tau q).fst =
      finiteModelCoefficientLinearEquiv
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau)))
        ((finiteModelSylvesterLinearEquiv A tau).symm
          (finiteNegativeCommonNumeratorLinearMap A tau q)).2 := by
  rfl

@[simp] theorem finiteNegativeAmbientLinearMap_snd
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    (finiteNegativeAmbientLinearMap A tau q).snd =
      finiteModelCoefficientLinearEquiv
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        ((finiteModelSylvesterLinearEquiv A tau).symm
          (finiteNegativeCommonNumeratorLinearMap A tau q)).1 := by
  rfl

/-- The negative Hilbert space is the embedded Blaschke numerator space. -/
abbrev finiteAlgebraicNegativeSpace (A : ℝ[X]) (tau : ℝ) :=
  LinearMap.range (finiteNegativeAmbientLinearMap A tau)

/-- First-coordinate projection from the embedded negative space to the
residual Euclidean block. -/
noncomputable def finiteAlgebraicCrossAngle
    (A : ℝ[X]) (tau : ℝ) :
    finiteAlgebraicNegativeSpace A tau →ₗ[ℂ]
      finiteResidualCoefficientHilbert A tau :=
  (WithLp.fstL 2 ℂ
      (finiteResidualCoefficientHilbert A tau)
      (finiteBlaschkeCoefficientHilbert A tau)).toLinearMap.comp
    (finiteAlgebraicNegativeSpace A tau).subtype

@[simp] theorem finiteAlgebraicCrossAngle_apply
    (A : ℝ[X]) (tau : ℝ)
    (x : finiteAlgebraicNegativeSpace A tau) :
    finiteAlgebraicCrossAngle A tau x =
      (x : finiteAlgebraicAmbient A tau).fst :=
  rfl

/-- The Sylvester reconstruction of an embedded Blaschke numerator. -/
theorem finiteNegativeCommonNumerator_decomposition
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)) *
        (((finiteModelSylvesterLinearEquiv A tau).symm
          (finiteNegativeCommonNumeratorLinearMap A tau q)).2 : ℂ[X]) +
      conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau)) *
        (((finiteModelSylvesterLinearEquiv A tau).symm
          (finiteNegativeCommonNumeratorLinearMap A tau q)).1 : ℂ[X]) =
      (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) := by
  calc
    _ = ((finiteModelSylvesterLinearEquiv A tau
          ((finiteModelSylvesterLinearEquiv A tau).symm
            (finiteNegativeCommonNumeratorLinearMap A tau q)) :
          finiteCommonNumeratorSpace A tau) : ℂ[X]) := by
        rw [finiteModelSylvesterLinearEquiv_apply_coe]
    _ = ((finiteNegativeCommonNumeratorLinearMap A tau q :
          finiteCommonNumeratorSpace A tau) : ℂ[X]) := by
        rw [(finiteModelSylvesterLinearEquiv A tau).apply_symm_apply]
    _ = _ := rfl

/-- Under the natural degree inequality, the algebraic cross-angle
projection is injective. -/
theorem finiteAlgebraicCrossAngle_injective
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hdegree :
      (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree ≤
        (lowerRootFactor (finiteEPolynomial A tau)).natDegree) :
    Function.Injective (finiteAlgebraicCrossAngle A tau) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨q, hqx⟩ := x.property
  have hxq : (finiteNegativeAmbientLinearMap A tau q).fst = 0 := by
    rw [hqx]
    exact hx
  let p := (finiteModelSylvesterLinearEquiv A tau).symm
    (finiteNegativeCommonNumeratorLinearMap A tau q)
  have hp2 : p.2 = 0 := by
    apply (finiteModelCoefficientLinearEquiv
      (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau)))).injective
    simpa [p] using hxq
  have hdecomp := finiteNegativeCommonNumerator_decomposition A tau q
  have hcommon :
      (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) =
        (p.1 : ℂ[X]) *
          conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)) := by
    simpa [p, hp2, mul_comm] using hdecomp.symm
  have hzero := finiteNegative_residualMultiple_transverse
    hA htau hdegree q p.1 hcommon
  apply Subtype.ext
  change (x : finiteAlgebraicAmbient A tau) = 0
  rw [← hqx, hzero.1, map_zero]

/-- Every nonzero vector in the embedded negative space has a nonzero second
coefficient block.  Algebraically, this is exactly the trivial intersection
of the two common-denominator model copies. -/
theorem finiteAlgebraicNegativeSpace_snd_ne_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {x : finiteAlgebraicNegativeSpace A tau} (hx : x ≠ 0) :
    (x : finiteAlgebraicAmbient A tau).snd ≠ 0 := by
  intro hsnd
  obtain ⟨q, hqx⟩ := x.property
  have hsndq : (finiteNegativeAmbientLinearMap A tau q).snd = 0 := by
    rw [hqx]
    exact hsnd
  let p := (finiteModelSylvesterLinearEquiv A tau).symm
    (finiteNegativeCommonNumeratorLinearMap A tau q)
  have hp1 : p.1 = 0 := by
    apply (finiteModelCoefficientLinearEquiv
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau)))).injective
    simpa [p] using hsndq
  let qS : finitePositiveModelSpace A tau :=
    ⟨(p.2 : ℂ[X]), by
      simpa [finitePositiveModelSpace, finiteModelSpace] using p.2.property⟩
  have hdecomp := finiteNegativeCommonNumerator_decomposition A tau q
  have hcommon :
      (qS : ℂ[X]) *
          conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) =
        (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) := by
    simpa [p, qS, hp1, mul_comm] using hdecomp
  have hzero := finiteModel_commonDenominator_transverse
    hA htau qS q hcommon
  apply hx
  apply Subtype.ext
  change (x : finiteAlgebraicAmbient A tau) = 0
  rw [← hqx, hzero.2, map_zero]

/-- The Euclidean algebraic cross angle is pointwise strictly contractive.
This follows from the `L²` product norm and the just-proved nonvanishing of
the complementary coordinate. -/
theorem finiteAlgebraicCrossAngle_pointwiseStrictContraction
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    GramWeilPointwiseStrictContraction
      (𝕜 := ℂ)
      (P := finiteResidualCoefficientHilbert A tau)
      (N := finiteAlgebraicNegativeSpace A tau)
      (finiteAlgebraicCrossAngle A tau) := by
  intro x hx
  have hsnd : (x : finiteAlgebraicAmbient A tau).snd ≠ 0 :=
    finiteAlgebraicNegativeSpace_snd_ne_zero hA htau hx
  change ‖(x : finiteAlgebraicAmbient A tau).fst‖ <
    ‖(x : finiteAlgebraicAmbient A tau)‖
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hsnd)]

theorem finiteResidualCoefficientHilbert_finrank
    (A : ℝ[X]) (tau : ℝ) :
    Module.finrank ℂ (finiteResidualCoefficientHilbert A tau) =
      (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau))).natDegree := by
  simp [finiteResidualCoefficientHilbert, EuclideanSpace]

@[simp] theorem finiteAlgebraicNegativeSpace_finrank
    (A : ℝ[X]) (tau : ℝ) :
    Module.finrank ℂ (finiteAlgebraicNegativeSpace A tau) =
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree := by
  rw [LinearMap.finrank_range_of_inj
    (finiteNegativeAmbientLinearMap_injective A tau)]
  exact finiteModelSpace_finrank
    (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau)))

/-- Exact inertia of the algebraically realized finite Gram--Weil defect. -/
theorem finiteAlgebraicGramWeilBlockDefect_hasQuadraticInertia
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hdegree :
      (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree ≤
        (lowerRootFactor (finiteEPolynomial A tau)).natDegree) :
    HasQuadraticInertia
      (gramWeilBlockDefectOperator
        (𝕜 := ℂ)
        (P := finiteResidualCoefficientHilbert A tau)
        (N := finiteAlgebraicNegativeSpace A tau)
        (finiteAlgebraicCrossAngle A tau))
      (gramWeilBlockDefectQuadratic
        (𝕜 := ℂ)
        (P := finiteResidualCoefficientHilbert A tau)
        (N := finiteAlgebraicNegativeSpace A tau)
        (finiteAlgebraicCrossAngle A tau))
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree
      ((conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))).natDegree -
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree)
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree := by
  simpa using gramWeilBlockDefect_hasQuadraticInertia
    (𝕜 := ℂ)
    (P := finiteResidualCoefficientHilbert A tau)
    (N := finiteAlgebraicNegativeSpace A tau)
    (C := finiteAlgebraicCrossAngle A tau)
    (finiteAlgebraicCrossAngle_injective hA htau hdegree)

end

end RiemannGaussian
