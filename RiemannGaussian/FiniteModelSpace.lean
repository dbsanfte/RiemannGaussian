import RiemannGaussian.FiniteZeroVectorSplit
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Algebraic finite model-space coordinates

For a rational inner representative `Q / P`, its finite algebraic model is
the space of numerators of degree strictly less than `P.natDegree`, evaluated
after division by `P`.  This file proves, without an appeal to Hardy-space
theory, that every difference quotient

`((Q / P)(z) - (Q / P)(gamma)) / (z - gamma)`

has a canonical coordinate in that finite-dimensional space when `Q` and
`P` have equal degree.  It then applies the construction to the two rational
inner factors `B` and `S` in the finite Krein--Langer decomposition.

This is deliberately an algebraic model.  Identifying its inner product with
the analytic half-plane model-space norm is a separate obligation.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- The numerator-coordinate space associated with denominator `P`. -/
def finiteModelSpace (P : ℂ[X]) : Submodule ℂ ℂ[X] :=
  Polynomial.degreeLT ℂ P.natDegree

instance finiteModelSpace_moduleFinite (P : ℂ[X]) :
    Module.Finite ℂ (finiteModelSpace P) := by
  change Module.Finite ℂ (Polynomial.degreeLT ℂ P.natDegree)
  infer_instance

/-- Evaluation of a finite model coordinate as the rational function `q / P`. -/
def finiteModelValue (P : ℂ[X]) (q : finiteModelSpace P) (z : ℂ) : ℂ :=
  (q : ℂ[X]).eval z / P.eval z

/-- The numerator which appears after clearing denominators in the difference
quotient for `Q / P` at `gamma`. -/
def finiteInnerDifferenceNumerator
    (Q P : ℂ[X]) (gamma : ℂ) : ℂ[X] :=
  C (P.eval gamma) * Q - C (Q.eval gamma) * P

/-- Divide the cleared difference numerator by its forced linear factor. -/
def finiteInnerDifferencePolynomial
    (Q P : ℂ[X]) (gamma : ℂ) : ℂ[X] :=
  finiteInnerDifferenceNumerator Q P gamma / (X - C gamma)

/-- The cleared difference numerator vanishes at the base point. -/
theorem finiteInnerDifferenceNumerator_eval_self
    (Q P : ℂ[X]) (gamma : ℂ) :
    (finiteInnerDifferenceNumerator Q P gamma).eval gamma = 0 := by
  simp [finiteInnerDifferenceNumerator]
  ring

/-- Polynomial reconstruction after removal of the forced linear factor. -/
theorem X_sub_C_mul_finiteInnerDifferencePolynomial
    (Q P : ℂ[X]) (gamma : ℂ) :
    (X - C gamma) * finiteInnerDifferencePolynomial Q P gamma =
      finiteInnerDifferenceNumerator Q P gamma := by
  apply Polynomial.IsRoot.mul_div_eq
  rw [Polynomial.IsRoot]
  exact finiteInnerDifferenceNumerator_eval_self Q P gamma

/-- Evaluation of the reconstruction identity. -/
theorem sub_mul_finiteInnerDifferencePolynomial_eval
    (Q P : ℂ[X]) (gamma z : ℂ) :
    (z - gamma) * (finiteInnerDifferencePolynomial Q P gamma).eval z =
      P.eval gamma * Q.eval z - Q.eval gamma * P.eval z := by
  have h := congrArg (Polynomial.eval z)
    (X_sub_C_mul_finiteInnerDifferencePolynomial Q P gamma)
  simpa [finiteInnerDifferenceNumerator] using h

/-- Equal numerator and denominator degrees force the divided-difference
numerator to have degree strictly below the denominator degree. -/
theorem finiteInnerDifferencePolynomial_mem_degreeLT
    {Q P : ℂ[X]} (gamma : ℂ)
    (hdegree : Q.natDegree = P.natDegree) :
    finiteInnerDifferencePolynomial Q P gamma ∈
      Polynomial.degreeLT ℂ P.natDegree := by
  rw [Polynomial.mem_degreeLT]
  let N := finiteInnerDifferenceNumerator Q P gamma
  have hNdegree : N.natDegree ≤ P.natDegree := by
    calc
      N.natDegree ≤
          max (C (P.eval gamma) * Q).natDegree
            (C (Q.eval gamma) * P).natDegree := by
        exact natDegree_sub_le _ _
      _ ≤ P.natDegree := by
        apply max_le
        · exact (natDegree_C_mul_le _ Q).trans_eq hdegree
        · exact natDegree_C_mul_le _ P
  by_cases hN : N = 0
  · simp [finiteInnerDifferencePolynomial, N, hN]
  · calc
      degree (finiteInnerDifferencePolynomial Q P gamma) =
          degree (N / (X - C gamma)) := rfl
      _ < degree N :=
        degree_div_lt hN (by simp [degree_X_sub_C])
      _ ≤ (P.natDegree : WithBot ℕ) :=
        (degree_le_natDegree (p := N)).trans
          (WithBot.coe_le_coe.mpr hNdegree)

/-- The canonical finite-model coordinate of the difference quotient. -/
def finiteInnerDifferenceCoordinate
    (Q P : ℂ[X]) (gamma : ℂ)
    (hdegree : Q.natDegree = P.natDegree) : finiteModelSpace P :=
  (P.eval gamma)⁻¹ •
    ⟨finiteInnerDifferencePolynomial Q P gamma,
      finiteInnerDifferencePolynomial_mem_degreeLT gamma hdegree⟩

@[simp] theorem coe_finiteInnerDifferenceCoordinate
    (Q P : ℂ[X]) (gamma : ℂ)
    (hdegree : Q.natDegree = P.natDegree) :
    ((finiteInnerDifferenceCoordinate Q P gamma hdegree :
        finiteModelSpace P) : ℂ[X]) =
      C (P.eval gamma)⁻¹ *
        finiteInnerDifferencePolynomial Q P gamma := by
  simp [finiteInnerDifferenceCoordinate, smul_eq_C_mul]

/-- Clearing the variable denominator of the canonical coordinate gives the
normalized numerator `Q - (Q(gamma) / P(gamma)) P`. -/
theorem X_sub_C_mul_coe_finiteInnerDifferenceCoordinate
    {Q P : ℂ[X]} (gamma : ℂ)
    (hdegree : Q.natDegree = P.natDegree)
    (hPgamma : P.eval gamma ≠ 0) :
    (X - C gamma) *
        ((finiteInnerDifferenceCoordinate Q P gamma hdegree :
          finiteModelSpace P) : ℂ[X]) =
      Q - C (Q.eval gamma / P.eval gamma) * P := by
  rw [coe_finiteInnerDifferenceCoordinate]
  calc
    (X - C gamma) *
        (C (P.eval gamma)⁻¹ *
          finiteInnerDifferencePolynomial Q P gamma) =
        C (P.eval gamma)⁻¹ *
          ((X - C gamma) *
            finiteInnerDifferencePolynomial Q P gamma) := by ring
    _ = C (P.eval gamma)⁻¹ *
        (C (P.eval gamma) * Q - C (Q.eval gamma) * P) := by
      rw [X_sub_C_mul_finiteInnerDifferencePolynomial]
      rfl
    _ = Q - C (Q.eval gamma / P.eval gamma) * P := by
      simp only [mul_sub, ← mul_assoc, ← C_mul]
      rw [inv_mul_cancel₀ hPgamma, C_1, one_mul]
      congr 1
      simp [div_eq_mul_inv, mul_comm]

/-- Evaluation is compatible with scalar multiplication of numerator
coordinates. -/
theorem finiteModelValue_smul
    (P : ℂ[X]) (c : ℂ) (q : finiteModelSpace P) (z : ℂ) :
    finiteModelValue P (c • q) z = c * finiteModelValue P q z := by
  simp [finiteModelValue]
  ring

/-- The coordinate evaluates to the literal rational difference quotient
where all three displayed denominators are nonzero. -/
theorem finiteModelValue_innerDifferenceCoordinate
    {Q P : ℂ[X]} {gamma z : ℂ}
    (hdegree : Q.natDegree = P.natDegree)
    (hPgamma : P.eval gamma ≠ 0) (hPz : P.eval z ≠ 0)
    (hzgamma : z ≠ gamma) :
    finiteModelValue P
        (finiteInnerDifferenceCoordinate Q P gamma hdegree) z =
      ((Q.eval z / P.eval z) - (Q.eval gamma / P.eval gamma)) /
        (z - gamma) := by
  rw [finiteInnerDifferenceCoordinate, finiteModelValue_smul,
    finiteModelValue]
  change (P.eval gamma)⁻¹ *
      ((finiteInnerDifferencePolynomial Q P gamma).eval z / P.eval z) = _
  have hrec := sub_mul_finiteInnerDifferencePolynomial_eval Q P gamma z
  field_simp [hPgamma, hPz, sub_ne_zero.mpr hzgamma]
  linear_combination hrec

/-- The algebraic finite model has exactly the denominator degree as its
complex dimension. -/
@[simp] theorem finiteModelSpace_finrank (P : ℂ[X]) :
    Module.finrank ℂ (finiteModelSpace P) = P.natDegree := by
  change Module.finrank ℂ (Polynomial.degreeLT ℂ P.natDegree) =
    P.natDegree
  simpa using
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ P.natDegree)

/-- The lower root factor cannot vanish at a zero of `A`: otherwise the exact
root factorization would make `E_tau` vanish there as well. -/
theorem lowerRootFactor_eval_ne_zero_at_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (lowerRootFactor (finiteEPolynomial A tau)).eval gamma ≠ 0 := by
  intro hzero
  apply finiteE_eval_ne_zero_at_root hA htau hgamma
  rw [finiteEPolynomial_eq_rootFactors hA htau]
  simp [hzero]

/-- Polynomial, rather than merely pointwise, form of `E_tau +
E_tau^sharp = 2 A`. -/
theorem finiteEPolynomial_add_finiteESharpPolynomial
    (A : ℝ[X]) (tau : ℝ) :
    finiteEPolynomial A tau + finiteESharpPolynomial A tau =
      C (2 : ℂ) * A.map Complex.ofRealHom := by
  simp only [finiteEPolynomial, finiteESharpPolynomial, smul_eq_C_mul,
    Polynomial.C_ofNat]
  ring

/-- Algebraic coordinate of the `B` difference quotient. -/
def finiteBlaschkeDifferenceCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    finiteModelSpace
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))) :=
  finiteInnerDifferenceCoordinate
    (upperRootFactor (finiteEPolynomial A tau))
    (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau))) gamma (by simp)

/-- Algebraic coordinate of the residual-inner `S` difference quotient. -/
def finiteResidualDifferenceCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    finiteModelSpace (lowerRootFactor (finiteEPolynomial A tau)) :=
  finiteInnerDifferenceCoordinate
    (conjugatePolynomial
      (lowerRootFactor (finiteEPolynomial A tau)))
    (lowerRootFactor (finiteEPolynomial A tau)) gamma (by simp)

/-- Evaluation of the `B` coordinate at an upper-half-plane point. -/
theorem finiteModelValue_blaschkeDifferenceCoordinate
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hzgamma : z ≠ gamma) :
    finiteModelValue
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        (finiteBlaschkeDifferenceCoordinate A tau gamma) z =
      (finiteBlaschkeValue A tau z -
          finiteBlaschkeValue A tau gamma) / (z - gamma) := by
  simpa [finiteBlaschkeDifferenceCoordinate, finiteBlaschkeValue,
    upperRootBlaschkeValue] using
    finiteModelValue_innerDifferenceCoordinate
      (Q := upperRootFactor (finiteEPolynomial A tau))
      (P := conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau)))
      (gamma := gamma) (z := z) (by simp)
      (conjugate_upperRootFactor_eval_ne_zero_at_root hA htau hgamma)
      (conjugate_upperRootFactor_eval_ne_zero_of_im_pos
        (finiteEPolynomial A tau) hz) hzgamma

/-- Evaluation of the residual-inner `S` coordinate at an upper-half-plane
point. -/
theorem finiteModelValue_residualDifferenceCoordinate
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hzgamma : z ≠ gamma) :
    finiteModelValue (lowerRootFactor (finiteEPolynomial A tau))
        (finiteResidualDifferenceCoordinate A tau gamma) z =
      (finiteInnerValue A tau z - finiteInnerValue A tau gamma) /
        (z - gamma) := by
  simpa [finiteResidualDifferenceCoordinate, finiteInnerValue,
    lowerRootInnerValue] using
    finiteModelValue_innerDifferenceCoordinate
      (Q := conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau)))
      (P := lowerRootFactor (finiteEPolynomial A tau))
      (gamma := gamma) (z := z) (by simp)
      (lowerRootFactor_eval_ne_zero_at_root hA htau hgamma)
      (lowerRootFactor_eval_ne_zero_of_im_pos
        (finiteEPolynomial A tau) hz) hzgamma

/-- The actual positive split coordinate, including its normalization. -/
def finitePositiveSplitCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    finiteModelSpace (lowerRootFactor (finiteEPolynomial A tau)) :=
  finiteZeroVectorHalfScale •
    finiteResidualDifferenceCoordinate A tau gamma

@[simp] theorem coe_finitePositiveSplitCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    ((finitePositiveSplitCoordinate A tau gamma :
        finiteModelSpace (lowerRootFactor (finiteEPolynomial A tau))) :
      ℂ[X]) =
      C finiteZeroVectorHalfScale *
        C ((lowerRootFactor (finiteEPolynomial A tau)).eval gamma)⁻¹ *
        finiteInnerDifferencePolynomial
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)))
          (lowerRootFactor (finiteEPolynomial A tau)) gamma := by
  simp [finitePositiveSplitCoordinate, finiteResidualDifferenceCoordinate,
    smul_eq_C_mul]
  ring

/-- The actual negative split coordinate, including its sign convention and
normalization. -/
def finiteNegativeSplitCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    finiteModelSpace
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))) :=
  (-finiteZeroVectorHalfScale) •
    finiteBlaschkeDifferenceCoordinate A tau gamma

@[simp] theorem coe_finiteNegativeSplitCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    ((finiteNegativeSplitCoordinate A tau gamma :
        finiteModelSpace
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))) : ℂ[X]) =
      C (-finiteZeroVectorHalfScale) *
        C ((conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).eval gamma)⁻¹ *
        finiteInnerDifferencePolynomial
          (upperRootFactor (finiteEPolynomial A tau))
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau))) gamma := by
  simp [finiteNegativeSplitCoordinate, finiteBlaschkeDifferenceCoordinate,
    smul_eq_C_mul]
  ring

/-- Clearing the variable factor in the positive split coordinate. -/
theorem X_sub_C_mul_coe_finitePositiveSplitCoordinate
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (X - C gamma) *
        ((finitePositiveSplitCoordinate A tau gamma :
          finiteModelSpace
            (lowerRootFactor (finiteEPolynomial A tau))) : ℂ[X]) =
      C finiteZeroVectorHalfScale *
        (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)) -
          C ((conjugatePolynomial
              (lowerRootFactor (finiteEPolynomial A tau))).eval gamma /
            (lowerRootFactor (finiteEPolynomial A tau)).eval gamma) *
            lowerRootFactor (finiteEPolynomial A tau)) := by
  rw [finitePositiveSplitCoordinate]
  simp only [Submodule.coe_smul, smul_eq_C_mul]
  calc
    (X - C gamma) *
        (C finiteZeroVectorHalfScale *
          ((finiteResidualDifferenceCoordinate A tau gamma :
            finiteModelSpace
              (lowerRootFactor (finiteEPolynomial A tau))) : ℂ[X])) =
        C finiteZeroVectorHalfScale *
          ((X - C gamma) *
            ((finiteResidualDifferenceCoordinate A tau gamma :
              finiteModelSpace
                (lowerRootFactor (finiteEPolynomial A tau))) : ℂ[X])) := by
      ring
    _ = _ := by
      rw [finiteResidualDifferenceCoordinate,
        X_sub_C_mul_coe_finiteInnerDifferenceCoordinate]
      exact lowerRootFactor_eval_ne_zero_at_root hA htau hgamma

/-- Clearing the variable factor in the negative split coordinate. -/
theorem X_sub_C_mul_coe_finiteNegativeSplitCoordinate
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (X - C gamma) *
        ((finiteNegativeSplitCoordinate A tau gamma :
          finiteModelSpace
            (conjugatePolynomial
              (upperRootFactor (finiteEPolynomial A tau)))) : ℂ[X]) =
      C (-finiteZeroVectorHalfScale) *
        (upperRootFactor (finiteEPolynomial A tau) -
          C ((upperRootFactor (finiteEPolynomial A tau)).eval gamma /
            (conjugatePolynomial
              (upperRootFactor (finiteEPolynomial A tau))).eval gamma) *
            conjugatePolynomial
              (upperRootFactor (finiteEPolynomial A tau))) := by
  rw [finiteNegativeSplitCoordinate]
  simp only [Submodule.coe_smul, smul_eq_C_mul]
  calc
    (X - C gamma) *
        (C (-finiteZeroVectorHalfScale) *
          ((finiteBlaschkeDifferenceCoordinate A tau gamma :
            finiteModelSpace
              (conjugatePolynomial
                (upperRootFactor (finiteEPolynomial A tau)))) : ℂ[X])) =
        C (-finiteZeroVectorHalfScale) *
          ((X - C gamma) *
            ((finiteBlaschkeDifferenceCoordinate A tau gamma :
              finiteModelSpace
                (conjugatePolynomial
                  (upperRootFactor (finiteEPolynomial A tau)))) : ℂ[X])) := by
      ring
    _ = _ := by
      rw [finiteBlaschkeDifferenceCoordinate,
        X_sub_C_mul_coe_finiteInnerDifferenceCoordinate]
      exact conjugate_upperRootFactor_eval_ne_zero_at_root
        hA htau hgamma

/-- Exact polynomial reconstruction of a zero quotient from its positive and
negative model coordinates.  The leading coefficient is kept on the left,
so no unrecorded division by it occurs. -/
theorem finiteSplitCoordinate_polynomial_identity
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    C (finiteEPolynomial A tau).leadingCoeff *
        (((finitePositiveSplitCoordinate A tau gamma :
            finiteModelSpace
              (lowerRootFactor (finiteEPolynomial A tau))) : ℂ[X]) *
            conjugatePolynomial
              (upperRootFactor (finiteEPolynomial A tau)) -
          ((finiteNegativeSplitCoordinate A tau gamma :
            finiteModelSpace
              (conjugatePolynomial
                (upperRootFactor (finiteEPolynomial A tau)))) : ℂ[X]) *
            lowerRootFactor (finiteEPolynomial A tau)) =
      C finiteZeroVectorScale * finiteZeroQuotientPolynomial A gamma := by
  let E := finiteEPolynomial A tau
  let Q := finiteESharpPolynomial A tau
  let U := upperRootFactor E
  let D := conjugatePolynomial U
  let L := lowerRootFactor E
  let V := conjugatePolynomial L
  let c := E.leadingCoeff
  let a := A.map Complex.ofRealHom
  have hE : E = C c * U * L := by
    simpa [E, U, L, c] using finiteEPolynomial_eq_rootFactors hA htau
  have hQ : Q = C c * D * V := by
    simpa [E, Q, U, D, L, V, c] using
      finiteESharpPolynomial_eq_rootFactors hA htau
  have hsum : C c * (U * L + D * V) = C (2 : ℂ) * a := by
    calc
      C c * (U * L + D * V) = E + Q := by
        rw [hE, hQ]
        ring
      _ = C (2 : ℂ) * a := by
        simpa [E, Q, a] using
          finiteEPolynomial_add_finiteESharpPolynomial A tau
  have hroot :=
    finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root
      hA htau hgamma
  change V.eval gamma / L.eval gamma = -(U.eval gamma / D.eval gamma)
    at hroot
  have hrootSum :
      V.eval gamma / L.eval gamma + U.eval gamma / D.eval gamma = 0 := by
    linear_combination hroot
  have hrootSumC :
      (C (V.eval gamma / L.eval gamma) : ℂ[X]) +
          C (U.eval gamma / D.eval gamma) = 0 := by
    rw [← map_add, hrootSum, map_zero]
  have hpos := X_sub_C_mul_coe_finitePositiveSplitCoordinate
    hA htau hgamma
  have hneg := X_sub_C_mul_coe_finiteNegativeSplitCoordinate
    hA htau hgamma
  change (X - C gamma) *
      (((finitePositiveSplitCoordinate A tau gamma :
        finiteModelSpace L) : ℂ[X])) =
      C finiteZeroVectorHalfScale *
        (V - C (V.eval gamma / L.eval gamma) * L) at hpos
  change (X - C gamma) *
      (((finiteNegativeSplitCoordinate A tau gamma :
        finiteModelSpace D) : ℂ[X])) =
      C (-finiteZeroVectorHalfScale) *
        (U - C (U.eval gamma / D.eval gamma) * D) at hneg
  have hquot := X_sub_C_mul_finiteZeroQuotientPolynomial A hgamma
  change (X - C gamma) * finiteZeroQuotientPolynomial A gamma = a at hquot
  apply mul_left_cancel₀ (X_sub_C_ne_zero gamma)
  change (X - C gamma) *
      (C c *
        (((finitePositiveSplitCoordinate A tau gamma :
          finiteModelSpace L) : ℂ[X]) * D -
        ((finiteNegativeSplitCoordinate A tau gamma :
          finiteModelSpace D) : ℂ[X]) * L)) =
      (X - C gamma) *
        (C finiteZeroVectorScale * finiteZeroQuotientPolynomial A gamma)
  rw [show (X - C gamma) *
      (C c *
        (((finitePositiveSplitCoordinate A tau gamma :
          finiteModelSpace L) : ℂ[X]) * D -
        ((finiteNegativeSplitCoordinate A tau gamma :
          finiteModelSpace D) : ℂ[X]) * L)) =
      C c *
        (((X - C gamma) *
          ((finitePositiveSplitCoordinate A tau gamma :
            finiteModelSpace L) : ℂ[X])) * D -
        ((X - C gamma) *
          ((finiteNegativeSplitCoordinate A tau gamma :
            finiteModelSpace D) : ℂ[X])) * L) by ring,
    hpos, hneg]
  rw [show (X - C gamma) *
      (C finiteZeroVectorScale * finiteZeroQuotientPolynomial A gamma) =
      C finiteZeroVectorScale *
        ((X - C gamma) * finiteZeroQuotientPolynomial A gamma) by ring,
    hquot]
  rw [show C c *
      ((C finiteZeroVectorHalfScale *
          (V - C (V.eval gamma / L.eval gamma) * L)) * D -
        (C (-finiteZeroVectorHalfScale) *
          (U - C (U.eval gamma / D.eval gamma) * D)) * L) =
      C finiteZeroVectorHalfScale * (C c * (U * L + D * V)) by
    rw [map_neg]
    linear_combination
      -(C c * C finiteZeroVectorHalfScale * D * L) * hrootSumC]
  have hscale :
      C finiteZeroVectorHalfScale * C (2 : ℂ) =
        C finiteZeroVectorScale := by
    rw [← C_mul]
    congr 1
    rw [finiteZeroVectorHalfScale]
    field_simp
  rw [hsum, ← mul_assoc, hscale]

/-- The positive (residual-inner) algebraic model space. -/
abbrev finitePositiveModelSpace (A : ℝ[X]) (tau : ℝ) :=
  finiteModelSpace (lowerRootFactor (finiteEPolynomial A tau))

/-- The negative (Blaschke) algebraic model space. -/
abbrev finiteNegativeModelSpace (A : ℝ[X]) (tau : ℝ) :=
  finiteModelSpace
    (conjugatePolynomial (upperRootFactor (finiteEPolynomial A tau)))

/-- The ordered positive/negative coordinate pair attached to a root. -/
def finiteRootSplitCoordinate
    (A : ℝ[X]) (tau : ℝ) (gamma : ℂ) :
    finitePositiveModelSpace A tau × finiteNegativeModelSpace A tau :=
  (finitePositiveSplitCoordinate A tau gamma,
    finiteNegativeSplitCoordinate A tau gamma)

/-- Synthesize a pair of finite model coordinates from coefficients indexed
by the distinct complex roots of `A`. -/
def finiteCoefficientToSplitPairLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    (↑(finiteComplexRootFinset A) → ℂ) →ₗ[ℂ]
      (finitePositiveModelSpace A tau ×
        finiteNegativeModelSpace A tau) where
  toFun g := ∑ gamma, g gamma • finiteRootSplitCoordinate A tau gamma
  map_add' g h := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c g := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- Synthesize the Lagrange quotient polynomial from root coefficients. -/
def finiteZeroQuotientSynthesisLinearMap (A : ℝ[X]) :
    (↑(finiteComplexRootFinset A) → ℂ) →ₗ[ℂ] ℂ[X] where
  toFun g := ∑ gamma, g gamma • finiteZeroQuotientPolynomial A gamma
  map_add' g h := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c g := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The polynomial numerator obtained by putting a positive/negative model
pair over the common product denominator. -/
def finiteSplitPairReconstructionLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    (finitePositiveModelSpace A tau × finiteNegativeModelSpace A tau) →ₗ[ℂ]
      ℂ[X] where
  toFun q :=
    C (finiteEPolynomial A tau).leadingCoeff *
      ((q.1 : ℂ[X]) *
          conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) -
        (q.2 : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau))
  map_add' q r := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    ring
  map_smul' c q := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
      RingHom.id_apply, smul_eq_C_mul]
    ring

/-- Reconstruction sends each root coordinate pair to the normalized
Lagrange quotient polynomial. -/
theorem finiteSplitPairReconstructionLinearMap_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (gamma : ↑(finiteComplexRootFinset A)) :
    finiteSplitPairReconstructionLinearMap A tau
        (finiteRootSplitCoordinate A tau gamma) =
      finiteZeroVectorScale • finiteZeroQuotientPolynomial A gamma := by
  change C (finiteEPolynomial A tau).leadingCoeff *
      (((finitePositiveSplitCoordinate A tau gamma :
          finitePositiveModelSpace A tau) : ℂ[X]) *
          conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) -
        ((finiteNegativeSplitCoordinate A tau gamma :
          finiteNegativeModelSpace A tau) : ℂ[X]) *
          lowerRootFactor (finiteEPolynomial A tau)) = _
  rw [finiteSplitCoordinate_polynomial_identity hA htau
    (finiteComplexRoot_eval_zero A gamma)]
  simp [smul_eq_C_mul]

/-- Reconstruction intertwines coefficient synthesis with the original
Lagrange quotient synthesis. -/
theorem finiteSplitPairReconstruction_comp_coefficientMap
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (g : ↑(finiteComplexRootFinset A) → ℂ) :
    finiteSplitPairReconstructionLinearMap A tau
        (finiteCoefficientToSplitPairLinearMap A tau g) =
      finiteZeroVectorScale • finiteZeroQuotientSynthesisLinearMap A g := by
  change finiteSplitPairReconstructionLinearMap A tau
      (∑ gamma, g gamma • finiteRootSplitCoordinate A tau gamma) =
    finiteZeroVectorScale •
      (∑ gamma, g gamma • finiteZeroQuotientPolynomial A gamma)
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro gamma _
  rw [map_smul, finiteSplitPairReconstructionLinearMap_root hA htau]
  simp [smul_smul, mul_comm]

/-- The zero-vector normalization is nonzero. -/
theorem finiteZeroVectorScale_ne_zero : finiteZeroVectorScale ≠ 0 := by
  rw [finiteZeroVectorScale]
  exact div_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))

/-- Lagrange quotient synthesis is injective for separable `A`. -/
theorem finiteZeroQuotientSynthesisLinearMap_injective
    {A : ℝ[X]} (hA : A.Separable) :
    Function.Injective (finiteZeroQuotientSynthesisLinearMap A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro g hg
  change ∑ gamma, g gamma • finiteZeroQuotientPolynomial A gamma = 0 at hg
  apply _root_.funext
  intro gamma
  exact (Fintype.linearIndependent_iff.mp
    (finiteZeroQuotientPolynomial_linearIndependent hA)) g hg gamma

/-- The coefficient-to-pair map is injective, now as a consequence of the
exact polynomial reconstruction rather than a dimension count alone. -/
theorem finiteCoefficientToSplitPairLinearMap_injective
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    Function.Injective (finiteCoefficientToSplitPairLinearMap A tau) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro g hg
  apply finiteZeroQuotientSynthesisLinearMap_injective hA
  have hreconstruct := congrArg
    (finiteSplitPairReconstructionLinearMap A tau) hg
  rw [map_zero,
    finiteSplitPairReconstruction_comp_coefficientMap hA htau] at hreconstruct
  simpa using (smul_eq_zero.mp hreconstruct).resolve_left
    finiteZeroVectorScale_ne_zero

/-- Domain and target of the coefficient-to-pair map have equal complex
dimension. -/
theorem finiteCoefficientToSplitPair_finrank_eq
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    Module.finrank ℂ (↑(finiteComplexRootFinset A) → ℂ) =
      Module.finrank ℂ
        (finitePositiveModelSpace A tau × finiteNegativeModelSpace A tau) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
    Fintype.card_coe, finiteComplexRootFinset_card hA]
  simpa [finitePositiveModelSpace, finiteNegativeModelSpace, Nat.add_comm]
    using (finiteEPolynomial_upper_add_lower hA htau).symm

/-- The rigorous coefficient-to-pair isomorphism for the finite algebraic
model. -/
noncomputable def finiteCoefficientToSplitPairLinearEquiv
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    (↑(finiteComplexRootFinset A) → ℂ) ≃ₗ[ℂ]
      (finitePositiveModelSpace A tau × finiteNegativeModelSpace A tau) :=
  (finiteCoefficientToSplitPairLinearMap A tau).linearEquivOfInjective
    (finiteCoefficientToSplitPairLinearMap_injective hA htau)
    (finiteCoefficientToSplitPair_finrank_eq hA htau)

@[simp] theorem finiteCoefficientToSplitPairLinearEquiv_apply
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (g : ↑(finiteComplexRootFinset A) → ℂ) :
    finiteCoefficientToSplitPairLinearEquiv hA htau g =
      finiteCoefficientToSplitPairLinearMap A tau g :=
  LinearMap.linearEquivOfInjective_apply _ _ _

/-- The positive algebraic coordinate evaluates to the previously constructed
positive split function. -/
theorem finiteModelValue_positiveSplitCoordinate
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hzgamma : z ≠ gamma) :
    finiteModelValue (lowerRootFactor (finiteEPolynomial A tau))
        (finitePositiveSplitCoordinate A tau gamma) z =
      finitePositiveSplitValue A tau gamma z := by
  rw [finitePositiveSplitCoordinate, finiteModelValue_smul,
    finiteModelValue_residualDifferenceCoordinate
      hA htau hgamma hz hzgamma, finitePositiveSplitValue]

/-- The negative algebraic coordinate evaluates to the previously constructed
negative split function. -/
theorem finiteModelValue_negativeSplitCoordinate
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hzgamma : z ≠ gamma) :
    finiteModelValue
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        (finiteNegativeSplitCoordinate A tau gamma) z =
      finiteNegativeSplitValue A tau gamma z := by
  rw [finiteNegativeSplitCoordinate, finiteModelValue_smul,
    finiteModelValue_blaschkeDifferenceCoordinate
      hA htau hgamma hz hzgamma, finiteNegativeSplitValue]

/-- The two algebraic model dimensions add to the full degree of `A`. -/
theorem finiteSplitModelSpace_finrank_add
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    Module.finrank ℂ
        (finiteModelSpace
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))) +
      Module.finrank ℂ
        (finiteModelSpace
          (lowerRootFactor (finiteEPolynomial A tau))) =
      A.natDegree := by
  simpa using finiteEPolynomial_upper_add_lower hA htau

/-- The normalized zero-vector identity can now be stated entirely through
elements of the two finite algebraic model spaces. -/
theorem finiteZeroVector_split_modelCoordinates
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hEz : (finiteEPolynomial A tau).eval z ≠ 0)
    (hzgamma : z ≠ gamma) :
    finiteBlaschkeValue A tau z * finiteZeroVectorValue A tau gamma z =
      finiteModelValue (lowerRootFactor (finiteEPolynomial A tau))
          (finitePositiveSplitCoordinate A tau gamma) z -
        finiteModelValue
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))
          (finiteNegativeSplitCoordinate A tau gamma) z := by
  rw [finiteModelValue_positiveSplitCoordinate hA htau hgamma hz hzgamma,
    finiteModelValue_negativeSplitCoordinate hA htau hgamma hz hzgamma]
  exact finiteZeroVector_split hA htau hgamma hz hEz hzgamma

end

end RiemannGaussian
