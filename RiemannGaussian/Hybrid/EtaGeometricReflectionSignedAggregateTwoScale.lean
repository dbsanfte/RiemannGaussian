import RiemannGaussian.Hybrid.EtaGeometricReflectionSignedAggregateUniversalScale

/-!
# Two-start tomography for the signed eta colour metric

At one geometric block start, the literal eta correlation contracts a
`2 × 2` reflected/original prefix metric against one completion-coefficient
row on each side.  The reflected coefficient becomes small relative to the
original coefficient along late blocks, so that single contraction does not
retain a uniformly visible copy of all four metric colours.

This module keeps one adjacent start before making that contraction.  Each
coefficient advances by its exact complex step mode.  For `q > 1`, the two
reflection colours have distinct step modes, so the adjacent-start coefficient
matrix has nonzero determinant.  Two probes recover an arbitrary colour
vector, and the four left/right cross probes recover an arbitrary `2 × 2`
colour metric exactly.

The specialization here probes the literal normalized-prefix metric at the
fixed start `n`; its `(0,0)` entry is exactly the existing eta coefficient
contraction.  The other entries use the adjacent coefficient rows while
retaining that same metric, rather than claiming that the prefix metric itself
is unchanged at `n + 1`.  This is an exact finite information-preservation
interface.  It proves no conditioning estimate, arithmetic bound, or
zero-proportion threshold.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- The exact multiplicative step by which one upper completion coefficient
advances when the geometric block start changes from `n` to `n + 1`. -/
def pairedEtaGeometricUpperCoefficientStepMode
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (i : Fin 2) : ℂ :=
  (((q : ℂ) ^
    (pairedEtaGeometricUpperReflectionPairZero rho i).val)⁻¹)

/-- Every upper completion coefficient obeys the exact geometric one-step
recurrence given by its colour step mode. -/
theorem pairedEtaGeometricUpperCompletionCoefficientVector_succ
    (q : ℕ) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) (i : Fin 2) :
    pairedEtaGeometricUpperCompletionCoefficientVector q rho (n + 1) i =
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n i *
        pairedEtaGeometricUpperCoefficientStepMode q rho i := by
  unfold pairedEtaGeometricUpperCompletionCoefficientVector
    pairedEtaGeometricUpperCoefficientStepMode
  rw [pairedEtaGeometricCompletedPrefixCoefficient_eq_leading_mul_inv_pow,
    pairedEtaGeometricCompletedPrefixCoefficient_eq_leading_mul_inv_pow,
    pow_succ]
  simp only [_root_.mul_inv_rev]
  ring

/-- At every base `q > 1`, the reflected and original colours of an upper
zero pair have distinct complex step modes. -/
theorem pairedEtaGeometricUpperCoefficientStepMode_ne
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    pairedEtaGeometricUpperCoefficientStepMode q rho 0 ≠
      pairedEtaGeometricUpperCoefficientStepMode q rho 1 := by
  intro hstep
  have hbase :
      (q : ℂ) ^
          (NontrivialZetaZero.conjugatePartner rho.1).val =
        (q : ℂ) ^ rho.1.val := by
    apply inv_injective
    simpa [pairedEtaGeometricUpperCoefficientStepMode,
      pairedEtaGeometricUpperReflectionPairZero] using hstep
  have hq0 : (q : ℂ) ^ rho.1.val ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast (show q ≠ 0 by omega)))
  have hratio :
      pairedEtaGeometricUpperPartnerToOriginalRatioBase q rho = 1 := by
    unfold pairedEtaGeometricUpperPartnerToOriginalRatioBase
    rw [hbase]
    exact div_self hq0
  have hlt :=
    norm_pairedEtaGeometricUpperPartnerToOriginalRatioBase_lt_one hq rho
  rw [hratio, norm_one] at hlt
  exact (lt_irrefl 1 hlt)

/-- The two adjacent geometric starts as rows and the two reflection colours
as columns. -/
def pairedEtaGeometricUpperTwoStartCoefficientMatrix
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := fun k i ↦
  pairedEtaGeometricUpperCompletionCoefficientVector q rho
    (n + (k : ℕ)) i

/-- Exact determinant factorization of the adjacent-start coefficient
matrix. -/
theorem det_pairedEtaGeometricUpperTwoStartCoefficientMatrix
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) :
    (pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n).det =
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0 *
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 *
        (pairedEtaGeometricUpperCoefficientStepMode q rho 1 -
          pairedEtaGeometricUpperCoefficientStepMode q rho 0) := by
  rw [Matrix.det_fin_two]
  unfold pairedEtaGeometricUpperTwoStartCoefficientMatrix
  simp only [Fin.isValue, Fin.val_zero, add_zero, Fin.val_one]
  rw [pairedEtaGeometricUpperCompletionCoefficientVector_succ,
    pairedEtaGeometricUpperCompletionCoefficientVector_succ]
  ring

/-- The adjacent-start coefficient matrix is nonsingular for every
`q > 1`. -/
theorem det_pairedEtaGeometricUpperTwoStartCoefficientMatrix_ne_zero
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    (pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n).det ≠ 0 := by
  rw [det_pairedEtaGeometricUpperTwoStartCoefficientMatrix]
  exact mul_ne_zero
    (mul_ne_zero
      (by
        unfold pairedEtaGeometricUpperCompletionCoefficientVector
        exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le _ n)
      (by
        unfold pairedEtaGeometricUpperCompletionCoefficientVector
        exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le _ n))
    (sub_ne_zero.mpr
      (pairedEtaGeometricUpperCoefficientStepMode_ne hq rho).symm)

/-- The two adjacent coefficient contractions of an arbitrary two-colour
vector. -/
def pairedEtaGeometricUpperTwoStartCoefficientObservation
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) (x : Fin 2 → ℂ) : Fin 2 → ℂ :=
  (pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n).mulVec x

/-- The two adjacent coefficient observations recover every two-colour vector
exactly. -/
theorem pairedEtaGeometricUpperTwoStartCoefficientObservation_recover
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ)
    (x : Fin 2 → ℂ) :
    ((pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n)⁻¹).mulVec
        (pairedEtaGeometricUpperTwoStartCoefficientObservation q rho n x) =
      x := by
  let A := pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n
  have hdet : A.det ≠ 0 :=
    det_pairedEtaGeometricUpperTwoStartCoefficientMatrix_ne_zero hq rho n
  let _ : Invertible A :=
    Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
  exact Matrix.inv_mulVec_eq_vec rfl

/-- The two adjacent coefficient rows are linearly independent over the
complex numbers. -/
theorem linearIndependent_pairedEtaGeometricUpperTwoStartCoefficientMatrix_rows
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    LinearIndependent ℂ
      (pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (det_pairedEtaGeometricUpperTwoStartCoefficientMatrix_ne_zero hq rho n)

/-- The same adjacent-start coefficient matrix with colours as rows and
starts as columns. -/
def pairedEtaGeometricUpperTwoStartColourCoefficientMatrix
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := fun i k ↦
  pairedEtaGeometricUpperCompletionCoefficientVector q rho
    (n + (k : ℕ)) i

/-- The colour-by-start orientation of the coefficient matrix is also
nonsingular for every `q > 1`. -/
theorem det_pairedEtaGeometricUpperTwoStartColourCoefficientMatrix_ne_zero
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    (pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q rho n).det ≠
      0 := by
  unfold pairedEtaGeometricUpperTwoStartColourCoefficientMatrix
  change
    ((pairedEtaGeometricUpperTwoStartCoefficientMatrix q rho n)ᵀ).det ≠ 0
  rw [Matrix.det_transpose]
  exact det_pairedEtaGeometricUpperTwoStartCoefficientMatrix_ne_zero hq rho n

/-- Four left/right adjacent-start probes of an arbitrary two-colour metric.
The left coefficient row is conjugated, as in the literal Hermitian eta
contraction. -/
def pairedEtaGeometricUpperTwoStartMetricObservation
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) (K : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q zeta n)ᴴ *
    K * pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q rho n

/-- The four adjacent-start probes recover an arbitrary two-colour metric
exactly by two-sided inversion. -/
theorem pairedEtaGeometricUpperTwoStartMetricObservation_recover
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) (K : Matrix (Fin 2) (Fin 2) ℂ) :
    ((pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q zeta n)ᴴ)⁻¹ *
        pairedEtaGeometricUpperTwoStartMetricObservation
          q zeta rho n K *
      (pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q rho n)⁻¹ =
    K := by
  let L :=
    (pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q zeta n)ᴴ
  let R := pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q rho n
  have hLdet : L.det ≠ 0 := by
    unfold L
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr
      (det_pairedEtaGeometricUpperTwoStartColourCoefficientMatrix_ne_zero
        hq zeta n)
  have hRdet : R.det ≠ 0 := by
    unfold R
    exact det_pairedEtaGeometricUpperTwoStartColourCoefficientMatrix_ne_zero
      hq rho n
  let _ : Invertible L :=
    Matrix.invertibleOfIsUnitDet L (isUnit_iff_ne_zero.mpr hLdet)
  let _ : Invertible R :=
    Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hRdet)
  unfold pairedEtaGeometricUpperTwoStartMetricObservation
  change L⁻¹ * (L * K * R) * R⁻¹ = K
  rw [Matrix.mul_assoc L K R,
    ← Matrix.mul_assoc L⁻¹ L (K * R), Matrix.inv_mul_of_invertible,
    Matrix.one_mul, Matrix.mul_assoc K R R⁻¹,
    Matrix.mul_inv_of_invertible, Matrix.mul_one]

/-- The four adjacent-start coefficient probes of the literal normalized
upper prefix-correlation metric at the fixed start `n`. -/
def pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  pairedEtaGeometricUpperTwoStartMetricObservation q zeta rho n
    (pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
      q zeta rho n M)

/-- Each specialized probe is the exact sum of its four signed complex colour
interactions, with the chosen left and right adjacent-start rows retained. -/
theorem pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation_apply
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (k l : Fin 2) :
    pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
        q zeta rho n M k l =
      ∑ i : Fin 2, ∑ j : Fin 2,
        star (pairedEtaGeometricUpperCompletionCoefficientVector
          q zeta (n + (k : ℕ)) i) *
          pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
            q zeta rho n M i j *
          pairedEtaGeometricUpperCompletionCoefficientVector
            q rho (n + (l : ℕ)) j := by
  unfold pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
    pairedEtaGeometricUpperTwoStartMetricObservation
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  simp_rw [Matrix.conjTranspose_apply]
  unfold pairedEtaGeometricUpperTwoStartColourCoefficientMatrix
  simp only [Fin.sum_univ_two]
  ring

/-- The first of the four probes is exactly the existing literal one-start
metric coefficient contraction. -/
theorem pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation_zero_zero
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
        q zeta rho n M 0 0 =
      pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M := by
  rw [pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation_apply]
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientContraction
  simp only [Fin.val_zero, add_zero, Fin.sum_univ_two]
  ring

/-- Four adjacent-start coefficient probes recover every entry of the literal
normalized upper prefix-correlation metric. -/
theorem pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation_recover
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    ((pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q zeta n)ᴴ)⁻¹ *
        pairedEtaGeometricCriticalUpperTwoStartMetricPrefixObservation
          q zeta rho n M *
      (pairedEtaGeometricUpperTwoStartColourCoefficientMatrix q rho n)⁻¹ =
    pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
      q zeta rho n M := by
  exact pairedEtaGeometricUpperTwoStartMetricObservation_recover
    hq zeta rho n
      (pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
        q zeta rho n M)

end

end RiemannGaussian
