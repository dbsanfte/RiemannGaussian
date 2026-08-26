import RiemannGaussian.FiniteKreinLanger

/-!
# Pointwise finite kernel decomposition

This file passes from the exact rational-function identity to pointwise
representatives wherever their denominators are nonzero.  It proves the
algebraic de Branges kernel-numerator decomposition and the special value
`S(gamma) = -B(gamma)` at every zero of the original separable polynomial.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Pointwise upper-root Blaschke factor for the finite homotopy. -/
def finiteBlaschkeValue (A : ℝ[X]) (tau : ℝ) (z : ℂ) : ℂ :=
  upperRootBlaschkeValue (finiteEPolynomial A tau) z

/-- Pointwise residual inner factor for the finite homotopy. -/
def finiteInnerValue (A : ℝ[X]) (tau : ℝ) (z : ℂ) : ℂ :=
  lowerRootInnerValue (finiteEPolynomial A tau) z

/-- Pointwise form of `B * Theta = S`.  The two hypotheses are precisely
the nonvanishing denominators not already forced by the factorization. -/
theorem finiteKreinLangerValue_cancellation
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ}
    (hEz : (finiteEPolynomial A tau).eval z ≠ 0)
    (hDz : (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau))).eval z ≠ 0) :
    finiteBlaschkeValue A tau z * finiteThetaValue A tau z =
      finiteInnerValue A tau z := by
  let E := finiteEPolynomial A tau
  let Q := finiteESharpPolynomial A tau
  let U := upperRootFactor E
  let D := conjugatePolynomial U
  let L := lowerRootFactor E
  let V := conjugatePolynomial L
  let c := E.leadingCoeff
  have hE : E = C c * U * L := by
    simpa [E, U, L, c] using finiteEPolynomial_eq_rootFactors hA htau
  have hQ : Q = C c * D * V := by
    simpa [E, Q, U, D, L, V, c] using
      finiteESharpPolynomial_eq_rootFactors hA htau
  have hEz' : E.eval z ≠ 0 := by simpa [E] using hEz
  have hDz' : D.eval z ≠ 0 := by simpa [E, U, D] using hDz
  have hUeval : U.eval z ≠ 0 := by
    intro hzero
    apply hEz'
    rw [hE]
    simp [hzero]
  have hLeval : L.eval z ≠ 0 := by
    intro hzero
    apply hEz'
    rw [hE]
    simp [hzero]
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr
    (finiteEPolynomial_ne_zero hA.ne_zero tau)
  change U.eval z / D.eval z * (Q.eval z / E.eval z) =
    V.eval z / L.eval z
  rw [hE, hQ]
  simp only [eval_mul, eval_C]
  field_simp [hUeval, hDz', hLeval, hc]

/-- In the open upper half-plane only a genuine zero of `E_tau` can obstruct
the pointwise identity; the two inner denominators are already nonzero. -/
theorem finiteKreinLangerValue_cancellation_of_im_pos
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} (hz : 0 < z.im)
    (hEz : (finiteEPolynomial A tau).eval z ≠ 0) :
    finiteBlaschkeValue A tau z * finiteThetaValue A tau z =
      finiteInnerValue A tau z := by
  apply finiteKreinLangerValue_cancellation hA htau hEz
  exact conjugate_upperRootFactor_eval_ne_zero_of_im_pos
    (finiteEPolynomial A tau) hz

/-- The unnormalized de Branges kernel numerator. -/
def innerKernelNumerator (phi : ℂ → ℂ) (z w : ℂ) : ℂ :=
  1 - phi z * conj (phi w)

/-- Pure algebra behind the finite positive-minus-negative kernel split. -/
theorem innerKernelNumerator_decomposition
    {B Theta S : ℂ → ℂ} {z w : ℂ}
    (hz : B z * Theta z = S z) (hw : B w * Theta w = S w) :
    B z * conj (B w) * innerKernelNumerator Theta z w =
      innerKernelNumerator S z w - innerKernelNumerator B z w := by
  rw [innerKernelNumerator, innerKernelNumerator, innerKernelNumerator,
    ← hz, ← hw]
  simp only [map_mul]
  ring

/-- The finite kernel numerator decomposes as the residual-inner kernel
minus the upper-root Blaschke kernel. -/
theorem finiteKernelNumerator_decomposition
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hEz : (finiteEPolynomial A tau).eval z ≠ 0)
    (hEw : (finiteEPolynomial A tau).eval w ≠ 0) :
    finiteBlaschkeValue A tau z * conj (finiteBlaschkeValue A tau w) *
        innerKernelNumerator (finiteThetaValue A tau) z w =
      innerKernelNumerator (finiteInnerValue A tau) z w -
        innerKernelNumerator (finiteBlaschkeValue A tau) z w := by
  apply innerKernelNumerator_decomposition
  · exact finiteKreinLangerValue_cancellation_of_im_pos hA htau hz hEz
  · exact finiteKreinLangerValue_cancellation_of_im_pos hA htau hw hEw

/-- The conjugated upper-root factor is nonzero at every zero of `A`. -/
theorem conjugate_upperRootFactor_eval_ne_zero_at_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau))).eval gamma ≠ 0 := by
  let E := finiteEPolynomial A tau
  let Q := finiteESharpPolynomial A tau
  let U := upperRootFactor E
  let D := conjugatePolynomial U
  let L := lowerRootFactor E
  let V := conjugatePolynomial L
  let c := E.leadingCoeff
  have hQfactor : Q = C c * D * V := by
    simpa [E, Q, U, D, L, V, c] using
      finiteESharpPolynomial_eq_rootFactors hA htau
  have hEgamma : E.eval gamma ≠ 0 := by
    simpa [E] using finiteE_eval_ne_zero_at_root hA htau hgamma
  have hQgamma : Q.eval gamma ≠ 0 := by
    rw [show Q.eval gamma = -E.eval gamma by
      simpa [E, Q] using
        finiteESharp_eval_eq_neg_finiteE_at_root A tau hgamma]
    exact neg_ne_zero.mpr hEgamma
  change D.eval gamma ≠ 0
  intro hzero
  apply hQgamma
  rw [hQfactor]
  simp [hzero]

/-- At every zero of `A`, the two inner factors have opposite values.  This
is the exact vanishing relation used by the zero-vector split. -/
theorem finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    finiteInnerValue A tau gamma = -finiteBlaschkeValue A tau gamma := by
  have hcancel := finiteKreinLangerValue_cancellation hA htau
    (finiteE_eval_ne_zero_at_root hA htau hgamma)
    (conjugate_upperRootFactor_eval_ne_zero_at_root hA htau hgamma)
  rw [finiteThetaValue_at_root hA htau hgamma] at hcancel
  simpa using hcancel.symm

theorem finiteBlaschkeValue_add_finiteInnerValue_at_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    finiteBlaschkeValue A tau gamma + finiteInnerValue A tau gamma = 0 := by
  rw [finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root hA htau hgamma,
    add_neg_cancel]

end

end RiemannGaussian
