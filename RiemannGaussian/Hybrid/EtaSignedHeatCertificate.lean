import RiemannGaussian.Hybrid.ProjectionHeatLeakage
import RiemannGaussian.EtaEnergyFiniteWindowInertia

/-!
# Signed spectral heat certificate for the literal finite eta zero window

This module applies the abstract Hermitian signed-heat calculus to the actual
multiplicity-weighted eta zero-window matrix.  The input is not a model or a
moment surrogate: it is

`pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T`,

whose entries retain the completed eta features, two hyperbolic channels,
analytic zero multiplicities, and the complete finite symmetric spectral
window.

Lean constructs its full spectral heat flow and signed spectral heat flow,
keeps the matrix-valued semigroup before taking traces, and proves genuine
positive-time integrability of the signed current.  The normalized singular
heat integral is exactly the matrix signature.  Together with the ordinary
heat-trace limit, it reconstructs the positive inertia exactly.

Finally, the already checked eta-specific inertia bound is translated into
this continuous language.  Thus the signed-heat expression is bounded by the
critical-line zero count plus the upper off-line zero count.  This is an exact
new representation of the existing certificate, not yet a stronger
zero-proportion estimate.
-/

open Complex Matrix Finset MeasureTheory Set Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-! ## Matrix-valued eta spectral heat -/

/-- The complete spectral heat flow of the literal finite eta zero-window
matrix. -/
def pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.hermitianHeatFlow
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The sign-bearing spectral heat flow of the literal finite eta
zero-window matrix. -/
def pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatFlow
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.hermitianSignedHeatFlow
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The real trace of the complete eta zero-window spectral heat flow. -/
def pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) : ℝ :=
  HermitianRankTrace.hermitianHeatTrace
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The real trace of the sign-bearing eta zero-window spectral heat flow. -/
def pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) : ℝ :=
  HermitianRankTrace.hermitianSignedHeatCurrent
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The spectral nullity of the literal finite eta zero-window matrix. -/
def pairedEtaTopPrefixFiniteZeroWindowZeroIndex
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) : ℕ :=
  HermitianRankTrace.zeroIndex
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)

/-- The complete eta zero-window spectral heat flow is Hermitian at every
real heat scale. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u).IsHermitian :=
  HermitianRankTrace.hermitianHeatFlow_isHermitian
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The complete eta zero-window spectral heat flow is positive semidefinite
at every real heat scale. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u).PosSemidef :=
  HermitianRankTrace.hermitianHeatFlow_posSemidef
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The sign-bearing eta zero-window spectral heat flow remains Hermitian. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatFlow_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatFlow cutoff hT u).IsHermitian :=
  HermitianRankTrace.hermitianSignedHeatFlow_isHermitian
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The matrix-valued eta spectral heat family obeys the exact additive
semigroup law. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_add
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u v : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT (u + v) =
      pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u *
        pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT v :=
  HermitianRankTrace.hermitianHeatFlow_add
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u v

/-- The signed spectral heat flow is the literal eta zero-window matrix
multiplied by its complete heat flow. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatFlow_eq_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatFlow cutoff hT u =
      pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T *
        pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u :=
  HermitianRankTrace.hermitianSignedHeatFlow_eq_mul
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-! ## Complete continuous observables -/

/-- The eta spectral heat trace is the full finite sum over the actual
eigenvalues of the literal eta zero-window matrix. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_eq_sum_eigenvalues
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace cutoff hT u =
      ∑ i, Real.exp (-u *
        ((pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT).eigenvalues i) ^ 2) :=
  HermitianRankTrace.hermitianHeatTrace_eq_sum_eigenvalues
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The eta signed heat current is the complete sign-bearing sum over the
actual eigenvalues of the literal eta zero-window matrix. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent_eq_sum_eigenvalues
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent cutoff hT u =
      ∑ i,
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT).eigenvalues i *
          Real.exp (-u *
            ((pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT).eigenvalues i) ^ 2) :=
  HermitianRankTrace.hermitianSignedHeatCurrent_eq_sum_eigenvalues
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) u

/-- The singularly weighted eta signed heat current is genuinely integrable
over positive proper time. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent_integrableOn
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn
      (fun u : ℝ ↦ u ^ (-(1 / 2 : ℝ)) *
        pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent cutoff hT u)
      (Set.Ioi 0) :=
  HermitianRankTrace.hermitianSignedHeatCurrent_integrableOn
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)

/-! ## Exact eta inertia recovery -/

/-- The normalized signed heat integral of the literal eta zero-window
matrix is exactly its positive index minus its negative index. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSignature_eq_signedHeatIntegral
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (1 / Real.sqrt Real.pi) *
        ∫ u : ℝ in Set.Ioi 0,
          u ^ (-(1 / 2 : ℝ)) *
            pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent cutoff hT u =
      (HermitianRankTrace.posIndex
          (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) : ℝ) -
        (HermitianRankTrace.negIndex
          (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) : ℝ) :=
  HermitianRankTrace.signature_eq_signedHeatIntegral
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)

/-- The positive inertia of the literal eta zero-window matrix is exactly
reconstructed from its dimension, nullity, and signed heat current. -/
theorem pairedEtaTopPrefixFiniteZeroWindowPosIndex_eq_signedHeat
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (HermitianRankTrace.posIndex
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) : ℝ) =
      (1 / 2 : ℝ) *
        ((Fintype.card (d × Fin 2) : ℝ) -
          (pairedEtaTopPrefixFiniteZeroWindowZeroIndex cutoff hT : ℝ) +
          (1 / Real.sqrt Real.pi) *
            ∫ u : ℝ in Set.Ioi 0,
              u ^ (-(1 / 2 : ℝ)) *
                pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent cutoff hT u) :=
  HermitianRankTrace.posIndex_eq_signedHeat
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)

/-- The positive-index implementation used by the signed-heat layer obeys
the existing eta-specific `#critical + #upper` bound. -/
theorem pairedEtaTopPrefixFiniteZeroWindowHermitianRankTracePosIndex_le_critical_add_upper
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    HermitianRankTrace.posIndex
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) ≤
      (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card := by
  change HermitianInertia.posIndex
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) ≤ _
  exact pairedEtaTopPrefixFiniteZeroWindowBlock_posIndex_le_critical_add_upper
    cutoff hT

/-- Continuous signed-heat form of the checked eta inertia certificate.  It
is exact on the left and bounded by the represented critical and upper
off-line zero counts on the right. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSignedHeatCertificate_le_critical_add_upper
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (1 / 2 : ℝ) *
        ((Fintype.card (d × Fin 2) : ℝ) -
          (pairedEtaTopPrefixFiniteZeroWindowZeroIndex cutoff hT : ℝ) +
          (1 / Real.sqrt Real.pi) *
            ∫ u : ℝ in Set.Ioi 0,
              u ^ (-(1 / 2 : ℝ)) *
                pairedEtaTopPrefixFiniteZeroWindowSignedSpectralHeatCurrent cutoff hT u) ≤
      ((spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card : ℕ) := by
  rw [← pairedEtaTopPrefixFiniteZeroWindowPosIndex_eq_signedHeat cutoff hT]
  exact_mod_cast
    pairedEtaTopPrefixFiniteZeroWindowHermitianRankTracePosIndex_le_critical_add_upper
      cutoff hT

/-- The ordinary eta spectral heat trace converges exactly to the nullity of
the literal eta zero-window matrix. -/
theorem tendsto_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_atTop_zeroIndex
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace cutoff hT)
      atTop
      (nhds (pairedEtaTopPrefixFiniteZeroWindowZeroIndex cutoff hT : ℝ)) :=
  HermitianRankTrace.tendsto_hermitianHeatTrace_atTop_zeroIndex
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)

end

end RiemannGaussian
