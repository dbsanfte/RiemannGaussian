import RiemannGaussian.Hybrid.EtaGeometricReflectionSumTiltAbsorption

/-!
# Correlation ledger for literal eta reflection-sum atoms

The certificate reserve depends on correlations between distinct literal
reflection-even frame atoms.  An upper off-line atom is stored as a
half-scaled realification of a complex reflection sum, so estimating its
packed correlation directly would hide both the complex phase and the two
zero/reflection channels.

This module first separates the real-correlation reserve of arbitrary finite
complex vectors into their full Hermitian Gram reserve plus the square of the
discarded imaginary correlation.  It then identifies an upper--upper packed
eta correlation exactly with the real part of the corresponding complex
reflection-sum correlation and expands that complex quantity into all four
original-channel correlations.  Consequently the literal upper--upper
certificate reserve has an exact two-part nonnegative ledger, while the
four-channel arithmetic carrier remains available for subsequent estimates.

No cross-atom arithmetic bound or improved zero proportion is asserted here.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Full Hermitian Gram-determinant reserve of two finite complex vectors. -/
def finiteComplexVectorHermitianGramReserve
    {m : Type*} [Fintype m] (v w : m → ℂ) : ℝ :=
  finiteComplexVectorNormSq v * finiteComplexVectorNormSq w -
    ‖star w ⬝ᵥ v‖ ^ 2

/-- Reserve obtained when only the real part of the complex correlation is
retained. -/
def finiteComplexVectorRealCorrelationReserve
    {m : Type*} [Fintype m] (v w : m → ℂ) : ℝ :=
  finiteComplexVectorNormSq v * finiteComplexVectorNormSq w -
    (star w ⬝ᵥ v).re ^ 2

/-- Discarding the imaginary correlation adds its exact square to the full
Hermitian Gram reserve. -/
theorem finiteComplexVectorRealCorrelationReserve_eq_hermitian_add_im_sq
    {m : Type*} [Fintype m] (v w : m → ℂ) :
    finiteComplexVectorRealCorrelationReserve v w =
      finiteComplexVectorHermitianGramReserve v w +
        (star w ⬝ᵥ v).im ^ 2 := by
  unfold finiteComplexVectorRealCorrelationReserve
    finiteComplexVectorHermitianGramReserve
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The full Hermitian Gram reserve of two finite complex vectors is
nonnegative. -/
theorem finiteComplexVectorHermitianGramReserve_nonneg
    {m : Type*} [Fintype m] (v w : m → ℂ) :
    0 ≤ finiteComplexVectorHermitianGramReserve v w := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
    (WithLp.toLp 2 w : EuclideanSpace ℂ m)
    (WithLp.toLp 2 v : EuclideanSpace ℂ m)
  simp only [EuclideanSpace.inner_toLp_toLp] at h
  have hselfV :
      (dotProduct v (star v)).re = finiteComplexVectorNormSq v := by
    rw [dotProduct_comm]
    exact congrArg Complex.re (star_dot_self_eq_finiteComplexVectorNormSq v)
  have hselfW :
      (dotProduct w (star w)).re = finiteComplexVectorNormSq w := by
    rw [dotProduct_comm]
    exact congrArg Complex.re (star_dot_self_eq_finiteComplexVectorNormSq w)
  have hcorr : dotProduct v (star w) = star w ⬝ᵥ v :=
    dotProduct_comm _ _
  have hcorrSwap :
      ‖dotProduct w (star v)‖ = ‖star w ⬝ᵥ v‖ := by
    calc
      ‖dotProduct w (star v)‖ = ‖star v ⬝ᵥ w‖ := by
        rw [dotProduct_comm]
      _ = ‖starRingEnd ℂ (star w ⬝ᵥ v)‖ := by
        rw [Matrix.star_dotProduct]
        simp only [starRingEnd_apply]
      _ = ‖star w ⬝ᵥ v‖ := by
        exact norm_star (star w ⬝ᵥ v)
  unfold finiteComplexVectorHermitianGramReserve
  change
    ‖dotProduct v (star w)‖ * ‖dotProduct w (star v)‖ ≤
      (dotProduct w (star w)).re * (dotProduct v (star v)).re at h
  rw [hselfW, hselfV, hcorr, hcorrSwap] at h
  nlinarith

/-- The real-correlation reserve is nonnegative, with no reality hypothesis
on the original complex correlation. -/
theorem finiteComplexVectorRealCorrelationReserve_nonneg
    {m : Type*} [Fintype m] (v w : m → ℂ) :
    0 ≤ finiteComplexVectorRealCorrelationReserve v w := by
  rw [finiteComplexVectorRealCorrelationReserve_eq_hermitian_add_im_sq]
  exact add_nonneg (finiteComplexVectorHermitianGramReserve_nonneg v w)
    (sq_nonneg _)

/-- Original completed eta channel sampled on the geometric cutoff block. -/
def pairedEtaGeometricOriginalChannelVector
    (q : ℕ) (rho : NontrivialZetaZero) (n M : ℕ) : Fin M → ℂ := fun j ↦
  pairedEtaTopPrefixFiniteOriginalChannelTerm rho
    (pairedEtaGeometricHyperbolicCutoff q n j)

/-- Complex Hermitian correlation of two recovered upper reflection sums. -/
def pairedEtaGeometricUpperReflectionSumCorrelation
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℂ :=
  star (pairedEtaGeometricUpperFrameRecoveredVector q T zeta n M) ⬝ᵥ
    pairedEtaGeometricUpperFrameRecoveredVector q T rho n M

/-- The recovered reflection-sum correlation retains Hermitian conjugate
symmetry before taking its real part. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelation_swap
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperReflectionSumCorrelation q rho zeta n M =
      starRingEnd ℂ
        (pairedEtaGeometricUpperReflectionSumCorrelation
          q zeta rho n M) := by
  unfold pairedEtaGeometricUpperReflectionSumCorrelation dotProduct
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.star_apply, map_mul, starRingEnd_apply, star_star]
  ring

/-- A recovered upper reflection sum is exactly the sum of the original
completed channels at the zero and its reflected partner. -/
theorem pairedEtaGeometricUpperFrameRecoveredVector_eq_reflected_add_original
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperFrameRecoveredVector q T rho n M =
      pairedEtaGeometricOriginalChannelVector q
          (NontrivialZetaZero.conjugatePartner rho.1) n M +
        pairedEtaGeometricOriginalChannelVector q rho.1 n M := by
  funext j
  exact pairedEtaReflectionEvenFrameVector_upper_recover_reflectionSum
    (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T rho j

/-- Correlation of two sampled original-channel vectors is the existing
completed eta-prefix Gram kernel at the geometric cutoff family. -/
theorem pairedEtaGeometricOriginalChannelVector_correlation_eq
    (q : ℕ) (sigma rho : NontrivialZetaZero) (n M : ℕ) :
    star (pairedEtaGeometricOriginalChannelVector q sigma n M) ⬝ᵥ
        pairedEtaGeometricOriginalChannelVector q rho n M =
      pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        sigma rho := by
  rfl

/-- The complex upper reflection-sum correlation retains all four
zero/reflection original-channel correlations exactly. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelation_eq_four_channels
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperReflectionSumCorrelation q zeta rho n M =
      star (pairedEtaGeometricOriginalChannelVector q
          (NontrivialZetaZero.conjugatePartner zeta.1) n M) ⬝ᵥ
          pairedEtaGeometricOriginalChannelVector q
            (NontrivialZetaZero.conjugatePartner rho.1) n M +
        star (pairedEtaGeometricOriginalChannelVector q
          (NontrivialZetaZero.conjugatePartner zeta.1) n M) ⬝ᵥ
          pairedEtaGeometricOriginalChannelVector q rho.1 n M +
        star (pairedEtaGeometricOriginalChannelVector q zeta.1 n M) ⬝ᵥ
          pairedEtaGeometricOriginalChannelVector q
            (NontrivialZetaZero.conjugatePartner rho.1) n M +
        star (pairedEtaGeometricOriginalChannelVector q zeta.1 n M) ⬝ᵥ
          pairedEtaGeometricOriginalChannelVector q rho.1 n M := by
  unfold pairedEtaGeometricUpperReflectionSumCorrelation
  rw [pairedEtaGeometricUpperFrameRecoveredVector_eq_reflected_add_original,
    pairedEtaGeometricUpperFrameRecoveredVector_eq_reflected_add_original]
  have hstar :
      star
          (pairedEtaGeometricOriginalChannelVector q
              (NontrivialZetaZero.conjugatePartner zeta.1) n M +
            pairedEtaGeometricOriginalChannelVector q zeta.1 n M) =
        star (pairedEtaGeometricOriginalChannelVector q
            (NontrivialZetaZero.conjugatePartner zeta.1) n M) +
          star (pairedEtaGeometricOriginalChannelVector q zeta.1 n M) := by
    ext j
    simp [Pi.star_apply]
  rw [hstar]
  simp only [add_dotProduct, dotProduct_add]
  ring

/-- The four retained channels are precisely four instances of the existing
completed original-channel eta Gram kernel. -/
theorem pairedEtaGeometricUpperReflectionSumCorrelation_eq_four_originalChannelCorrelations
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperReflectionSumCorrelation q zeta rho n M =
      pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          (NontrivialZetaZero.conjugatePartner zeta.1)
          (NontrivialZetaZero.conjugatePartner rho.1) +
        pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          (NontrivialZetaZero.conjugatePartner zeta.1) rho.1 +
        pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          zeta.1 (NontrivialZetaZero.conjugatePartner rho.1) +
        pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          zeta.1 rho.1 := by
  rw [pairedEtaGeometricUpperReflectionSumCorrelation_eq_four_channels,
    pairedEtaGeometricOriginalChannelVector_correlation_eq,
    pairedEtaGeometricOriginalChannelVector_correlation_eq,
    pairedEtaGeometricOriginalChannelVector_correlation_eq,
    pairedEtaGeometricOriginalChannelVector_correlation_eq]

/-- Applying half-scaled hyperbolic realification to both vectors retains
exactly the real part of their original complex correlation. -/
theorem star_half_complexHyperbolicRealification_dot_half_eq_re
    {m : Type*} [Fintype m] (v w : m → ℂ) :
    star ((1 / 2 : ℂ) • complexHyperbolicRealification w) ⬝ᵥ
        ((1 / 2 : ℂ) • complexHyperbolicRealification v) =
      (((star w ⬝ᵥ v).re : ℂ)) := by
  have hstar :
      star ((1 / 2 : ℂ) • complexHyperbolicRealification w) =
        (1 / 2 : ℂ) • star (complexHyperbolicRealification w) := by
    ext x
    simp [Pi.star_apply]
  rw [hstar]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [star_complexHyperbolicRealification_dot_eq_four_mul_re]
  ring

/-- The packed correlation of two literal upper frame atoms is exactly the
real part of their complex reflection-sum correlation. -/
theorem pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_re
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    star (pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr zeta)) ⬝ᵥ
      pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) =
      ((pairedEtaGeometricUpperReflectionSumCorrelation
        q zeta rho n M).re : ℂ) := by
  let cutoff : Fin M → ℕ := fun k ↦
    pairedEtaGeometricHyperbolicCutoff q n k
  rw [pairedEtaReflectionEvenFrameVector_upper_eq_half_realification_reflectionSum
      cutoff T zeta,
    pairedEtaReflectionEvenFrameVector_upper_eq_half_realification_reflectionSum
      cutoff T rho]
  rw [star_half_complexHyperbolicRealification_dot_half_eq_re]
  unfold pairedEtaGeometricUpperReflectionSumCorrelation
  rw [pairedEtaGeometricUpperFrameRecoveredVector_eq_reflected_add_original,
    pairedEtaGeometricUpperFrameRecoveredVector_eq_reflected_add_original]
  rfl

/-- Thus the literal packed upper--upper correlation is the real part of the
explicit four-kernel completed eta ledger. -/
theorem pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_four_originalChannelCorrelations_re
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    star (pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr zeta)) ⬝ᵥ
      pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) =
      ((pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            (NontrivialZetaZero.conjugatePartner zeta.1)
            (NontrivialZetaZero.conjugatePartner rho.1) +
          pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            (NontrivialZetaZero.conjugatePartner zeta.1) rho.1 +
          pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            zeta.1 (NontrivialZetaZero.conjugatePartner rho.1) +
          pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            zeta.1 rho.1).re : ℂ) := by
  rw [pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_re,
    pairedEtaGeometricUpperReflectionSumCorrelation_eq_four_originalChannelCorrelations]

/-- The literal upper--upper certificate reserve is exactly the full complex
Gram reserve plus the squared imaginary reflection-sum correlation. -/
theorem pairedEtaReflectionEvenFrameUpperPairReserve_eq_hermitian_add_im_sq
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) *
        pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr zeta) -
        (star (pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr zeta)) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr rho)).re ^ 2 =
      finiteComplexVectorHermitianGramReserve
          (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M)
          (pairedEtaGeometricUpperFrameRecoveredVector q T zeta n M) +
        (pairedEtaGeometricUpperReflectionSumCorrelation
          q zeta rho n M).im ^ 2 := by
  rw [pairedEtaReflectionEvenFrameAtomNormSq_upper_eq_recovered,
    pairedEtaReflectionEvenFrameAtomNormSq_upper_eq_recovered,
    pairedEtaReflectionEvenFrameCorrelation_upper_upper_eq_re]
  exact finiteComplexVectorRealCorrelationReserve_eq_hermitian_add_im_sq
    (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M)
    (pairedEtaGeometricUpperFrameRecoveredVector q T zeta n M)

/-- Every literal upper--upper pair reserve is nonnegative, with its two
information-preserving nonnegative pieces exposed by the preceding ledger. -/
theorem pairedEtaReflectionEvenFrameUpperPairReserve_nonneg
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    0 ≤ pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) *
        pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr zeta) -
        (star (pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr zeta)) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr rho)).re ^ 2 := by
  rw [pairedEtaReflectionEvenFrameUpperPairReserve_eq_hermitian_add_im_sq]
  exact add_nonneg
    (finiteComplexVectorHermitianGramReserve_nonneg _ _)
    (sq_nonneg _)

/-- The actual multiplicity-weighted upper--upper summand occurring in the
complete reflection-even decorrelation reserve. -/
def pairedEtaGeometricUpperPairWeightedDecorrelationReserve
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
    pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
      (pairedEtaReflectionEvenFrameAtomNormSq
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr rho) *
          pairedEtaReflectionEvenFrameAtomNormSq
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr zeta) -
        (star (pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr zeta)) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr rho)).re ^ 2)

/-- The weighted upper--upper reserve keeps the positive multiplicity weight,
the full complex Gram reserve, and the additional imaginary-correlation
square as an exact ledger. -/
theorem pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperPairWeightedDecorrelationReserve
        q zeta rho n M =
      pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
        pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
          (finiteComplexVectorHermitianGramReserve
              (pairedEtaGeometricUpperFrameRecoveredVector q T rho n M)
              (pairedEtaGeometricUpperFrameRecoveredVector q T zeta n M) +
            (pairedEtaGeometricUpperReflectionSumCorrelation
              q zeta rho n M).im ^ 2) := by
  unfold pairedEtaGeometricUpperPairWeightedDecorrelationReserve
  rw [pairedEtaReflectionEvenFrameUpperPairReserve_eq_hermitian_add_im_sq]

/-- Every actual multiplicity-weighted upper--upper reserve summand is
nonnegative. -/
theorem pairedEtaGeometricUpperPairWeightedDecorrelationReserve_nonneg
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    0 ≤ pairedEtaGeometricUpperPairWeightedDecorrelationReserve
      q zeta rho n M := by
  rw [pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq]
  exact mul_nonneg
    (mul_nonneg
      (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr rho)).le
      (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr zeta)).le)
    (add_nonneg
      (finiteComplexVectorHermitianGramReserve_nonneg _ _)
      (sq_nonneg _))

end

end RiemannGaussian
