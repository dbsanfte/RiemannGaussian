import RiemannGaussian.EtaEnergyFiniteWindowMultiplicityRankTrace

/-!
# Pair-correlation expansion of the finite eta Frobenius mass

This module rewrites the coherent Frobenius mass of the genuine finite eta
zero-window block as an exact double sum over pairs of spectral zeta zeros.
The summand is the real part of the square of a Hermitian feature
correlation, weighted by the two analytic zero multiplicities.

The square is deliberately not replaced by an absolute square.  Its complex
phase records the signed off-diagonal cancellation that a future arithmetic
estimate must control.  This file proves the identity only; it assumes no
pair-correlation estimate.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

namespace HermitianInertia

/-- The Frobenius mass of a finite real-weighted sum of complex-symmetric
rank-one matrices is the corresponding signed, phase-preserving double
feature correlation. -/
theorem frobSq_finsetSum_real_smul_vecMulVec_eq_pairCorrelation
    {n α : Type*} [Fintype n] (s : Finset α)
    (w : α → ℝ) (v : α → n → ℂ) :
    frobSq (∑ a ∈ s, (w a : ℂ) • Matrix.vecMulVec (v a) (v a)) =
      ∑ a ∈ s, ∑ b ∈ s,
        (((w a * w b : ℝ) : ℂ) *
          (star (v b) ⬝ᵥ v a) ^ 2).re := by
  unfold frobSq
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_vecMulVec, RCLike.star_def,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  have hdot :
      star (v b) ⬝ᵥ ((star (v b) ⬝ᵥ v a) • v a) =
        (star (v b) ⬝ᵥ v a) ^ 2 := by
    unfold dotProduct
    rw [pow_two, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [smul_mul, mul_smul_comm, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, hdot]
  simp only [smul_eq_mul]
  apply congrArg Complex.re
  have hwstar : starRingEnd ℂ (w b : ℂ) = (w b : ℂ) := by simp
  rw [hwstar]
  rw [show ((w a * w b : ℝ) : ℂ) = (w a : ℂ) * (w b : ℂ) by
    push_cast
    rfl]
  ring

end HermitianInertia

/-- The exact signed zero-pair correlation associated with the complete
finite eta window. -/
def pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ spectralZetaZeroWindow T,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff sigma) ⬝ᵥ
          pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) ^ 2).re

/-- The literal finite eta block has Frobenius mass equal to the signed
double correlation over its genuine spectral zero window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_pairCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.frobSq
        (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) =
      pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowBlock
    pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass
  have h :=
    HermitianInertia.frobSq_finsetSum_real_smul_vecMulVec_eq_pairCorrelation
      (spectralZetaZeroWindow T)
      (fun rho ↦ (analyticZetaZeroMultiplicity rho : ℝ))
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff)
  convert h using 1
  all_goals norm_cast

/-- The previously named coherent entrywise mass is exactly the signed
zero-pair correlation mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_pairCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass cutoff T := by
  rw [← pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_coherentMass]
  exact
    pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_pairCorrelationMass
      cutoff T

end

end RiemannGaussian
