import RiemannGaussian.EtaEnergyFiniteWindowTrace
import RiemannGaussian.HermitianRankTrace.RankTrace

/-!
# Rank--trace inequality for the finite eta zero window

This module applies the rank--trace theorem adapted from Anthropic's
`zeta23` linear-algebra development to the literal finite eta block.  The
positive matrix is the critical-line block.  The Hermitian perturbation is
the off-line real block minus the off-line imaginary block.

The existing genuine-zero rank and positive-index bounds therefore give a
single unconditional inequality involving the exact eta traces and coherent
Frobenius mass.  The final theorem expands every matrix scalar into the
finite spectral sums already proved in the preceding module.  It assumes no
zero-location statement and supplies no arithmetic estimate for those sums.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-! ## Named scalar ledger -/

/-- The multiplicity-weighted critical-line squared-feature mass in one
finite eta window. -/
def pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralCriticalZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) *
      ∑ j, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j‖ ^ 2

/-- The signed off-line trace mass: twice the real-coordinate mass minus
twice the imaginary-coordinate mass over representatives of reflected
off-line pairs. -/
def pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  (∑ rho ∈ spectralUpperZetaZeroWindow T,
    (2 * analyticZetaZeroMultiplicity rho : ℝ) *
      ∑ j, ‖complexVectorReal
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2) -
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    (2 * analyticZetaZeroMultiplicity rho : ℝ) *
      ∑ j, ‖complexVectorImag
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2

/-- The coherent squared Frobenius mass of the complete eta zero window,
written entrywise as a finite spectral sum. -/
def pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ i, ∑ j, ‖∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) *
      pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j *
      pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho i‖ ^ 2

/-- The rank--trace inequality specialized to the literal finite eta
zero-window decomposition.  The count penalties are the genuine distinct
critical-line and upper off-line zero counts. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_rankTrace_ineq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T c : ℝ}
    (hT : 0 ≤ T) (hc : 0 < c) :
    c * HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T) -
      c ^ 2 / 4 * (spectralCriticalZetaZeroWindow T).card +
      2 * c * HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T -
          pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) -
      c ^ 2 * (spectralUpperZetaZeroWindow T).card ≤
        HermitianInertia.frobSq
          (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) := by
  classical
  let P := pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T
  let Q := pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T -
    pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T
  have hP : P.PosSemidef := by
    simpa only [P] using
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T
  have hQ : Q.IsHermitian := by
    exact
      (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef
          cutoff T).isHermitian.sub
        (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef
          cutoff T).isHermitian
  have hr : P.rank ≤ (spectralCriticalZetaZeroWindow T).card := by
    simpa only [P] using
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rank_le_card cutoff T
  have hbHermitianInertia :
      HermitianInertia.posIndex hQ ≤
        (spectralUpperZetaZeroWindow T).card := by
    simpa only [Q] using
      pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_posIndex_le_card
        cutoff T
  have hb :
      HermitianRankTrace.posIndex hQ ≤
        (spectralUpperZetaZeroWindow T).card := by
    simpa only [HermitianRankTrace.posIndex, HermitianInertia.posIndex] using
      hbHermitianInertia
  have h := HermitianRankTrace.rank_trace_ineq hP hQ hr hb hc
  have hdecomp :
      pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T = P + Q := by
    simpa only [P, Q] using
      pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
        cutoff hT
  rw [← hdecomp] at h
  simpa only [P, Q, HermitianRankTrace.rtrace, HermitianInertia.rtrace,
    HermitianRankTrace.frobSq, HermitianInertia.frobSq] using h

/-! ## Exact identification and rank--trace closure -/

/-- The named on-line scalar mass is exactly the real trace of the on-line
eta block. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq_mass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T) =
      pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T := by
  simpa only [pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass] using
    pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq cutoff T

/-- The named signed off-line scalar mass is exactly the real trace of the
off-line Hermitian difference. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq_mass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T -
          pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) =
      pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T := by
  simpa only [pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass] using
    pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq cutoff T

/-- The named coherent scalar mass is exactly the squared Frobenius mass of
the complete eta block. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_coherentMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.frobSq
        (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) =
      pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T := by
  simpa only [pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass] using
    pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq cutoff T

/-- Fully scalar rank--trace ledger for the genuine eta zero window.  It
retains the coherent spectral sum on the right and charges the actual
critical-line and upper off-line zero counts on the left. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_rankTrace_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T c : ℝ}
    (hT : 0 ≤ T) (hc : 0 < c) :
    c * pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T -
      c ^ 2 / 4 * (spectralCriticalZetaZeroWindow T).card +
      2 * c * pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T -
      c ^ 2 * (spectralUpperZetaZeroWindow T).card ≤
        pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T := by
  simpa only [
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq_mass,
      pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq_mass,
      pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_coherentMass] using
    pairedEtaTopPrefixFiniteZeroWindowBlock_rankTrace_ineq cutoff hT hc

/-- The `c = 2` rank--trace ledger, rearranged so the critical-line count is
the upper bound.  This is the concrete finite-window interface for future
eta-arithmetic trace/Frobenius estimates. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_rankTrace_two_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    2 * pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
      4 * pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T -
      4 * (spectralUpperZetaZeroWindow T).card -
      pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T ≤
        (spectralCriticalZetaZeroWindow T).card := by
  have h := pairedEtaTopPrefixFiniteZeroWindow_rankTrace_ledger
    cutoff hT (c := 2) (by norm_num)
  norm_num at h
  linarith

end

end RiemannGaussian
