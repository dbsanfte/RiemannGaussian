import RiemannGaussian.ZetaSignedWindowMultiplicity
import RiemannGaussian.EtaCurrentMomentMoebiusInverse

/-!
# Actual zero simplicity, separation, and the original head current

The simultaneous window estimate proves simplicity and uniqueness near
the right boundary. Reflection transfers the multiplicity count to the
left boundary. In either edge layer the original current consequently
uses its literal head and full inverse sum, with multiplicity one proved
from the actual prime estimate rather than supplied as a premise.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every actual zero in the explicit edge window is simple. -/
theorem analyticZetaZeroMultiplicity_eq_one_in_signedEdgeWindow (y : ℝ) (hy : 1 ≤ |y|)
    (rho : NontrivialZetaZero) (hrho : InZetaSignedEdgeWindow y rho) :
    analyticZetaZeroMultiplicity rho = 1 := by
  have h := sum_multiplicity_le_one_in_signedEdgeWindow y hy {rho} (by simpa using hrho)
  simp only [Finset.sum_singleton] at h
  have := analyticZetaZeroMultiplicity_positive rho
  omega

/-- Two actual zeros in the same explicit right-edge window must be the same zero. -/
theorem eq_of_mem_signedEdgeWindow (y : ℝ) (hy : 1 ≤ |y|) (rho tau : NontrivialZetaZero)
    (hrho : InZetaSignedEdgeWindow y rho) (htau : InZetaSignedEdgeWindow y tau) : rho = tau := by
  by_contra hne
  have h := sum_multiplicity_le_one_in_signedEdgeWindow y hy {rho, tau} (by
    intro xi hxi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxi
    rcases hxi with rfl | rfl
    · exact hrho
    · exact htau)
  simp only [Finset.sum_pair hne] at h
  have := analyticZetaZeroMultiplicity_positive rho
  have := analyticZetaZeroMultiplicity_positive tau
  omega

/-- Distinct zeros in the indicated common right-edge layer have an explicit ordinate separation. -/
theorem signedEdgeWindowWidth_lt_im_sub_of_ne (rho tau : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) (hne : rho ≠ tau)
    (hrho : 1 - zetaSignedEdgeWindowWidth rho.1.im ≤ rho.1.re)
    (htau : 1 - zetaSignedEdgeWindowWidth rho.1.im ≤ tau.1.re) :
    zetaSignedEdgeWindowWidth rho.1.im < |tau.1.im - rho.1.im| := by
  by_contra h
  apply hne
  apply eq_of_mem_signedEdgeWindow rho.1.im hy rho tau
  · exact ⟨hrho, by simpa using (zetaSignedEdgeWindowWidth_pos rho.1.im).le⟩
  · exact ⟨htau, le_of_not_gt h⟩

/-- Reflection preserves the complete finite multiplicity count, giving the same bound at the left edge. -/
theorem sum_multiplicity_le_one_in_signedLeftEdgeWindow (y : ℝ) (hy : 1 ≤ |y|)
    (S : Finset NontrivialZetaZero)
    (hS : ∀ rho ∈ S, rho.1.re ≤ zetaSignedEdgeWindowWidth y ∧
      |rho.1.im - y| ≤ zetaSignedEdgeWindowWidth y) :
    ∑ rho ∈ S, analyticZetaZeroMultiplicity rho ≤ 1 := by
  have hi : Function.Injective NontrivialZetaZero.conjugatePartner :=
    (show Function.Involutive NontrivialZetaZero.conjugatePartner from
      NontrivialZetaZero.conjugatePartner_conjugatePartner).injective
  have h := sum_multiplicity_le_one_in_signedEdgeWindow y hy
    (S.image NontrivialZetaZero.conjugatePartner) (by
      intro tau htau
      obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp htau
      have hr := hS rho hrho
      constructor
      · simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
          Complex.one_re, Complex.conj_re]
        linarith [hr.1]
      · simpa using hr.2)
  simpa only [Finset.sum_image hi.injOn, analyticZetaZeroMultiplicity_conjugatePartner] using h

/-- An actual zero within the explicit width of either edge has analytic multiplicity one. -/
theorem analyticZetaZeroMultiplicity_eq_one_of_near_edge (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|)
    (hedge : min rho.1.re (1 - rho.1.re) ≤ zetaSignedEdgeWindowWidth rho.1.im) :
    analyticZetaZeroMultiplicity rho = 1 := by
  rcases min_le_iff.mp hedge with hleft | hright
  · have h := sum_multiplicity_le_one_in_signedLeftEdgeWindow rho.1.im hy {rho} (by
      intro tau htau
      have he : tau = rho := Finset.mem_singleton.mp htau
      subst tau
      exact ⟨hleft, by simpa using (zetaSignedEdgeWindowWidth_pos rho.1.im).le⟩)
    simp only [Finset.sum_singleton] at h
    have := analyticZetaZeroMultiplicity_positive rho
    omega
  · exact analyticZetaZeroMultiplicity_eq_one_in_signedEdgeWindow rho.1.im hy rho
      ⟨by linarith, by simpa using (zetaSignedEdgeWindowWidth_pos rho.1.im).le⟩

/-- Near either edge the original current has its exact full head inverse representation, with simplicity discharged. -/
theorem pairedEtaLeadingCurrent_eq_momentInverse_head_of_near_edge
    (rho : NontrivialZetaZero) (hy : 1 ≤ |rho.1.im|)
    (hedge : min rho.1.re (1 - rho.1.re) ≤ zetaSignedEdgeWindowWidth rho.1.im) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (∑ d ∈ Finset.Icc 1 (2 * (N + 2)),
        etaSignedCompletedPair
          (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
          (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho) 0
            (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)
          (pairedEtaHeadCompletedMoment rho N 0)
          (pairedEtaCompletedMomentInverseTerm rho 0 (pairedEtaLogTailCutoff (N + 2))
            (2 * (N + 2)) d)).re :=
  pairedEtaLeadingCurrent_eq_momentInverse_head rho
    (analyticZetaZeroMultiplicity_eq_one_of_near_edge rho hy hedge) N

end

end RiemannGaussian
