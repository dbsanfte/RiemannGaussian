/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RectangularRemovableBoundary
import RiemannGaussian.SuzukiCarrierRealBoundary

/-!
# The actual signed Suzuki contour with its bottom on the real axis

Real xi nodes are permitted on the bottom edge. Their complete principal
parts vanish for every mixed pair without a repeated real node, so the
finite contour has its actual real Gram bottom and its complete original
xi source and carrier-pole correction. No boundary-limit hypothesis is
left in this comparison. The large vertical sides and signed pole sum
still require independent estimates before a global exclusion follows.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- An upper rectangle with a literal real bottom and three safe side
lines. Real xi zeros on its bottom edge are explicitly allowed. -/
def SuzukiXiCarrierRealRectangleAdmissible (l r u : ℝ) : Prop :=
  l < r ∧ 0 < u ∧ ∀ c ∈ suzukiXiCarrierSingularSet,
    c.re ≠ l ∧ c.re ≠ r ∧ c.im ≠ u

/-- Actual real-bottom admissible rectangles exist at every outer
scale at least one, with each outer coordinate within one of that scale. -/
theorem exists_suzukiXiCarrierRealRectangleAdmissible {R : ℝ} (hR : 1 ≤ R) :
    ∃ l r u : ℝ, SuzukiXiCarrierRealRectangleAdmissible l r u ∧
      (-R - 1 < l ∧ l < -R) ∧ (R < r ∧ r < R + 1) ∧ R < u ∧ u < R + 1 := by
  obtain ⟨l, r, _b, u, hadm, hl, hr, _hb, hu⟩ :=
    exists_suzukiXiCarrierUpperRectangleAdmissible hR (delta := 1) (by norm_num)
  exact ⟨l, r, u, ⟨hadm.1, by linarith [hu.1], fun c hc =>
    ⟨(hadm.2.2 c hc).1, (hadm.2.2 c hc).2.1, (hadm.2.2 c hc).2.2.2⟩⟩, hl, hr, hu⟩

/-- Every side of the actual real-bottom mixed contour is integrable
for a noncolliding pair; real exceptional values cause no missing premise. -/
theorem rectangularBoundaryIntegrable_suzukiXiMixedCarrierChannel_real
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    rectangularBoundaryIntegrable l r 0 u (suzukiXiMixedCarrierChannel rho sigma) := by
  have htop (x : ℝ) : (x : ℂ) + (u : ℂ) * I ∉ suzukiXiCarrierSingularSet := by
    intro hc
    exact (hadm.2.2 _ hc).2.2 (by simp)
  have hleft (y : ℝ) : (l : ℂ) + (y : ℂ) * I ∉ suzukiXiCarrierSingularSet := by
    intro hc
    exact (hadm.2.2 _ hc).1 (by simp)
  have hright (y : ℝ) : (r : ℂ) + (y : ℂ) * I ∉ suzukiXiCarrierSingularSet := by
    intro hc
    exact (hadm.2.2 _ hc).2.1 (by simp)
  have hcont (γ : ℝ → ℂ) (hγ : Continuous γ) (hne : ∀ t, γ t ∉ suzukiXiCarrierSingularSet) :
      Continuous (fun t => suzukiXiMixedCarrierChannel rho sigma (γ t)) :=
    continuous_comp_of_forall_analyticAt _ _ hγ
      (fun t => analyticAt_suzukiXiMixedCarrierChannel_of_not_mem rho sigma (hne t))
  refine ⟨?_, (hcont _ (by fun_prop) htop).intervalIntegrable l r,
    (hcont _ (by fun_prop) hright).intervalIntegrable 0 u,
    (hcont _ (by fun_prop) hleft).intervalIntegrable 0 u⟩
  simpa only [ofReal_zero, zero_mul, add_zero] using
    (integrable_suzukiXiMixedCarrierChannel_ofReal_of_no_real_collision rho sigma h).intervalIntegrable

/-- The original first mixed contour with real bottom equals its
complete finite residue sum. Every boundary xi singularity is removed
using its proved zero principal part, including multiple xi nodes. -/
theorem suzukiXiMixedCarrierChannel_real_rectangle_eq_residues
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    rectangularBoundaryIntegral l r 0 u (suzukiXiMixedCarrierChannel rho sigma) =
      (2 * Real.pi : ℝ) * I *
        ∑ c ∈ suzukiXiCarrierPoleWindow l r 0 u, suzukiXiMixedCarrierLocalResidue rho sigma c := by
  apply rectangularBoundaryIntegral_eq_residues_of_removable_boundary
    l r 0 u (suzukiXiCarrierPoleWindow l r 0 u) (suzukiXiMixedCarrierChannel rho sigma)
    suzukiXiMixedCarrierLocalOrder (suzukiXiMixedCarrierLocalNumerator rho sigma)
  · exact fun c hc => (mem_suzukiXiCarrierPoleWindow.mp hc).1
  · intro c hc
    have hmem := mem_suzukiXiCarrierPoleWindow.mp hc
    have hbox : (l ≤ c.re ∧ c.re ≤ r) ∧ 0 ≤ c.im ∧ c.im ≤ u := by
      simpa [Complex.Rectangle, Complex.mem_reProdIm,
        uIcc_of_le hadm.1.le, uIcc_of_le hadm.2.1.le] using hmem.1
    by_cases him : c.im = 0
    · right
      obtain ⟨x, rfl⟩ : ∃ x : ℝ, c = (x : ℂ) :=
        ⟨c.re, Complex.ext (by simp) (by simpa using him)⟩
      have hxi : riemannXiSpectral (x : ℂ) = 0 := hmem.2.elim id
        riemannXiSpectral_eq_zero_of_suzukiXiEValue_ofReal_eq_zero
      refine ⟨suzukiXiMixedCarrierLocalPrincipalPart_eq_zero_ofReal rho sigma h hxi, ?_⟩
      have hp := suzukiXiMixedCarrierLocalPrincipalPart_eq_zero_ofReal rho sigma h hxi ((x : ℂ) + 1)
      simpa [suzukiXiMixedCarrierLocalOrder, hxi, poleTaylorPrincipalPart, poleTaylorResidue] using hp
    · left
      have hn := hadm.2.2 c hmem.2
      exact ⟨lt_of_le_of_ne hbox.1.1 hn.1.symm, lt_of_le_of_ne hbox.1.2 hn.2.1,
        lt_of_le_of_ne hbox.2.1 (Ne.symm him), lt_of_le_of_ne hbox.2.2 hn.2.2⟩
  · exact rectangularBoundaryIntegrable_suzukiXiMixedCarrierChannel_real rho sigma h hadm
  · intro z hz hn
    exact analyticAt_suzukiXiMixedCarrierChannel_of_not_mem rho sigma
      (fun hb => hn (mem_suzukiXiCarrierPoleWindow.mpr ⟨hz, hb⟩))
  · exact fun c _ => analyticAt_suzukiXiMixedCarrierLocalNumerator rho sigma c
  · exact fun c _ => suzukiXiMixedCarrierChannel_eventually_eq_local_model rho sigma c

/-- The actual real-bottom contour separates its reflected xi source
from every genuine carrier pole, retaining all complex residues and orders. -/
theorem suzukiXiMixedCarrierChannel_real_rectangle_eq_source_add_poles
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    rectangularBoundaryIntegral l r 0 u (suzukiXiMixedCarrierChannel rho sigma) =
      (2 * Real.pi : ℝ) * I *
        (suzukiXiMixedContourXiSource rho sigma l r 0 u +
          ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u,
            suzukiXiMixedCarrierPoleResidue rho sigma c) := by
  rw [suzukiXiMixedCarrierChannel_real_rectangle_eq_residues rho sigma h hadm,
    suzukiXiMixedCarrierLocalResidue_sum_eq_source_add_poles]

/-- The actual truncated real Gram plus all oriented outer sides equals
the reflected xi source and full Hermitian carrier-pole correction. This
has no displaced-bottom or unproved real-axis-limit assumption. -/
theorem suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) {l r u : ℝ}
    (hadm : SuzukiXiCarrierRealRectangleAdmissible l r u) :
    suzukiXiTruncatedBoundaryCarrierGramKernel rho sigma l r +
        suzukiXiOtherSidesGram rho sigma l r 0 u =
      (Real.pi : ℂ) *
        (suzukiXiMixedContourXiSource rho sigma l r 0 u +
          starRingEnd ℂ (suzukiXiMixedContourXiSource sigma rho l r 0 u) +
          (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u, suzukiXiMixedCarrierPoleResidue rho sigma c) +
          starRingEnd ℂ (∑ c ∈ suzukiXiCarrierGenuinePoleWindow l r 0 u,
            suzukiXiMixedCarrierPoleResidue sigma rho c)) := by
  rw [← suzukiXiDisplacedBottomGram_zero_eq_truncatedGram rho sigma h]
  have heq : suzukiXiDisplacedBottomGram rho sigma l r 0 +
      suzukiXiOtherSidesGram rho sigma l r 0 u =
      (rectangularBoundaryIntegral l r 0 u (suzukiXiMixedCarrierChannel rho sigma) -
        starRingEnd ℂ (rectangularBoundaryIntegral l r 0 u (suzukiXiMixedCarrierChannel sigma rho))) /
          (2 * I) := by
    rw [← suzukiXiMixedCarrierBottom_add_otherSides, ← suzukiXiMixedCarrierBottom_add_otherSides]
    unfold suzukiXiDisplacedBottomGram suzukiXiOtherSidesGram
    rw [map_add]
    ring
  rw [heq, suzukiXiMixedCarrierChannel_real_rectangle_eq_source_add_poles rho sigma h hadm,
    suzukiXiMixedCarrierChannel_real_rectangle_eq_source_add_poles sigma rho
      (suzukiXiMixed_no_real_collision_symm rho sigma h) hadm]
  simp only [map_mul, map_add, conj_ofReal, conj_I]
  push_cast
  field_simp
  ring

end
end RiemannGaussian
