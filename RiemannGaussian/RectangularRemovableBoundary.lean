/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticHorizontalBoundary
import RiemannGaussian.RectangularPoleIntegral

/-!
# Finite residue formulas with removable boundary points

Literal meromorphic functions may use discontinuous totalized values at
removable boundary singularities. Finite exceptional sets do not affect
the four line integrals. Full Laurent subtraction therefore still gives
the exact residue formula when each selected boundary point has zero
principal part and zero residue.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- Finite changes to a complex function leave its oriented rectangular
boundary integral unchanged, including changes at the corners. -/
theorem rectangularBoundaryIntegral_eq_of_finite_exception
    {f g : ℂ → ℂ} (S : Finset ℂ) (he : ∀ z ∉ S, f z = g z) (l r b u : ℝ) :
    rectangularBoundaryIntegral l r b u f = rectangularBoundaryIntegral l r b u g := by
  have hv (v : ℝ) : (∫ y : ℝ in b..u, f ((v : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in b..u, g ((v : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral_comp_eq_of_finite_exception S he
    intro x y h
    simpa using congrArg Complex.im h
  unfold rectangularBoundaryIntegral
  rw [horizontalIntervalIntegral_eq_of_finite_exception S he l r b,
    horizontalIntervalIntegral_eq_of_finite_exception S he l r u, hv r, hv l]

/-- Complete Laurent regularization gives the exact finite residue
formula even when the selected finite set includes removable boundary
points. Such points have their entire principal part proved zero. -/
theorem rectangularBoundaryIntegral_eq_residues_of_removable_boundary
    (l r b u : ℝ) (S : Finset ℂ) (f : ℂ → ℂ)
    (order : ℂ → ℕ) (numerator : ℂ → ℂ → ℂ)
    (hSU : ∀ c ∈ S,
      c ∈ Complex.Rectangle ((l : ℂ) + (b : ℂ) * I) ((r : ℂ) + (u : ℂ) * I))
    (hS : ∀ c ∈ S,
      (l < c.re ∧ c.re < r ∧ b < c.im ∧ c.im < u) ∨
      ((∀ z, poleTaylorPrincipalPart (order c) (numerator c) c z = 0) ∧
        poleTaylorResidue (order c) (numerator c) c = 0))
    (hint : rectangularBoundaryIntegrable l r b u f)
    (hoff : ∀ z ∈ Complex.Rectangle ((l : ℂ) + (b : ℂ) * I) ((r : ℂ) + (u : ℂ) * I),
      z ∉ S → AnalyticAt ℂ f z)
    (hnum : ∀ c ∈ S, AnalyticAt ℂ (numerator c) c)
    (hmodel : ∀ c ∈ S, f =ᶠ[𝓝[≠] c] fun z => numerator c z / (z - c) ^ order c) :
    rectangularBoundaryIntegral l r b u f =
      (2 * Real.pi : ℝ) * I * ∑ c ∈ S, poleTaylorResidue (order c) (numerator c) c := by
  obtain ⟨H, hH, hHeq⟩ := exists_finitePole_analytic_regularization _ S f order numerator
    hSU hoff hnum hmodel
  have hHint : rectangularBoundaryIntegral l r b u H = 0 :=
    rectangularBoundaryIntegral_eq_zero_of_differentiableOn l r b u H
      (fun z hz => (hH z hz).differentiableAt.differentiableWithinAt)
  have hparts : ∀ c ∈ S,
      rectangularBoundaryIntegrable l r b u
        (poleTaylorPrincipalPart (order c) (numerator c) c) := by
    intro c hc
    rcases hS c hc with hs | hz
    · exact rectangularBoundaryIntegrable_poleTaylorPrincipalPart _ _ _
        hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    · rw [funext hz.1]
      exact ⟨intervalIntegrable_const, intervalIntegrable_const,
        intervalIntegrable_const, intervalIntegrable_const⟩
  have hsum := rectangularBoundaryIntegrable_finsetSum l r b u S _ hparts
  change rectangularBoundaryIntegrable l r b u (finitePolePrincipalSum S order numerator) at hsum
  have he : rectangularBoundaryIntegral l r b u
      (fun z => f z - finitePolePrincipalSum S order numerator z) = 0 := by
    rw [rectangularBoundaryIntegral_eq_of_finite_exception S
      (fun z hz => (hHeq z hz).symm) l r b u, hHint]
  rw [rectangularBoundaryIntegral_sub l r b u hint hsum] at he
  rw [sub_eq_zero.mp he]
  unfold finitePolePrincipalSum
  rw [rectangularBoundaryIntegral_finsetSum l r b u S _ hparts, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rcases hS c hc with hs | hz
  · exact rectangularBoundaryIntegral_poleTaylorPrincipalPart _ _ _
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  · rw [funext hz.1, hz.2]
    simp [rectangularBoundaryIntegral]

end
end RiemannGaussian
