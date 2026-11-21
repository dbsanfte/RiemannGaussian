import CheckAlpogePrincipalSymmetricDesigns
import CheckAlpogePrincipalDimensionCounts
import Formalism.LocalToGlobal.GlobalTheory.TransposeBaseMatrixInfinity
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice

/-! # The geometric suppliers for a principal design with symmetric columns -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.L2.Forms
open Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

/-- At a word with finite level character and trivial stabilizers, the
archive's three geometric theorems supply the inputs to the congruence bound. -/
theorem principal_hecke_of_symmetric_columns (D : D7) (F : ColsTiedSym D) (u : D.what₂.Word)
    (hs : product_first_zeroth_parts.HidaSetting D u) (h : SymmetricLevelInputs F u) :
    SecondBranchInclusionLength D u ∧ HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u := by
  have ht : RT.FormsTwistCompatibilityFamily D u := ⟨_, _, F.forms u, h.1⟩
  have hf : RT.ConcreteFormsLevelZero D u := ⟨ht, h.2⟩
  exact ⟨LemB.second_branch_all_members D u hs hf,
    PI.IntegralAtBasePointLattice.integral_at_t0_lattice D u ht h.2 hs,
    UnramifiedTrace.hecke_ramified_zero_all D u hs hf⟩

/-- The base and division slopes on a counted principal family now follow
from symmetric columns with roots of the two auxiliary prime orders. -/
theorem rh_of_principal_symmetric_geometry (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧
    D.family.CoverAll ∧ CountF D.family ∧ HasSymmetricColumnsAndRoots D.family) : RiemannHypothesis :=
  rh_of_principal_symmetric_comparisons ColValS.colValOfTiedS_holds principal_hecke_of_symmetric_columns h

/-- The counting input can be supplied entirely by the dimension ratio at one
reference word and its logarithmic variation over all words. -/
theorem rh_of_principal_symmetric_rank_counts (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ D.family.CoverAll ∧
    ReferenceRankCount D.family ∧ HasSymmetricColumnsAndRoots D.family) : RiemannHypothesis := by
  apply rh_of_principal_symmetric_geometry
  intro δ hδ
  obtain ⟨ε, D, hloss, habs, hch, hc, hr, hs⟩ := h δ hδ
  exact ⟨ε, D, hloss, habs, hch, hc, principal_count_of_reference_ranks D.family hr, hs⟩

/-- Only the absolute rank bounds at the reference word remain in the count. -/
theorem rh_of_principal_reference_bounds (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ D.family.CoverAll ∧
    ReferenceRankBounds D.family ∧ HasSymmetricColumnsAndRoots D.family) : RiemannHypothesis := by
  apply rh_of_principal_symmetric_rank_counts
  intro δ hδ
  obtain ⟨ε, D, hloss, habs, hch, hc, hb, hs⟩ := h δ hδ
  exact ⟨ε, D, hloss, habs, hch, hc, referenceRankCount_of_bounds D.family hb, hs⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_reference_bounds
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
