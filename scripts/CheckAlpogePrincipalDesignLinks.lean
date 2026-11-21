import CheckAlpogePrincipalAdelicDesigns
import Formalism.LocalToGlobal.NormalizedHeckeFactors.EtaClosed
import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens

/-! # Group and Hecke comparisons for individual principal designs -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2

/-- After a choice of exponent, one threshold works for every sufficiently
large selected family. The chosen design supplies the Mertens estimate.
Compatible group lattices and tied local Hecke data supply two of the
geometric comparisons in the principal criterion. -/
theorem principal_design_group_and_hecke :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ K : TransportedAlt,
      ∀ (Fm : FamP ε) (CH C0 : ℝ), Fm.Large K CH → ChosenE Fm C0 CH →
      Formalism.L2.G.GroupCompatibilityFamily Fm →
      (∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i))
        (_ : NormalizedLocalCompatibility (Fm.D x i) M), HeckeTied (Fm.D x i) M) →
      LinkEta Fm ∧ LinkG Fm := by
  let fam : FamClass := fun Fm => Formalism.L2.G.GroupCompatibilityFamily Fm ∧ ∃ C0 CH, ChosenE Fm C0 CH
  have hL := Formalism.L2.G.linkG_concrete5 fam (Closed.of_class fun _ _ h => h.1)
    (Closed.of_class fun Fm _ h => by
      obtain ⟨C0,CH,hchosen⟩ := h.2
      exact admissible_tops_mertens Fm (topsF_of_chosenE Fm hchosen))
  obtain ⟨ε₀, h₀, hL⟩ := hL
  refine ⟨ε₀, h₀, fun ε hε hsmall => ?_⟩
  obtain ⟨K, hK⟩ := hL ε hε hsmall
  exact ⟨K, fun Fm CH C0 hlarge hchosen hgroup hhecke =>
    ⟨linkEta_closed Fm hhecke, hK Fm CH ⟨hgroup,C0,CH,hchosen⟩ hlarge⟩⟩

/-- Level-zero forms are one of the fields of the existing group comparison. -/
theorem principal_design_group_forms {ε : ℝ} (Fm : FamP ε)
    (hg : Formalism.L2.G.GroupCompatibilityFamily Fm) : HasLevelZeroForms Fm := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨max a (Fm.x1 + 1), fun x hx i u => ?_⟩
  have hx₁ := le_of_max_le_right hx
  obtain ⟨G⟩ := ha x (le_of_max_le_left hx) i (by linarith)
  exact ⟨G.forms u⟩

/-- The group data used for the Hecke comparison already contains the level-zero
forms at every word. It supplies the rank and frame estimates on the same family. -/
theorem principal_design_group_rank_and_share {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hTu : TuSize Fm)
    (hg : Formalism.L2.G.GroupCompatibilityFamily Fm) :
    J.MuRank Fm ∧ ∃ b : ℝ, ∀ x ≥ b, ∀ i : Fm.Ix x, ∃ de : ℝ,
      0 ≤ de ∧ Real.sqrt de ≤ Real.exp (-(x ^ (ε/8))) ∧ ∀ u,
        ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤ de * ((Fm.D x i).duS u : ℝ) :=
  principal_family_rank_and_share_of_forms Fm hε hTu (principal_design_group_forms Fm hg)

/-- The group data alone supply the ramified rank required by the design criterion. -/
theorem rh_of_principal_group_designs (h : ∀ δ : ℝ, 0 < δ → ∃ ε eD eL : ℝ,
    0 < ε ∧ (eD + eL + 7) * ε ≤ δ ∧
      ∃ D : PrincipalComparisonData ε eD eL, Formalism.L2.G.GroupCompatibilityFamily D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_adelic_designs
  intro δ hδ
  obtain ⟨ε, eD, eL, he, hloss, D, hD⟩ := h δ hδ
  exact ⟨ε, eD, eL, he, hloss, D, principal_design_group_forms _ hD⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.principal_design_group_and_hecke,
      ``RiemannGaussian.AlpogeWindow.principal_design_group_rank_and_share,
      ``RiemannGaussian.AlpogeWindow.rh_of_principal_group_designs] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
