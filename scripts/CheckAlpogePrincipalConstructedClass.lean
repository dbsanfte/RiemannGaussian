import CheckAlpogePrincipalTrueGeometry
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DutySevenLibrary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffFieldRootsOfUnityTypePrimesHermitianStages

/-! # Counting and selected weights in the archive's constructed family class -/

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.StandardLattice
open GlobalTheory.Fc GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Core.Cls

/-- Updating the division lattice in a constructed point preserves the target
dimension, the Weyl degrees and the two roots in its coefficient field. -/
theorem principal_geometry_of_built_point {K : Ctx} (β : BPt K) :
    BaseVolumeEqualsMass β.D ∧ SigmaDegreeTwoSidedBoundOfGap β.D ∧ RootsG β.D := by
  refine ⟨volume_mass_of_dimension_formula β.O ?_, sigma_degree_of_weyl_dimension ?_,
    coeffField_rootsOfUnity_typePrimes_hermitianStages β.X⟩
  · have he : β.D.what₂.Dstar = β.X.B.Dstar :=
      (β.D.Dstar_eq β.D.u₀).symm.trans (β.X.C.A_Dstar _)
    rw [he, β.c.isOver.sizes.2]
    unfold DsPre
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (β.c.dsig_eq τ).symm
  · exact fun ρ => (β.c.dsig_eq ρ).trans (DsLow.trueDsig_eq_dimV _ _)

/-- Every bundle in the constructed class is tied to its originating point.
The bundle supplies the symmetric columns and the point supplies the mass, degree and roots. -/
theorem principal_geometry_of_bundle_selection {ε : ℝ} (Fm : FamP ε) {Q : V4.Slot} {Lk : LkT Bundle}
    {E : Par → BdP Bundle} {𝒜 : FamClass} {σ : RawSel Bundle 𝒜} (hs : IsSel Q Lk E 𝒜 σ) (hc : 𝒜 Fm) :
    ChosenWall Fm ∧ CountF Fm ∧ HasSymmetricColumnsAndRoots Fm := by
  obtain ⟨κ, _, hclass, hbuilt⟩ := hs Fm hc
  have hduty := (GlobalTheory.EX.DQ.familyClass_sevenDuties_and_stableLattices _ Fm hclass).1
  have hw := (GlobalTheory.EX.DQ.duty_seven_library ε Fm hduty).2.2.2.2.1
  have hp : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
      BaseVolumeEqualsMass (Fm.D x i) ∧ SigmaDegreeTwoSidedBoundOfGap (Fm.D x i) ∧
      RootsG (Fm.D x i) ∧ Nonempty (Formalism.L2.Forms.ColsTiedSym (Fm.D x i)) := by
    intro x hx i
    obtain ⟨K, β, _, _, _, _, he⟩ := (hbuilt x hx i).1
    have e : Fm.D x i = β.D := congrArg Sigma.fst he
    have hg := e.symm ▸ principal_geometry_of_built_point β
    exact ⟨hg.1, hg.2.1, hg.2.2, ⟨(σ Fm hc x hx i).R.T.cols⟩⟩
  refine ⟨hw, principal_count_of_mass_and_degree (fun x hx i => ⟨(hp x hx i).1, (hp x hx i).2.1⟩),
    Fm.x1 + 1, fun x hx i => ?_⟩
  obtain ⟨_, _, hr, hcols⟩ := hp x (by linarith) i
  exact ⟨hcols, fun k => (hr k).1⟩

theorem principal_geometry_of_constructed_class {ε : ℝ} (Fm : FamP ε) {Q : V4.Slot} {Lk : LkT Bundle}
    {E : Par → BdP Bundle} (hc : cls Q Lk E Fm) :
    ChosenWall Fm ∧ CountF Fm ∧ HasSymmetricColumnsAndRoots Fm :=
  principal_geometry_of_bundle_selection Fm (pick_isSel Q Lk E) hc

/-- A winning principal comparison design in the archive's constructed class
suffices at each exponent loss. The class supplies the geometric counts and weights. -/
theorem rh_of_principal_constructed_class (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧
    ∃ (Q : V4.Slot) (Lk : LkT Bundle) (E : Par → BdP Bundle), cls Q Lk E D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_selected_geometry
  intro δ hδ
  obtain ⟨ε, D, hl, hC, hH, Q, Lk, E, hc⟩ := h δ hδ
  exact ⟨ε, D, hl, hC, hH, principal_geometry_of_constructed_class D.family hc⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_constructed_class
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
