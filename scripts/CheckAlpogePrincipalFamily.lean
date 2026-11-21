import CheckAlpogeTiedPrincipal
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

/-! # The archive's connected geometric family at the principal character -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

/-- The geometric connection is required only at the principal character and
at window exponent 3/2. The archive's TopG implies this restriction. -/
def PrincipalFamilyConnection : Prop :=
  HostExW (3/2) (GChi PChar.one).req → FamilyClassConnected ((GChi PChar.one).cls (3/2))

theorem principal_family_connection_of_topG (hg : TopG) : PrincipalFamilyConnection :=
  fun hhost => hg (3/2) (GChi PChar.one) (by norm_num) hhost (hypV_of_cls PChar.one (3/2))

/-- One connected family class at the principal character gives the exact
zeta endpoint through the archive's geometric comparison. -/
theorem rh_of_principal_connected_family (hf : FamilyClassConnected ((GChi PChar.one).cls (3/2))) :
    RiemannHypothesis := by
  apply rh_of_tied_principal_level (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm)
    (la := 3/2) (by norm_num) (UpperTheory.Comparison₂.level_gm_le_on_family_scales _)
  obtain ⟨eD,eL,ε₁,h₁,hFam⟩ := hf
  refine ⟨eD,eL,ε₁,h₁,fun ε hε hsmall => ?_⟩
  obtain ⟨Fm,hcls,htied⟩ := hFam ε hε hsmall
  exact ⟨Fm,eFamC_of_cls PChar.one (3/2) Fm hcls,hcls.1,htied⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.principal_family_connection_of_topG,
      ``RiemannGaussian.AlpogeWindow.rh_of_principal_connected_family] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
