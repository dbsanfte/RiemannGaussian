import CheckAlpogePrincipalArchivedBundleChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkBrest
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosedFamilyAdmissibleTwistLink
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelectionClosedOfWuDecay
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WireSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkIrr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkAltAltBis

/-! # Comparisons on the selected reciprocity-based principal family -/

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk
open Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
open Formalism.HC Formalism.L2.Top3 Formalism.L2.Top4
open GlobalTheory.EX GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
open Formalism.MainNotions.StandardLattice.HarishChandraReduction
open UpperTheory.Top

set_option maxHeartbeats 4000000 in
/-- The reciprocity-based rows supply the weighted, irreducibility, divisor and
spectral comparisons on the very same family as the principal rank bound. -/
theorem rh_of_principal_archived_bundle_rows
    {Q : V4.Slot} {hL : UpperTheory.Zero.LLC.RecTExists} {p : Parameters hL}
    {E : Par → BdP BundleCondition}
    (h : HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)
    (hs : IsSel Q (BundleLinkage p) E h.𝒜 h.σ)
    (hd : DC.DesignChoices (DC.WithTw fun Fm => h.𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) 3 (fun _ => cTmin))
    (green : GlobalTheory.GLq.Green) : RiemannHypothesis := by
  let sel : Formalism.L2.TwistSelection h.𝒜 := familySelection h.σ
  let selS : SelectionSpectralCondition h.𝒜 sel := spectralConditionOfRawSelection h.σ
  let selP : BaseLevelTiedChoiceAlt h.𝒜 sel := baseLevelChoiceOfRawSelection h.σ
  let selDH : SelectionDefiniteHeightCondition h.𝒜 sel := definiteHeightOfRawSelection h.σ
  let selC : ColumnChoiceCompatibleSelection h.𝒜 sel selP :=
    fun Fm hc x hx k i => (columnChoiceOfRawSelection h.σ Fm hc x hx k i).toS
  let selB : SelectionBundle h.𝒜 sel selS selP selDH selC := selectionBundleOfRawSelection h.σ
  have dv := fun {ε : ℝ} (Fm : FamP ε) hc x hx k i =>
    (GlobalTheory.Cp.divRows3G_iff _).1 (h.hDivG Fm hc x hx k i)
  have rows : Closed (D3 3 h.𝒜) fun Fm CH => ∀ hc : D3 3 h.𝒜 Fm,
      RowsAtSelAlt sel (indefiniteRealisationChoiceOfSelection selB)
        (fun Fm hc x hx k i C CH => Formalism.L2.Top4Wire2.DefRowsFAlt
          (indefiniteRealisationChoiceOfSelection selB) Fm hc x hx k i C CH)
        (SingleMapCondition selB) Fm (d3_a hc) CH := h.rRows.imp fun _ _ _ r hc => by
    obtain ⟨C, h0, x0, r⟩ := r hc
    refine ⟨C, h0, x0, fun x hx k hx0 i => ?_⟩
    obtain ⟨a, d⟩ := r x hx k hx0 i
    exact ⟨⟨a.w1, a.covol, a.onto, a.lamLow, a.seeIso, a.miStar, a.fun0, a.pass, a.kap⟩, d⟩
  have rest := GlobalTheory.Top.link_brest_alt h.𝒜 sel selS selP selDH selC selB
    h.hRB h.hPA dv h.hDcPtG rows h.tie
  have hCsz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 h.𝒜) fun _ => 0
  have oneMap : Closed (D3 3 h.𝒜) fun Fm _ => ∀ hc : D3 3 h.𝒜 Fm,
      EventuallyAlongSelection sel Fm (d3_a hc) ((SingleMapCondition selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx k _ i j => (h.hRB Fm (d3_a hc) x hx k i).oneMap j⟩
  have admissible := GlobalTheory.Top.closed_family_admissible_twist_link_alt h.𝒜 sel
    h.aPt0 h.aPtTw h.aPer0 h.aPerTw h.aP10 h.aAtG ((GlobalTheory.Cp.serv_t_iff_formalism_serv_t _ _).1 h.hServ)
  have count := GlobalTheory.Top.selection_closed_of_wu_decay_alt h.𝒜 sel selS selP selDH selC selB
    h.hWu h.hRF h.selJ h.jOn rows
  let rank {ε : ℝ} (Fm : FamP ε) (hc : D3 3 h.𝒜 Fm) :=
    RankOfDivisionKernel sel selS selP selDH selC (kernelChoiceOfSelection selB)
      (indefiniteRealisationChoiceOfSelection selB) h.hPA Fm hc
  have bridge : Closed (D3 3 h.𝒜) fun Fm CH => ∀ hc : D3 3 h.𝒜 Fm, TuSize Fm → DGamSize Fm →
      Formalism.L2.DIV.DivisionKernelConstantBounds Fm (rank Fm hc) 2 CH := by
    apply (rest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (h.hMt Fm (d3_a hc))).and
      (rows.and (oneMap.and (hCsz.and (admissible.and (h.aC2.and count))))))).imp
    intro _ Fm CH _ data hc hTu hDGam
    obtain ⟨r, cut, rr, om, cz, adm, c2, c5⟩ := data
    exact (r hc hTu hDGam).toRows_alt (fun hN => GlobalTheory.Top.wire_sel_alt h.𝒜 sel selS selP selDH selC
      selB h.hTw h.hPA dv h.hDcPtG Fm hc CH cz hDGam (rr hc) (om hc) (r hc hTu hDGam).bu hN)
      cut adm (complement_two_of_items c2) c5
  have divisibility := Formalism.L2.DIV.closed_linkDIVt_of_closed_bridge_kernel (D3 3 h.𝒜) 2 rank bridge
  have irreducible := GlobalTheory.Top.Irr.closed_linkIRR_of_join_count green h.𝒜 sel h.cIc h.hcI h.irrC
  have spectral := GlobalTheory.Top.link_alt_alt_bis h.𝒜 sel selS h.hWu h.hRF h.hTF
    h.c30 h.hc30 h.sTy h.sNG h.sM h.sLp h.sO h.h30 h.hInstR
  have sizes : Closed (D3 3 h.𝒜) fun Fm _ => TuSize Fm ∧ DGamSize Fm :=
    Closed.of_class fun _ _ hc => hc.2.2
  have sub {ε : ℝ} (Fm : FamP ε) (hc : D3 3 (fun Fm => h.𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) Fm) :
      D3 3 h.𝒜 Fm := ⟨⟨⟨⟨hc.1.1.1.1.1, hc.1.1.1.2⟩, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  apply rh_of_principal_archived_bundle_choices hs hd 2 (by norm_num)
  exact (Pk.Closed.sub (h.nRest.and (irreducible.and (divisibility.and (spectral.and sizes)))) sub).imp
    fun _ _ _ ⟨hn, hi, hv, hS, hTu, hDGam⟩ _ _ => ⟨hn, hi, hv hTu hDGam, hS hTu⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_archived_bundle_rows
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
