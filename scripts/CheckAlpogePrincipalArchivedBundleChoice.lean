import CheckAlpogePrincipalArchivedBundleRank
import CheckAlpogePrincipalConstructedClass
import Formalism.LocalToGlobal.ClassOfRecordOfChoice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo

/-! # Principal designs selected from the archived reciprocity-based bundles -/

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.MainNotions.Pk Formalism.HC Formalism.L2
open Formalism.MainNotions.Lnk
open GlobalTheory.EX GlobalTheory.Fc GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
open GlobalTheory.Core.Cls UpperTheory.Top

private theorem thin_at_built_point {κ : Par} {K : Ctx} (hk : κ.Of K) (β : BPt K) :
    ChThin_at β.D β.O.L.sc.x β.O.L.sc.eps κ.c6 := by
  have hthin := hk.2.2.2.2.host.2.2.2.2.2.2.2.1
  change ThinOK β.p.L.sc κ.c6 β.X.B.host
  rw [β.sc]
  have transfer {B : Pre} (h : K.Over B) : ThinOK K.s κ.c6 B.host := by
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := h
    exact hthin
  exact transfer β.c.isOver

/-- Thinness on the originating hosts passes to the records of the selected family. -/
theorem principal_thin_of_archived_bundles {ε : ℝ} {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜}
    {Q : V4.Slot} {Lk : LkT BundleCondition} {E : Par → BdP BundleCondition}
    (hs : IsSel Q Lk E 𝒜 σ) (Fm : FamP ε) (hc : 𝒜 Fm) :
    ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6 := by
  obtain ⟨κ, hlink, _, hbuilt⟩ := hs Fm hc
  refine ⟨κ.c6, hlink.pos.2.1, Fm.x1 + 1, fun x hx i => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  have h := Built.ind (R := fun D O _ _ => ChThin_at D O.L.sc.x O.L.sc.eps κ.c6)
    (fun _ β _ _ hk _ _ => thin_at_built_point hk β) (hbuilt x hx' i).1
  change ChThin_at (Fm.D x i) (Fm.L x i).sc.x (Fm.L x i).sc.eps κ.c6 at h
  rwa [Fm.L_x x i hx', Fm.L_eps x i] at h

/-- The class number formula and the symmetric columns of these same bundles bound the dimension ratio. -/
theorem principal_proviso_of_archived_bundles {ε : ℝ} {𝒜 : FamClass} (σ : RawSel BundleCondition 𝒜)
    (Fm : FamP ε) (hc : 𝒜 Fm) : ChosenProviso Fm 3 := by
  apply StandardLattice.HarishChandraReduction.chosenProviso_min Fm 3 (Real.exp_one_lt_d9.le.trans (by norm_num))
    (fun _ _ _ => GlobalTheory.ColClassNumber.classNumber_all _ _)
  apply Ext.Lw.rank_conditions_of_lowest_space
  exact ⟨Fm.x1 + 1, fun x hx i u => Ext.Lw.mu0Tie_of_sym (σ Fm hc x (by linarith) i).R.T.cols u⟩

open Formalism.MainNotions.StandardLattice Formalism.MainNotions.StandardLattice.HarishChandraReduction
open Formalism.L2.Top3

/-- The height of the selected torus factors obeys the explicit geometric bound. -/
theorem principal_tu_size_of_archived_bundles {ε : ℝ} {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜}
    {Q : V4.Slot} {Lk : LkT BundleCondition} {E : Par → BdP BundleCondition}
    (hs : IsSel Q Lk E 𝒜 σ) (Fm : FamP ε) (hc : 𝒜 Fm) (hTu : cTmin Fm.CYL ≤ Fm.CTu) :
    TuSize Fm := by
  obtain ⟨κ, _, _, hb⟩ := hs Fm hc
  have geom (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :=
    Built.ind (R := fun D _ _ _ => BaseVolumeEqualsMass D ∧ SigmaDegreeTwoSidedBoundOfGap D)
      (fun _ β _ _ _ _ _ => ⟨(principal_geometry_of_built_point β).1, (principal_geometry_of_built_point β).2.1⟩)
      (hb x hx i).1
  have count := division_level_prime_family Fm
    ⟨0, fun x _ _ i => massRatio_of_modelMassRatio (Fm.D x i) GlobalTheory.Mass.siegelMassRatio_holds⟩
    ⟨0, fun x _ hx i => (geom x hx i).1⟩ ⟨0, fun x _ hx i => (geom x hx i).2⟩
  let C := max 5 (Fm.CYL + 1)
  obtain ⟨a, ha⟩ := count C C
  obtain ⟨b, hb⟩ := Formalism.MainNotions.GlobalTheoryTheory.rowsAF_fam Fm C
  apply Formalism.MainNotions.GlobalTheoryTheory.tuSize_fam Fm (cTmin Fm.CYL) (max a b) _ hTu
  intro x hx hx' i
  exact part_five_all_of_explicit _ _ _ _ _ (ha x (le_of_max_le_left hx) hx' i)
    (hb x (le_of_max_le_right hx) hx' i) (le_max_left _ _) (le_max_right _ _)

/-- A design for the principal host yields an actual chosen family at any requested threshold.
The selected records supply the thinness, dimension ratio and torus-size bounds. -/
theorem principal_designs_of_archived_bundle_choices {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜}
    {Q : V4.Slot} {Lk : LkT BundleCondition} {E : Par → BdP BundleCondition}
    (hs : IsSel Q Lk E 𝒜 σ)
    (hd : DC.DesignChoices (DC.WithTw fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) 3 (fun _ => cTmin)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ K : TransportedAlt, ∃ (Fm : FamP ε) (CH : ℝ),
      D3 3 (fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) Fm ∧
      0 < CH ∧ Fm.Large K CH ∧ ChosenE Fm 3 CH ∧ Fm.CF = CH := by
  obtain ⟨ε₀, h₀, chooseFam⟩ := hd
  refine ⟨ε₀, h₀, fun ε hε hsmall K => ?_⟩
  let oneMid : TransportedAlt := ⟨0, fun _ => 0, fun _ => 1, fun _ => 0⟩
  obtain ⟨Fm, CH, C5, Cb, ⟨⟨hc, hp⟩, htw⟩, _, hlarge, h5, hb, hthick, htt, hbad, hqd,
    hcode, hbox, hrows, hdvd, htu, htame, hCF, _, hCYL⟩ := chooseFam ε hε hsmall (K.sup oneMid)
  obtain ⟨hK, hM⟩ := (Fm.large_sup K oneMid CH).1 hlarge
  have hCH : (1 : ℝ) ≤ CH := hM.2.2.1 CH (by simp [FamP.cMid])
  obtain ⟨c6, h6, hthin⟩ := principal_thin_of_archived_bundles hs Fm hc
  have hchosen : ChosenE Fm 3 CH := ⟨C5, c6, Cb, h5, h6, hb, hthick, htt, hbad, hqd, hthin,
    principal_proviso_of_archived_bundles σ Fm hc, hcode⟩
  have hclass : WithChN (fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) Fm :=
    ⟨⟨hc, hp⟩, hdvd, htame, hbox, hrows, hCYL⟩
  exact ⟨Fm, CH, ⟨⟨withSm_of_withChN Fm hclass, htw⟩, ⟨CH, hchosen⟩,
    principal_tu_size_of_archived_bundles hs Fm hc htu, dGamSize_of_dvd Fm hdvd⟩,
    one_pos.trans_le hCH, hK, hchosen, hCF⟩

theorem principal_geometry_of_archived_selection {ε : ℝ} (Fm : FamP ε) {Q : V4.Slot} {Lk : LkT BundleCondition}
    {E : Par → BdP BundleCondition} {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜} (hs : IsSel Q Lk E 𝒜 σ) (hc : 𝒜 Fm) :
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

/-- Four estimates on sufficiently large principal designs suffice uniformly in the exponent. -/
theorem rh_of_principal_archived_bundle_choices {𝒜 : FamClass} {σ : RawSel BundleCondition 𝒜} {Q : V4.Slot}
    {hL : UpperTheory.Zero.LLC.RecTExists} {p : Parameters hL} {E : Par → BdP BundleCondition}
    (hs : IsSel Q (BundleLinkage p) E 𝒜 σ)
    (hd : DC.DesignChoices (DC.WithTw fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) 3 (fun _ => cTmin))
    (Cabs : ℝ) (habs : 0 ≤ Cabs)
    (hcmp : Closed (D3 3 fun Fm => 𝒜 Fm ∧ (GChi PChar.one).cls (3/2) Fm) fun Fm CH =>
      ChosenE Fm 3 CH → Fm.CF = CH → LinkN Fm ∧ LinkIRR Fm ∧ LinkDIVt Fm Cabs CH ∧ LinkS Fm 3) :
    RiemannHypothesis := by
  obtain ⟨d, hd0, chooseFam⟩ := principal_designs_of_archived_bundle_choices hs hd
  obtain ⟨a, ha, getThreshold⟩ := hcmp
  apply rh_of_principal_selected_geometry
  intro δ hδ
  obtain ⟨ε₀, h₀, links⟩ := principal_links_of_archived_bundles
  have hpos : 0 < Cabs + 7 := by linarith
  let ε := min (min ε₀ d) (min a (δ / (Cabs + 7)))
  have hε : 0 < ε := lt_min (lt_min h₀ hd0) (lt_min ha (div_pos hδ hpos))
  have hleft : ε ≤ min ε₀ d := min_le_left _ _
  have hright : ε ≤ min a (δ / (Cabs + 7)) := min_le_right _ _
  obtain ⟨K, hK⟩ := links ε hε (hleft.trans (min_le_left _ _))
  obtain ⟨K', hK'⟩ := getThreshold ε hε (hright.trans (min_le_left _ _))
  obtain ⟨Fm, CH, hclass, hCH, hlarge, hchosen, hCF⟩ :=
    chooseFam ε hε (hleft.trans (min_le_right _ _)) (K.sup K')
  obtain ⟨hlarge, hlarge'⟩ := (Fm.large_sup K K' CH).1 hlarge
  obtain ⟨hc, hp⟩ := d3_a hclass
  obtain ⟨hn, hirr, hdiv, hspectral⟩ := hK' Fm CH hclass hlarge' hchosen hCF
  obtain ⟨hEta, hG⟩ := hK 𝒜 σ Fm CH 3 hc hlarge hchosen
  have hrank := principal_lift_rank_of_archived_bundles hs Fm hc
  let design : PrincipalLocalComparisonData ε :=
    ⟨Fm, hp, Cabs, CH, 3, hchosen, hn, hEta, hirr, hrank, hdiv, hG, hspectral⟩
  have hloss := (le_div_iff₀ hpos).mp (hright.trans (min_le_right _ _))
  exact ⟨ε, design, (mul_comm ε _).symm ▸ hloss, habs, hCH,
    principal_geometry_of_archived_selection Fm hs hc⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_archived_bundle_choices
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
