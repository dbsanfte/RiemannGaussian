import CheckAlpogePrincipalRankBound
import CheckAlpogePrincipalDesignLinks
import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermWCellLastMulMulVecEqOfInWb
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTP

/-! # Principal lift rank on the archived reciprocity-based bundles -/

namespace RiemannGaussian.AlpogeWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2
open GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

/-- The selected rows of the reciprocity-based bundles identify the theta-source
dimension with the base row count. -/
theorem principal_lift_rank_of_archived_bundles {ε : ℝ} {𝒜 : FamClass}
    {σ : RawSel BundleCondition 𝒜} {Q : V4.Slot}
    {hL : UpperTheory.Zero.LLC.RecTExists} {p : Parameters hL} {E : Par → BdP BundleCondition}
    (selected : IsSel Q (BundleLinkage p) E 𝒜 σ) (Fm : FamP ε) (hc : 𝒜 Fm) :
    BoundedLiftRank Fm := by
  obtain ⟨_, _, _, built⟩ := selected Fm hc
  apply boundedLiftRank_of_source 1 (Fm.x1 + 1)
  intro x hx i j hj
  have hx' : Fm.x1 < x := by linarith only [hx]
  let b := σ Fm hc x hx' i
  have rows : Rows.RowsHold0_3 b.P := by
    apply Built.ind (R := fun _ _ _ b => Rows.RowsHold0_3 b.P) ?_ (built x hx' i).1
    intro K β c b' _ _ linked
    obtain ⟨q, b'', ⟨w⟩, he⟩ := linked
    have equality := congrArg (fun s : Σ (D : D7) (O : GlobalTheory.EX.OB.Obj D),
      BundleCondition D O c => Rows.RowsHold0_3 s.2.2.P) he
    apply cast equality.symm
    have prim := GlobalTheory.Fc.RL.PrimAt.of_wit_alt w
    exact b''.B.Q.rowsHold0 b''.C.toS.ok1 prim.2 prim.1
  have hj' := Finset.mem_Icc.mp hj
  obtain ⟨k, rfl⟩ : ∃ k : Fin (Fm.D x i).R.m, j = k.val + 1 :=
    ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hbase : (Fm.D x i).what₂.D0 = b.P.S0.D :=
    GlobalTheory.rowSide_card_eq_of_coord (Fm.ex x hx' i).p0.s (Fm.D x i).what₂.onb0 b.P.I.eRR0
  rw [one_mul, Formalism.L2.N.ExtNRows3.finrank_Mj_eq_dW b.P k,
    Formalism.L2.N.ExtNRows3.dW_eq_D b.P rows k, hbase]

/-- The same normalized bundles give the group compatibility and local Hecke comparison. -/
theorem principal_links_of_archived_bundles :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ K : TransportedAlt,
    ∀ (𝒜 : FamClass), RawSel BundleCondition 𝒜 → ∀ (Fm : FamP ε) (CH C0 : ℝ), 𝒜 Fm →
      Fm.Large K CH → ChosenE Fm C0 CH → LinkEta Fm ∧ LinkG Fm := by
  obtain ⟨ε₀, h₀, getK⟩ := principal_design_group_and_hecke
  refine ⟨ε₀, h₀, fun ε hε hsmall => ?_⟩
  obtain ⟨K, hK⟩ := getK ε hε hsmall
  refine ⟨K, fun 𝒜 σ Fm CH C0 hc hlarge hchosen => hK Fm CH C0 hlarge hchosen ?_ ?_⟩
  · exact ⟨Fm.x1, fun x _ i hx => ⟨(σ Fm hc x hx i).R.T.g⟩⟩
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    let N := (σ Fm hc x (by linarith) i).R.T.n
    exact ⟨N.gal.mt, N.cover, N.gal.hecke⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.principal_lift_rank_of_archived_bundles,
      ``RiemannGaussian.AlpogeWindow.principal_links_of_archived_bundles] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
