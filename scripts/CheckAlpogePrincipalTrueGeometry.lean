import CheckAlpogePrincipalSymmetricGeometry
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTrueWith
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DsPPosAndLower
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.LocalToGlobal.GlobalTheory.LossRequirementsOfSmallShares

/-! # The geometric count on families of constructed column records -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk
open Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.StandardLattice
open GlobalTheory.Core.Cls GlobalTheory.Mem GlobalTheory.Mem.Top

/-- The columns and the roots of both prime orders belong to the same selected record. -/
theorem symmetric_geometry_of_true_family {ε : ℝ} {Fm : FamP ε} (h : TrueF Fm) :
    HasSymmetricColumnsAndRoots Fm := by
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  obtain ⟨S⟩ := (h x (by linarith) i).selB
  exact ⟨⟨S.cols⟩, fun k => (S.roots k).1⟩

/-- Cancelling the common index and formal degrees in the positive target dimension identifies the base volume. -/
theorem volume_mass_of_dimension_formula {D : D7} (O : GlobalTheory.EX.OB.Obj D)
    (ht : D.what₂.Dstar = massI D D.R.r * idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    BaseVolumeEqualsMass D := by
  have hv : D.what₂.Dstar = volY0 D * idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ := O.ex.Dstar_def
  rw [mul_assoc] at hv ht
  have hp : 0 < D.what₂.Dstar := (D.Dstar_eq D.u₀).symm.trans_gt (D.mem D.u₀).A.Dstar_pos
  rw [ht] at hp
  exact mul_right_cancel₀ (right_ne_zero_of_mul hp.ne') (hv.symm.trans ht)

theorem volume_mass_of_true_record {D : D7} {O : GlobalTheory.EX.OB.Obj D} (h : IsTrue D O) :
    BaseVolumeEqualsMass D := by
  refine IsTrue.ind (R := fun D _ => BaseVolumeEqualsMass D) ?_ h
  intro K B f T w Z O p
  let D := w.D Z
  have he : D.what₂.Dstar = B.Dstar :=
    (D.Dstar_eq D.u₀).symm.trans (w.C.A_Dstar _)
  apply volume_mass_of_dimension_formula O
  change D.what₂.Dstar = _
  rw [he, p.isOver.sizes.2]
  unfold DsPre
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (p.dsig τ).symm

/-- On a constructed record the formal degree equals the Weyl dimension.
The elementary product inequality for that dimension gives the packet bound. -/
theorem sigma_degree_of_weyl_dimension {D : D7} (hd : ∀ ρ, D.dsig ρ = dimV (rowLam D ρ)) :
    SigmaDegreeTwoSidedBoundOfGap D := by
  intro e he _ ρ _
  let l := rowLam D ρ
  have hl : Formalism.QuantumDeterminants.IsHCParam l := by
    have hh := Vol.lamSH_isHCParam D.R (D.hc ρ)
    rw [param_vector_eq_line_param] at hh
    have transport {m n : ℕ} (eq : m = n) (l : Fin n → ℝ) :
        Formalism.QuantumDeterminants.IsHCParam (fun i => l (Fin.cast eq i)) →
        Formalism.QuantumDeterminants.IsHCParam l := by subst n; exact id
    exact transport _ _ hh
  have hdim := dim_weyl_pos_of_strictAnti l hl.1
  rw [hd]
  constructor
  · exact mul_le_of_le_one_left hdim.le (by linarith [(Real.exp_pos _).trans_le he])
  · have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau (rowSgn D) l hl
    rw [← dimV_eq_fdegHC _ hl.1, count_plus_line_sign, count_minus_line_sign] at hle
    have ht := (formalDegreeFactor_pos_of_strictAnti (rowSgn D) l hl.1).le
    have hp : (1 : ℝ) ≤ pY D := by exact_mod_cast (signature_counts_ge_one D).1
    have hq : (1 : ℝ) ≤ qY D := by exact_mod_cast (signature_counts_ge_one D).2
    have ha := abs_param_sup_nonneg l
    have hfac : 1 ≤ 3 * (pY D : ℝ) * qY D :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hp) hq
    have hb := le_mul_of_one_le_left ha hfac
    exact hle.trans (mul_le_mul (by linarith : dTau (rowSgn D) l ≤ 4 * dTau (rowSgn D) l)
      (pow_le_pow_left₀ ha hb _) (pow_nonneg ha _) (by linarith))

theorem sigma_degree_of_true_record {D : D7} {O : GlobalTheory.EX.OB.Obj D} (h : IsTrue D O) :
    SigmaDegreeTwoSidedBoundOfGap D := by
  apply sigma_degree_of_weyl_dimension
  refine IsTrue.ind (R := fun D _ => ∀ ρ, D.dsig ρ = dimV (rowLam D ρ)) ?_ h
  intro K B f T w Z O p ρ
  exact (p.dsig ρ).trans (DsLow.trueDsig_eq_dimV _ _)

theorem principal_count_of_mass_and_degree {ε : ℝ} {Fm : FamP ε}
    (h : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, BaseVolumeEqualsMass (Fm.D x i) ∧
      SigmaDegreeTwoSidedBoundOfGap (Fm.D x i)) : CountF Fm := by
  apply countF_fam Fm
  apply family_part_five_of_explicit_constants
  apply division_level_prime_family
  · exact ⟨0, fun x _ _ i => massRatio_of_modelMassRatio (Fm.D x i) GlobalTheory.Mass.siegelMassRatio_holds⟩
  · exact ⟨0, fun x _ hx i => (h x hx i).1⟩
  · exact ⟨0, fun x _ hx i => (h x hx i).2⟩

/-- All three geometric inputs to the level count hold on the constructed records. -/
theorem principal_count_of_true_family {ε : ℝ} {Fm : FamP ε} (h : TrueF Fm) : CountF Fm :=
  principal_count_of_mass_and_degree fun x hx i =>
    ⟨volume_mass_of_true_record (h x hx i), sigma_degree_of_true_record (h x hx i)⟩

theorem rh_of_principal_true_families (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ D.family.CoverAll ∧ TrueF D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_symmetric_geometry
  intro δ hδ
  obtain ⟨ε, D, hl, hC, hH, hc, ht⟩ := h δ hδ
  exact ⟨ε, D, hl, hC, hH, hc, principal_count_of_true_family ht, symmetric_geometry_of_true_family ht⟩

/-- The weights selected by the construction suffice if their small-order prime sums
satisfy the chosen-weight estimate on every sufficiently late member. -/
theorem rh_of_principal_selected_geometry (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ ChosenWall D.family ∧
      CountF D.family ∧ HasSymmetricColumnsAndRoots D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_adelic_designs
  intro δ hδ
  obtain ⟨ε, D, hloss, hC, hH, hw, hn, hs⟩ := h δ hδ
  let Fm := D.family
  obtain ⟨hf, a, ha⟩ := principal_column_estimates_of_symmetric Fm
    Formalism.L2.GlobalTheoryTheory.ColValS.colValOfTiedS_holds principal_hecke_of_symmetric_columns hn
    hs
  have hM := principal_base_slopes_of_columns Fm hn ⟨a, fun x hx i u => ((ha x hx i).2 u).1⟩
  have hN := principal_places_of_level_estimates Fm hn hf D.linkG
    (principal_level_estimates_of_congruence Fm hn hf ⟨a, fun x hx i =>
      ⟨(ha x hx i).1, fun u => ((ha x hx i).2 u).2⟩⟩)
  refine ⟨ε, D.Cabs, 0, fam_eps_pos Fm, by simpa using hloss, ⟨D, ?_⟩, hf⟩
  intro hchosen hin
  obtain ⟨C5, c6, _, h6, hT2, hTT, hBad, hW, hQD, hThin, hPr, hCode⟩ :=
    Formalism.L2.GlobalTheoryTheory.Loss7.loss_requirements_of_small_shares Fm D.C0 D.CH hchosen hw
  obtain ⟨hLat, hFrame⟩ := principal_frame_of_forms Fm hH (principal_chosen_constant_one_le hchosen hf)
    (levelPrimeGrowth_of_tuGe (principal_level_lower_of_count Fm hn)) hf hPr hCode hin.2.1 hin.2.2.1 hin.2.2.2.1
  have hSmall := Formalism.L2.GlobalTheoryTheory.Loss7.losses_of_small_share_weight Fm hTT hBad hin.1
  exact linkCore Fm D.Cabs D.CH 0 C5 c6 hC hH.le le_rfl h6 hn hM (slopesNF_of Fm hN)
    hLat (nodesF Fm) hFrame (lossF_of_7 Fm hSmall hW) (charF Fm) (size_windows_of_thick_density Fm hT2)
    hTT hQD hThin hin.2.2.1 hin.2.2.2.1

theorem rh_of_principal_selected_families (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ ChosenWall D.family ∧ TrueF D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_selected_geometry
  intro δ hδ
  obtain ⟨ε, D, hl, hC, hH, hw, ht⟩ := h δ hδ
  exact ⟨ε, D, hl, hC, hH, hw, principal_count_of_true_family ht, symmetric_geometry_of_true_family ht⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.rh_of_principal_true_families,
      ``RiemannGaussian.AlpogeWindow.rh_of_principal_selected_families] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
