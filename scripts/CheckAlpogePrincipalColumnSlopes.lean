import CheckAlpogePrincipalCharacterSlopes
import Formalism.LocalToGlobal.GlobalTheory.GL4.ClassMapArchimedean
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SlopesMFOfCountFam

/-! # Base-lattice slopes from the column data on the selected family -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk
open Formalism.L2.GlobalTheoryTheory.TraceIntegrality
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

/-- A nonzero level-zero form makes the proviso ratio positive. A constant
whose inverse and value bound that ratio must be at least one. -/
theorem principal_chosen_constant_one_le {ε C0 CH : ℝ} {Fm : FamP ε}
    (h : ChosenE Fm C0 CH) (hf : HasLevelZeroForms Fm) : 1 ≤ C0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨a, ha⟩, _⟩ := h
  obtain ⟨b, hb⟩ := hf
  obtain ⟨x, hx, _, _, ⟨i⟩⟩ := Fm.toFamCore.exists_pt (max a b)
  let D := Fm.D x i
  let L := Fm.L x i
  let u := D.u₀
  obtain ⟨Tf⟩ := hb x (le_of_max_le_right hx) i u
  obtain ⟨hlo, hhi⟩ := ha x (le_of_max_le_left hx) i u
  have hd : 0 < (D.duS u : ℝ) := Nat.cast_pos.mpr (unramified_dimension_pos_of_forms Tf)
  have hg : 0 < GamL L := Real.exp_pos _
  have hs : 0 < D.what₂.Dstar := (D.Dstar_eq u).symm.trans_gt (D.mem u).A.Dstar_pos
  have hpos : 0 < C0 := (div_pos (mul_pos hd (sq_pos_of_pos hg)) hs).trans_le hhi
  have hsq : 1 ≤ C0 * C0 := (div_le_iff₀ hpos).1 (by simpa only [one_div] using hlo.trans hhi)
  by_contra! hsmall
  nlinarith only [hsq, mul_pos (sub_pos.mpr hsmall) (by linarith : 0 < 1 + C0)]

/-- The exact column slope gives the lower bound. The class map at infinity
controls the maximum slope. Counting makes both bounds uniform in the family. -/
theorem principal_base_slopes_of_columns {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (hcol : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    SlopesMF Fm := by
  have hmax := third_proposition_of_class (fun D =>
    slopeMaxClass_of_map D (class_map_of_archimedean D (class_map_archimedean D))) Fm
  exact flipTwoThree.slopesMF_of_count_fam Fm (slope_proposition_family Fm) hmax hn
    (Formalism.L2.GlobalTheoryTheory.Places.dlSize _ Fm) hcol

/-- For each positive exponent loss, it suffices to find the chosen principal
design with cover, counts, level-zero forms, columns and integral congruence
bounds on its words, and the two auxiliary roots in its coefficient fields. -/
theorem rh_of_principal_column_designs (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧
    HasLevelZeroForms D.family ∧ D.family.CoverAll ∧ CountF D.family ∧
    ∃ a : ℝ, ∀ x ≥ a, ∀ i : D.family.Ix x,
      (∀ k, ∃ z : (D.family.D x i).what₂.LL, IsPrimitiveRoot z ((D.family.D x i).host.g k)) ∧
      ∀ u, Nonempty (flipTwoThree.ColVal (D.family.D x i) u) ∧
        CongruenceLatticeLengthBound (D.family.D x i) u) : RiemannHypothesis := by
  apply rh_of_principal_level_lattice_designs
  intro δ hδ
  obtain ⟨ε, D, hloss, habs, hch, hf, hc, hn, a, ha⟩ := h δ hδ
  refine ⟨ε, D, hloss, habs, hch, principal_chosen_constant_one_le D.chosen hf, hf, hc, hn, ?_, ?_⟩
  · exact principal_base_slopes_of_columns D.family hn ⟨a, fun x hx i u => ((ha x hx i).2 u).1⟩
  · exact principal_level_estimates_of_congruence D.family hn hf
      ⟨a, fun x hx i => ⟨(ha x hx i).1, fun u => ((ha x hx i).2 u).2⟩⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_column_designs
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
