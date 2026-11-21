import CheckAlpogePrincipalAdelicDesigns
import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen

/-! # The integral frame and global comparison from adelic forms -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk

/-- A level prime above b makes the dimension lost at the ramified places
exponentially small on every word. -/
theorem principal_ramified_share_of_forms {ε : ℝ} (Fm : FamP ε)
    (hTu : LevelPrimeGrowth Fm) (hforms : HasLevelZeroForms Fm) : RamShareF Fm := by
  obtain ⟨a, ha⟩ := hforms
  obtain ⟨b, hb⟩ := principal_ramified_share_of_level_growth Fm (fam_eps_pos Fm) hTu
    ⟨a, fun x hx i u => localNormRankBound_of_free_classes _ u
      ((ha x hx i u).elim freeLevelClasses_of_forms)⟩
  refine ⟨b, fun x hx i => ⟨_, sq_nonneg _, ?_, hb x hx i⟩⟩
  exact (Real.sqrt_sq (Real.exp_pos _).le).le

/-- The sums of local invariant dimensions control the real frame error. The full
division lattice and the chosen code then give the integral frame on the same family. -/
theorem principal_frame_of_forms {ε Cabs CH C0 : ℝ} (Fm : FamP ε)
    (hCH : 0 < CH) (hC0 : 1 ≤ C0) (hTu : LevelPrimeGrowth Fm) (hforms : HasLevelZeroForms Fm)
    (hp : ChosenProviso Fm C0) (hc : ChosenCode Fm C0 CH)
    (hS : LinkS Fm C0) (hI : LinkIRR Fm) (hD : LinkDIV Fm Cabs CH) :
    LatF Fm ∧ FrameF Fm CH := by
  have hC := zero_lt_one.trans_le hC0
  have hr := principal_family_rank_of_forms Fm hforms
  have hs := principal_ramified_share_of_forms Fm hTu hforms
  have hn := principal_family_nuFull Fm
  have hlat := latF Fm hD hn hr (rrRankF_of Fm Cabs CH C0 hC hS hp hI hD)
  have hreal := frameRealF_of' Fm Cabs CH C0 hCH.le hD hI hS hp hn hr
    (matKF_of Fm Cabs CH C0 hC hS hp hD) hs
  exact ⟨hlat, frameF_of Fm CH C0 hCH hC0 hreal hlat hp hc hn⟩

/-- On a family covering the admissible weights, the pointwise small-order-prime
estimate supplies zero loss. Counting and the two slope estimates suffice for
the remaining global argument once the adelic forms have supplied the frame. -/
theorem principal_global_of_points {ε Cabs CH C0 : ℝ} (Fm : FamP ε)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 1 ≤ C0)
    (hTu : LevelPrimeGrowth Fm) (hforms : HasLevelZeroForms Fm) (hcov : Fm.CoverAll)
    (hCount : CountF Fm) (hSM : SlopesMF Fm) (hPlaces : PlacesF Fm)
    (hpoints : StatementsAtPointsLargeScales Fm) : LinkGLOBAL Fm Cabs CH C0 Cabs 0 := by
  intro hchosen hin
  have hcode : ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hp, hc⟩ := hchosen
    exact ⟨hp, hc⟩
  obtain ⟨hlat, hframe⟩ := principal_frame_of_forms Fm hCH hC0 hTu hforms hcode.1 hcode.2
    hin.2.1 hin.2.2.1 hin.2.2.2.1
  have hloss := lossF_of_core Fm (estimates_of_points_family Fm hcov hpoints)
  exact linkGLOBAL_of Fm Cabs CH C0 0 hCabs hCH.le le_rfl hCount hSM
    (fun _ _ => slopesNF_of Fm hPlaces) (fun _ => hlat) (nodesF Fm)
    (fun _ _ _ _ _ => hframe) (fun _ _ _ _ _ => hloss) (charF Fm)
    (size_windows_of_thick_set Fm) hcov hchosen hin

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.principal_frame_of_forms,
      ``RiemannGaussian.AlpogeWindow.principal_global_of_points] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
