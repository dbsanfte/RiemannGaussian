import CheckAlpogePrincipalCountingDesigns
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

/-! # Recovering the level-prime count from one rank ratio and its variation -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk
open Formalism.MainNotions.GlobalTheoryTheory

/-- The archive's rank ratio on a word, on the logarithmic scale of the level prime. -/
noncomputable def rankLog (D : D7) (u : D.what₂.Word) : ℝ := Real.log (D.mem u).A.Xu

theorem rankLog_eq (D : D7) (u : D.what₂.Word) : rankLog D u =
    1 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.what₂.Dstar / ((D.mem u).A.duStar : ℝ)) := by
  unfold rankLog ColumnsAtT.Xu
  rw [Real.log_rpow (div_pos (D.mem u).A.Dstar_pos (Nat.cast_pos.mpr (D.mem u).A.duStar_pos)), D.Dstar_eq u]

/-- On every sufficiently late member the prime lies within two logarithmic
units of the rank ratio. This uses only the defining prime window. -/
theorem principal_level_log_vs_rank {ε : ℝ} (Fm : FamP ε) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) :
    let D := Fm.D x i
    rankLog D u - 2 ≤ Real.log ((D.mem u).A.T : ℝ) ∧ Real.log ((D.mem u).A.T : ℝ) ≤ rankLog D u + 1 := by
  let D := Fm.D x i
  let A := (D.mem u).A
  have hxpos : 0 < A.Xu := Real.rpow_pos_of_pos (div_pos A.Dstar_pos (Nat.cast_pos.mpr A.duStar_pos)) _
  have hgpos : 0 < A.GamP := one_pos.trans A.one_lt_gammaP
  have hstart : 0 < A.Tstar := mul_pos hxpos (Real.rpow_pos_of_pos hgpos _)
  have hfk : 1 ≤ (D.R.f : ℝ) * D.R.k := by
    have hf : (1 : ℝ) ≤ D.R.f := by
      have hf := D.R.toFrame.ord_pos
      exact_mod_cast (show 1 ≤ D.R.f by unfold Ranks.f Ranks.n; omega)
    exact one_le_mul_of_one_le_of_one_le hf (by linarith [(JDB.db_rk D).1])
  have heq : Real.log A.Tstar = rankLog D u - 2 * (Real.log A.GamP / ((D.R.f : ℝ) * D.R.k)) := by
    unfold ColumnsAtT.Tstar rankLog
    rw [Real.log_mul hxpos.ne' (Real.rpow_pos_of_pos hgpos _).ne', Real.log_rpow hgpos]
    ring
  obtain ⟨hl, hu⟩ := D.T_win u
  have hlow := Real.log_le_log hstart hl
  have hhi := Real.log_le_log (hstart.trans_le hl) hu
  have hγ : Real.log A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ 1 := logGam_le Fm x hx i u
  have hγ0 : 0 ≤ Real.log A.GamP / ((D.R.f : ℝ) * D.R.k) := div_nonneg (Real.log_nonneg A.one_lt_gammaP.le) (by linarith)
  have hfac : 0 < 1 + 1 / ((D.R.f : ℝ) * D.R.k) := by positivity
  have hfac' : Real.log (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos hfac, (div_le_one (by linarith : 0 < (D.R.f : ℝ) * D.R.k)).2 hfk]
  change Real.log (A.T : ℝ) ≤ Real.log ((1 + 1 / ((D.R.f : ℝ) * D.R.k)) * A.Tstar) at hhi
  rw [Real.log_mul hfac.ne' hstart.ne', heq] at hhi
  change Real.log A.Tstar ≤ Real.log (A.T : ℝ) at hlow
  rw [heq] at hlow
  change rankLog D u - 2 ≤ Real.log (A.T : ℝ) ∧ Real.log (A.T : ℝ) ≤ rankLog D u + 1
  exact ⟨by linarith only [hlow, hγ], by linarith only [hhi, hγ0, hfac']⟩

/-- It suffices to estimate the rank ratio at the reference word and bound the
variation of its logarithm across the words. -/
def ReferenceRankCount {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ C a : ℝ, 0 ≤ C ∧ ∀ x ≥ a, ∀ i : Fm.Ix x,
    let D := Fm.D x i
    let L := Fm.L x i
    (∑ j ∈ SizeData₂.lifts D, 1 / (D.R.f : ℝ) * ∑ τ, Real.log (wj D j τ * D.host.v / Real.pi)) +
      D.R.m * lgG D - C * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) ≤ rankLog D D.u₀ ∧
    rankLog D D.u₀ ≤ C * D.R.m * L.sc.L ∧
    ∀ u, |rankLog D u - rankLog D D.u₀| ≤ C * Real.log D.R.k

/-- The common mass and level-index factors cancel between words. The Weyl dimension
variation therefore applies to every member once the family size estimates hold. -/
theorem principal_rank_variation {ε : ℝ} (Fm : FamP ε) (x : ℝ) (h3 : 3 ≤ x)
    (hx : Fm.x1 < x) (i : Fm.Ix x) (u v : (Fm.D x i).what₂.Word) :
    |rankLog (Fm.D x i) u - rankLog (Fm.D x i) v| ≤ 16 * Real.log (Fm.D x i).R.k := by
  have heq := jnt_logXu (Fm.D x i) (StandardLattice.factDuStar_fam Fm x hx i)
    (StandardLattice.factDstar_fam Fm x hx i)
  simp only [rankLog, heq]
  exact (StandardLattice.weylLawVariation_holds _ _ _ 16 le_rfl _ _
    (JDB.dataB_fam Fm x h3 hx i)).2 u v

/-- The two absolute estimates that remain at the reference word. -/
def ReferenceRankBounds {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ C a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x,
    let D := Fm.D x i
    let L := Fm.L x i
    (∑ j ∈ SizeData₂.lifts D, 1 / (D.R.f : ℝ) * ∑ τ, Real.log (wj D j τ * D.host.v / Real.pi)) +
      D.R.m * lgG D - C * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) ≤ rankLog D D.u₀ ∧
    rankLog D D.u₀ ≤ C * D.R.m * L.sc.L

theorem referenceRankCount_of_bounds {ε : ℝ} (Fm : FamP ε) (h : ReferenceRankBounds Fm) :
    ReferenceRankCount Fm := by
  obtain ⟨C, a, ha⟩ := h
  refine ⟨max C 16, max (max a 3) (Fm.x1 + 1), (by positivity), fun x hx i => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hx1 : Fm.x1 < x := by linarith only [le_of_max_le_right hx]
  have h3 := le_of_max_le_right (le_of_max_le_left hx)
  obtain ⟨hl, hu⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
  have hL : 0 ≤ L.sc.L := Real.rpow_nonneg (zero_le_one.trans L.sc.one_lt_alt.le) _
  have hrd : 1 ≤ D.host.rdE := (Fm.sizes x hx1 i).2.2.2.2.2.2.1.2.2.2.2.2.2.1
  have hLa : 0 ≤ L.La := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le L.sc.one_lt_alt.le
      (Real.one_le_exp hL)) hrd)
  refine ⟨le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left C 16)
    (show 0 ≤ L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k by positivity)) _) hl,
    hu.trans (by gcongr; exact le_max_left C 16), fun u => ?_⟩
  exact (principal_rank_variation Fm x h3 hx1 i u D.u₀).trans (mul_le_mul_of_nonneg_right
    (le_max_right C 16) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D.R.k by have := D.R.k_ge; omega))))

theorem principal_count_of_reference_ranks {ε : ℝ} (Fm : FamP ε) (h : ReferenceRankCount Fm) : CountF Fm := by
  obtain ⟨C, a, hC, ha⟩ := h
  refine ⟨2 * C + 4, max (max a 3) (Fm.x1 + 1), by linarith, fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  have hx1 : Fm.x1 < x := by linarith only [le_of_max_le_right hx]
  have hx3 : 3 ≤ x := le_of_max_le_right (le_of_max_le_left hx)
  obtain ⟨hl, hu, hw⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
  have h0 := principal_level_log_vs_rank Fm x hx1 i u
  have hv := abs_le.mp (hw u)
  have hsize := JDB.db_basic L (Fm.sizes x hx1 i) (by rw [Fm.L_x x i hx1]; exact hx3)
  have hk3 : (3 : ℝ) ≤ D.R.k := (JDB.db_rk D).1
  have hk : 0 < (D.R.k : ℝ) := by linarith
  have hlog : 1 ≤ Real.log D.R.k := by
    have ht : Real.exp 1 ≤ (D.R.k : ℝ) := by linarith [Real.exp_one_lt_d9]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hkL : Real.log D.R.k ≤ L.sc.L := by
    simpa only [Scale.b, Real.log_exp] using Real.log_le_log hk hsize.2.2.2.1
  have hrd : 1 ≤ D.host.rdE := by
    have hp : Real.pi ≤ D.host.v := (JDB.dataB_fam Fm x hx3 hx1 i).1
    unfold Host.v at hp
    linarith [Real.pi_gt_three]
  have hLa : L.sc.L ≤ L.La := by
    change _ ≤ Real.log ((L.sc.x * Real.exp L.sc.L) * D.host.rdE)
    rw [Real.log_mul (mul_pos (one_pos.trans L.sc.one_lt_alt) (Real.exp_pos _)).ne' (one_pos.trans_le hrd).ne',
      Real.log_mul (one_pos.trans L.sc.one_lt_alt).ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith [Real.log_nonneg L.sc.one_lt_alt.le, Real.log_nonneg hrd]
  let E := L.La + (D.R.m : ℝ)^2 * L.La / D.R.k
  have hLE : L.sc.L ≤ E := hLa.trans (le_add_of_nonneg_right (div_nonneg
    (mul_nonneg (sq_nonneg _) (by linarith [hsize.1] : 0 ≤ L.La)) hk.le))
  have hm : 1 ≤ (D.R.m : ℝ) := by linarith [(JDB.db_rk D).2.1]
  have hmL : L.sc.L ≤ (D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_left (by linarith [hsize.1]) hm
  constructor
  · have he := mul_le_mul_of_nonneg_left (hkL.trans hLE) hC
    change _ - C * E ≤ rankLog D D.u₀ at hl
    change _ - (2*C+4) * E ≤ _
    linarith only [hl, hv.1, h0.1, he, hsize.1, hLE]
  constructor
  · have he := mul_le_mul_of_nonneg_left (hkL.trans hmL) hC
    linarith only [hu, hv.2, h0.2, he, hsize.1, hmL]
  · intro u'
    have h1 := principal_level_log_vs_rank Fm x hx1 i u'
    have hv' := abs_le.mp (hw u')
    apply abs_le.mpr
    constructor <;> linarith only [hv.1, hv.2, hv'.1, hv'.2, h0.1, h0.2, h1.1, h1.2, hlog]

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.principal_count_of_reference_ranks
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
