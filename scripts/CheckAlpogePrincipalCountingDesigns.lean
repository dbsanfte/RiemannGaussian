import CheckAlpogePrincipalFrame
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime

/-! # Principal comparison from family counts and slopes -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk
open Formalism.MainNotions.GlobalTheoryTheory

/-- The lower half of the counting inequality already forces the level prime
above b^(m/2). Its main term grows as 16 m L while the error is at most 8 C L. -/
theorem principal_level_lower_of_count {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm) :
    ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x, (Fm.L x i).TuGe := by
  obtain ⟨C, a, hC, ha⟩ := hcount
  obtain ⟨b, hb⟩ := m_large Fm (C + 1)
  obtain ⟨c, hc⟩ := ev_pow_le_exp 1 ε 1 one_pos (fam_eps_pos Fm)
  refine ⟨max (max a b) (max c (max 3 (Fm.x1 + 1))), fun x hx i u => ?_⟩
  have h₁ := le_of_max_le_left hx
  have h₂ := le_of_max_le_right hx
  have h₃ := le_of_max_le_right h₂
  have hx₁ : Fm.x1 < x := by linarith only [le_of_max_le_right h₃]
  have hx₃ : 3 ≤ x := le_of_max_le_left h₃
  let D := Fm.D x i
  let L := Fm.L x i
  have hL₁ : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hLx : Real.log L.sc.x ≤ L.sc.L := by
    have hh := hc x (le_of_max_le_left h₂) (by linarith only [hx₃])
    rw [Real.rpow_one, one_mul] at hh
    change Real.log (Fm.L x i).sc.x ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    rw [Fm.L_x x i hx₁, Fm.L_eps x i]
    exact (Real.log_le_iff_le_exp (by linarith only [hx₃])).2 hh
  have hB := JDB.dataB_fam Fm x hx₃ hx₁ i
  have hv : 0 < D.host.v := Real.pi_pos.trans_le hB.1
  have hLa : L.La ≤ 4 * L.sc.L := by
    have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
    change Real.log (L.sc.x * Real.exp L.sc.L * D.host.rdE) ≤ _
    rw [hrd, Real.log_mul (mul_pos (zero_lt_one.trans L.sc.one_lt_alt) (Real.exp_pos _)).ne'
      (mul_pos (by norm_num) hv).ne', Real.log_mul (zero_lt_one.trans L.sc.one_lt_alt).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hv.ne']
    linarith only [hLx, hB.2.1, hL₁, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmk : (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    have H : (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k := hB.2.2.2.1
    exact (le_mul_of_one_le_right (sq_nonneg _) hL₁).trans H
  have hk : 0 < (D.R.k : ℝ) := by exact_mod_cast (show 0 < D.R.k by have := D.R.m_add_three_le_k; omega)
  have hterm : (D.R.m : ℝ) ^ 2 * L.La / D.R.k ≤ 4 * L.sc.L := by
    apply (div_le_iff₀ hk).2
    calc _ ≤ (D.R.m : ℝ) ^ 2 * (4 * L.sc.L) := mul_le_mul_of_nonneg_left hLa (sq_nonneg _)
         _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmk (by linarith only [hL₁])
  have herror := mul_le_mul_of_nonneg_left (add_le_add hLa hterm) hC
  have hmain := lowB_ge D L.sc _ 0 _ _ hB
  simp only [max_self, zero_mul, sub_zero, StandardLattice.lowB, Fin.sum_univ_two] at hmain
  have hcuw := (ha x (le_of_max_le_left h₁) i u).1
  change (∑ j ∈ SizeData₂.lifts D, 1 / (D.R.f : ℝ) *
      ∑ τ, Real.log (wj D j τ * D.host.v / Real.pi)) + D.R.m * lgG D -
      C * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ) at hcuw
  have heq : SizeData₂.lifts D = Finset.Ico (0 + 1) (D.R.m + 1) := by ext j; simp [SizeData₂.lifts]
  rw [heq, ← Finset.sum_Ico_add' (fun j => 1 / (D.R.f : ℝ) *
    ∑ τ, Real.log (wj D j τ * D.host.v / Real.pi)) 0 D.R.m 1, ← Finset.range_eq_Ico,
    lgG, Real.log_mul (Nat.cast_ne_zero.mpr (D.host.g_prime 0).ne_zero)
      (Nat.cast_ne_zero.mpr (D.host.g_prime 1).ne_zero)] at hcuw
  have hm := mul_le_mul_of_nonneg_right (hb x (le_of_max_le_right h₁) hx₁ i) (show 0 ≤ L.sc.L by linarith)
  have hCL := mul_nonneg hC (show 0 ≤ L.sc.L by linarith)
  change Real.exp L.sc.L ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ)
  rw [← Real.exp_mul]
  apply (Real.le_log_iff_exp_le (by exact_mod_cast (D.mem u).A.T_prime.pos)).1
  change (C + 1) * L.sc.L ≤ (D.R.m : ℝ) * L.sc.L at hm
  linarith only [hmain, hcuw, herror, hm, hCL, hL₁]

/-- The chosen bad-prime and top-set bounds, with the group comparison,
give the point estimates needed for zero small-prime loss. -/
theorem principal_global_of_counts {ε Cabs CH C0 : ℝ} (Fm : FamP ε)
    (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 1 ≤ C0) (hforms : HasLevelZeroForms Fm)
    (hcov : Fm.CoverAll) (hCount : CountF Fm) (hSM : SlopesMF Fm) (hPlaces : PlacesF Fm) :
    LinkGLOBAL Fm Cabs CH C0 Cabs 0 := by
  intro hchosen hin
  have hpoints : StatementsAtPointsLargeScales Fm := by
    obtain ⟨_, _, Cb, _, _, _, _, hTT, hBad, _⟩ := hchosen
    exact Formalism.L2.GlobalTheoryTheory.Loss.loss_points_of_choices Fm Cb hTT hBad hin.1
  exact principal_global_of_points Fm hCabs hCH hC0 (levelPrimeGrowth_of_tuGe (principal_level_lower_of_count Fm hCount))
    hforms hcov hCount hSM hPlaces hpoints hchosen hin

/-- The global comparison on a covering design can be supplied by the count,
the base-lattice slopes and the place estimates, with eL = 0. -/
theorem rh_of_principal_counting_designs (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ 1 ≤ D.C0 ∧
    HasLevelZeroForms D.family ∧ D.family.CoverAll ∧ CountF D.family ∧ SlopesMF D.family ∧ PlacesF D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_adelic_designs
  intro δ hδ
  obtain ⟨ε, D, hloss, hC, hH, hC0, hf, hcov, hn, hm, hp⟩ := h δ hδ
  exact ⟨ε, D.Cabs, 0, fam_eps_pos D.family, by simpa using hloss,
    ⟨D, principal_global_of_counts D.family hC hH hC0 hf hcov hn hm hp⟩, hf⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_counting_designs
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
