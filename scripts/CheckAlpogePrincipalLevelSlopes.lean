import CheckAlpogePrincipalCountingDesigns
import Formalism.LocalToGlobal.GlobalTheory.PlacesMin

/-! # The remaining division-slope estimates at the level prime -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk
open Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

def LevelLengthBoundAt {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (C : ℝ) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u) ∧
    (L.lenMN u w : ℝ) ≤ C * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * D.duS u

/-- With no level operator at a place, its image is the ramified lattice itself.
The local quotient then has length zero. -/
theorem level_unseen {D : D7} {L : SizeData₂ D} (hNu : DV.NuDef D L) (hT : NuAtTDef D L)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T)
    (hs : (D.fm u).seenP w = false) :
    DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u) ∧ (L.lenMN u w : ℝ) = 0 := by
  have heq := Formalism.L2.GlobalTheoryTheory.Places.nlam_eq_sram D u w hs
  constructor
  · intro x hx
    have hloc : InLoc (D.plEq w) (L.NuLat u) x :=
      ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩
    have hmem := (hT u w hw x).1 hloc
    rw [heq] at hmem
    obtain ⟨s, hsu, hsx⟩ := D.locSpan u w _ hmem.1
    refine ⟨s, hsu, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    change (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
    rwa [map_smul]
  · have hz : DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 := by
      rw [D.lenLoc_atT hT u w hw, heq, Submodule.comap_subtype_self]
      exact Module.length_eq_zero_iff.2 (Submodule.Quotient.subsingleton_iff.2 rfl)
    have hh := hNu.2.2 u w 0 hz
    have he : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (D.what₂.places.ramIdx_pos w).ne'
    exact (mul_eq_zero.mp (by simpa using hh.symm)).resolve_right he

/-- At the level prime we use the mean slope, local containment and an upper
bound for each local length in terms of the unramified dimension. -/
def LevelLatticeEstimates {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ C a : ℝ, 0 ≤ C ∧ ∀ x ≥ a, ∀ (i : Fm.Ix x) u,
    RamifiedSlopeFormula (Fm.D x i) u ∧ LevelLengthBoundAt (Fm.L x i) u C

private theorem level_rank_and_max {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (LocalQuadraticParts.MuH D u).muMax ≤ ((D.fm u).lat 0).muMax := by
  obtain ⟨M⟩ := free_rank_model_of_split Tf (stabilizers_trivial_of_two_level_primes Tf) (splitAtT_of_tied Tf.atT)
  have hT : 3 ≤ (D.mem u).A.T :=
    lt_of_le_of_ne (D.mem u).A.T_prime.two_le (D.T_ne_two u).symm
  have hr : ((D.mem u).A.du : ℚ) = (D.duS u : ℚ) * (1 - 1 / (((D.mem u).A.T : ℚ) - 1)) ^ D.R.f :=
    ramified_rank_of_model _ M hT
  have hcast := congrArg (Rat.cast : ℚ → ℝ) hr
  push_cast at hcast
  refine ⟨hcast.trans (mul_comm _ _), ?_⟩
  rw [show (LocalQuadraticParts.MuH D u).muMax = (D.fm u).ramLat.muMax from (D.ram_slopes u).2.1]
  exact ramified_max_slope_le D u (ramified_lattice_ne_bot D u
    (ramified_forms_ne_bot D u M hT (unramified_dimension_pos_of_forms Tf)))

private theorem level_length_sum {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (B : ℝ) (hB : 0 ≤ B)
    (hr : 0 < (D.mem u).A.du) (hd : (D.duS u : ℝ) ≤ 2 * ((D.mem u).A.du : ℝ))
    (hlen : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (L.lenMN u w : ℝ) ≤ B * D.duS u)
    (S : Finset D.what₂.places.Pl) (hS : ∀ w ∈ S, D.what₂.places.resChar w = (D.mem u).A.T) :
    (∑ w ∈ S, SizeData₂.sz w (L.lenMN u w)) / ((D.mem u).A.du : ℝ) ≤
      4 * B * Real.log ((D.mem u).A.T : ℝ) := by
  let r : ℝ := (D.mem u).A.du
  have hr' : 0 < r := Nat.cast_pos.mpr hr
  apply (div_le_iff₀ hr').2
  calc ∑ w ∈ S, SizeData₂.sz w (L.lenMN u w)
      ≤ ∑ w ∈ S, (4 * B * r) * lE w := by
        apply Finset.sum_le_sum
        intro w hw
        have hm := (hlen w (hS w hw)).trans (mul_le_mul_of_nonneg_left hd hB)
        have hw0 : 0 ≤ lE w := mul_nonneg (J.logWeight_nonneg w) (Nat.cast_nonneg _)
        rw [sz_eq]
        change _ ≤ 4 * B * (D.mem u).A.du * lE w
        linarith only [mul_le_mul_of_nonneg_left hm hw0]
    _ = (4 * B * r) * ∑ w ∈ S, lE w := (Finset.mul_sum ..).symm
    _ ≤ (4 * B * r) * Real.log ((D.mem u).A.T : ℝ) := mul_le_mul_of_nonneg_left
      (J.sum_lwP_e_le D _ (D.mem u).A.T_prime S hS) (by positivity)
    _ = _ := by ring

theorem principal_level_estimates_of_forms {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm)
    (hf : HasLevelZeroForms Fm) (hlocal : LevelLatticeEstimates Fm) : LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨C, a, hC, ha⟩ := hlocal
  obtain ⟨b, hb⟩ := principal_ramified_share_of_forms Fm
    (levelPrimeGrowth_of_tuGe (principal_level_lower_of_count Fm hcount)) hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨4 * C, max (max a b) (max c (Fm.x1 + 1)), fun x hx i u => ?_⟩
  let D := Fm.D x i
  let L := Fm.L x i
  obtain ⟨Tf⟩ := hc x (le_of_max_le_left (le_of_max_le_right hx)) i u
  obtain ⟨hs, hl⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i u
  obtain ⟨hRank, hMax⟩ := level_rank_and_max Tf
  have he := fam_eps_pos Fm
  have hlate : Fm.x1 < x := by linarith only [le_of_max_le_right (le_of_max_le_right hx)]
  have hx1 : 1 ≤ x := (Fm.one_lt_family_threshold.trans hlate).le
  have htwo : 2 ≤ Real.exp (x ^ (ε/8)) :=
    (by linarith [Real.exp_one_gt_d9] : (2 : ℝ) ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr (Real.one_le_rpow hx1 (by positivity)))
  obtain ⟨de, hd, hsq, hdim⟩ := hb x (le_of_max_le_right (le_of_max_le_left hx)) i
  rw [Real.exp_neg, ← one_div] at hsq
  have hhalf := hsq.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo)
  have hde : de ≤ 1/2 := by
    nlinarith only [Real.sq_sqrt hd, mul_self_le_mul_self (Real.sqrt_nonneg de) hhalf]
  have hdim' : (D.duS u : ℝ) ≤ 2 * ((D.mem u).A.du : ℝ) := by
    linarith only [(hdim u).trans (mul_le_mul_of_nonneg_right hde (Nat.cast_nonneg _))]
  let B := C * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b')
  have hB : 0 ≤ B := by
    have hsa : 0 < L.sc.a := mul_pos (zero_lt_one.trans L.sc.one_lt_alt) (Real.exp_pos _)
    have hsb : 0 < L.sc.b' := div_pos hsa (Real.exp_pos _)
    have hTT : 0 ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
    dsimp only [B]
    positivity
  have hall (w) (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
      DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u) ∧ (L.lenMN u w : ℝ) ≤ B * D.duS u := by
    cases hseen : (D.fm u).seenP w with
    | true => exact hl w hw hseen
    | false =>
      obtain ⟨hinc, hz⟩ := level_unseen (Fm.nuDef x hlate i) (Fm.ex x hlate i).lat.atT u w hw hseen
      exact ⟨hinc, hz.trans_le (mul_nonneg hB (Nat.cast_nonneg _))⟩
  refine ⟨hRank, (D.ram_slopes u).1.trans hs, hMax, fun w hw => (hall w hw).1, ?_⟩
  intro S hS
  have hsum := level_length_sum L u B hB (ramified_dimension_pos_of_forms Tf) hdim'
    (fun w hw => (hall w hw).2) S hS
  calc _ ≤ _ := hsum
       _ = _ := by dsimp only [B, D, L]; ring

/-- The level-size bound holds with the constant from the upper counting inequality. -/
theorem principal_level_size_of_count {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm) :
    ∃ C : ℝ, TuSize ({ Fm with CTu := C } : FamP ε) := by
  obtain ⟨t, ht⟩ := principal_level_lower_of_count Fm hcount
  obtain ⟨C, a, _, ha⟩ := hcount
  exact ⟨C, max t a, fun x hx i =>
    ⟨ht x (le_of_max_le_left hx) i, fun u => (ha x (le_of_max_le_right hx) i u).2.1⟩⟩

/-- Commensurability and rank come from the forms and the defining lattices.
The count supplies the two level-size inequalities for the place comparison. -/
theorem principal_places_of_level_estimates {ε : ℝ} (Fm : FamP ε) (hcount : CountF Fm)
    (hf : HasLevelZeroForms Fm) (hg : LinkG Fm) (hlocal : LevelLatticeEstimates Fm) : PlacesF Fm := by
  have h26 := principal_level_estimates_of_forms Fm hcount hf hlocal
  obtain ⟨C, hTu⟩ := principal_level_size_of_count Fm hcount
  let F' : FamP ε := { Fm with CTu := C }
  have hcomm : NuCommensF F' := by
    refine ⟨Fm.x1 + 1, fun x hx i u => ?_⟩
    have hx' : Fm.x1 < x := by linarith
    exact principal_nu_commens (Fm.nuDef x hx' i) (Fm.ex x hx' i).lat.atT u
  have hr := principal_family_rank_of_forms Fm hf
  exact Formalism.L2.GlobalTheoryTheory.Places.placesF_min' F' h26 hcomm hTu hr hg (principal_family_linkMu Fm hr)

theorem rh_of_principal_level_lattice_designs (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ 1 ≤ D.C0 ∧
    HasLevelZeroForms D.family ∧ D.family.CoverAll ∧ CountF D.family ∧ SlopesMF D.family ∧ LevelLatticeEstimates D.family) :
    RiemannHypothesis := by
  apply rh_of_principal_counting_designs
  intro δ hδ
  obtain ⟨ε, D, hδ', hC, hH, hC0, hf, hc, hn, hm, hl⟩ := h δ hδ
  exact ⟨ε, D, hδ', hC, hH, hC0, hf, hc, hn, hm, principal_places_of_level_estimates D.family hn hf D.linkG hl⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_level_lattice_designs
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
