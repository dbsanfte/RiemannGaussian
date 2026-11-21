import CheckAlpogePrincipalLevelSlopes
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeFormulaOfCharacterFinite
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni

/-! # The ramified mean slope from the two auxiliary roots of unity -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.L2.Forms
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

/-- At step zero the unipotent character has no multiplicative blocks.
Roots of orders g₀ and g₁ in the coefficient field suffice for all its values. -/
theorem finite_level_character_of_roots {D : D7} {u : D.what₂.Word} (T : Forms0 D u)
    (hroot : ∀ k, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.host.g k)) : ChiFin0 T := by
  obtain ⟨n, hn, hx⟩ := GlobalTheory.unipotent_type_character_finite_order
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime hroot
  refine ⟨n, hn, fun i hi h x => ?_⟩
  subst i
  exact hx x

/-- The large-scale Hida setting follows from counting. Thus the geometric
mean-slope formula applies to the actual forms wherever the auxiliary roots exist. -/
theorem principal_level_estimates_of_roots {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (hf : HasLevelZeroForms Fm) (h : ∃ C a : ℝ, 0 ≤ C ∧ ∀ x ≥ a, ∀ i : Fm.Ix x,
      (∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)) ∧
      ∀ u, LevelLengthBoundAt (Fm.L x i) u C) : LevelLatticeEstimates Fm := by
  obtain ⟨K, hK⟩ := principal_level_size_of_count Fm hn
  let F' : FamP ε := { Fm with CTu := K }
  obtain ⟨b, hb⟩ := Formalism.L2.GlobalTheoryTheory.Places.settingF_of F' hK
  obtain ⟨c, hc⟩ := hf
  obtain ⟨C, a, hC, ha⟩ := h
  refine ⟨C, max (max a b) (max c (Fm.x1 + 1)), hC, fun x hx i u => ?_⟩
  have hx₁ : Fm.x1 < x := by linarith only [le_of_max_le_right (le_of_max_le_right hx)]
  obtain ⟨hr, hlen⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
  obtain ⟨T⟩ := hc x (le_of_max_le_left (le_of_max_le_right hx)) i u
  exact ⟨slope_formula_of_character_finite (hb x (le_of_max_le_right (le_of_max_le_left hx)) hx₁ i u)
    T (finite_level_character_of_roots T hr) (stabilizers_trivial_of_two_level_primes T), hlen u⟩

/-- The counting inequality controls the weight sum in the integral congruence
estimate, giving the same local length constant 9 for every selected family. -/
theorem principal_level_lengths_of_congruence {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, CongruenceLatticeLengthBound (Fm.D x i) u) :
    ∃ b : ℝ, ∀ x ≥ b, ∀ (i : Fm.Ix x) u, LevelLengthBoundAt (Fm.L x i) u 9 := by
  obtain ⟨K, hK⟩ := principal_level_size_of_count Fm hn
  let F' : FamP ε := { Fm with CTu := K }
  obtain ⟨C, hW⟩ := J.numsL_wtsL_fam F' hK (Formalism.L2.GlobalTheoryTheory.Places.dlSize _ F')
  obtain ⟨b, hb⟩ := hW C le_rfl 3 le_rfl
  obtain ⟨a, ha⟩ := h
  refine ⟨max (max a b) (Fm.x1 + 1), fun x hx i u w hw _ => ?_⟩
  have hx' : Fm.x1 < x := by linarith only [le_of_max_le_right hx]
  let D := Fm.D x i
  let L := Fm.L x i
  have hc := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
  have hT := (Fm.ex x hx' i).lat.atT
  have hNu := Fm.nuDef x hx' i
  have hW := hb x (le_of_max_le_right (le_of_max_le_left hx)) i
  have hsum := J.fifthLevelSizes_of_weights (by norm_num : (1 : ℝ) ≤ 3) hW.1 hW.2 u w hw
  obtain ⟨_, n, hlen, hbound⟩ := hc u w hw
  have hnorm := hNu.2.2 u w n ((J.lenAtT D L hT u w hw).trans hlen)
  refine ⟨nuAtT_of hT (fun v t ht => (hc v t ht).1) u w hw, ?_⟩
  have hram : 0 < (D.what₂.places.ramIdx w : ℝ) := Nat.cast_pos.mpr (D.what₂.places.ramIdx_pos w)
  have hupper : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) *
      (D.R.m * D.duS u * (9 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b'))) :=
    hbound.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hram.le)
  apply (le_of_mul_le_mul_left (a := (D.what₂.places.ramIdx w : ℝ)) _ hram)
  calc (D.what₂.places.ramIdx w : ℝ) * (L.lenMN u w : ℝ) = n := (mul_comm _ _).trans hnorm.symm
       _ ≤ _ := hupper
       _ = _ := by ring

/-- The archive's integral congruence bound is sufficient for the entire
level-lattice estimate. Counting fixes its normalized local constant at 9. -/
theorem principal_level_estimates_of_congruence {ε : ℝ} (Fm : FamP ε) (hn : CountF Fm)
    (hf : HasLevelZeroForms Fm) (h : ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x,
      (∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)) ∧
      ∀ u, CongruenceLatticeLengthBound (Fm.D x i) u) : LevelLatticeEstimates Fm := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := principal_level_lengths_of_congruence Fm hn ⟨a, fun x hx i => (ha x hx i).2⟩
  exact principal_level_estimates_of_roots Fm hn hf ⟨9, max a b, by norm_num, fun x hx i =>
    ⟨(ha x (le_of_max_le_left hx) i).1, hb x (le_of_max_le_right hx) i⟩⟩

/-- For a principal family with the two auxiliary roots of unity in its
coefficient fields, the only extra conditions at the level prime are the
local lattice inclusions and the bounds on their individual lengths. -/
theorem rh_of_principal_character_designs (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
    (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧ 1 ≤ D.C0 ∧
    HasLevelZeroForms D.family ∧ D.family.CoverAll ∧ CountF D.family ∧ SlopesMF D.family ∧
    ∃ C a : ℝ, 0 ≤ C ∧ ∀ x ≥ a, ∀ i : D.family.Ix x,
      (∀ k, ∃ z : (D.family.D x i).what₂.LL, IsPrimitiveRoot z ((D.family.D x i).host.g k)) ∧
      ∀ u, LevelLengthBoundAt (D.family.L x i) u C) : RiemannHypothesis := by
  apply rh_of_principal_level_lattice_designs
  intro δ hδ
  obtain ⟨ε, D, hloss, habs, hch, h0, hf, hc, hn, hm, hl⟩ := h δ hδ
  exact ⟨ε, D, hloss, habs, hch, h0, hf, hc, hn, hm, principal_level_estimates_of_roots D.family hn hf hl⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.principal_level_estimates_of_congruence,
      ``RiemannGaussian.AlpogeWindow.rh_of_principal_character_designs] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
