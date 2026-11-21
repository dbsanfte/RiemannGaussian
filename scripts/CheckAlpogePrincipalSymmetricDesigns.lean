import CheckAlpogePrincipalColumnSlopes
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified

/-! # Recovering the local comparisons from symmetric column data -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.L2.Forms
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

/-- The geometric data are required only on the selected family, after a
threshold that may depend on the exponent loss. -/
def HasSymmetricColumnsAndRoots {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x, Nonempty (ColsTiedSym (Fm.D x i)) ∧
    ∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)

/-- At each word the symmetric form has trivial class stabilizers and its
level character takes finite-order values in the coefficient field. -/
def SymmetricLevelInputs {D : D7} (F : ColsTiedSym D) (u : D.what₂.Word) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ∀ x : ((F.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U,
    ((((F.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
    ∃ r : D.what₂.LL, D.what₂.embLL r = ((((F.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)) ∧
  product_first_zeroth_parts.admS D u

theorem symmetric_level_inputs_of_roots {D : D7} (F : ColsTiedSym D)
    (hr : ∀ k, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.host.g k)) (u : D.what₂.Word) :
    SymmetricLevelInputs F u := by
  obtain ⟨n, hn, hχ⟩ := finite_level_character_of_roots (F.forms u).to0 hr
  exact ⟨⟨n, hn, hχ 0 (Nat.zero_le _) rfl⟩, stabilizers_trivial_of_two_level_primes (F.forms u).to0⟩

/-- The count supplies the Hida setting for the column and integral Hecke estimates at each word. -/
theorem principal_column_estimates_of_symmetric {ε : ℝ} (Fm : FamP ε)
    (hcol : ∀ (D : D7), ColsTiedSym D → flipTwoThree.adm3 D → ∀ u, Nonempty (flipTwoThree.ColVal D u))
    (hhecke : ∀ (D : D7) (F : ColsTiedSym D) u, product_first_zeroth_parts.HidaSetting D u →
      SymmetricLevelInputs F u → SecondBranchInclusionLength D u ∧ HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u)
    (hn : CountF Fm) (hc : HasSymmetricColumnsAndRoots Fm) :
    HasLevelZeroForms Fm ∧ ∃ a : ℝ, ∀ x ≥ a, ∀ i : Fm.Ix x,
      (∀ k, ∃ z : (Fm.D x i).what₂.LL, IsPrimitiveRoot z ((Fm.D x i).host.g k)) ∧
      ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u) ∧ CongruenceLatticeLengthBound (Fm.D x i) u := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨K, hK⟩ := principal_level_size_of_count Fm hn
  let F' : FamP ε := { Fm with CTu := K }
  obtain ⟨b, hb⟩ := Formalism.L2.GlobalTheoryTheory.Places.settingF_of F' hK
  refine ⟨⟨a, fun x hx i u => ?_⟩, max (max a b) (Fm.x1 + 1), fun x hx i => ?_⟩
  · obtain ⟨F⟩ := (ha x hx i).1
    exact ⟨(F.forms u).to0⟩
  · obtain ⟨⟨F⟩, hr⟩ := ha x (le_of_max_le_left (le_of_max_le_left hx)) i
    have hx' : Fm.x1 < x := by linarith only [le_of_max_le_right hx]
    have hadm : flipTwoThree.adm3 (Fm.D x i) :=
      fun u => stabilizers_trivial_of_two_level_primes (F.forms u).to0
    refine ⟨hr, fun u => ⟨hcol _ F hadm u, ?_⟩⟩
    have hs := hb x (le_of_max_le_right (le_of_max_le_left hx)) hx' i u
    obtain ⟨hB, hI, hR⟩ := hhecke _ F u hs (symmetric_level_inputs_of_roots F hr u)
    exact congruence_no_kernel_minimal hs hB hI hR

/-- The column comparison and the integral Hecke statements give the RH criterion on a covering family. -/
theorem rh_of_principal_symmetric_comparisons
    (hcol : ∀ (D : D7), ColsTiedSym D → flipTwoThree.adm3 D → ∀ u, Nonempty (flipTwoThree.ColVal D u))
    (hhecke : ∀ (D : D7) (F : ColsTiedSym D) u, product_first_zeroth_parts.HidaSetting D u →
      SymmetricLevelInputs F u → SecondBranchInclusionLength D u ∧ HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u)
    (h : ∀ δ : ℝ, 0 < δ → ∃ (ε : ℝ) (D : PrincipalLocalComparisonData ε),
      (D.Cabs + 7) * ε ≤ δ ∧ 0 ≤ D.Cabs ∧ 0 < D.CH ∧
      D.family.CoverAll ∧ CountF D.family ∧ HasSymmetricColumnsAndRoots D.family) : RiemannHypothesis := by
  apply rh_of_principal_column_designs
  intro δ hδ
  obtain ⟨ε, D, hloss, habs, hch, hc, hn, hs⟩ := h δ hδ
  obtain ⟨hf, hest⟩ := principal_column_estimates_of_symmetric D.family hcol hhecke hn hs
  exact ⟨ε, D, hloss, habs, hch, hf, hc, hn, hest⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_symmetric_comparisons
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
