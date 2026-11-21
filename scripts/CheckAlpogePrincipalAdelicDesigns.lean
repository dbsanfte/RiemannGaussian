import CheckAlpogePrincipalDesigns
import CheckAlpogePrincipalAdelicForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.GroupActionMulSingleEqDilation

/-! # Principal comparison designs from genuine level-zero forms -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

/-- Even for a small level prime, a nonzero genuine space has nonzero
ramified part. Every factor in the product rank formula is positive at an odd prime. -/
theorem ramified_dimension_pos_of_forms {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    0 < (D.mem u).A.du := by
  let A := (D.mem u).A
  obtain ⟨M⟩ := free_rank_model_of_split Tf (stabilizers_trivial_of_two_level_primes Tf)
    (splitAtT_of_tied Tf.atT)
  have h := ramified_rank_mul A M
  have ht : 2 < A.T := lt_of_le_of_ne A.T_prime.two_le (D.T_ne_two u).symm
  have hpos : 0 < D.duS u * (A.T - 2) ^ D.R.f :=
    Nat.mul_pos (unramified_dimension_pos_of_forms Tf) (pow_pos (by omega) _)
  change A.du * (A.T - 1) ^ D.R.f = D.duS u * (A.T - 2) ^ D.R.f at h
  rw [← h] at hpos
  exact Nat.pos_of_mul_pos_right hpos

theorem principal_family_rank_of_forms {ε : ℝ} (Fm : FamP ε) (h : HasLevelZeroForms Fm) :
    J.MuRank Fm := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := principal_family_nuFull Fm
  refine ⟨max a b, fun x hx i u => ?_⟩
  change 0 < (Fm.D x i).div.d u
  rw [(hb x (le_of_max_le_right hx) i).rank u]
  exact (ha x (le_of_max_le_left hx) i u).elim ramified_dimension_pos_of_forms

/-- A principal family construction which supplies level-zero forms does not
need separate hypotheses on ramified ranks, level-prime size or stabilizer size. -/
theorem rh_of_principal_adelic_designs (h : ∀ δ : ℝ, 0 < δ → ∃ ε eD eL : ℝ,
    0 < ε ∧ (eD + eL + 7) * ε ≤ δ ∧
      ∃ D : PrincipalComparisonData ε eD eL, HasLevelZeroForms D.family) : RiemannHypothesis := by
  apply rh_of_principal_designs
  intro δ hδ
  obtain ⟨ε, eD, eL, he, hloss, D, hD⟩ := h δ hδ
  exact ⟨ε, eD, eL, he, hloss, ⟨⟨D, principal_family_rank_of_forms _ hD⟩⟩⟩

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_adelic_designs
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
