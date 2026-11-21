import CheckAlpogePrincipalLevel
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin

/-! # Specialize the archive's geometric hypotheses before applying the zeta criterion -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.HC Formalism.MainNotions

/-- Only the estimates and window witnesses for the principal cyclic level enter.
The family and its witness may change when the exponent changes. -/
theorem rh_of_tied_principal_level {Fam : ℝ → Type 1}
    (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
    (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)
    {la : ℝ} (hla : 1 < la)
    (hc : ChebyshevInequalityOnWindows @core @Tied (Level.cyc PChar.one))
    (hw : ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc PChar.one)) :
    RiemannHypothesis := by
  apply rh_of_principal_level_windows hla
  obtain ⟨eD,eL,ε₁,h1,hs⟩ := hw
  intro θ hθ _
  obtain ⟨ε,hε,hsmall,hexp⟩ := exists_small_eps (eD+eL+7) (sub_pos.mpr hθ) h1
  obtain ⟨Fm,he,hW,hT⟩ := hs ε hε hsmall
  obtain ⟨x₁,hx⟩ := hc eD eL ε hε Fm he hT
  apply ((windows_iff _ la).mp hW).mono (x0 := max 1 x₁)
  intro x hxb hmem
  exact (hx x (le_of_max_le_right hxb) hmem).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_left hxb) (by linarith only [hexp]))

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let name := ``RiemannGaussian.AlpogeWindow.rh_of_tied_principal_level
  let axs ← Lean.collectAxioms name
  for ax in axs do
    unless [``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"{name} depends on {axs}"
