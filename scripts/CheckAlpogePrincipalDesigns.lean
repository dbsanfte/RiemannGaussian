import CheckAlpogePrincipalFamily
import CheckAlpogePrincipalRounding
import CheckAlpogePrincipalRankBound

/-! # Principal geometric designs with arbitrarily small total exponent loss -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

/-- The principal class and local comparisons on a single selected family. -/
structure PrincipalLocalComparisonData (ε : ℝ) where
  family : FamP ε
  principal : (GChi PChar.one).cls (3/2) family
  Cabs : ℝ
  CH : ℝ
  C0 : ℝ
  chosen : ChosenE family C0 CH
  linkN : LinkN family
  linkEta : LinkEta family
  irreducibility : LinkIRR family
  liftRank : BoundedLiftRank family
  division : LinkDIVt family Cabs CH
  linkG : LinkG family
  linkS : LinkS family C0

/-- The constants and the losses in the global comparison may vary with the family. -/
structure PrincipalComparisonData (ε eD eL : ℝ) extends PrincipalLocalComparisonData ε where
  global : LinkGLOBAL family Cabs CH C0 eD eL

structure PrincipalComparisonDesign (ε eD eL : ℝ) extends PrincipalComparisonData ε eD eL where
  muRank : J.MuRank family

/-- The principal window implication needs just one winning design for each
positive exponent loss. All estimates used to tie a design refer to that family. -/
theorem rh_of_principal_designs (h : ∀ δ : ℝ, 0 < δ → ∃ ε eD eL : ℝ,
    0 < ε ∧ (eD + eL + 7) * ε ≤ δ ∧ Nonempty (PrincipalComparisonDesign ε eD eL)) :
    RiemannHypothesis := by
  apply rh_of_principal_level_windows (la := 3/2) (by norm_num)
  intro θ hθ _
  obtain ⟨ε,eD,eL,hε,hloss,⟨D⟩⟩ := h (θ - 1/2) (sub_pos.mpr hθ)
  have hdiv := D.division D.linkEta (divinN_of_bounded_rank D.family hε
    (hypV_of_cls PChar.one (3/2) D.family D.principal) D.linkN D.liftRank)
  have hmu := principal_family_linkMu D.family D.muRank
  have htied := D.global D.chosen ⟨D.linkG,D.linkS,D.irreducibility,hdiv,hmu⟩
  obtain ⟨x₁,hx⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales (Level.cyc PChar.one)
    eD eL ε hε D.family (eFamC_of_cls PChar.one (3/2) D.family D.principal) htied
  apply ((windows_iff D.family.toFamCore (3/2)).mp D.principal.1).mono (x0 := max 1 x₁)
  intro x hx₀ hwin
  exact (hx x (le_of_max_le_right hx₀) hwin).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_left hx₀) (by linarith only [hloss]))

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.rh_of_principal_designs
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
