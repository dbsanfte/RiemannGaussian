import OAI.NumberTheory.DirichletL.Detector.LowRow
import OAI.NumberTheory.DirichletL.Detector.LowCutoff
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Exact native auxiliary-prime coefficient/window interface, without a rho input. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace OpenAIReview.AuxiliaryHeckeCorrelation
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CanonicalRowCompletion ProbeRow ProbeCompleted ProbePhysical
local notation "O" => ActualEisensteinCubic.O

/-- Evaluation of the actual cube coefficient, including nonprimitive J. -/
theorem native_cube_apply (Psi : O →* ℂ) (J : Ideal O) :
    cubeWeight Psi J = star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
      Psi (primaryGenerator J)^3 / (Ideal.absNorm J : ℂ) := rfl

/-- The actual row keeps the exact sextic multiplier even on nonunits. -/
theorem native_row_square (eta : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (l m a : O)
    (ha : Supported (Ideal.span {a})) :
    rowCoefficient eta Xi s hs (l^2*m) a =
      idealRowHom l (Ideal.span {a})^2 * rowCoefficient eta Xi s hs m a := by
  rw [rowCoefficient_apply, rowCoefficient_apply, idealRowHom_argument_mul,
    idealRowHom_argument_pow l 2 _ ha]
  ring

/-- Literal corrected coefficient scaling; every cube valuation and overlap stays. -/
theorem native_corrected_square (eta : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (l m : O)
    (S : Finset (Ideal O)) (D I J : Ideal O)
    (hI : Supported I) (hJ : Supported J) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D (rowCoefficient eta Xi s hs (l^2*m)) W X I J =
      (idealRowHom l I)^2 * (idealRowHom l J)^6 *
        correctedSummand S D (rowCoefficient eta Xi s hs m) W X I J := by
  have hi := (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1
  have hj := (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)).1
  have hri := native_row_square eta Xi s hs l m (primaryGenerator I) (hi.symm ▸ hI)
  have hrj := native_row_square eta Xi s hs l m (primaryGenerator J) (hj.symm ▸ hJ)
  rw [hi] at hri
  rw [hj] at hrj
  simp only [correctedSummand, markedSummand, summand, columnWeight,
    native_cube_apply, hri, hrj]
  ring

/-- Away from the auxiliary prime, the entire cube factor cancels exactly. -/
theorem native_corrected_square_coprime_cube (eta : HeckeFamily.Character)
    (Xi : O →* ℂ) (s : O) (hs : Supported (Ideal.span {s})) (l m : O)
    (S : Finset (Ideal O)) (D I J : Ideal O)
    (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime J (Ideal.span {l})) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D (rowCoefficient eta Xi s hs (l^2*m)) W X I J =
      (idealRowHom l I)^2 *
        correctedSummand S D (rowCoefficient eta Xi s hs m) W X I J := by
  have h6 := idealRowHom_sixth_mask l J hJ
  rw [idealRowHom_argument_pow l 6 J hJ, ite_eq_left hcop] at h6
  rw [native_corrected_square eta Xi s hs l m S D I J hI hJ W X, h6, mul_one]

/-- The actual canonical numerator window cannot contain both Hecke partners. -/
theorem native_window_square_disjoint (q x : ℝ) (hq : 7 ≤ q)
    (hx : lowOuterCutoff 1 4 x ≠ 0) : lowOuterCutoff 1 4 (q^2*x) = 0 := by
  have hb := lowOuterCutoff_support 1 4 (by norm_num) (by norm_num) hx
  have hq2 : 49 ≤ q^2 := by nlinarith [sq_nonneg (q-7)]
  have hx0 : 0 ≤ x := by linarith [hb.1]
  have hp := mul_le_mul_of_nonneg_right hq2 hx0
  exact lowOuterCutoff_large 1 4 (by norm_num) _ (by nlinarith [hb.1])

end OpenAIReview.AuxiliaryHeckeCorrelation
#lint+ in OpenAIReview.AuxiliaryHeckeCorrelation

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut decls : Nat := 0
  let mut thms : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    decls := decls+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then thms := thms+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless decls>0 do throwError "Empty auxiliary Hecke audit."
  logInfo m!"Auxiliary Hecke audit: {decls} declarations, {thms} theorems; standard axioms only."
  IO.FS.writeFile ".lake/arithmetic-operator-auxiliary-hecke-correlation-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal corrected native coefficient scaling, cube mask and actual physical-window separation; no rho theorem or saving"),
      ("declarations",toJson decls),("theoremsIncludingHelpers",toJson thms),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr reports)]).pretty
