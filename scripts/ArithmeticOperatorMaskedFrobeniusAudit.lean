/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Exact native-cutoff obstruction to a masked Frobenius row operation

The integer congruence x^p = x mod p survives multiplication by a cutoff.
Preserving the same determinant additionally requires the lower *masked*
correction to lie in the preceding row span. The literal cutoff 2*n <= 4
fails that requirement on the common columns n=1,2,3. Closing the masked
flags repairs the operation but changes the retained degrees and determinant.
These are finite integer examples, not an arithmetic source estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Matrix
namespace RiemannGaussian.ArithmeticOperatorMaskedFrobeniusAudit

/-- The precise native cutoff on the three common positive columns. -/
def cutoffMask (j : Fin 3) : ℤ := if 2 * (j.val + 1) ≤ 4 then 1 else 0

/-- Rows 1,n,1_(2*n<=4)*n^2. -/
def maskedOriginal : Matrix (Fin 3) (Fin 3) ℤ := !![1,1,1; 1,2,3; 1,4,0]

/-- The last row is pointwise even after the valid integer Frobenius rewrite. -/
def maskedReplacement : Matrix (Fin 3) (Fin 3) ℤ := !![1,1,1; 1,2,3; 0,2,0]

/-- The unpaid boundary correction is 1_(2*n<=4)*n. -/
def maskedCorrection : Matrix (Fin 3) (Fin 3) ℤ := !![1,1,1; 1,2,3; 1,2,0]

theorem masked_row_is_literal_cutoff (j : Fin 3) :
    maskedOriginal 2 j = cutoffMask j * ((j.val + 1 : ℕ) : ℤ)^2 := by
  fin_cases j <;> norm_num [maskedOriginal, cutoffMask]

theorem replacement_is_literal_frobenius (j : Fin 3) :
    maskedReplacement 2 j = cutoffMask j *
      ((((j.val + 1 : ℕ) : ℤ)^2) - ((j.val + 1 : ℕ) : ℤ)) := by
  fin_cases j <;> norm_num [maskedReplacement, cutoffMask]

theorem correction_is_literal_boundary (j : Fin 3) :
    maskedCorrection 2 j = cutoffMask j * ((j.val + 1 : ℕ) : ℤ) := by
  fin_cases j <;> norm_num [maskedCorrection, cutoffMask]

theorem exact_row_residual (j : Fin 3) :
    maskedOriginal 2 j = maskedReplacement 2 j + maskedCorrection 2 j := by
  fin_cases j <;> norm_num [maskedOriginal, maskedReplacement, maskedCorrection]

theorem replacement_row_even (j : Fin 3) : 2 ∣ maskedReplacement 2 j := by
  fin_cases j <;> norm_num [maskedReplacement]

theorem masked_original_det : maskedOriginal.det = -7 := by
  norm_num [Matrix.det_fin_three, maskedOriginal]

theorem masked_replacement_det : maskedReplacement.det = -4 := by
  norm_num [Matrix.det_fin_three, maskedReplacement]

theorem masked_correction_det : maskedCorrection.det = -3 := by
  norm_num [Matrix.det_fin_three, maskedCorrection]

theorem exact_determinant_residual :
    maskedOriginal.det = maskedReplacement.det + maskedCorrection.det := by
  rw [masked_original_det, masked_replacement_det, masked_correction_det]
  norm_num

theorem original_not_even : ¬ (2 : ℤ) ∣ maskedOriginal.det := by
  rw [masked_original_det]
  norm_num

theorem replacement_changes_determinant : maskedReplacement.det ≠ maskedOriginal.det := by
  rw [masked_original_det, masked_replacement_det]
  norm_num

/-- Even a rational lower-row combination cannot absorb this correction. -/
theorem correction_not_in_earlier_span : ¬ ∃ a b : ℚ, ∀ j : Fin 3,
    (maskedCorrection 2 j : ℚ) = a * (maskedOriginal 0 j : ℚ) +
      b * (maskedOriginal 1 j : ℚ) := by
  rintro ⟨a,b,h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [maskedCorrection, maskedOriginal] at h0 h1 h2
  linarith

/-- Repair on the same columns: inside constants, inside n, outside constants.
The degree-two row is no longer retained. -/
def repairedThree : Matrix (Fin 3) (Fin 3) ℤ := !![1,1,0; 1,2,0; 0,0,1]

theorem repaired_three_det : repairedThree.det = 1 := by
  norm_num [Matrix.det_fin_three, repairedThree]

/-- A larger repaired flag at cutoff 2*n<=6 retains one degree-two row. -/
def repairedFour : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,1,1,0; 1,2,3,0; 1,4,9,0; 0,0,0,1]

/-- The same masked flag with its degree-two row replaced by n^2-n. -/
def repairedFourReplacement : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,1,1,0; 1,2,3,0; 0,2,6,0; 0,0,0,1]

theorem repaired_four_row_identity (j : Fin 4) :
    repairedFourReplacement 2 j = repairedFour 2 j - repairedFour 1 j := by
  fin_cases j <;> norm_num [repairedFourReplacement, repairedFour]

theorem repaired_four_det : repairedFour.det = 2 := by
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, repairedFour,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]

theorem repaired_four_replacement_det : repairedFourReplacement.det = 2 := by
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, repairedFourReplacement,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]

theorem repaired_four_same_nonzero_det :
    repairedFourReplacement.det = repairedFour.det ∧ repairedFour.det ≠ 0 := by
  rw [repaired_four_det, repaired_four_replacement_det]
  norm_num

/-- A second prime, with the same positive columns, shows the same cutoff defect. -/
def maskedPrimeThree : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,1,1,1; 1,2,3,4; 1,4,9,16; 1,8,27,0]

theorem masked_prime_three_det : maskedPrimeThree.det = -116 := by
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, maskedPrimeThree,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]

theorem prime_three_literal_cutoff (j : Fin 4) :
    maskedPrimeThree 3 j = (if 3 * (j.val + 1) ≤ 9 then (1 : ℤ) else 0) *
      ((j.val + 1 : ℕ) : ℤ)^3 := by
  fin_cases j <;> norm_num [maskedPrimeThree]

/-- The p=3 pointwise Frobenius rewrite, still on the original four columns. -/
def maskedPrimeThreeReplacement : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,1,1,1; 1,2,3,4; 1,4,9,16; 0,6,24,0]

theorem prime_three_literal_replacement (j : Fin 4) :
    maskedPrimeThreeReplacement 3 j =
      (if 3 * (j.val + 1) ≤ 9 then (1 : ℤ) else 0) *
        ((((j.val + 1 : ℕ) : ℤ)^3) - ((j.val + 1 : ℕ) : ℤ)) := by
  fin_cases j <;> norm_num [maskedPrimeThreeReplacement]

theorem prime_three_replacement_row_divisible (j : Fin 4) :
    3 ∣ maskedPrimeThreeReplacement 3 j := by
  fin_cases j <;> norm_num [maskedPrimeThreeReplacement]

theorem prime_three_replacement_det : maskedPrimeThreeReplacement.det = -108 := by
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, maskedPrimeThreeReplacement,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]

theorem masked_prime_three_not_divisible : ¬ (3 : ℤ) ∣ maskedPrimeThree.det := by
  rw [masked_prime_three_det]
  norm_num

end RiemannGaussian.ArithmeticOperatorMaskedFrobeniusAudit

#lint+ in RiemannGaussian.ArithmeticOperatorMaskedFrobeniusAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty masked Frobenius audit."
  logInfo m!"Masked Frobenius audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-frobenius-cutoff-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-frobenius-cutoff-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact native-cutoff determinant obstruction and finite masked-flag repair; no RH estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
