/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCoupledSummandAudit
import OAI.NumberTheory.DirichletL.Descent.Completion
import OAI.NumberTheory.DirichletL.Eisenstein.PrimeRecurrence
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Cube shift after the actual twist and total-index marks

The native squarefree Gauss column is unchanged and every cube order is
retained. The true cube shift rescales the physical window and the
total-index mark. A fixed-scale commutator has exactly those two
discrepancies, with the numerator-dependent row and all complex phases
retained. Neither discrepancy is estimated here.

The genuine source residue is cube-invariant; a multiplicative twist
only changes its exact eigenvalue. This does not identify a globally
cuspidal twisted form or a hypothetical-zero Mellin residue.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.CubeTwist
open OAI OAI.CompletedGauss OAI.CanonicalRowCompletion
open OAI.CubicEisenstein hiding summand
open OAI.ConcreteTraceCRT
open OAI.SevenEighths.InverseMoment
local notation "O" => OAI.ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The physical label, not either slot separately, is multiplied by the cube. -/
theorem total_index_cube_shift (I J P : Id) :
    I * (P * J)^3 = P^3 * (I * J^3) := by ring

/-- Exact physical argument, including zero ideals and zero scale. -/
theorem physical_argument_cube_shift (I J P : Id) (X : ℝ) :
    (Ideal.absNorm I : ℝ) * (Ideal.absNorm (P*J) : ℝ)^3 / X =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)^3 /
        (X / (Ideal.absNorm P : ℝ)^3) := by
  simp only [map_mul, Nat.cast_mul, mul_pow, div_div_eq_mul_div]
  ring

/-- No squarefree/cube, Gaussian, or numerator mask is completed. -/
theorem summand_cube_shift (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (I J P : Id) :
    summand Ψ W X I (P*J) =
      cubeWeight Ψ P * summand Ψ W (X/(Ideal.absNorm P : ℝ)^3) I J := by
  unfold summand
  rw [map_mul, physical_argument_cube_shift]
  ring

/-- The exact actual numerator-dependent cube multiplier. -/
theorem actual_shifted_marked_atom (Ψ : O →* ℂ) (a f m : O)
    (W : ℝ → ℂ) (X : ℝ) (d : Id → ℂ) (I J P : Id) :
    summand (rowTwist Ψ a f m) W X I (P*J) * d (I*(P*J)^3) =
      (cubeWeight (rowTwist Ψ a f 1) P * idealRowHom m P^3) *
        summand (rowTwist Ψ a f m) W (X/(Ideal.absNorm P : ℝ)^3) I J *
          d (P^3*(I*J^3)) := by
  rw [summand_cube_shift, total_index_cube_shift, cubeWeight_row_factor]

/-- Direct endpoint in the existing completed API. The left side is only
the genuine shifted cube subfamily; no unshifted column is completed. -/
theorem shifted_completedT_eq (Ψ : O →* ℂ) (a f m : O)
    (W : ℝ → ℂ) (X : ℝ) (d : Id → ℂ) (P : Id) :
    (∑' I : Id, ∑' J : Id,
      summand (rowTwist Ψ a f m) W X I (P*J) * d (I*(P*J)^3)) =
      (cubeWeight (rowTwist Ψ a f 1) P * idealRowHom m P^3) *
        markedCompletedT (rowTwist Ψ a f m) W (X/(Ideal.absNorm P : ℝ)^3)
          (fun A => d (P^3*A)) := by
  simp_rw [actual_shifted_marked_atom]
  simp only [markedCompletedT, mul_assoc, tsum_mul_left]

/-- Joining before norms leaves the exact signed mark commutator. -/
theorem finite_mark_commutator (Ψ : O →* ℂ) (a f m : O)
    (W : ℝ → ℂ) (X : ℝ) (d : Id → ℂ) (I P : Id) (F : Finset Id) :
    (∑ J ∈ F, summand (rowTwist Ψ a f m) W X I (P*J) * d (I*(P*J)^3)) -
      (cubeWeight (rowTwist Ψ a f 1) P * idealRowHom m P^3) *
        ∑ J ∈ F, summand (rowTwist Ψ a f m) W
          (X/(Ideal.absNorm P : ℝ)^3) I J * d (I*J^3) =
      (cubeWeight (rowTwist Ψ a f 1) P * idealRowHom m P^3) *
        ∑ J ∈ F, summand (rowTwist Ψ a f m) W
          (X/(Ideal.absNorm P : ℝ)^3) I J *
            (d (P^3*(I*J^3)) - d (I*J^3)) := by
  simp_rw [actual_shifted_marked_atom]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro J _
  ring

/-- A divisor mark coprime to the shifted prime is genuinely invariant. -/
theorem coprime_divisor_mark (D P A : Id) (h : IsCoprime D P) :
    (if D ∣ P^3*A then (1:ℂ) else 0) = if D ∣ A then 1 else 0 := by
  rw [h.pow_right.dvd_mul_left_iff]

/-- The prime mark on the shift is one, with its unit endpoint retained. -/
theorem shifted_prime_mark (P A : Id) :
    (if P ∣ P^3*A then (1:ℂ) else 0) = 1 := by
  have hd : P ∣ P^3*A := by
    refine ⟨P^2*A, ?_⟩
    ring
  rw [ite_eq_left hd]

/-- A prime mark leaves its exact complementary population, not zero. -/
theorem finite_prime_mark_commutator (Ψ : O →* ℂ) (a f m : O)
    (W : ℝ → ℂ) (X : ℝ) (I P : Id) (F : Finset Id) :
    (∑ J ∈ F, summand (rowTwist Ψ a f m) W X I (P*J) *
      (if P ∣ I*(P*J)^3 then (1:ℂ) else 0)) -
      (cubeWeight (rowTwist Ψ a f 1) P * idealRowHom m P^3) *
        ∑ J ∈ F, summand (rowTwist Ψ a f m) W
          (X/(Ideal.absNorm P : ℝ)^3) I J *
            (if P ∣ I*J^3 then (1:ℂ) else 0) =
      (cubeWeight (rowTwist Ψ a f 1) P * idealRowHom m P^3) *
        ∑ J ∈ F, summand (rowTwist Ψ a f m) W
          (X/(Ideal.absNorm P : ℝ)^3) I J *
            (1 - (if P ∣ I*J^3 then (1:ℂ) else 0)) := by
  simpa only [shifted_prime_mark] using
    finite_mark_commutator Ψ a f m W X (fun A => if P ∣ A then 1 else 0) I P F

/-- Keeping the original scale retains the full Vstar/Gaussian jump. -/
theorem fixed_scale_atom_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (d : Id → ℂ) (I J P : Id) :
    summand Ψ W X I (P*J) * d (I*(P*J)^3) -
      cubeWeight Ψ P * summand Ψ W X I J * d (I*J^3) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        cubeWeight Ψ P * cubeWeight Ψ J) *
          ((Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ)^3 /
              (X/(Ideal.absNorm P : ℝ)^3)) -
             Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ)^3/X)) *
                d (P^3*(I*J^3)) +
           Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ)^3/X) *
              (d (P^3*(I*J^3)) - d (I*J^3))) := by
  unfold summand
  rw [map_mul, physical_argument_cube_shift, total_index_cube_shift]
  ring

/-- Actual residual coefficients have the same native cube recurrence. -/
theorem actual_residual_coefficient_cube (p : O) (hp : Prime p)
    (hprimary : OAI.ActualEisensteinCubic.lambda^2 ∣ p-1)
    (h : O) (hh : h ≠ 0) :
    sourceResidualFourierCoefficient (h*p^3) =
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) : ℂ) *
        sourceResidualFourierCoefficient h :=
  sourceResidualFourierCoefficient_cube_sqrt p hp.ne_zero
    (cubicSource_cubeAverage p hp hprimary) h hh

/-- A genuine multiplicative twist changes the exact cube eigenvalue. -/
theorem twisted_source_cube (Ψ : O →* ℂ) (a f m p h : O)
    (hp : Prime p) (hprimary : OAI.ActualEisensteinCubic.lambda^2 ∣ p-1)
    (hh : h ≠ 0) :
    sourceArithmeticResidue (h*p^3) * rowTwist Ψ a f m (h*p^3) =
      sourceArithmeticResidue h * rowTwist Ψ a f m h *
        (rowTwist Ψ a f m p)^3 := by
  rw [sourceArithmeticResidue_prime_cube p hp hprimary h hh, map_mul, map_pow]
  ring

/-- If the cube multiplier is one, the twist kills the complete source too. -/
theorem twisted_source_unit_cube (Ψ : O →* ℂ) (a f m p h : O)
    (hp : Prime p) (hprimary : OAI.ActualEisensteinCubic.lambda^2 ∣ p-1)
    (hh : h ≠ 0) (he : (rowTwist Ψ a f m p)^3 = 1) :
    sourceArithmeticResidue (h*p^3) * rowTwist Ψ a f m (h*p^3) =
      sourceArithmeticResidue h * rowTwist Ψ a f m h := by
  rw [twisted_source_cube Ψ a f m p h hp hprimary hh, he, mul_one]

/-- Retaining an arbitrary physical mask leaves only its exact cube jump
after the true twisted eigenvalue has been subtracted. -/
theorem twisted_source_mask_commutator (Ψ : O →* ℂ) (a f m p h : O)
    (hp : Prime p) (hprimary : OAI.ActualEisensteinCubic.lambda^2 ∣ p-1)
    (hh : h ≠ 0) (w : O → ℂ) :
    sourceArithmeticResidue (h*p^3) * rowTwist Ψ a f m (h*p^3) * w (h*p^3) -
      (rowTwist Ψ a f m p)^3 *
        (sourceArithmeticResidue h * rowTwist Ψ a f m h * w h) =
      sourceArithmeticResidue h * rowTwist Ψ a f m h *
        (rowTwist Ψ a f m p)^3 * (w (h*p^3)-w h) := by
  rw [twisted_source_cube Ψ a f m p h hp hprimary hh]
  ring

/-- An invariant mask adds no surviving term after the matching eigenvalue. -/
theorem twisted_source_invariant_mask (Ψ : O →* ℂ) (a f m p h : O)
    (hp : Prime p) (hprimary : OAI.ActualEisensteinCubic.lambda^2 ∣ p-1)
    (hh : h ≠ 0) (w : O → ℂ) (hw : w (h*p^3)=w h) :
    sourceArithmeticResidue (h*p^3) * rowTwist Ψ a f m (h*p^3) * w (h*p^3) -
      (rowTwist Ψ a f m p)^3 *
        (sourceArithmeticResidue h * rowTwist Ψ a f m h * w h) = 0 := by
  rw [twisted_source_mask_commutator Ψ a f m p h hp hprimary hh w, hw, sub_self,
    mul_zero]

end OpenAIReview.CubeTwist

#lint+ in OpenAIReview.CubeTwist

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
  unless declarations>0 do throwError "Empty cube twist audit."
  logInfo m!"Cube twist audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cube-twist"
  IO.FS.writeFile ".lake/arithmetic-operator-cube-twist/axioms.json"
    (Json.mkObj [("scope",toJson "exact native cube twist/mark/window commutators; no all-cusp, cutoff bound, or hypothetical-zero source asymptotic"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
