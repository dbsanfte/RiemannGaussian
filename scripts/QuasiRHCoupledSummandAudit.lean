/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCoupledResidueAudit
import OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
import Lean.Util.CollectAxioms

/-!
# Actual completed-coefficient matching audit

The complete squarefree/cube coefficient is factored before joining its
actual additive Gauss row. The Gaussian/window, height and any exterior
complex mask are retained. On a matching shared-prime column the join is
exactly a punctured signed mass, not a mean-zero row.

This refutes automatic local orthogonality for this actual coefficient
class. It neither estimates the signed mass nor its complete physical
probe, and it asserts no zero-source asymptotic.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.CoupledSummand
open OAI OAI.CompletedGauss OAI.CanonicalRowCompletion
open OAI.ConcretePrimeRowBridge hiding O columnWeight
open OAI.CubicEisenstein hiding O summand
open OAI.SevenEighths.ProbePhysical OAI.GaussianShiftedPartition
open OpenAIReview.CoupledResidue
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Exact row factor even on the zero/nonprimary column. -/
theorem columnWeight_row_factor (Ψ : O →* ℂ) (a f m : O) (I : Ideal O) :
    columnWeight (rowTwist Ψ a f m) I =
      columnWeight (rowTwist Ψ a f 1) I * idealRowHom m I := by
  by_cases hI : primaryGenerator I = 0
  · have hz : squarefreeGaussCoefficient I = 0 := by
      simp [squarefreeGaussCoefficient, hI]
    simp [columnWeight, hz]
  · unfold columnWeight
    rw [rowTwist_row_factor, (primaryGenerator_spec I hI).1]
    ring

/-- Both completed slots must be joined: the phase lives at `I*J^3`. -/
theorem summand_row_factor (Ψ : O →* ℂ) (a f m : O)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    summand (rowTwist Ψ a f m) W X I J =
      summand (rowTwist Ψ a f 1) W X I J * idealRowHom m (I * J^3) := by
  unfold summand
  rw [columnWeight_row_factor, cubeWeight_row_factor, map_mul, map_pow]
  ring

/-- A matching shared prime is removed only from the phase; all cofactor
phases remain, and the nonunit puncture is exact. -/
theorem matching_cofactor_atom (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (B : Ideal O) (m : O) :
    idealRowHom m ((Ideal.span {p})^(6*t+1) * B) * sexticGauss p hp (-m) =
      if m ∈ Ideal.span {p} then 0 else
        (actualSextic (Ideal.span {p}) hg (-1) *
          gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
            idealRowHom m B := by
  rw [map_mul, actual_matching_valuation p hg t]
  have h := actual_matching_atom p hp hg m
  by_cases hm : m ∈ Ideal.span {p}
  · rw [ite_eq_left hm] at h ⊢
    calc
      _ = (idealRowHom m (Ideal.span {p}) * sexticGauss p hp (-m)) *
          idealRowHom m B := by ring
      _ = 0 := by rw [h, zero_mul]
  · rw [ite_eq_right hm] at h ⊢
    calc
      _ = (idealRowHom m (Ideal.span {p}) * sexticGauss p hp (-m)) *
          idealRowHom m B := by ring
      _ = _ := by rw [h]

/-- Exact native coefficient on `I=P,J=P^(2t)`, without completing or
discarding the Gaussian/window or either complex phase. -/
theorem matching_summand_atom (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ)
    (Ψ : O →* ℂ) (a f m : O) (W : ℝ → ℂ) (X : ℝ) :
    summand (rowTwist Ψ a f m) W X (Ideal.span {p}) ((Ideal.span {p})^(2*t)) *
        sexticGauss p hp (-m) =
      if m ∈ Ideal.span {p} then 0 else
        summand (rowTwist Ψ a f 1) W X (Ideal.span {p}) ((Ideal.span {p})^(2*t)) *
          (actualSextic (Ideal.span {p}) hg (-1) *
            gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) := by
  rw [summand_row_factor, mul_assoc, actual_completed_matching p hg t,
    actual_matching_atom p hp hg]
  split_ifs <;> simp

/-- The exterior annular, Mellin, ray and height weight remains one signed
punctured mass. No separate-row cancellation is available here. -/
theorem matching_summand_weighted (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ)
    (Ψ : O →* ℂ) (a f : O) (W : ℝ → ℂ) (X : ℝ)
    (F : Finset O) (w : O → ℂ) :
    (∑ m ∈ F, w m *
      summand (rowTwist Ψ a f m) W X (Ideal.span {p}) ((Ideal.span {p})^(2*t)) *
        sexticGauss p hp (-m)) =
      (summand (rowTwist Ψ a f 1) W X (Ideal.span {p}) ((Ideal.span {p})^(2*t)) *
        (actualSextic (Ideal.span {p}) hg (-1) *
          gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp))) *
            ∑ m ∈ F.filter (fun m => m ∉ Ideal.span {p}), w m := by
  simp_rw [mul_assoc, matching_summand_atom p hp hg t Ψ a f]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m ∈ Ideal.span {p}
  · simp [hm]
  · simp [hm, mul_comm, mul_left_comm, mul_assoc]

/-- The actual matching Gauss constant is nonzero, including its phase. -/
theorem actual_matching_constant_ne_zero (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    actualSextic (Ideal.span {p}) hg (-1) *
      gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp) ≠ 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  apply mul_ne_zero
  · exact MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))
  · apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_ne_zero
    · exact actual_character_nonprincipal p hg hc
    · exact OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp

/-- A nonzero native coefficient and nonzero punctured mass cannot be
annihilated by squarefree/cube support or the Gaussian mask alone. -/
theorem matching_summand_weighted_ne_zero (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (t : ℕ)
    (Ψ : O →* ℂ) (a f : O) (W : ℝ → ℂ) (X : ℝ)
    (F : Finset O) (w : O → ℂ)
    (hcoef : summand (rowTwist Ψ a f 1) W X (Ideal.span {p})
      ((Ideal.span {p})^(2*t)) ≠ 0)
    (hmass : (∑ m ∈ F.filter (fun m => m ∉ Ideal.span {p}), w m) ≠ 0) :
    (∑ m ∈ F, w m *
      summand (rowTwist Ψ a f m) W X (Ideal.span {p}) ((Ideal.span {p})^(2*t)) *
        sexticGauss p hp (-m)) ≠ 0 := by
  rw [matching_summand_weighted p hp hg t Ψ a f W X F w]
  exact mul_ne_zero (mul_ne_zero hcoef (actual_matching_constant_ne_zero p hp hg hc)) hmass

end OpenAIReview.CoupledSummand

#lint+ in OpenAIReview.CoupledSummand

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
  unless declarations>0 do throwError "Empty actual coupled summand audit."
  logInfo m!"Actual coupled summand audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-coupled-summand"
  IO.FS.writeFile ".lake/arithmetic-operator-coupled-summand/axioms.json"
    (Json.mkObj [("scope",toJson "actual squarefree/cube Gaussian coefficient matching with all finite complex masks; no whole-probe bound or zero-source asymptotic"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
