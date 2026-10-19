/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Exact factorial saturation of interval-mask polynomial flags

Closing all lower polynomial rows separately on interval cells is one
valid repair of the masked Frobenius obstruction. This leaf evaluates its
common determinant for arbitrary cell sizes and integer translations.
It is exactly a product of superfactorials, independent of cell locations.
Thus this particular repair supplies no additional determinant factor
beyond ordinary factorial arithmetic. This does not exclude other
cutoff-compatible evaluation spaces or estimate any signed prime sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Matrix
namespace RiemannGaussian.ArithmeticOperatorIntervalDeterminantAudit

/-- Polynomial degrees on one translated interval of consecutive integers. -/
def intervalFlag (n : ℕ) (a : ℤ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  (Matrix.vandermonde (fun j : Fin (n+1) => (j : ℤ)+a))ᵀ

/-- Every interval flag has exactly its ordinary superfactorial determinant. -/
theorem intervalFlag_det (n : ℕ) (a : ℤ) :
    (intervalFlag n a).det = (n.superFactorial : ℤ) := by
  simp only [intervalFlag, Matrix.det_transpose, Matrix.det_vandermonde_add]
  exact Matrix.det_vandermonde_id_eq_superFactorial n

/-- All columns are retained. Each block contains the complete lower
polynomial flag on its own interval and is zero on the other cells. -/
def maskedFlags {B : ℕ} (length : Fin B → ℕ) (start : Fin B → ℤ) :
    Matrix (Σ b : Fin B, Fin (length b+1)) (Σ b : Fin B, Fin (length b+1)) ℤ :=
  Matrix.blockDiagonal' (fun b => intervalFlag (length b) (start b))

/-- Canonical identification of a masked block with its local degree indices. -/
def blockIndex {B : ℕ} (length : Fin B → ℕ) (b : Fin B) :
    Fin (length b+1) ≃ {i : Σ c : Fin B, Fin (length c+1) // i.1=b} where
  toFun j := ⟨⟨b,j⟩,rfl⟩
  invFun i := i.property ▸ i.val.2
  left_inv j := rfl
  right_inv := by
    rintro ⟨⟨c,j⟩,h⟩
    cases h
    rfl

/-- The retained block is literally its translated interval evaluation matrix. -/
theorem maskedFlags_block {B : ℕ} (length : Fin B → ℕ) (start : Fin B → ℤ)
    (b : Fin B) :
    ((maskedFlags length start).toSquareBlock Sigma.fst b).submatrix
      (blockIndex length b) (blockIndex length b) = intervalFlag (length b) (start b) := by
  ext i j
  simp [maskedFlags, blockIndex, Matrix.toSquareBlock, Matrix.toSquareBlockProp,
    Matrix.submatrix_apply, Matrix.blockDiagonal'_apply_eq]

/-- General finite common-column repair: no extra cross-cell factor remains.
Cell lengths may grow and the cells need not have equal sizes. -/
theorem maskedFlags_det {B : ℕ} (length : Fin B → ℕ) (start : Fin B → ℤ) :
    (maskedFlags length start).det = ∏ b, ((length b).superFactorial : ℤ) := by
  have htri : Matrix.BlockTriangular (maskedFlags length start) Sigma.fst := by
    intro i j hij
    exact Matrix.blockDiagonal'_apply_ne
      (fun b : Fin B => intervalFlag (length b) (start b))
      (k := i.1) (k' := j.1) i.2 j.2 (ne_of_gt hij)
  rw [htri.det_fintype]
  apply Finset.prod_congr rfl
  intro b _
  calc
    _ = (((maskedFlags length start).toSquareBlock Sigma.fst b).submatrix
        (blockIndex length b) (blockIndex length b)).det :=
      (Matrix.det_submatrix_equiv_self (blockIndex length b) _).symm
    _ = _ := by rw [maskedFlags_block, intervalFlag_det]

/-- Translations of entire cells cannot encode a new determinant source. -/
theorem maskedFlags_det_translation_invariant {B : ℕ} (length : Fin B → ℕ)
    (start other : Fin B → ℤ) :
    (maskedFlags length start).det = (maskedFlags length other).det := by
  rw [maskedFlags_det, maskedFlags_det]

/-- The factorial normalization consumes the entire determinant, including
all prime valuations, not merely the first Frobenius extraction. -/
theorem maskedFlags_det_factorials {B : ℕ} (length : Fin B → ℕ) (start : Fin B → ℤ) :
    (maskedFlags length start).det =
      ∏ b, ∏ j ∈ Finset.range (length b+1), (j.factorial : ℤ) := by
  rw [maskedFlags_det]
  apply Finset.prod_congr rfl
  intro b _
  norm_cast
  exact (Nat.prod_range_succ_factorial (length b)).symm

end RiemannGaussian.ArithmeticOperatorIntervalDeterminantAudit

#lint+ in RiemannGaussian.ArithmeticOperatorIntervalDeterminantAudit

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
  unless declarations>0 do throwError "Empty interval determinant audit."
  logInfo m!"Interval determinant audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-interval-determinant"
  IO.FS.writeFile ".lake/arithmetic-operator-interval-determinant/axioms.json"
    (Json.mkObj [("scope",toJson "arbitrary finite interval-mask flags have exactly a product-of-factorials determinant; no prime estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
