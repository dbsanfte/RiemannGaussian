/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The rank cost of closure under every literal prefix cutoff

Over any ring and in any characteristic, a submodule of the finite column
function space which contains the constant one row and is invariant under
EVERY prefix cutoff is the entire function space. Successive prefixes give
the individual column delta rows. Nested prefix closure also gives exact
interval restrictions; a finite cell-invariant row space decomposes into
its cell restrictions.

This is a scoped obstruction to keeping a PROPER earlier-row filtration
space closed under all prefixes. It is not an obstruction to closure of
the FINAL row space of a full-rank determinant: that space is already top.
Nor does it disprove a weighted filtration whose permitted cutoff family
changes with the row. Native
prime-dependent cutoffs need not distinguish every column, and need not
satisfy this stronger full-prefix hypothesis. No claim about every filtered
Frobenius mechanism, prime estimate, zero source, or RH follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace RiemannGaussian.ArithmeticOperatorCutoffRankAudit

variable {R : Type*} [Ring R] {N : ℕ}

/-- Retain precisely the literal columns with index below `k`. -/
def prefixCutoff (k : ℕ) (f : Fin N → R) : Fin N → R :=
  fun j => if j.val < k then f j else 0

/-- The half-open interval of literal column indices `[lo,hi)`. -/
def intervalCutoff (lo hi : ℕ) (f : Fin N → R) : Fin N → R :=
  fun j => if lo ≤ j.val ∧ j.val < hi then f j else 0

/-- Exact interval restriction is the difference of two nested prefixes. -/
theorem intervalCutoff_eq_sub (lo hi : ℕ) (h : lo ≤ hi) (f : Fin N → R) :
    intervalCutoff lo hi f = prefixCutoff hi f - prefixCutoff lo f := by
  ext j
  by_cases hlo : j.val < lo
  · have hhi : j.val < hi := lt_of_lt_of_le hlo h
    simp [intervalCutoff, prefixCutoff, hlo, hhi, Nat.not_le_of_lt hlo]
  · have hlo' : lo ≤ j.val := Nat.le_of_not_gt hlo
    by_cases hhi : j.val < hi <;>
      simp [intervalCutoff, prefixCutoff, hlo, hlo', hhi]

/-- Only the two stated nested cutoff operations are needed for this row. -/
theorem intervalCutoff_mem (W : Submodule R (Fin N → R))
    (lo hi : ℕ) (h : lo ≤ hi) (f : Fin N → R)
    (hlo : prefixCutoff lo f ∈ W) (hhi : prefixCutoff hi f ∈ W) :
    intervalCutoff lo hi f ∈ W := by
  rw [intervalCutoff_eq_sub lo hi h f]
  exact W.sub_mem hhi hlo

/-- Two successive constant prefixes isolate exactly one column. -/
theorem prefix_succ_sub_prefix_one (i : Fin N) :
    prefixCutoff (i.val+1) (fun _ : Fin N => (1 : R)) -
      prefixCutoff i.val (fun _ : Fin N => (1 : R)) =
        fun j => if i=j then 1 else 0 := by
  ext j
  by_cases hij : i=j
  · subst j
    simp [prefixCutoff]
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hj : j.val < i.val
    · have hj' : j.val < i.val+1 := by omega
      simp [prefixCutoff, hij, hj, hj']
    · have hj' : ¬ j.val < i.val+1 := by omega
      simp [prefixCutoff, hij, hj, hj']

/-- Full-prefix invariance and the constant one row force every delta row. -/
theorem delta_mem_of_prefix_invariant (W : Submodule R (Fin N → R))
    (hone : (fun _ : Fin N => (1 : R)) ∈ W)
    (hcut : ∀ k ≤ N, ∀ f ∈ W, prefixCutoff k f ∈ W) (i : Fin N) :
    (fun j => if i=j then (1 : R) else 0) ∈ W := by
  rw [← prefix_succ_sub_prefix_one i]
  exact W.sub_mem (hcut (i.val+1) (by omega) _ hone)
    (hcut i.val (by omega) _ hone)

/-- The full-prefix closure hypothesis uses every literal column; it is
stronger than closure under a possibly nondistinguishing native cutoff family. -/
theorem eq_top_of_prefix_invariant (W : Submodule R (Fin N → R))
    (hone : (fun _ : Fin N => (1 : R)) ∈ W)
    (hcut : ∀ k ≤ N, ∀ f ∈ W, prefixCutoff k f ∈ W) : W = ⊤ := by
  apply top_unique
  intro f _
  rw [pi_eq_sum_univ f]
  exact W.sum_mem fun i _ => W.smul_mem (f i)
    (delta_mem_of_prefix_invariant W hone hcut i)

/-- Literal restriction to a cell of a fixed finite partition. -/
def cellRestriction {ι κ : Type*} [DecidableEq κ]
    (cell : ι → κ) (b : κ) (f : ι → R) : ι → R :=
  fun j => if cell j=b then f j else 0

/-- The cell restrictions retain all columns and reconstruct the row exactly. -/
theorem sum_cellRestriction {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (cell : ι → κ) (f : ι → R) : ∑ b, cellRestriction cell b f = f := by
  ext j
  simp [cellRestriction]

/-- Distinct cell restrictions have disjoint support. -/
theorem cellRestriction_other {ι κ : Type*} [DecidableEq κ]
    (cell : ι → κ) (b c : κ) (h : b ≠ c) (f : ι → R) :
    cellRestriction cell b (cellRestriction cell c f) = 0 := by
  ext j
  by_cases hb : cell j=b
  · simp [cellRestriction, hb, h]
  · simp [cellRestriction, hb]

/-- A cell-invariant submodule is exactly the sum of its individual cell
restrictions. No independent arithmetic constraint is obtained here. -/
theorem mem_iff_cellRestrictions {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : Submodule R (ι → R)) (cell : ι → κ)
    (hcell : ∀ b, ∀ f ∈ W, cellRestriction cell b f ∈ W) (f : ι → R) :
    f ∈ W ↔ ∀ b, cellRestriction cell b f ∈ W := by
  constructor
  · intro hf b
    exact hcell b f hf
  · intro hf
    rw [← sum_cellRestriction cell f]
    exact W.sum_mem fun b _ => hf b

end RiemannGaussian.ArithmeticOperatorCutoffRankAudit

#lint+ in RiemannGaussian.ArithmeticOperatorCutoffRankAudit

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
  unless declarations>0 do throwError "Empty cutoff rank audit."
  logInfo m!"Cutoff rank audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cross-cell-minor"
  IO.FS.writeFile ".lake/arithmetic-operator-cross-cell-minor/axioms.json"
    (Json.mkObj [("scope",toJson "full-prefix invariant constant-containing submodule is full; exact interval and finite cell decomposition; no native prime estimate or RH source"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
