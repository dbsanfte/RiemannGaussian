/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceLayout

/-! # Executed finite universal integer numerator entries
The ordered differences use the computable sorted Fin list, rather than the
noncomputable multiset representative `Finset.toList` in the semantic formula.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeUniversalNumeratorExecution
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.MatrixSupport BinomialInterpolation
open SqrtLog
variable {r Q Δ R : ℕ}

/-- Commuting register swaps make the difference independent of list ordering. -/
theorem integerDifference_perm (i : Fin Δ) {a b : List (Fin Q)} (h : a.Perm b)
    (f : UniversalType r Q Δ → ℤ) (u : UniversalType r Q Δ) :
    LayoutNumerator.integerDifference i a f u = LayoutNumerator.integerDifference i b f u := by
  induction h generalizing u with
  | nil => rfl
  | cons a h ih => simp only [LayoutNumerator.integerDifference, ih]
  | swap a b l =>
    simp only [LayoutNumerator.integerDifference]
    rw [swapPositions_commute i {a} {b}]
    ring
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ u).trans (ih₂ u)

/-- Literal integer entry from the supplied finite parity vector and all active subsets. -/
def entry (c : Fin R → ℤ) (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) : ℤ :=
  ∑ j ∈ Finset.range R, extendCoefficients c j * 2^(R-1-j) *
    ∑ S ∈ (activePositions t).powersetCard j,
      LayoutNumerator.integerDifference i (S.sort (· ≤ ·)) (LayoutNumerator.integerDelta y)
        (swapPositions i (activePositions t) u)

/-- The compiled sorted-difference formula is the source's actual integer numerator. -/
theorem entry_eq (A : ℕ) (c : Fin R → ℤ)
    (hc : c = parityCoefficients (K := ℤ) A R)
    (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    entry c i t u y = LayoutNumerator.entry i t A R u y := by
  subst c
  unfold entry LayoutNumerator.entry
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  exact integerDifference_perm i (Finset.sort_perm_toList _ _) _ _

/-- Zero extension to the head/slot joint fibre, with all membership decisions explicit. -/
def extended (c : Fin R → ℤ) (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : UniversalType r Q Δ) : ℤ :=
  if u.head t = g ∧ u.slot i t ≠ g then
    if y.head t = g ∧ y.slot i t ≠ g then entry c i t u y else 0
  else 0

/-- The zero extension is the very same source joint numerator, not an arbitrary matrix. -/
theorem extended_eq (A : ℕ) (c : Fin R → ℤ)
    (hc : c = parityCoefficients (K := ℤ) A R)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (u y : UniversalType r Q Δ) :
    extended c i t g u y = SubexpAnnihilation.zeroExtendMatrix (joint t g i)
      (LayoutNumerator.joint i t g A R) u y := by
  unfold extended SubexpAnnihilation.zeroExtendMatrix
  change (if u.head t = g ∧ u.slot i t ≠ g then
      if y.head t = g ∧ y.slot i t ≠ g then entry c i t u y else 0 else 0) =
    (if u.head t = g ∧ u.slot i t ≠ g then
      if y.head t = g ∧ y.slot i t ≠ g then LayoutNumerator.entry i t A R u y else 0 else 0)
  rw [entry_eq A c hc]

#print axioms entry_eq
end RiemannGaussian.SemiprimeUniversalNumeratorExecution
