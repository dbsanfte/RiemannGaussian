/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTernaryFactor
import RiemannGaussian.SemiprimeSubdividedEntry

/-! # Ternary adapter for the literal public factor graph
No indexed-layout enumeration or either OpenAI layout import branch is used.
The original ordered graph and its two-occurrence ports are unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeTernaryPublicFactor
open scoped BigOperators
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters
open SemiprimeMacroEntryBitPrimitives SemiprimeSubdividedEntry SemiprimePublicFactorCount
open SemiprimeTernaryFactor SemiprimeCountRecovery

/-- The original public edge alphabet; no auxiliary ternary variables. -/
abbrev Variables (N : ℕ) (_hN : 0<N) :=
  Edge (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))
/-- The original public local factors, including equality vertices. -/
abbrev Factors (N : ℕ) (_hN : 0<N) :=
  SubdividedVertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))
/-- Literal original port coordinate, independent of the alphabet. -/
def coordinate (N : ℕ) (hN : 0<N) (v : Factors N hN)
    (slot : Fin (subdividedArity v)) : Variables N hN :=
  orderedEdgeAt (digitCount_bounds (bitLength_pos hN)).1
    (publicConfig N hN).cap ⟨v,slot⟩

/-- The existing graph proves exact occurrence two for the unchanged scopes. -/
theorem occurrence_two (N : ℕ) (hN : 0<N) (a : Variables N hN) :
    (∑ v : Factors N hN, ∑ i : Fin (subdividedArity v),
      if coordinate N hN v i=a then (1 : ℕ) else 0)=2 :=
  ordered_edge_occurrence_two (publicConfig N hN).digits_pos (publicConfig N hN).cap a

/-- Coverage is derived from the original exact occurrence theorem. -/
theorem coverage (N : ℕ) (hN : 0<N) (a : Variables N hN) :
    ∃ v i, coordinate N hN v i=a := by
  classical
  by_contra h
  have hn : ∀ v i, coordinate N hN v i≠a := by simpa using h
  have hc := occurrence_two N hN a
  simp only [hn,ite_false,Finset.sum_const_zero] at hc
  omega

/-- Actual ternary public checker: a complete scan followed by the original paid entry. -/
def checker (N : ℕ) (hN : 0<N) (v : Factors N hN) :
    (Fin (subdividedArity v) → Fin 3) → CheckRun :=
  liftChecker (subdividedArity v) (publicSubdividedEntry N hN v)

/-- The literal ternary predicate for the unchanged original public network. -/
def predicate (N : ℕ) (hN : 0<N) (x : Variables N hN → Fin 3) : Bool :=
  ternaryPredicate subdividedArity (publicSubdividedEntry N hN) (coordinate N hN) x

/-- Each physical ternary entry pays the full original entry plus a linear port scan. -/
theorem checker_clock (N : ℕ) (hN : 0<N) (v : Factors N hN)
    (input : Fin (subdividedArity v) → Fin 3) :
    (checker N hN v input).clock ≤
      4*subdividedArity v+1048576*(64*bitLength N+2)^10+2 := by
  exact liftChecker_clock _ _ _ _ (publicSubdividedEntry_polynomial N hN v)

/-- Pure original Boolean function-assignment endpoint for a generic factor-system adapter. -/
theorem boolean_factor_count (N : ℕ) (hN : 0<N) :
    acceptedCount (booleanPredicate subdividedArity (publicSubdividedEntry N hN)
      (coordinate N hN))=Fintype.card (OrdinaryFactors N) := by
  rw [boolean_count_tensor]
  simp_rw [publicSubdividedEntry_correct]
  exact public_tensor_factor_count N hN

/-- Exact natural factor count, with original graph coverage and correctness discharged. -/
theorem factor_count (N : ℕ) (hN : 0<N) :
    acceptedCount (predicate N hN)=Fintype.card (OrdinaryFactors N) := by
  change acceptedCount (ternaryPredicate subdividedArity (publicSubdividedEntry N hN)
    (coordinate N hN))=_
  calc
    _ = acceptedCount (booleanPredicate subdividedArity (publicSubdividedEntry N hN)
      (coordinate N hN)) := ternary_count_boolean _ _ _ (coverage N hN)
    _ = _ := boolean_factor_count N hN

/-- Prefix restrictions remain on the old ports and preserve the exact restricted Boolean count. -/
theorem prefix_count (N : ℕ) (hN : 0<N) (fixed : List (Variables N hN × Bool)) :
    acceptedCount (ternaryPredicate subdividedArity
      (fun v => prefixChecker (subdividedArity v) (coordinate N hN v)
        (publicSubdividedEntry N hN v) fixed) (coordinate N hN))=
    acceptedCount (restricted (fun x a => x a)
      (booleanPredicate subdividedArity (publicSubdividedEntry N hN) (coordinate N hN)) fixed) :=
  ternary_prefix_count _ _ _ (coverage N hN) fixed

end RiemannGaussian.SemiprimeTernaryPublicFactor
