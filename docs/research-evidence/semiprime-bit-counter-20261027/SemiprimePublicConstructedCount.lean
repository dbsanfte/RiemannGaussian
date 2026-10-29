/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeScheduledCounter
import RiemannGaussian.SemiprimePublicFactorCount

/-!
# The constructed public counter counts ordinary factors

This joins the actual scheduled row construction and ordered Boolean tables to
the whole-family factor-count theorem. It is a semantic composition theorem;
execution of the finite choices and the full primitive-bit bound are separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace RiemannGaussian.SemiprimePublicConstructedCount
open scoped BigOperators
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroGraphExtension
open SemiprimeMacroParameters SemiprimePublicFactorCount
open SemiprimeScheduledCounter SemiprimeSourceLayoutRate
open SemiprimeCounterSearch SemiprimeCountRecovery SemiprimeConstructedCounter
attribute [local instance] Classical.propDecidable

/-- Reindexing the counter's finite sets as literal Boolean wire assignments. -/
def assignmentEquiv (A : Type) [Fintype A] [DecidableEq A] :
    Finset A ≃ (A → Bool) where
  toFun := assignmentBit
  invFun f := Finset.univ.filter (fun a => f a = true)
  left_inv x := by ext a; simp [assignmentBit]
  right_inv f := by funext a; simp [assignmentBit]

/-- The local-conjunction counter is the literal zero/one tensor contraction. -/
theorem accepted_eq_tensor {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]
    (arity : E → ℕ) (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coordinate : (e : E) → Fin (arity e) → A) :
    acceptedCount (originalPredicate arity table coordinate) =
      ∑ assignment : A → Bool, ∏ e : E,
        if table e (fun i => assignment (coordinate e i)) then (1 : ℕ) else 0 := by
  unfold acceptedCount
  apply Fintype.sum_equiv (assignmentEquiv A)
  intro x
  rw [boolean_product_indicator]
  simp only [originalPredicate, assignmentEquiv, Equiv.coe_fn_mk, decide_eq_true_eq]
  rfl

/-- The constructed counter's empty restriction is a literal tensor sum. -/
theorem constructed_empty_count {A E : Type} [Fintype A] [DecidableEq A]
    [Fintype E] [DecidableEq E] {arity : E → ℕ}
    {coordinate : (e : E) → Fin (arity e) → A}
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) :
    prefixCount (problem table coverage p) [] =
      ∑ assignment : A → Bool, ∏ e : E,
        if table e (fun i => assignment (coordinate e i)) then (1 : ℕ) else 0 := by
  rw [constructed_prefix_count]
  have he : restricted assignmentBit (originalPredicate arity table coordinate) [] =
      originalPredicate arity table coordinate := by
    funext x
    simp only [restricted, List.all_nil, Bool.and_true]
  rw [he]
  exact accepted_eq_tensor arity table coordinate

/-- Coverage is derived from the actual two occurrences of every public bit. -/
theorem public_coverage {L : ℕ} (hL : 0 < L)
    (a : Edge (firstAxis L) (secondAxis L) (digitCount L)) :
    ∃ v i, publicCoordinate hL v i = a := by
  by_contra h
  have hn : ∀ v i, publicCoordinate hL v i ≠ a := by simpa using h
  have hc := ordered_edge_occurrence_two (digitCount_bounds hL).1
    (public_digit_capacity hL) a
  have hz : (∑ v : SubdividedVertex (firstAxis L) (secondAxis L) (digitCount L),
      ∑ i : Fin (subdividedArity v),
        if publicCoordinate hL v i = a then (1 : ℕ) else 0) = 0 := by simp [hn]
  change (∑ v : SubdividedVertex (firstAxis L) (secondAxis L) (digitCount L),
    ∑ i : Fin (subdividedArity v),
      if publicCoordinate hL v i = a then (1 : ℕ) else 0) = 2 at hc
  omega

/-- The actual public row-construction counter; no supplied replacement rows. -/
def publicProblem (N : ℕ) (hN : 0 < N)
    (hg : sourceLayoutGuard (variableCount (bitLength N)) (scopeBound (bitLength N))) :
    Problem (Edge (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
      (SubdividedVertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))) :=
  problem (subdividedTable (publicConfig N hN))
    (public_coverage (bitLength_pos hN)) (publicParameters (bitLength_pos hN) hg)

/-- Every restricted query is exactly the count of original accepting assignments
with those fixed wire bits. Inconsistent restrictions correctly have count zero. -/
theorem public_prefix_count (N : ℕ) (hN : 0 < N)
    (hg : sourceLayoutGuard (variableCount (bitLength N)) (scopeBound (bitLength N)))
    (fixed : List (Edge (firstAxis (bitLength N)) (secondAxis (bitLength N))
      (digitCount (bitLength N)) × Bool)) :
    prefixCount (publicProblem N hN hg) fixed =
      acceptedCount (restricted assignmentBit
        (originalPredicate subdividedArity (subdividedTable (publicConfig N hN))
          (publicCoordinate (bitLength_pos hN))) fixed) :=
  constructed_prefix_count _ _ _ fixed

/-- The completely constructed public count equals the ordinary ordered proper
factor-pair cardinal for every positive integer meeting the executable layout guard. -/
theorem public_constructed_factor_count (N : ℕ) (hN : 0 < N)
    (hg : sourceLayoutGuard (variableCount (bitLength N)) (scopeBound (bitLength N))) :
    prefixCount (publicProblem N hN hg) [] = Fintype.card (OrdinaryFactors N) := by
  exact (constructed_empty_count (subdividedTable (publicConfig N hN))
    (public_coverage (bitLength_pos hN)) (publicParameters (bitLength_pos hN) hg)).trans
      (public_tensor_factor_count N hN)

/-- Public constructed counting detects a proper factor exactly, including squares. -/
theorem public_constructed_positive_iff (N : ℕ) (hN : 0 < N)
    (hg : sourceLayoutGuard (variableCount (bitLength N)) (scopeBound (bitLength N))) :
    0 < prefixCount (publicProblem N hN hg) [] ↔ Nonempty (OrdinaryFactors N) := by
  rw [public_constructed_factor_count, Fintype.card_pos_iff]

/-- No additional counter calls are introduced by the public-graph composition. -/
theorem public_search_queries (N : ℕ) (hN : 0 < N)
    (hg : sourceLayoutGuard (variableCount (bitLength N)) (scopeBound (bitLength N)))
    (indices : List (Edge (firstAxis (bitLength N)) (secondAxis (bitLength N))
      (digitCount (bitLength N)))) :
    (counterSearch (publicProblem N hN hg) indices).queries ≤ indices.length + 1 :=
  counterSearch_queries_le _ _

end RiemannGaussian.SemiprimePublicConstructedCount
