/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterCompose
import RiemannGaussian.SemiprimeCountRecovery

/-!
# Original-network prefix search from the actual counter

Prefixes are enforced inside the original local tables at every occurrence of a
fixed bit. No unary factors, new variables, scope changes or correctness oracle
are introduced. Counter execution and its bit cost remain separate obligations.
-/
namespace RiemannGaussian.SemiprimeCounterSearch
open scoped BigOperators
open Polynomial
open RiemannGaussian.SemiprimeCounterCompose
open RiemannGaussian.SemiprimeCounterNative
open RiemannGaussian.SemiprimeHermiteRecovery
open RiemannGaussian.SemiprimeCountRecovery
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]

/-- Literal original assignment bit. -/
def assignmentBit (x : Finset A) (a : A) : Bool := decide (a ∈ x)

/-- All original local tensors accept their actual input coordinates. -/
def originalPredicate (arity : E → ℕ)
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coordinate : (e : E) → Fin (arity e) → A) (x : Finset A) : Bool :=
  decide (∀ e, table e (fun i => assignmentBit x (coordinate e i)) = true)

/-- Every-occurrence policy: all owned occurrences of every fixed bit must agree.
The domain and arity of this local table are identical to the original table. -/
def prefixTable (arity : E → ℕ)
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coordinate : (e : E) → Fin (arity e) → A) (fixed : List (A × Bool))
    (e : E) (input : Fin (arity e) → Bool) : Bool :=
  table e input && decide (∀ pair ∈ fixed, ∀ i, coordinate e i = pair.1 → input i = pair.2)

/-- Scalar zero/one entries supplied to the algebraic tensor counter. -/
def rationalTable (arity : E → ℕ)
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (e : E) (input : Fin (arity e) → Bool) : ℚ := if table e input then 1 else 0

theorem prefix_accept_iff (arity : E → ℕ)
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coordinate : (e : E) → Fin (arity e) → A)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (fixed : List (A × Bool)) (x : Finset A) :
    (∀ e, prefixTable arity table coordinate fixed e
      (fun i => assignmentBit x (coordinate e i)) = true) ↔
      restricted assignmentBit (originalPredicate arity table coordinate) fixed x = true := by
  simp only [prefixTable, Bool.and_eq_true, decide_eq_true_eq]
  simp only [restricted, originalPredicate, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    refine ⟨fun e => (h e).1, ?_⟩
    intro pair hp
    obtain ⟨e, i, hi⟩ := coverage pair.1
    simpa only [hi] using (h e).2 pair hp i hi
  · rintro ⟨hbase, hfixed⟩ e
    refine ⟨hbase e, ?_⟩
    intro pair hp i hi
    simpa only [hi] using hfixed pair hp

omit [Fintype A] in
theorem rational_product_indicator (arity : E → ℕ)
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coordinate : (e : E) → Fin (arity e) → A) (x : Finset A) :
    (∏ e, rationalTable arity table e (fun i => assignmentBit x (coordinate e i))) =
      if originalPredicate arity table coordinate x then (1 : ℚ) else 0 := by
  classical
  by_cases h : ∀ e, table e (fun i => assignmentBit x (coordinate e i)) = true
  · simp [rationalTable, originalPredicate, h]
  · have he : ∃ e, table e (fun i => assignmentBit x (coordinate e i)) = false := by
      push Not at h
      simpa only [Bool.not_eq_true] using h
    obtain ⟨e, he⟩ := he
    rw [Finset.prod_eq_zero (Finset.mem_univ e) (by simp [rationalTable, he])]
    simp [originalPredicate, h]

/-- Actual row/design data needed by the counter; no supplied contraction value. -/
structure Problem (A E : Type) [Fintype A] [DecidableEq A] [Fintype E] where
  /-- Original local arities. -/
  arity : E → ℕ
  /-- Original Boolean local tables. -/
  table : (e : E) → (Fin (arity e) → Bool) → Bool
  /-- Original port coordinates. -/
  coordinate : (e : E) → Fin (arity e) → A
  /-- Every searched original bit has at least one existing occurrence. -/
  coverage : ∀ a, ∃ e i, coordinate e i = a
  /-- Actual polynomial replacement rows. -/
  rows : (e : E) → Fin (arity e) → A → Polynomial ℚ
  /-- Number of positive rational sample nodes. -/
  Q : ℕ
  /-- Degree bound of each replacement row. -/
  R : ℕ
  /-- Sample node count is positive. -/
  Q_pos : 0 < Q
  /-- Local row-certified measurement data, independent of local table contents. -/
  design : (t : samplePoints Q) → NodeCertificate arity (fun e i v => (rows e i v).eval t)
  /-- Actual row degree certificate. -/
  row_degree : ∀ e i v, (rows e i v).natDegree ≤ R
  /-- Literal physical-coordinate restoration. -/
  restoration : ∀ e i v, (rows e i v).eval 0 = if v=coordinate e i then 1 else 0

/-- Actual rational counter expression on the original scopes with a fixed prefix. -/
def prefixCounter (p : Problem A E) (fixed : List (A × Bool)) : ℚ :=
  counterValue p.arity (rationalTable p.arity (prefixTable p.arity p.table p.coordinate fixed))
    p.rows p.Q p.R ((∑ e, p.arity e)*p.R/p.Q+1) p.design

/-- Natural count read from the literal rational counter result. -/
def prefixCount (p : Problem A E) (fixed : List (A × Bool)) : ℕ := Nat.floor (prefixCounter p fixed)

theorem prefixCounter_eq_accepted (p : Problem A E) (fixed : List (A × Bool)) :
    prefixCounter p fixed =
      (acceptedCount (restricted assignmentBit (originalPredicate p.arity p.table p.coordinate) fixed) : ℕ) := by
  rw [prefixCounter, counterValue_eq_original _ _ _ _ _ p.Q_pos _ p.row_degree _ p.restoration]
  simp only [originalContraction, acceptedCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  change (∏ e, rationalTable p.arity (prefixTable p.arity p.table p.coordinate fixed) e
    (fun i => assignmentBit x (p.coordinate e i))) = _
  rw [rational_product_indicator]
  have heq : originalPredicate p.arity (prefixTable p.arity p.table p.coordinate fixed) p.coordinate x =
      restricted assignmentBit (originalPredicate p.arity p.table p.coordinate) fixed x := by
    apply Bool.eq_iff_iff.mpr
    simpa only [originalPredicate, decide_eq_true_eq] using
      prefix_accept_iff p.arity p.table p.coordinate p.coverage fixed x
  rw [heq]

theorem prefixCount_eq_accepted (p : Problem A E) (fixed : List (A × Bool)) :
    prefixCount p fixed =
      acceptedCount (restricted assignmentBit (originalPredicate p.arity p.table p.coordinate) fixed) := by
  rw [prefixCount, prefixCounter_eq_accepted]
  simp

/-- Search driven by the actual fixed-prefix counter, with one initial count. -/
def counterSearch (p : Problem A E) (indices : List A) : SearchResult A :=
  search (prefixCount p) indices

/-- One actual counter call initially and at most one for each requested bit. -/
theorem counterSearch_queries_le (p : Problem A E) (indices : List A) :
    (counterSearch p indices).queries ≤ indices.length+1 :=
  search_queries_le (prefixCount p) indices

/-- Empty result is equivalent to absence of an original accepting assignment. -/
theorem counterSearch_none_iff (p : Problem A E) (indices : List A) :
    (counterSearch p indices).values = none ↔
      ¬ ∃ x, originalPredicate p.arity p.table p.coordinate x = true := by
  exact search_none_iff (prefixCount p) assignmentBit
    (originalPredicate p.arity p.table p.coordinate) (prefixCount_eq_accepted p) indices

/-- Returned bits belong to one original accepting assignment, without a count
correctness oracle premise: that equality was proved from the actual counter. -/
theorem counterSearch_some_sound (p : Problem A E) (indices : List A)
    (values : List (A × Bool)) (h : (counterSearch p indices).values = some values) :
    values.map Prod.fst = indices ∧ ∃ x,
      originalPredicate p.arity p.table p.coordinate x = true ∧
      ∀ pair ∈ values, assignmentBit x pair.1 = pair.2 := by
  exact search_some_sound (prefixCount p) assignmentBit
    (originalPredicate p.arity p.table p.coordinate) (prefixCount_eq_accepted p)
    indices values h

#print axioms counterSearch_queries_le
#print axioms counterSearch_none_iff
#print axioms counterSearch_some_sound
#print axioms prefixCounter_eq_accepted
#print axioms prefixCount_eq_accepted
end
end RiemannGaussian.SemiprimeCounterSearch
