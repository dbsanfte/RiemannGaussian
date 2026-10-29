/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAcquiredSourceCounter
import RiemannGaussian.SemiprimeCounterSearch
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Prefix search driven by the actual acquired scalar counter -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeAcquiredPrefixSearch
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeLocalArrayFrontend SemiprimeCounterSearch SemiprimeCountRecovery
open SemiprimeMacroEntryBitPrimitives
variable {n F r Q : ℕ} [NeZero r]

/-- Explicit finite every-occurrence restriction on the unchanged local scope. -/
def prefixGate (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) : Bool :=
  fixed.all (fun pair => (List.finRange (arity e)).all
    (fun i => decide (coordinate e i=pair.1 → input i=pair.2)))

/-- The executed gate imposes every fixed bit on every occurrence. -/
theorem prefixGate_correct (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    prefixGate arity coordinate fixed e input =
      decide (∀ pair ∈ fixed, ∀ i, coordinate e i=pair.1 → input i=pair.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [prefixGate, List.all_eq_true, decide_eq_true_eq, List.mem_finRange, true_implies]

/-- Paid original local bit checker plus the actual finite restriction scan. -/
def entry (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) : EntryReport :=
  let original := base e input
  let accept := original.accepted && prefixGate arity coordinate fixed e input
  let budget := original.clock+fixed.length*(3*arity e+2)+1
  ⟨if accept then 1 else 0,budget,budget⟩

/-- The integer entry callback is exactly the original rational prefix table. -/
theorem entry_value (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    ((entry arity coordinate base fixed e input).value : ℚ)=
      rationalTable arity (prefixTable arity (fun e a => (base e a).accepted) coordinate fixed) e input := by
  simp only [entry, prefixGate_correct, rationalTable, prefixTable, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rfl

/-- Natural prefix count obtained from the executed source-to-scalar interpreter. -/
def prefixCount (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun) (fixed : List (Fin n × Bool)) : ℕ :=
  Nat.floor (SemiprimeAcquiredSourceCounter.count (r := r) (Q := Q) arity coordinate eps R B J
    (entry arity coordinate base fixed)).value

/-- Every prefix count is the original restricted acceptance count; no count oracle is supplied. -/
theorem prefixCount_correct (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (coverage : ∀ a, ∃ e i, coordinate e i=a)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hJ : 0<J) (hprecision : (∑ e, arity e)*R<Q*J) (fixed : List (Fin n × Bool)) :
    prefixCount (r := r) (Q := Q) arity coordinate eps R B J base fixed =
      acceptedCount (restricted assignmentBit
        (originalPredicate arity (fun e a => (base e a).accepted) coordinate) fixed) := by
  have hs := SemiprimeAcquiredSourceCounter.count_correct arity coordinate eps R B J
    (entry arity coordinate base fixed) howner hQ hAQ hJ hprecision
  have he : SemiprimeCounterNative.originalContraction arity
      (fun e eta => ((entry arity coordinate base fixed e eta).value : ℚ)) coordinate =
      (acceptedCount (restricted assignmentBit
        (originalPredicate arity (fun e a => (base e a).accepted) coordinate) fixed) : ℕ) := by
    simp only [SemiprimeCounterNative.originalContraction, acceptedCount, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro x _
    simp only [entry_value]
    change (∏ e, rationalTable arity (prefixTable arity (fun e a => (base e a).accepted)
      coordinate fixed) e (fun i => assignmentBit x (coordinate e i))) = _
    rw [rational_product_indicator]
    have hp : originalPredicate arity
        (prefixTable arity (fun e a => (base e a).accepted) coordinate fixed) coordinate x =
        restricted assignmentBit (originalPredicate arity (fun e a => (base e a).accepted) coordinate) fixed x := by
      apply Bool.eq_iff_iff.mpr
      simpa only [originalPredicate, decide_eq_true_eq] using
        prefix_accept_iff arity (fun e a => (base e a).accepted) coordinate coverage fixed x
    rw [hp]
  unfold prefixCount
  rw [hs,he,Nat.floor_natCast]

/-- Search all literal indexed wire bits using only actual acquired prefix counts. -/
def search (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun) : SearchResult (Fin n) :=
  SemiprimeCountRecovery.search
    (prefixCount (r := r) (Q := Q) arity coordinate eps R B J base) (List.finRange n)

/-- There are at most one initial and one conditional query per actual wire. -/
theorem search_queries (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun) :
    (search (r := r) (Q := Q) arity coordinate eps R B J base).queries ≤ n+1 := by
  simpa only [search, List.length_finRange] using SemiprimeCountRecovery.search_queries_le
    (prefixCount (r := r) (Q := Q) arity coordinate eps R B J base) (List.finRange n)

/-- Reconstruct a selected wire directly from the returned literal bit list. -/
def selectedBits (values : List (Fin n × Bool)) (i : Fin n) : Bool :=
  values.any (fun p => decide (p.1=i) && p.2)

/-- A complete sound selected list reconstructs its one common original witness. -/
theorem selectedBits_eq (values : List (Fin n × Bool)) (bits : Fin n → Bool)
    (hcover : ∀ i, ∃ p ∈ values, p.1=i)
    (hsound : ∀ p ∈ values, bits p.1=p.2) (i : Fin n) : selectedBits values i=bits i := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨p,hp,hv⟩ := List.any_eq_true.mp h
    have hv' : decide (p.1=i)=true ∧ p.2=true := by simpa only [Bool.and_eq_true] using hv
    obtain ⟨hi,hb⟩ := hv'
    have he : p.1=i := of_decide_eq_true hi
    exact (he ▸ hsound p hp).trans hb
  · intro h
    obtain ⟨p,hp,hi⟩ := hcover i
    apply List.any_eq_true.mpr
    refine ⟨p,hp,?_⟩
    have hb : p.2=true := (hsound p hp).symm.trans (by simpa only [hi] using h)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using And.intro hi hb

/-- Every executed prefix callback remains a literal zero/one integer tensor entry. -/
theorem entry_abs (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).value.natAbs ≤ 1 := by
  change (if (base e input).accepted && prefixGate arity coordinate fixed e input then (1 : ℤ) else 0).natAbs ≤ 1
  split_ifs <;> decide

/-- Callback accounting retains the paid bit checker and the finite local restriction scan. -/
theorem entry_work (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).arithmetic=
      (base e input).clock+fixed.length*(3*arity e+2)+1 ∧
    (entry arity coordinate base fixed e input).reads=
      (base e input).clock+fixed.length*(3*arity e+2)+1 := ⟨rfl,rfl⟩

end RiemannGaussian.SemiprimeAcquiredPrefixSearch
