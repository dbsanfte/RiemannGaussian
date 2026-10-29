/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramTrie
import RiemannGaussian.SemiprimeSourceHistogramGrouping

/-! # Actual streaming physical collision-square histogram
Each key visits one trie path. The returned old frequency k drives the physical
increment 2k+1 and compact accumulated sum. No final-bin catalogue is executed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramSquares
open SemiprimeBitArithmetic
open SemiprimeSourceHistogramGrouping
open SemiprimeSourceHistogramTrie (Trie CompactCounters)
open SemiprimeSourceCompactBits (Compact)

/-- Actual dictionary, compact accumulated square-count and all retained reports. -/
structure State where
  /-- Acquired persistent frequency trie. -/
  trie : Trie
  /-- Physical compact collision-square total. -/
  bits : List Bool
  /-- Every trie/arithmetic/cell/control stage already executed. -/
  clock : ℕ

/-- Empty physical state contains no frequency answer or allocated bins. -/
def initial : State := ⟨.empty,[],1⟩

/-- One physical streaming step, with the old counter acquired once by bump.
Little-endian false-processed is the actual doubled counter, not an encoded Nat. -/
def step (state : State) (key : List Bool) : State :=
  let changed := SemiprimeSourceHistogramTrie.bump state.trie key
  let term := SemiprimeSourceCompactBits.increment (false::changed.old)
  let total := SemiprimeSourceCompactBits.add state.bits term.bits
  ⟨changed.trie,total.bits,state.clock+changed.clock+term.clock+total.clock+
    key.length+changed.old.length+10⟩

/-- Original key order is traversed literally, retaining the same acquired state. -/
def fold : List (List Bool) → State → State
  | [],state => ⟨state.trie,state.bits,state.clock+1⟩
  | key::keys,state =>
    let next := step state key
    let rest := fold keys next
    ⟨rest.trie,rest.bits,rest.clock+3⟩

/-- Complete generic key-list acquisition with no supplied frequencies. -/
def acquire (keys : List (List Bool)) : State := fold keys initial

/-- Proof-only ordered collision count; runtime never executes this pair scan. -/
def collisions (keys : List (List Bool)) : ℕ :=
  pairs keys (fun a b => if a=b then (1:ℕ) else 0)

/-- One equality row is exactly the literal occurrence count. -/
theorem row_count (keys : List (List Bool)) (key : List Bool) :
    (keys.map (fun a => if a=key then (1:ℕ) else 0)).sum=keys.count key := by
  induction keys with
  | nil => simp
  | cons a keys ih => by_cases h : a=key <;> simp [h,ih,Nat.add_comm]

/-- Appending one original occurrence creates precisely 2k+1 ordered collisions. -/
theorem collisions_append (keys : List (List Bool)) (key : List Bool) :
    collisions (keys++[key])=collisions keys+2*keys.count key+1 := by
  have hl := row_count keys key
  have hr : (keys.map (fun a => if key=a then (1:ℕ) else 0)).sum=keys.count key := by
    simpa only [eq_comm] using hl
  unfold collisions pairs
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.sum_map_add,ite_true,Nat.add_zero]
  rw [hl,hr]
  omega

/-- Pointwise executed total update from the SAME physically returned old counter. -/
theorem step_value (state : State) (key : List Bool) :
    bitValue (step state key).bits=bitValue state.bits+
      2*SemiprimeSourceHistogramTrie.value state.trie key+1 := by
  simp only [step,SemiprimeSourceCompactBits.add_value,
    SemiprimeSourceCompactBits.increment_value,SemiprimeSourceHistogramTrie.bump_old,
    bitValue,SemiprimeSourceHistogramTrie.value,bitNat,Bool.false_eq_true,ite_false]
  omega

/-- Every executed total remains canonical compact bits. -/
theorem step_compact (state : State) (key : List Bool) : Compact (step state key).bits :=
  SemiprimeSourceCompactBits.add_compact _ _

/-- The proof-view names actual processed frequencies and their square total. -/
def Good (processed : List (List Bool)) (state : State) : Prop :=
  (∀ key,SemiprimeSourceHistogramTrie.value state.trie key=processed.count key) ∧
    bitValue state.bits=collisions processed ∧ CompactCounters state.trie ∧ Compact state.bits

/-- Actual empty acquisition has zero frequencies and zero collision total. -/
theorem initial_good : Good [] initial := by
  refine ⟨?_,rfl,SemiprimeSourceHistogramTrie.empty_compact,trivial⟩
  intro key
  simp [initial,SemiprimeSourceHistogramTrie.value,SemiprimeSourceHistogramTrie.stored_empty,bitValue]

/-- Every actual streamed processed has the literal original occurrence counts. -/
theorem step_good (processed : List (List Bool)) (state : State) (key : List Bool)
    (hs : Good processed state) : Good (processed++[key]) (step state key) := by
  refine ⟨?_,?_,SemiprimeSourceHistogramTrie.bump_compact _ _ hs.2.2.1,step_compact state key⟩
  · intro query
    change SemiprimeSourceHistogramTrie.value
      (SemiprimeSourceHistogramTrie.bump state.trie key).trie query=_
    rw [SemiprimeSourceHistogramTrie.bump_value,hs.1 query]
    by_cases h : query=key <;> simp [List.count_append,h,Ne.symm]
  · rw [step_value,hs.1 key,hs.2.1,collisions_append]

/-- Loop invariant is established from actual steps, not supplied final state. -/
theorem fold_good (keys processed : List (List Bool)) (state : State) (hs : Good processed state) :
    Good (processed++keys) (fold keys state) := by
  induction keys generalizing processed state with
  | nil => simpa only [Good,fold,List.append_nil] using hs
  | cons key keys ih =>
    have h := ih (processed++[key]) (step state key) (step_good processed state key hs)
    simpa only [Good,fold,List.append_assoc,List.singleton_append] using h

/-- All original keys, duplicates, empty keys and processed-related keys are exact. -/
theorem acquire_good (keys : List (List Bool)) : Good keys (acquire keys) := by
  simpa only [acquire,List.nil_append] using fold_good keys [] initial initial_good

/-- Exact physical final lookup against literal List.count, including absent keys. -/
theorem lookup_final (keys : List (List Bool)) (key : List Bool) :
    bitValue (SemiprimeSourceHistogramTrie.lookup (acquire keys).trie key).bits=keys.count key := by
  rw [SemiprimeSourceHistogramTrie.lookup_value]
  exact (acquire_good keys).1 key

/-- The actual accumulator equals the original collision-pair count. -/
theorem acquire_value (keys : List (List Bool)) :
    bitValue (acquire keys).bits=collisions keys := (acquire_good keys).2.1

/-- Final sparse-bin squares are a theorem, never an extra executed scan. -/
theorem acquire_squares (keys : List (List Bool)) :
    bitValue (acquire keys).bits=∑ key∈keys.toFinset,(keys.count key)^2 := by
  rw [acquire_value]
  have h := pair_grouping (fun a : List Bool => a) keys
  change collisions keys=∑ key∈(keys.map id).toFinset,
    (multiplicity (id : List Bool → List Bool) keys key)^2 at h
  have hm (key : List Bool) : multiplicity (id : List Bool → List Bool) keys key=keys.count key := by
    exact (indicator_sum (id : List Bool → List Bool) keys key).symm.trans (row_count keys key)
  simp only [hm,List.map_id] at h
  exact h

end RiemannGaussian.SemiprimeSourceHistogramSquares
