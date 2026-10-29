/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
import RiemannGaussian.SemiprimeD1CounterMaximum
/-! # Exact raw-key frequencies and original compact maximum, without any transported clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMeaning
open SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceCompactBits (Compact)
/-- Numeric dictionary lookup is an exact byte-key first-match read, including all high-zero raw suffixes. -/
theorem read_cons (raw value:List Bool) (rows:Rows) (q:List Bool) :
    read ((raw,value)::rows) q=if raw=q then value else read rows q :=by
  unfold SemiprimeD1StackSourceKeyFrequencyEncoding.read coded
  simp only [List.map_cons,SemiprimeD1StackOwnerLookup.result,encoded_eq]
  split <;> rfl
/-- Every present payload is compact; absence is compact zero. -/
theorem read_compact (rows:Rows) (q:List Bool) (h:∀r∈rows,Compact r.2) :Compact (read rows q) :=by
  induction rows with
  | nil=>trivial
  | cons r rows ih=>
    rw [read_cons]
    split
    · exact h r (by simp)
    · exact ih (fun row hr=>h row (by simp [hr]))
/-- Strict physical maximum comparison gives the ordinary maximum value, retaining old word on ties. -/
theorem nextMaximum_value (a b:List Bool) :bitValue (nextMaximum a b)=max (bitValue a) (bitValue b) :=by
  unfold nextMaximum
  split_ifs with h
  · exact (Nat.max_eq_right (le_of_lt ((SemiprimeD1StackWordLessExecution.answer_true a b).mp h))).symm
  · have hn:bitValue b≤bitValue a:=by
      have hh:¬ bitValue a<bitValue b:=fun g=>h ((SemiprimeD1StackWordLessExecution.answer_true a b).mpr g)
      omega
    exact (Nat.max_eq_left hn).symm
/-- Maximum replacement selects one of its actual compact input words. -/
theorem nextMaximum_compact (a b:List Bool) (ha:Compact a) (hb:Compact b) :Compact (nextMaximum a b) :=by
  unfold nextMaximum;split_ifs <;> assumption
/-- Exact dictionary counts, intrinsic compactness, upper bound and attained maximum are proof invariants only. -/
structure Good (keys:List (List Bool)) (s:Summary) :Prop where
  /-- Actual first-match numeric result is the literal raw-byte frequency. -/
  counts:∀q,bitValue (read s.rows q)=keys.count q
  /-- Every retained historical override is a compact binary word. -/
  counters:∀r∈s.rows,Compact r.2
  /-- Actual maximum is compact, including empty zero. -/
  compact:Compact s.maximum
  /-- Every raw-byte frequency is bounded by the actual maximum. -/
  dominates:∀q,keys.count q≤bitValue s.maximum
  /-- A positive maximum is an actually present frequency. -/
  attained:bitValue s.maximum=0 ∨ ∃q,bitValue s.maximum=keys.count q
/-- Empty actual dictionary and maximum satisfy the count invariant. -/
theorem empty_good :Good [] empty :=by
  refine ⟨?_,?_,trivial,?_,Or.inl rfl⟩
  · intro q;rfl
  · intro r hr;cases hr
  · intro q;exact Nat.zero_le _
/-- One real compact increment and head override update precisely one exact raw-key frequency. -/
theorem step_good (keys:List (List Bool)) (s:Summary) (raw:List Bool) (h:Good keys s) :
    Good (keys++[raw]) (step s raw) :=by
  have hv:bitValue (nextCount s.rows raw)=keys.count raw+1:=by
    rw [nextCount,SemiprimeD1StackSourceEnvironmentEncoding.successor_value,h.counts]
  have hc:Compact (nextCount s.rows raw):=SemiprimeD1StackSourceEnvironmentEncoding.successor_compact _
  have hm:bitValue (step s raw).maximum=max (bitValue s.maximum) (keys.count raw+1):=by
    change bitValue (nextMaximum s.maximum (nextCount s.rows raw))=_
    rw [nextMaximum_value,hv]
  refine ⟨?_,?_,nextMaximum_compact _ _ h.compact hc,?_,?_⟩
  · intro q
    change bitValue (read ((raw,nextCount s.rows raw)::s.rows) q)=_
    rw [read_cons]
    by_cases he:raw=q
    · subst q
      simp only [ite_true]
      rw [hv]
      simp only [List.count_append,List.count_singleton,beq_self_eq_true,ite_true]
    · simp only [he,ite_false]
      rw [h.counts]
      simp [List.count_append,he]
  · intro r hr
    rcases List.mem_cons.mp hr with hr|hr
    · subst r;exact hc
    · exact h.counters r hr
  · intro q
    rw [hm]
    by_cases he:q=raw
    · subst q
      have hh:(keys++[raw]).count raw=keys.count raw+1:=by simp
      rw [hh]
      exact le_max_right _ _
    · have hh:(keys++[raw]).count q=keys.count q:=by simp [List.count_append,Ne.symm he]
      rw [hh]
      exact (h.dominates q).trans (le_max_left _ _)
  · rw [hm]
    by_cases he:bitValue s.maximum≤keys.count raw+1
    · right;refine ⟨raw,?_⟩
      rw [Nat.max_eq_right he]
      simp
    · have he':keys.count raw+1≤bitValue s.maximum:=by omega
      rw [Nat.max_eq_left he']
      rcases h.attained with hz|⟨q,hq⟩
      · exact Or.inl hz
      · right;refine ⟨q,?_⟩
        by_cases hqr:q=raw
        · subst q;have hd:=h.dominates raw;omega
        · rw [hq];simp [List.count_append,Ne.symm hqr]
/-- The SAME chronological fold establishes every frequency and maximum from the empty physical source. -/
theorem fold_good (keys processed:List (List Bool)) (s:Summary) (h:Good processed s) :
    Good (processed++keys) (keys.foldl step s) :=by
  induction keys generalizing processed s with
  | nil=>simpa only [List.foldl_nil,List.append_nil] using h
  | cons key keys ih=>
    simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using
      ih (processed++[key]) (step s key) (step_good processed s key h)
/-- Exact raw-key counts and compact maximum hold for every key vector, with no wellformed-label advice. -/
theorem acquire_good (keys:List (List Bool)) :Good keys (acquire keys) :=by
  simpa only [acquire,List.nil_append] using fold_good keys [] empty empty_good
/-- The actual compact maximum is byte-for-byte the frozen original CounterMaximum result, independent of its report clock. -/
theorem maximum_original (keys:List (List Bool)) :
    (acquire keys).maximum=(SemiprimeD1CounterMaximum.maxState (SemiprimeSourceHistogramSquares.acquire keys)).bits :=by
  let old:=SemiprimeSourceHistogramSquares.acquire keys
  have ho:=SemiprimeSourceHistogramSquares.acquire_good keys
  have hn:=acquire_good keys
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hn.compact
    (SemiprimeD1CounterMaximum.maximumTrie_compact old.trie ho.2.2.1)
  apply Nat.le_antisymm
  · rcases hn.attained with hz|⟨q,hq⟩
    · rw [hz];exact Nat.zero_le _
    · rw [hq,←ho.1 q]
      exact SemiprimeD1CounterMaximum.lookup_le_maximum old.trie q
  · exact SemiprimeD1CounterMaximum.maximumTrie_le old.trie _ (fun q=>by
      rw [ho.1 q]
      exact hn.dominates q)
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMeaning
