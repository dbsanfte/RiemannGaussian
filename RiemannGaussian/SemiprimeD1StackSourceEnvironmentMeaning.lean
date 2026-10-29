/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
/-! # Exact original reverse-prefix/default meaning of physical marked lookup
These statements describe the actual source dictionary. No original environment,
lookup function, active/free verdict or clock becomes a runtime argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentMeaning
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentEncoding
open SemiprimeBitArithmetic (bitValue)
/-- Exact original reverse-list single-element indexing, with default empty ID outside the prefix. -/
theorem getD_append_single (xs:List (List Bool)) (x:List Bool) (i:Nat) :
    ((xs++[x])[i]?).getD []=if i=xs.length then x else (xs[i]?).getD [] :=by
  induction xs generalizing i with
  | nil=>cases i  <;> simp
  | cons y ys ih=>cases i with
    | zero=>simp
    | succ i=>simpa using ih i
/-- Physical newest-first prefix order agrees exactly with the old prefix dictionary expected value. -/
theorem expected_cons (id:List Bool) (ids:List (List Bool)) (i:Nat) :
    SemiprimeSourceHistogramPrefix.expected (id::ids) i=
      if i=ids.length then normalize id else SemiprimeSourceHistogramPrefix.expected ids i :=by
  simp only [SemiprimeSourceHistogramPrefix.expected,List.reverse_cons,getD_append_single,List.length_reverse]
  split  <;> simp only [normalize_trim]
/-- Original finite reverse-prefix read equals the literal reversed-list index/default. -/
theorem readRun_getD (ids:List (List Bool)) (i:Nat) :
    (SemiprimeMaterializedWordSearch.readRun [] ids i).value=((ids.reverse[i]?).getD []) :=by
  induction ids with
  | nil=>rfl
  | cons id ids ih=>
    simp only [SemiprimeMaterializedWordSearch.readRun,List.reverse_cons,getD_append_single,List.length_reverse]
    split  <;> simp only [ih]
/-- Exact found/missing payload of the marked prefix dictionary. -/
def markedRead (ids:List (List Bool)) (i:Nat) :List Bool :=
  if i < ids.length then true::SemiprimeSourceHistogramPrefix.expected ids i else []
/-- Prefix extension assigns precisely the current actual next key; older bindings retain their order and values. -/
theorem markedRead_cons (id:List Bool) (ids:List (List Bool)) (i:Nat) :
    markedRead (id::ids) i=if i=ids.length then marked id else markedRead ids i :=by
  unfold markedRead
  rw [List.length_cons,expected_cons]
  by_cases h:i=ids.length
  · subst i
    simp only [Nat.lt_succ_self,ite_true,marked]
  · have he:(i < ids.length+1)↔i < ids.length:=by omega
    simp only [h,ite_false,he]
/-- The real first-match lookup has exactly the old normalized reverse-prefix value and an explicit present marker. -/
theorem lookup_prefix (query:List Bool) (ids:List (List Bool)) :
    (SemiprimeD1StackOwnerLookup.result query (prefixRows ids) []).1=markedRead ids (bitValue query) :=by
  induction ids with
  | nil=>simp [markedRead,prefixRows,SemiprimeD1StackOwnerLookup.result]
  | cons id ids ih=>
    rw [prefixRows,SemiprimeD1StackOwnerLookup.result,variableKey_value,markedRead_cons]
    by_cases h:bitValue query=ids.length
    · simp only [h,ite_true]
    · simp only [Ne.symm h,h,ite_false,ih]
/-- Missing means outside the acquired prefix; arbitrary high-zero query padding is handled numerically. -/
theorem present_iff (ids:List (List Bool)) (query:List Bool) :
    (markedRead ids (bitValue query)).head?=some true↔bitValue query < ids.length :=by
  unfold markedRead
  split  <;> simp_all
/-- Absence is distinct from a selected zero ID, whose actual compact payload is empty after its true marker. -/
theorem marked_zero (word:List Bool) (hz:bitValue word=0) :marked word=[true] :=by
  have he:normalize word=[]:=SemiprimeSourceCompactWordIds.compact_value_injective _ _ (normalize_compact word)
    trivial (by rw [normalize_value,hz];rfl)
  rw [marked,he]
/-- Exact fixed-prefix/default read bridge, normalized by the actual source rather than an advised payload. -/
theorem readFixed_original (ids:List (List Bool)) (query:List Bool) :
    SemiprimeSourceHistogramPrefix.expected ids (bitValue query)=
      normalize (SemiprimeSourceWordIdEnvironment.readFixed [] ids query).value :=by
  rw [SemiprimeSourceWordIdEnvironment.readFixed_value,readRun_getD,normalize_trim]
  rfl
/-- The selector's missing/free equivalence requires actual valid endpoints and the exact remaining prefix interval. -/
theorem missing_free (ids:List (List Bool)) (query:List Bool) (N:Nat) (hk:ids.length ≤ N) (hq:bitValue query < N) :
    (markedRead ids (bitValue query)).head?=none↔
      bitValue query∈List.range' ids.length (N-ids.length) :=by
  unfold markedRead
  by_cases h:bitValue query < ids.length
  · simp only [h,ite_true,List.head?_cons,reduceCtorEq,false_iff]
    intro hm
    have he:=List.mem_range'.mp hm
    omega
  · simp only [h,ite_false,List.head?_nil,true_iff]
    apply List.mem_range'.mpr
    exact ⟨bitValue query-ids.length,by omega,by omega⟩
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentMeaning
