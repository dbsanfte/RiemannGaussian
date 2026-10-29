/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramRowKeys
import RiemannGaussian.SemiprimeSourceHistogramFeatureBits
import RiemannGaussian.SemiprimeSourceHistogramDictRefinement

/-! # Actual one-pass fixed/free head histogram acquisition
Free vertices only increment their actual counter. Every fixed vertex performs
one prefix-ID lookup and one all-coordinate row query before histogramming.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramHeadBits
open SemiprimeBitArithmetic SemiprimeMaterializedWords
open SemiprimeSourceHistogramTrie (Trie)
open SemiprimeSourceCompactBits (Compact)

/-- Original vertex code and its once-acquired physical dictionary key. -/
structure Vertex where
  /-- Original native finite-index metadata for the interval mask. -/
  code : ℕ
  /-- Actual compact physical variable key. -/
  key : List Bool

/-- Acquire one original variable key with its full encoder report. -/
def vertex {n : ℕ} (i : Fin n) : Run Vertex :=
  let out := SemiprimeSourceHistogramPortKeys.encodeKey i.val
  ⟨⟨i.val,out.bits⟩,out.clock+2⟩

/-- Actual static vertex-key cache in the original supplied finite list order. -/
def verticesWith {n : ℕ} : List (Fin n) → Run (List Vertex)
  | [] => ⟨[],1⟩
  | i::is =>
    let first := vertex i
    let tail := verticesWith is
    ⟨first.value::tail.value,first.work+tail.work+3⟩

/-- Original-input static cache acquisition with paid finite-index generation. -/
def acquireVertices (n : ℕ) : Run (List Vertex) :=
  let indices := SemiprimePaidFiniteEnumerationLists.fin n
  let out := verticesWith indices.value
  ⟨out.value,indices.work+out.work+3⟩

/-- Exact acquired original vertex order. -/
theorem verticesWith_value {n : ℕ} (is : List (Fin n)) :
    (verticesWith is).value=is.map (fun i => (vertex i).value) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [verticesWith,List.map_cons,ih]

/-- Every original finite vertex occurs once in its actual original order. -/
theorem acquireVertices_value (n : ℕ) :
    (acquireVertices n).value=(List.finRange n).map (fun i => (vertex i).value) := by
  simp only [acquireVertices,verticesWith_value,SemiprimePaidFiniteEnumerationLists.fin_value]

/-- Original input acquisition derives physical key value and compactness. -/
theorem vertex_rep {n : ℕ} (i : Fin n) :
    Compact (vertex i).value.key ∧ bitValue (vertex i).value.key=i.val :=
  ⟨SemiprimeSourceHistogramPortKeys.encodeKey_compact _,
    SemiprimeSourceHistogramPortKeys.encodeKey_value _⟩

/-- Append actual histogram key references by a paid list-spine traversal. -/
def appendKeys : List (List Bool) → List (List Bool) → Run (List (List Bool))
  | [],ys => ⟨ys,1⟩
  | x::xs,ys =>
    let out := appendKeys xs ys
    ⟨x::out.value,out.work+3⟩

/-- No reordering or duplication occurs in the actual key append. -/
theorem appendKeys_value (xs ys : List (List Bool)) :
    (appendKeys xs ys).value=xs++ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [appendKeys,List.cons_append,ih]

/-- Actual list-spine copies are linear in the newly produced key list. -/
theorem appendKeys_work (xs ys : List (List Bool)) :
    (appendKeys xs ys).work=3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [appendKeys,List.length_cons,ih];omega

/-- Actual all-coordinate key stream and physical fixed/free counters. -/
structure HeadData where
  /-- Actual fixed-vertex coordinate-colour keys, preserving all multiplicities. -/
  keys : List (List Bool)
  /-- Physical number of fixed original vertices. -/
  fixed : List Bool
  /-- Physical number of free original vertices. -/
  free : List Bool
  /-- All key queries, appends, increments and original control stages. -/
  clock : ℕ

/-- Traverse the cached static vertices once; free vertices skip every label read. -/
def produce (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) : List Vertex → HeadData
  | [] => ⟨[],[],[],1⟩
  | v::vs =>
    let rest := produce cache dict k s vs
    if SemiprimeSourceHistogramFeatureBits.active k s v.code then
      let total := SemiprimeSourceCompactBits.increment rest.free
      ⟨rest.keys,rest.fixed,total.bits,rest.clock+total.clock+12⟩
    else
      let id := SemiprimeSourceHistogramTrie.lookup dict v.key
      let row := SemiprimeSourceHistogramRowKeys.readKeys cache.source.dictionary cache.coordinates id.bits
      let joined := appendKeys row.keys rest.keys
      let total := SemiprimeSourceCompactBits.increment rest.fixed
      ⟨joined.value,total.bits,rest.free,
        rest.clock+id.clock+row.clock+joined.work+total.clock+20⟩

/-- Mathematical exact fixed-vertex key list, with runtime answers only as semantics. -/
def keyList (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) : List (List Bool) :=
  vs.flatMap (fun v => if SemiprimeSourceHistogramFeatureBits.active k s v.code then [] else
    (SemiprimeSourceHistogramRowKeys.readKeys cache.source.dictionary cache.coordinates
      (SemiprimeSourceHistogramTrie.stored dict v.key)).keys)

/-- Literal actual key-stream identity, including original vertex-major order. -/
theorem produce_keys (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) : (produce cache dict k s vs).keys=keyList cache dict k s vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · simp [produce,keyList,ha,ih]
    · simp [produce,keyList,ha,appendKeys_value,SemiprimeSourceHistogramTrie.lookup_bits,ih]

/-- The acquired physical fixed counter is the actual original interval-filter count. -/
theorem produce_fixed (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) : bitValue (produce cache dict k s vs).fixed=
      (vs.filter (fun v => !(SemiprimeSourceHistogramFeatureBits.active k s v.code))).length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · simp [produce,ha,ih]
    · simp [produce,ha,SemiprimeSourceCompactBits.increment_value,ih]

/-- The acquired physical free counter is the actual original interval-filter count. -/
theorem produce_free (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) : bitValue (produce cache dict k s vs).free=
      (vs.filter (fun v => SemiprimeSourceHistogramFeatureBits.active k s v.code)).length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · simp [produce,ha,SemiprimeSourceCompactBits.increment_value,ih]
    · simp [produce,ha,ih]

/-- Both actual acquired counters are canonical compact physical words. -/
theorem produce_compact (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) :
    Compact (produce cache dict k s vs).fixed ∧ Compact (produce cache dict k s vs).free := by
  induction vs with
  | nil => exact ⟨trivial,trivial⟩
  | cons v vs ih =>
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · exact ⟨by simpa only [produce,ha,ite_true] using ih.1,
        by simpa only [produce,ha,ite_true] using
          SemiprimeSourceCompactBits.increment_compact (produce cache dict k s vs).free⟩
    · exact ⟨by simpa only [produce,ha,Bool.false_eq_true,ite_false] using
          SemiprimeSourceCompactBits.increment_compact (produce cache dict k s vs).fixed,
        by simpa only [produce,ha,Bool.false_eq_true,ite_false] using ih.2⟩

/-- Complete actual head-key acquisition and sparse collision-square output. -/
structure Result where
  /-- Actual physical fixed/free counters and vertex-major coordinate keys. -/
  head : HeadData
  /-- Executed sparse dictionary and collision-square accumulator. -/
  histogram : SemiprimeSourceHistogramSquares.State
  /-- Complete retained head pass plus actual sparse-histogram report. -/
  clock : ℕ

/-- Feed the actual acquired key list to the executed histogram, without n² pairs. -/
def acquire (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) : Result :=
  let head := produce cache dict k s vs
  let squares := SemiprimeSourceHistogramSquares.acquire head.keys
  ⟨head,squares,head.clock+squares.clock+3⟩

/-- Actual output equals the collision count of the exact original fixed-key stream. -/
theorem acquire_value (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) :
    bitValue (acquire cache dict k s vs).histogram.bits=
      SemiprimeSourceHistogramSquares.collisions (keyList cache dict k s vs) := by
  simp only [acquire,SemiprimeSourceHistogramSquares.acquire_value,produce_keys]

end RiemannGaussian.SemiprimeSourceHistogramHeadBits
