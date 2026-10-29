/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1LeafCounter
import RiemannGaussian.SemiprimeFiniteEnumerations

/-! # Concrete bipartite tensor-network data
Factor-major owner rows and two vectors of literal local tensor tables are
stored data. Typed incidence maps are reads from those rows. Canonical global
edge numbers are computed by finite searches in the actual incidence list;
they do not identify parallel edges. Native metadata/control lowering is a
separate obligation from the physical coefficient-word reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1TensorNetwork
open scoped BigOperators
open SemiprimeD1JetAxes

/-- Literal factor-major owner rows, retaining every repeated occurrence. -/
abbrev Rows (n : ℕ) := List (List (Fin n))

/-- Read one actual cached factor degree. -/
def arity {n : ℕ} (rows : Rows n) (e : Fin rows.length) : ℕ := rows[e.val].length

/-- The original dependent incidence type, now determined by literal rows. -/
abbrev Incidence {n : ℕ} (rows : Rows n) := (e : Fin rows.length) × Fin (arity rows e)

/-- The incidence owner is a literal cached finite-index read. -/
def owner {n : ℕ} (rows : Rows n) (i : Incidence rows) : Fin n := rows[i.1.val][i.2.val]

/-- Actual finite occurrence list; distinct parallel ports remain distinct. -/
def incidences {n : ℕ} (rows : Rows n) : List (Incidence rows) :=
  (SemiprimeFiniteEnumerations.indexedIncidences rows.length (arity rows)).values

/-- Actual number of variables in the incidence representation. -/
def scope {n : ℕ} (rows : Rows n) : ℕ := (incidences rows).length

/-- Literal computed factor-major global edge identifier. -/
def edgeID {n : ℕ} (rows : Rows n) (i : Incidence rows) : ℕ := (incidences rows).idxOf i

/-- Every typed occurrence is present in the actual enumeration. -/
theorem incidence_mem {n : ℕ} (rows : Rows n) (i : Incidence rows) : i ∈ incidences rows :=
  (SemiprimeFiniteEnumerations.indexedIncidences rows.length (arity rows)).complete i

/-- The actual incidence stream has no repeated occurrence. -/
theorem incidences_nodup {n : ℕ} (rows : Rows n) : (incidences rows).Nodup :=
  (SemiprimeFiniteEnumerations.indexedIncidences rows.length (arity rows)).nodup

/-- The actual variable scope is exactly the sum of the original cached arities. -/
theorem scope_eq_sum {n : ℕ} (rows : Rows n) : scope rows = ∑ e, arity rows e :=
  SemiprimeFiniteEnumerations.indexedIncidences_length rows.length (arity rows)

/-- Computed occurrence identifiers are in range, without an identifier oracle. -/
theorem edgeID_lt {n : ℕ} (rows : Rows n) (i : Incidence rows) : edgeID rows i < scope rows :=
  List.idxOf_lt_length_of_mem (incidence_mem rows i)

/-- Distinct actual occurrences never acquire the same global identifier. -/
theorem edgeID_injective {n : ℕ} (rows : Rows n) : Function.Injective (edgeID rows) := by
  intro i j hij
  have hi := List.getElem?_idxOf (incidence_mem rows i)
  have hj := List.getElem?_idxOf (incidence_mem rows j)
  change (incidences rows)[edgeID rows i]? = some i at hi
  change (incidences rows)[edgeID rows j]? = some j at hj
  rw [hij, hj] at hi
  exact Option.some.inj hi.symm

/-- The actual port order of a left vertex, as global occurrence identifiers. -/
def leftPorts {n : ℕ} (rows : Rows n) (v : Fin n) : List ℕ :=
  ((incidences rows).filter (fun i => decide (owner rows i = v))).map (edgeID rows)

/-- The actual port order of a right factor, as global occurrence identifiers. -/
def rightPorts {n : ℕ} (rows : Rows n) (e : Fin rows.length) : List ℕ :=
  ((incidences rows).filter (fun i => decide (i.1 = e))).map (edgeID rows)

/-- Every actual left port is a valid global variable. -/
theorem leftPorts_lt {n : ℕ} (rows : Rows n) (v : Fin n) (p : ℕ) (hp : p ∈ leftPorts rows v) :
    p < scope rows := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact edgeID_lt rows i

/-- Every actual right port is a valid global variable. -/
theorem rightPorts_lt {n : ℕ} (rows : Rows n) (e : Fin rows.length)
    (p : ℕ) (hp : p ∈ rightPorts rows e) : p < scope rows := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact edgeID_lt rows i

/-- No local left table repeats a global variable, including parallel ports. -/
theorem leftPorts_nodup {n : ℕ} (rows : Rows n) (v : Fin n) : (leftPorts rows v).Nodup :=
  ((incidences_nodup rows).filter _).map (edgeID_injective rows)

/-- No local right table repeats a global variable. -/
theorem rightPorts_nodup {n : ℕ} (rows : Rows n) (e : Fin rows.length) :
    (rightPorts rows e).Nodup :=
  ((incidences_nodup rows).filter _).map (edgeID_injective rows)

/-- An occurrence belongs to exactly its actual cached owner on the left. -/
theorem edgeID_mem_leftPorts {n : ℕ} (rows : Rows n) (v : Fin n) (i : Incidence rows) :
    edgeID rows i ∈ leftPorts rows v ↔ owner rows i = v := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hji := edgeID_injective rows he
    subst j
    exact of_decide_eq_true (List.mem_filter.mp hj).2
  · intro h
    exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨incidence_mem rows i, by simp only [h, decide_true]⟩, rfl⟩

/-- An occurrence belongs to exactly its actual cached factor on the right. -/
theorem edgeID_mem_rightPorts {n : ℕ} (rows : Rows n) (e : Fin rows.length) (i : Incidence rows) :
    edgeID rows i ∈ rightPorts rows e ↔ i.1 = e := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hji := edgeID_injective rows he
    subst j
    exact of_decide_eq_true (List.mem_filter.mp hj).2
  · intro h
    exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨incidence_mem rows i, by simp only [h, decide_true]⟩, rfl⟩

/-- Two different left vertices have disjoint actual variable scopes. -/
theorem leftPorts_disjoint {n : ℕ} (rows : Rows n) (v w : Fin n) (hne : v ≠ w) :
    List.Disjoint (leftPorts rows v) (leftPorts rows w) := by
  apply List.disjoint_left.mpr
  intro p hp hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hv : owner rows i = v := of_decide_eq_true (List.mem_filter.mp hi).2
  have hw' := (edgeID_mem_leftPorts rows w i).mp hw
  exact hne (hv.symm.trans hw')

/-- Two different right factors have disjoint actual variable scopes. -/
theorem rightPorts_disjoint {n : ℕ} (rows : Rows n) (e f : Fin rows.length) (hne : e ≠ f) :
    List.Disjoint (rightPorts rows e) (rightPorts rows f) := by
  apply List.disjoint_left.mpr
  intro p hp hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have he : i.1 = e := of_decide_eq_true (List.mem_filter.mp hi).2
  have hf' := (edgeID_mem_rightPorts rows f i).mp hf
  exact hne (he.symm.trans hf')

/-- Entire current network is finite literal data, with no entry evaluators. -/
structure Network where
  /-- Actual old owner-vertex count, including isolated vertices. -/
  leftCount : ℕ
  /-- Actual factor-major original owner rows. -/
  rows : Rows leftCount
  /-- Cached entire left tensor tables and their literal ordered port lists. -/
  left : Vector SemiprimeD1LeafCounter.Vertex leftCount
  /-- Cached entire right tensor tables and their literal ordered port lists. -/
  right : Vector SemiprimeD1LeafCounter.Vertex rows.length

/-- Intrinsic data-layout check; it supplies neither truth entries nor contractions. -/
def WellFormed (net : Network) : Prop :=
  (∀ v : Fin net.leftCount, (net.left[v.val]).ports = leftPorts net.rows v) ∧
  (∀ e : Fin net.rows.length, (net.right[e.val]).ports = rightPorts net.rows e)

/-- Both literal vertex caches, including every zero-port tensor exactly once. -/
def vertices (net : Network) : List SemiprimeD1LeafCounter.Vertex := net.left.toList ++ net.right.toList

/-- Canonical table data in the actual current coefficient context. -/
def Good (ctx : Context) (net : Network) : Prop := SemiprimeD1LeafCounter.Good ctx (vertices net)

/-- A literal network's actual global table dimension. -/
def edgeCount (net : Network) : ℕ := scope net.rows

/-- The actual eager leaf call consumes only the concrete cached network data. -/
def leaf (ctx : Context) (net : Network) : SemiprimeD1LeafCounter.LeafRun (edgeCount net) :=
  SemiprimeD1LeafCounter.run (edgeCount net) ctx (vertices net)

/-- Every stored vertex has a legal local scope once the concrete layout passes. -/
theorem wellFormed_vertices (net : Network) (hw : WellFormed net) :
    SemiprimeD1LeafCounter.WellFormed (edgeCount net) (vertices net) := by
  intro v hv p hp
  rcases List.mem_append.mp hv with hl | hr
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hl
    rw [Vector.getElem_toList] at he
    subst v
    rw [hw.1 ⟨i, by simpa only [Vector.length_toList] using hi⟩] at hp
    exact leftPorts_lt net.rows _ p hp
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    rw [Vector.getElem_toList] at he
    subst v
    rw [hw.2 ⟨i, by simpa only [Vector.length_toList] using hi⟩] at hp
    exact rightPorts_lt net.rows _ p hp

/-- Executed leaf semantics is the complete contraction of all literal current entries. -/
theorem leaf_value (ctx : Context) (hp : ∀ q ∈ ctx.axes, 0 < q) (net : Network) :
    SemiprimeD1JetInterpretation.interpret ctx (leaf ctx net).words =
      ∑ bits : Fin (edgeCount net) → Bool,
        ((vertices net).map (fun v => SemiprimeD1JetInterpretation.interpret ctx
          (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment bits v)))).prod :=
  SemiprimeD1LeafCounter.run_value (edgeCount net) ctx hp (vertices net)

end RiemannGaussian.SemiprimeD1TensorNetwork
