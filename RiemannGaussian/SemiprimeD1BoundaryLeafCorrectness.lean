import RiemannGaussian.SemiprimeD1BoundaryRecordsLookup
import RiemannGaussian.SemiprimeD1BoundaryRecordsReduction
import RiemannGaussian.SemiprimeD1BoundaryLeaf

/-! Exact full-jet semantics of the concrete boundary contraction loops. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafCorrectness
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsLookup
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecordsSort
open SemiprimeD1BoundaryLeaf
open SemiprimeD1JetAxes (Context)
open SemiprimeD1JetInterpretation (interpret Carrier)

theorem rekey_value (source target : List Nat) (es : List Entry) :
    (rekey source target es).value = es.map (fun e =>
      (⟨(project e.key source target).value,e.words⟩ : Entry)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [rekey, List.map_cons, ih]

/-- Executed projection, sort and grouping preserve the sum at each new address. -/
theorem contract_weighted (ctx : Context) (hp : ctx.Positive)
    (source target : List Nat) (es : List Entry) (key : List Bool) :
    weighted ctx (contract ctx source target es).value key =
      (es.map (fun e => if (project e.key source target).value = key then
        interpret ctx e.words else 0)).sum := by
  change weighted ctx (group ctx (sort (rekey source target es).value).value).value key = _
  rw [group_weighted ctx hp, weighted_perm ctx (sort_perm _), rekey_value]
  simp only [weighted, List.map_map, Function.comp_def]

/-- Multiplication of one actual stored vertex preserves each original address. -/
theorem attach_vertex_weighted (ctx : Context) (hp : ctx.Positive)
    (source : List Nat) (v : Vertex) (es : List Entry) (key : List Bool) :
    weighted ctx (attach ctx source v.ports es (tableEntries v.table).value).value key =
      (es.map (fun e => if e.key = key then interpret ctx e.words *
        interpret ctx (SemiprimeD1TensorTables.lookup v.table
          (project e.key source v.ports).value).words else 0)).sum := by
  rw [weighted_perm ctx (attach_vertex_perm ctx source v es)]
  simp only [weighted, List.map_map, Function.comp_def,
    SemiprimeD1JetOperations.interpret_mul ctx _ _ hp]

/-- Each cursor join multiplies precisely the value at its projected address. -/
theorem attach_vertex_weighted_factor (ctx : Context) (hp : ctx.Positive)
    (source : List Nat) (v : Vertex) (es : List Entry) (key : List Bool) :
    weighted ctx (attach ctx source v.ports es (tableEntries v.table).value).value key =
      weighted ctx es key * interpret ctx (SemiprimeD1TensorTables.lookup v.table
        (project key source v.ports).value).words := by
  rw [attach_vertex_weighted ctx hp]
  induction es with
  | nil => simp [weighted]
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, weighted] at ih ⊢
    rw [add_mul, ← ih]
    by_cases h : e.key = key <;> simp [h]

/-- The actual repeated vertex cursor loop computes the full product of all
stored local jets, including vertices with no ports. -/
theorem multiplyVertices_weighted (ctx : Context) (hp : ctx.Positive)
    (source : List Nat) (vs : List Vertex) (es : List Entry) (key : List Bool) :
    weighted ctx (multiplyVertices ctx source vs es).value key =
      weighted ctx es key * (vs.map (fun v => interpret ctx
        (SemiprimeD1TensorTables.lookup v.table
          (project key source v.ports).value).words)).prod := by
  induction vs generalizing es with
  | nil => simp [multiplyVertices]
  | cons v vs ih =>
    change weighted ctx (multiplyVertices ctx source vs
      (attach ctx source v.ports es (tableEntries v.table).value).value).value key = _
    rw [ih, attach_vertex_weighted_factor ctx hp]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- Proof-side serialization of one record's executed local multiplications. -/
def vertexProducts (ctx : Context) (source : List Nat) : List Vertex → Entry → Entry
  | [],e => e
  | v::vs,e => vertexProducts ctx source vs
      ⟨e.key,(SemiprimeD1JetRingBits.mul ctx e.words
        (SemiprimeD1TensorTables.lookup v.table
          (project e.key source v.ports).value).words).words⟩

/-- All actual cursor reorderings are accounted for by literal record permutation. -/
theorem multiplyVertices_perm (ctx : Context) (source : List Nat)
    (vs : List Vertex) (es : List Entry) :
    (multiplyVertices ctx source vs es).value.Perm
      (es.map (vertexProducts ctx source vs)) := by
  induction vs generalizing es with
  | nil => simp [multiplyVertices, vertexProducts]
  | cons v vs ih =>
    exact (ih _).trans (by
      simpa only [List.map_map, Function.comp_def, vertexProducts] using
        (attach_vertex_perm ctx source v es).map (vertexProducts ctx source vs))

theorem vertexProducts_key (ctx : Context) (source : List Nat)
    (vs : List Vertex) (e : Entry) : (vertexProducts ctx source vs e).key = e.key := by
  induction vs generalizing e with
  | nil => rfl
  | cons v vs ih => exact ih _

theorem vertexProducts_interpret (ctx : Context) (hp : ctx.Positive) (source : List Nat)
    (vs : List Vertex) (e : Entry) :
    interpret ctx (vertexProducts ctx source vs e).words =
      interpret ctx e.words * (vs.map (fun v => interpret ctx
        (SemiprimeD1TensorTables.lookup v.table
          (project e.key source v.ports).value).words)).prod := by
  induction vs generalizing e with
  | nil => simp [vertexProducts]
  | cons v vs ih =>
    rw [vertexProducts, ih, SemiprimeD1JetOperations.interpret_mul ctx _ _ hp]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- A concrete class bucket is exactly the projected sum of its incident
assignment records with the product of all acquired local full jets. -/
theorem bucket_weighted (ctx : Context) (hp : ctx.Positive)
    (g : SemiprimeD1BoundaryPlan.Graph) (vertices : List Vertex)
    (colours : List Nat) (c : Nat) (key : List Bool) :
    weighted ctx (bucket ctx g vertices colours c).value.entries key =
      ((seed ctx (classPorts g colours c).1.length).value.map (fun e =>
        if (project e.key (classPorts g colours c).1 (classPorts g colours c).2).value = key
        then interpret ctx e.words * ((classVertices vertices colours c).map (fun v =>
          interpret ctx (SemiprimeD1TensorTables.lookup v.table
            (project e.key (classPorts g colours c).1 v.ports).value).words)).prod
        else 0)).sum := by
  unfold bucket
  rw [contract_weighted ctx hp]
  have h := (multiplyVertices_perm ctx (classPorts g colours c).1
    (classVertices vertices colours c) (seed ctx (classPorts g colours c).1.length).value).map
      (fun e => if (project e.key (classPorts g colours c).1
        (classPorts g colours c).2).value = key then interpret ctx e.words else 0)
  rw [h.sum_eq]
  simp only [List.map_map, Function.comp_def, vertexProducts_key,
    vertexProducts_interpret ctx hp]

/-- The actual two cursor joins of a merge multiply the two stored tensor
entries selected by the union address, before summing to the symmetric boundary. -/
theorem merge_weighted (ctx : Context) (hp : ctx.Positive) (left right : Tensor)
    (hl : left.entries.Pairwise SemiprimeD1BoundaryRecordsOrder.EntryLE)
    (hr : right.entries.Pairwise SemiprimeD1BoundaryRecordsOrder.EntryLE) (key : List Bool) :
    weighted ctx (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries key =
      ((seed ctx (unionPorts left.ports right.ports).length).value.map (fun e =>
        if (project e.key (unionPorts left.ports right.ports)
          (remainingPorts left.ports right.ports)).value = key then
          interpret ctx e.words *
            interpret ctx (lookupWords left.entries
              (project e.key (unionPorts left.ports right.ports) left.ports).value) *
            interpret ctx (lookupWords right.entries
              (project e.key (unionPorts left.ports right.ports) right.ports).value)
        else 0)).sum := by
  let source := unionPorts left.ports right.ports
  let first := (attach ctx source left.ports (seed ctx source.length).value left.entries).value
  let second := (attach ctx source right.ports first right.entries).value
  change weighted ctx (contract ctx source (remainingPorts left.ports right.ports) second).value key = _
  rw [contract_weighted ctx hp]
  have hsecond := attach_perm ctx source right.ports first right.entries hr
  have hfirst := attach_perm ctx source left.ports (seed ctx source.length).value left.entries hl
  let f := fun e : Entry => if
    (project e.key source (remainingPorts left.ports right.ports)).value = key
    then interpret ctx e.words else 0
  change (second.map f).sum = _
  rw [(hsecond.map f).sum_eq]
  simp only [List.map_map, Function.comp_def]
  rw [(hfirst.map (fun e => f
    ⟨e.key,(SemiprimeD1JetRingBits.mul ctx e.words
      (lookupWords right.entries (project e.key source right.ports).value)).words⟩)).sum_eq]
  simp only [List.map_map, Function.comp_def, f,
    SemiprimeD1JetOperations.interpret_mul ctx _ _ hp]
  rfl

end RiemannGaussian.SemiprimeD1BoundaryLeafCorrectness
