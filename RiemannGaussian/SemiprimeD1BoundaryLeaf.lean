/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecords
import RiemannGaussian.SemiprimeD1TensorTapeLeaf

/-! # Concrete boundary leaf from literal network data

The closed source acquires its own deterministic partition, enumerates only
class-incident and merge-union addresses, executes sorted request joins, and
returns the complete canonical jet. No global assignment-value table is an
output. A separately paid decidable layout/canonicality check permits the old
leaf as an honest fallback on malformed data. Numerical and finite-machine
clock certification remain separate from the executed native work reports.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryPlan (Work Graph Plan)
open SemiprimeD1BoundaryRecords (Entry Tensor)
open SemiprimeD1JetAxes (Context)
/-- Original literal tensor-network input. -/
abbrev Network := SemiprimeD1TensorNetwork.Network
/-- Original stored local tensor and its ordered occurrence ports. -/
abbrev Vertex := SemiprimeD1LeafCounter.Vertex
/-- Complete coefficient words paired with the executed native report. -/
abbrev JetRun := SemiprimeD1JetRingBits.Run

/-- Select incident and boundary edge ordinals by an actual endpoint scan. -/
def classPorts (g : Graph) (colours : List Nat) (c : Nat) : List Nat × List Nat :=
  let numbered:=g.edges.zipIdx
  let incident:=numbered.filter (fun (e,_) => colours.getD e.1 0==c || colours.getD e.2 0==c)
  let boundary:=numbered.filter (fun (e,_) =>
    (colours.getD e.1 0==c)!=(colours.getD e.2 0==c))
  (incident.map Prod.snd,boundary.map Prod.snd)

/-- Actual vertices of one colour, including zero-port vertices. -/
def classVertices (vertices : List Vertex) (colours : List Nat) (c : Nat) : List Vertex :=
  ((vertices.zipIdx).filter (fun (_,i) => colours.getD i 0==c)).map Prod.fst

/-- Pay one sequential local-table acquisition and request join per vertex. -/
def multiplyVertices (ctx : Context) (ports : List Nat) :
    List Vertex → List Entry → Work (List Entry)
  | [],acc => ⟨acc,1⟩
  | v::vs,acc =>
    let table:=SemiprimeD1BoundaryRecords.tableEntries v.table
    let attached:=SemiprimeD1BoundaryRecords.attach ctx ports v.ports acc table.value
    let tail:=multiplyVertices ctx ports vs attached.value
    ⟨tail.value,table.clock+attached.clock+tail.clock+v.ports.length+5⟩

/-- Build one full class boundary tensor by only its incident assignments. -/
def bucket (ctx : Context) (g : Graph) (vertices : List Vertex)
    (colours : List Nat) (c : Nat) : Work Tensor :=
  let ports:=classPorts g colours c
  let selected:=classVertices vertices colours c
  let seed:=SemiprimeD1BoundaryRecords.seed ctx ports.1.length
  let products:=multiplyVertices ctx ports.1 selected seed.value
  let out:=SemiprimeD1BoundaryRecords.contract ctx ports.1 ports.2 products.value
  ⟨⟨ports.2,out.value⟩,seed.clock+products.clock+out.clock+
    (g.vertices+g.edges.length+colours.length+1)^3+3⟩

/-- Sorted finite metadata union; its size is at most the global edge count. -/
def unionPorts (xs ys : List Nat) : List Nat :=
  ((xs++ys).mergeSort (·≤·)).eraseDups

/-- The new boundary is the symmetric difference, never the intersection. -/
def remainingPorts (xs ys : List Nat) : List Nat :=
  (unionPorts xs ys).filter (fun p => xs.contains p != ys.contains p)

/-- Merge full boundary tensors by sorted request joins and equal-key sums. -/
def merge (ctx : Context) (left right : Tensor) : Work Tensor :=
  let ports:=unionPorts left.ports right.ports
  let boundary:=remainingPorts left.ports right.ports
  let seed:=SemiprimeD1BoundaryRecords.seed ctx ports.length
  let first:=SemiprimeD1BoundaryRecords.attach ctx ports left.ports seed.value left.entries
  let second:=SemiprimeD1BoundaryRecords.attach ctx ports right.ports first.value right.entries
  let out:=SemiprimeD1BoundaryRecords.contract ctx ports boundary second.value
  ⟨⟨boundary,out.value⟩,seed.clock+first.clock+second.clock+out.clock+
    (left.ports.length+right.ports.length+1)^4+7⟩

/-- Consecutive colour merges; each intermediate retains all jet coordinates. -/
def mergeAll (ctx : Context) : Tensor → List Tensor → Work Tensor
  | tensor,[] => ⟨tensor,1⟩
  | tensor,next::rest =>
    let head:=merge ctx tensor next
    let tail:=mergeAll ctx head.value rest
    ⟨tail.value,head.clock+tail.clock+3⟩

/-- Actual stored input-byte inventory for acquisition/copy costs. -/
def inputMass (vertices : List Vertex) : Nat :=
  (vertices.map (fun v => SemiprimeD1TensorTables.storage v.table+
    (v.ports.map (fun p => Nat.size p+1)).sum+3)).sum

/-- Exact executed leaf result plus its retained acquired plan/tensor.
These diagnostics contain boundary tensors, never the `2^M` global value table. -/
structure Run where
  /-- Actual deterministic partition. -/
  plan : Plan
  /-- Actual final empty-boundary tensor. -/
  tensor : Tensor
  /-- Canonical contracted words and the whole own native report. -/
  result : JetRun

/-- Closed acquisition and contraction. Only current context/network data enter. -/
def acquire (ctx : Context) (net : Network) : Run :=
  let g:=SemiprimeD1BoundaryPlan.graph net
  let vertices:=SemiprimeD1TensorNetwork.vertices net
  let plan:=SemiprimeD1BoundaryPlan.acquire g
  let buckets:=(List.range plan.k).map (bucket ctx g vertices plan.colours)
  let head:=buckets.headD ⟨⟨[],[]⟩,1⟩
  let out:=mergeAll ctx head.value (buckets.tail.map Work.value)
  let words:=(out.value.entries.headD ⟨[],[]⟩).words
  let copied:=SemiprimeD1JetAxes.copyVector words
  ⟨plan,out.value,⟨copied.1,plan.clock+(buckets.map Work.clock).sum+out.clock+copied.2+
    10*inputMass vertices+(g.vertices+g.edges.length+1)^4+11⟩⟩

/-- Leaner leaf interface: no eager global assignment table is returned. -/
def run (ctx : Context) (net : Network) : JetRun := (acquire ctx net).result

/-- Executable compactness test; empty is the only compact zero. -/
def compactCheck : List Bool → Bool
  | [] => true
  | b::bs => compactCheck bs && (if bs=[] then b else true)

/-- The literal compactness test exactly checks the existing invariant. -/
theorem compactCheck_correct (bits : List Bool) :
    compactCheck bits=true ↔ SemiprimeSourceCompactBits.Compact bits := by
  induction bits with
  | nil => simp [compactCheck,SemiprimeSourceCompactBits.Compact]
  | cons b bs ih =>
    cases bs <;> simp_all [compactCheck,SemiprimeSourceCompactBits.Compact]

/-- Check every original coordinate, including shape, compactness and width. -/
def wordsCheck (ctx : Context) (words : List (List Bool)) : Bool :=
  words.length==ctx.rank && words.all (fun w => compactCheck w && decide (w.length≤ctx.precision))

/-- The executable word check is exactly canonicality, not Fits advice. -/
theorem wordsCheck_correct (ctx : Context) (words : List (List Bool)) :
    wordsCheck ctx words=true ↔ SemiprimeD1TensorTables.GoodWords ctx words := by
  simp only [wordsCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq,
    SemiprimeD1TensorTables.GoodWords,compactCheck_correct]

/-- Traverse all actual leaves once and validate full canonical coefficient data. -/
def tableCheck (ctx : Context) : {n : Nat} → SemiprimeD1TensorTables.Table n → Bool
  | _,.leaf words => wordsCheck ctx words
  | _,.fork low high => tableCheck ctx low && tableCheck ctx high

/-- Every stored local table is checked by its actual tree traversal. -/
theorem tableCheck_correct (ctx : Context) {n : Nat} (t : SemiprimeD1TensorTables.Table n) :
    tableCheck ctx t=true ↔ SemiprimeD1TensorTables.Good ctx t := by
  induction t with
  | leaf ws => exact wordsCheck_correct ctx ws
  | fork l r hl hr => simp only [tableCheck,Bool.and_eq_true,hl,hr,SemiprimeD1TensorTables.Good]

/-- Computable ordered-port validation against actual original incidence rows. -/
def layoutCheck (net : Network) : Bool :=
  (List.finRange net.leftCount).all (fun i =>
    (net.left[i.val]).ports==SemiprimeD1TensorNetwork.leftPorts net.rows i) &&
  (List.finRange net.rows.length).all (fun i =>
    (net.right[i.val]).ports==SemiprimeD1TensorNetwork.rightPorts net.rows i)

/-- Layout validation exactly recovers the original ordered-port predicate. -/
theorem layoutCheck_correct (net : Network) :
    layoutCheck net=true ↔ SemiprimeD1TensorNetwork.WellFormed net := by
  simp [layoutCheck,SemiprimeD1TensorNetwork.WellFormed]

/-- Validity checker takes no graph/entry/proof answer as a runtime operand. -/
def validate (ctx : Context) (net : Network) : Work Bool :=
  let vertices:=SemiprimeD1TensorNetwork.vertices net
  let value:=layoutCheck net && vertices.all (fun v => tableCheck ctx v.table)
  let metadata:=vertices.length+SemiprimeD1TensorNetwork.edgeCount net+
    (vertices.map (fun v => v.ports.length)).sum+ctx.axes.sum+ctx.precision+2
  ⟨value,(metadata+1)^6+20*(inputMass vertices+1)*(metadata+1)^2⟩

/-- The closed computable guard accepts exactly the original layout/canonicality.
No width-performance success test is part of this predicate. -/
theorem validate_correct (ctx : Context) (net : Network) :
    (validate ctx net).value=true ↔
      SemiprimeD1TensorNetwork.WellFormed net ∧ SemiprimeD1TensorNetwork.Good ctx net := by
  simp only [validate,Bool.and_eq_true,layoutCheck_correct,List.all_eq_true,
    tableCheck_correct,SemiprimeD1TensorNetwork.Good,SemiprimeD1LeafCounter.Good]

/-- Checked total leaf: malformed inputs run the existing paid tape leaf.
Width success is not tested or assumed; valid original inputs use the new path. -/
def checked (ctx : Context) (net : Network) : JetRun :=
  let valid:=validate ctx net
  if valid.value then
    let out:=run ctx net
    ⟨out.words,valid.clock+out.clock+3⟩
  else
    let out:=SemiprimeD1TensorTapeLeaf.leaf ctx net
    ⟨out.words,valid.clock+out.clock+3⟩

end RiemannGaussian.SemiprimeD1BoundaryLeaf
