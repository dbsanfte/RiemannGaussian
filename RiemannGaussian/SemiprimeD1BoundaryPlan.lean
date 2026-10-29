/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetwork

/-! # Executable deterministic boundary partition

Only the literal incidence rows are read. Conditional potentials enumerate at
most four endpoint colours, never all vertex colourings. Integer scaling avoids
rational arithmetic and rounding. This is a native executable/list-work report;
its subsequent correctness and bounds do not identify it with a stack machine.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryPlan

/-- Acquired endpoint pairs; parallel occurrences keep distinct list positions. -/
structure Graph where
  /-- Number of actual vertices, including isolated vertices. -/
  vertices : Nat
  /-- Original occurrence order, with distinct left/right endpoint families. -/
  edges : List (Nat × Nat)
  deriving Repr

/-- Literal endpoint acquisition from the existing factor-major incidence list. -/
def graph (net : SemiprimeD1TensorNetwork.Network) : Graph :=
  ⟨(SemiprimeD1TensorNetwork.vertices net).length,
    (SemiprimeD1TensorNetwork.incidences net.rows).map (fun i =>
      ((SemiprimeD1TensorNetwork.owner net.rows i).val,net.leftCount+i.1.val))⟩

/-- Endpoint acquisition does not change the global assignment dimension. -/
theorem graph_edges_length (net : SemiprimeD1TensorNetwork.Network) :
    (graph net).edges.length=SemiprimeD1TensorNetwork.edgeCount net := by
  simp only [graph,List.length_map,SemiprimeD1TensorNetwork.edgeCount,
    SemiprimeD1TensorNetwork.scope]

/-- One concrete list operation and its retained bit-work allowance. -/
structure Work (α : Type) where
  /-- Actual constructed result. -/
  value : α
  /-- All explicit loop/read/arithmetic allowances. -/
  clock : Nat
  deriving Repr

/-- Loads used by the bucket and consecutive-fixed merge algorithms. -/
inductive Load where
  /-- Edges touching one colour class. -/
  | bucket (colour : Nat)
  /-- Edges crossing the old/new/future three-way partition. -/
  | merge (step : Nat)
  deriving Repr, DecidableEq

/-- Complete ordered list of the `2*K-1` loads when `K>=2`. -/
def loads (k : Nat) : List Load :=
  (List.range k).map Load.bucket ++ (List.range (k-1)).map (fun j => .merge (j+2))

/-- Region of one colour at an actual consecutive merge. -/
def region (j c : Nat) : Nat := if c<j-1 then 0 else if c=j-1 then 1 else 2

/-- Literal membership indicator, retaining the complete merge union boundary. -/
def indicator : Load → Nat → Nat → Bool
  | .bucket c,a,b => a==c || b==c
  | .merge j,a,b => !(region j a==region j b)

/-- Unconditional load mean numerator, with common denominator `K^2`. -/
def meanNumerator (m k : Nat) : Load → Nat
  | .bucket _ => m*(2*k-1)
  | .merge j => 2*m*(j*(k+1-j)-1)

/-- Enumerate only a specified number of local colours, in ascending order. -/
def colourWords (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range k).flatMap (fun c => (colourWords k n).map (c::·))

/-- Concrete endpoint list for one or two indicator factors. -/
def endpoints (es : List (Nat × Nat)) : List Nat :=
  (es.flatMap (fun e => [e.1,e.2])).eraseDups

/-- Read the actual fixed fixed or the actual local colour assignment. -/
def readColour (fixed unknown sample : List Nat) (v : Nat) : Nat :=
  if v<fixed.length then fixed.getD v 0 else sample.getD (unknown.idxOf v) 0

/-- Scaled conditional expectation of one/two local indicator factors.
The only generated assignments have at most four coordinates. -/
def localExpectation (scale k : Nat) (fixed : List Nat) (load : Load)
    (es : List (Nat × Nat)) : Work Nat :=
  let vs:=endpoints es
  let unknown:=vs.filter (fun v => !(v<fixed.length))
  let samples:=colourWords k unknown.length
  let successes:=(samples.filter (fun sample => es.all (fun e =>
    indicator load (readColour fixed unknown sample e.1)
      (readColour fixed unknown sample e.2)))).length
  let answer:=successes*k^(scale-unknown.length)
  let size:=fixed.length+vs.length+es.length+k+scale+2
  ⟨answer,(samples.length+1)*(size+1)^4⟩

/-- Exact integer `K^4`-scaled conditional quadratic potential.
Ordered edge pairs include diagonal terms, so no covariance term is omitted. -/
def potential (g : Graph) (k : Nat) (fixed : List Nat) : Work Int :=
  let reports:=(loads k).map (fun load =>
    let single:=g.edges.map (fun e => localExpectation 2 k fixed load [e])
    let pairs:=g.edges.flatMap (fun e => g.edges.map (fun f =>
      localExpectation 4 k fixed load [e,f]))
    let mu:=meanNumerator g.edges.length k load
    let x:=(pairs.map (fun r => r.value)).sum
    let y:=(single.map (fun r => r.value)).sum
    ((x:Int)-2*(mu:Int)*(y:Int)+(mu:Int)^2,
      (pairs.map (fun r => r.clock)).sum+(single.map (fun r => r.clock)).sum+
        (g.edges.length+k+fixed.length+2)^4))
  ⟨(reports.map Prod.fst).sum,(reports.map Prod.snd).sum+reports.length+1⟩

/-- Count actual incidences of a vertex; a parallel edge is counted separately. -/
def degree (g : Graph) (v : Nat) : Nat :=
  (g.edges.filter (fun e => e.1==v || e.2==v)).length

/-- Maximum actual degree; no supplied degree bound occurs in the runtime data. -/
def maxDegree (g : Graph) : Nat :=
  ((List.range g.vertices).map (degree g)).foldl max 0

/-- Integer cube comparison chooses the first sufficient colour count.
The bounded search includes `M+2`, so it terminates without real cube roots. -/
def chooseK (g : Graph) : Nat :=
  let d:=maxDegree g
  ((List.range (g.edges.length+1)).map (·+2)).find?
    (fun k => g.edges.length≤k^3*d) |>.getD 2

/-- Candidate tie policy: ascending order and strict improvement only. -/
def leastCandidate (g : Graph) (k : Nat) (fixed : List Nat) : Work Nat :=
  let candidates:=(List.range k).map (fun c =>
    let p:=potential g k (fixed++[c]); (c,p.value,p.clock))
  let best:=candidates.foldl (fun best next =>
    if next.2.1<best.2.1 then next else best) (candidates.headD (0,0,0))
  ⟨best.1,(candidates.map (fun p => p.2.2)).sum+
    (candidates.length+1)*(fixed.length+g.edges.length+k+2)^3⟩

/-- Assign every vertex, using only the local conditional potential above. -/
def extend (g : Graph) (k : Nat) : Nat → List Nat → Work (List Nat)
  | 0,fixed => ⟨fixed,fixed.length+1⟩
  | n+1,fixed =>
    let head:=leastCandidate g k fixed
    let tail:=extend g k n (fixed++[head.value])
    ⟨tail.value,head.clock+tail.clock+fixed.length+3⟩

/-- Acquired colours and exact executed load measurements. -/
structure Plan where
  /-- Integer-acquired colour count. -/
  k : Nat
  /-- One actual colour per vertex, in original vertex order. -/
  colours : List Nat
  /-- Measured load list, in the same order as `loads`. -/
  measured : List Nat
  /-- Complete acquisition/partition/list arithmetic report. -/
  clock : Nat
  deriving Repr

/-- Executed load count on the actual acquired partition. -/
def loadValue (g : Graph) (colours : List Nat) (l : Load) : Nat :=
  (g.edges.filter (fun e => indicator l (colours.getD e.1 0)
    (colours.getD e.2 0))).length

/-- Closed partition acquisition, with no colouring or width advice. -/
def acquire (g : Graph) : Plan :=
  let k:=chooseK g
  let out:=extend g k g.vertices []
  let measured:=(loads k).map (loadValue g out.value)
  ⟨k,out.value,measured,out.clock+(g.vertices+g.edges.length+k+2)^6⟩

/-- Exact greatest measured assignment dimension. -/
def Plan.width (p : Plan) : Nat := p.measured.foldl max 0

end RiemannGaussian.SemiprimeD1BoundaryPlan
