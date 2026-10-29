/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketReplayBudget
import RiemannGaussian.SemiprimeD1GroupBalance

/-! # Executed physical group-child graph from the actual sparse packet inventory
Colour tests read physical acquired rows. Packet grouping compares literal byte
strings, not numeric aliases. Native original finite indices remain explicit
metadata; no semantic finite-word getter enters the executed builder.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1ChildGraph
open SemiprimeMaterializedWords SemiprimeBitArithmetic
open SemiprimeD1PacketInventory

/-- Literal byte equality, preserving empty/padded distinctions in packet keys. -/
def equalBytes : List Bool→List Bool→Run Bool
  | [],[] => ⟨true,2⟩
  | x::xs,y::ys =>
    if x==y then
      let tail := equalBytes xs ys
      ⟨tail.value,tail.work+6⟩
    else ⟨false,4⟩
  | _,_ => ⟨false,2⟩

/-- Exact equality of the actual copied/framed bytes. -/
theorem equalBytes_correct (xs ys : List Bool) : (equalBytes xs ys).value=true ↔ xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalBytes]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equalBytes]
    | cons y ys =>
      by_cases h : x=y
      · subst y
        simpa only [equalBytes,beq_self_eq_true,ite_true,List.cons.injEq,true_and] using ih ys
      · simp [equalBytes,h]

/-- Physically copy one coordinate after paying each preceding list-cell visit. -/
def readCoordinate : List (List Bool)→ℕ→SemiprimeSourceCompactBits.Report
  | [],_ => ⟨[],2⟩
  | x::_,0 =>
    let out := SemiprimeSourceCompactBits.copy x
    ⟨out.bits,out.clock+3⟩
  | _::xs,q+1 =>
    let out := readCoordinate xs q
    ⟨out.bits,out.clock+4⟩

/-- No colour answer is supplied to the coordinate scan. -/
theorem readCoordinate_bits (row : List (List Bool)) (q : ℕ) :
    (readCoordinate row q).bits=(row[q]?).getD [] := by
  induction row generalizing q with
  | nil => rfl
  | cons x xs ih =>
    cases q with
    | zero => exact SemiprimeSourceCompactBits.copy_bits x
    | succ q => exact ih q

/-- Physical unsigned colour equality, including both acquired borrow flags. -/
def testColour (target : List Bool) (q : ℕ) (row : List (List Bool)) : Run Bool :=
  let coordinate := readCoordinate row q
  let order := SemiprimeBitIndexClipping.leSignedBits ⟨false,coordinate.bits⟩ ⟨false,target⟩
  ⟨SemiprimeD1OrientationBits.equality order,coordinate.clock+order.clock+4⟩

/-- Exact value of the actually executed physical equality test. -/
theorem testColour_correct (target : List Bool) (q : ℕ) (row : List (List Bool)) :
    (testColour target q row).value=true ↔
      bitValue ((row[q]?).getD [])=bitValue target := by
  rw [←readCoordinate_bits]
  exact SemiprimeD1OrientationBits.equality_exact _ _

/-- One actual retained original endpoint in a packet slot. -/
structure Endpoint (vertices : ℕ) where
  /-- Original old vertex, now on the common child owner side. -/
  vertex : Fin vertices
  /-- Actual acquired packet key. -/
  packet : List Bool
  /-- Actual orientation slot bits. -/
  slot : List Bool
  /-- Positive original real-port occurrence ID. -/
  edge : List Bool
  /-- True for original owner endpoint, false for original factor endpoint. -/
  side : Bool

/-- Both possible old endpoints of one actual placement. -/
def endpoints {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) (out : Placement) : Endpoint (n+F)×Endpoint (n+F) :=
  (⟨⟨(owner i).val,by omega⟩,out.packet,out.slot,out.edge,true⟩,
   ⟨⟨n+i.1.val,by omega⟩,out.packet,out.slot,out.edge,false⟩)

/-- Read both selected original rows once; retain either, both or neither endpoint. -/
def one {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (arity e)) (out : Placement) : Run (List (Endpoint (n+F))) :=
  let rows := SemiprimeD1PacketRows.read dict a out.source
  let rowTest := testColour target q rows.left
  let factorTest := testColour target q rows.right
  let pair := endpoints owner i out
  let row := if rowTest.value then [pair.1] else []
  let column := if factorTest.value then [pair.2] else []
  ⟨row++column,rows.clock+rowTest.work+factorTest.work+20⟩

/-- Actual original-port/placement pair traversal, preserving each multiplicity. -/
def scan {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool) :
    List (((e : Fin F)×Fin (arity e))×Placement)→Run (List (Endpoint (n+F)))
  | [] => ⟨[],2⟩
  | (i,out)::rest =>
    let here := one owner dict a q target i out
    let tail := scan owner dict a q target rest
    ⟨here.value++tail.value,here.work+tail.work+here.value.length+6⟩

/-- Physical packet equality/filter traversal; no unit-cost hash dictionary. -/
def bucket {vertices : ℕ} (packet : List Bool) :
    List (Endpoint vertices)→Run (List (Endpoint vertices))
  | [] => ⟨[],2⟩
  | e::es =>
    let tested := equalBytes e.packet packet
    let tail := bucket packet es
    ⟨if tested.value then e::tail.value else tail.value,tested.work+tail.work+5⟩

/-- Acquire each observed factor's endpoint bucket exactly once. -/
def buckets {vertices : ℕ} (es : List (Endpoint vertices)) :
    List (List Bool)→Run (List (List (Endpoint vertices)))
  | [] => ⟨[],2⟩
  | packet::packets =>
    let here := bucket packet es
    let tail := buckets es packets
    ⟨here.value::tail.value,here.work+tail.work+4⟩

/-- Cached concrete child graph, in the original n/F/arity/owner representation. -/
structure Graph (vertices : ℕ) where
  /-- Actual observed packet keys. -/
  packetKeys : List (List Bool)
  /-- Actual selected old endpoints before packet grouping. -/
  endpoints : List (Endpoint vertices)
  /-- Once-cached packet-factor incidence buckets. -/
  factors : List (List (Endpoint vertices))
  /-- All retained parent, physical colour/read and grouping reports. -/
  work : ℕ

/-- Concrete child factor arities; empty observed factors have arity zero. -/
def arity {vertices : ℕ} (graph : Graph vertices) (e : Fin graph.factors.length) : ℕ :=
  graph.factors[e.val].length

/-- Concrete child incidence map, reading only the actual cached endpoint buckets. -/
def owner {vertices : ℕ} (graph : Graph vertices)
    (i : (e : Fin graph.factors.length)×Fin (arity graph e)) : Fin vertices :=
  (graph.factors[i.1.val][i.2.val]).vertex

/-- Reuse the actual sparse replay once across coordinate/colour children. -/
def fromReplay {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity)
    (q : Fin a) (g : Fin r) : Graph (n+F) :=
  let target := SemiprimeSourceHistogramPortKeys.encodeKey g.val
  let ports := source.padding.source.selection.cache.data.metadata.incidences
  let paired := ports.zip source.placements
  let emitted := scan inputOwner source.padding.source.selection.cache.rows.source.dictionary
    a q.val target.bits paired
  let grouped := buckets emitted.value source.state.packets
  ⟨source.state.packets,emitted.value,grouped.value,
    source.state.clock+target.clock+emitted.work+grouped.work+ports.length+source.placements.length+12⟩

/-- Original-input child graph endpoint, without supplied labels or row answers. -/
def acquire (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) : Graph (n+F) :=
  fromReplay inputOwner (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) q g

/-- Literal byte comparison pays every visited pair of key bits. -/
theorem equalBytes_work (xs ys : List Bool) : (equalBytes xs ys).work≤6*xs.length+4 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalBytes]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equalBytes]
    | cons y ys =>
      have hh := ih ys
      simp only [equalBytes]
      split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

/-- Original coordinate payload bounds pay copies and all preceding list cells. -/
theorem readCoordinate_clock (row : List (List Bool)) (q B : ℕ)
    (hb : ∀ x∈row,x.length≤B) : (readCoordinate row q).clock≤4*q+3*B+4 := by
  induction row generalizing q with
  | nil => simp [readCoordinate]
  | cons x xs ih =>
    cases q with
    | zero =>
      have hh := hb x List.mem_cons_self
      simp only [readCoordinate,SemiprimeSourceCompactBits.copy_clock]
      omega
    | succ q =>
      have hh := ih q (fun y hy => hb y (List.mem_cons_of_mem _ hy))
      simp only [readCoordinate]
      omega

/-- Reusing a parent inventory never drops its original acquisition report. -/
theorem fromReplay_retains {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) :
    source.state.clock≤(fromReplay inputOwner source q g).work := by
  unfold fromReplay
  dsimp only
  omega

end RiemannGaussian.SemiprimeD1ChildGraph
