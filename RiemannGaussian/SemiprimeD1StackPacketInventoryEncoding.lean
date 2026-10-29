/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventory
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMeaning
import RiemannGaussian.SemiprimeD1PacketInventory
/-! # Exact physical sparse-inventory overrides and placement-output ABI
All lists, maps and original row/index interpretations are semantic proof data.
The fixed source receives only its selected-key vector and acquired catalogue.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
open SemiprimeD1StackPacketInventory
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Dict
export SemiprimeD1StackSourceKeyFrequencyEncoding (Rows dictionary read encoded)
export SemiprimeD1StackSourceKeyFrequencyMeaning (read_cons)
end Dict
namespace Counter
export SemiprimeD1StackSourceEnvironmentEncoding (successor successor_value successor_compact)
end Counter
namespace Native
export SemiprimeD1PacketInventory (Placement)
end Native
/-- Literal physical six-field placement payload, in original source/padding/packet/slot/edge/valid order. -/
def placementBytes (p:Native.Placement):List Bool:=
  frame p.source (frame p.padding (frame p.packet (frame p.slot (frame p.edge (frame [p.valid] [])))))
/-- Mathematical interpretation of the actual physically acquired sparse cache, retaining every obsolete map override. -/
structure Summary where
  /-- Actual newest-first raw-key/count rows; stored comparison keys are sentinel-encoded only by dictionary. -/
  classes:Dict.Rows
  /-- Actual newest-first raw-packet/true marker rows. -/
  seen:Dict.Rows
  /-- Actual newest-first raw-packet-slot/positive-edge rows. -/
  slots:Dict.Rows
  /-- Actual newest-first first-discovery packet list. -/
  packets:List (List Bool)
  /-- Actual compact last-positive-occurrence word. -/
  edge:List Bool
  /-- Actual placements in original chronological occurrence order. -/
  placements:List Native.Placement
/-- Exactly the four physically seeded false terminators and zero edge before reading any occurrence. -/
def empty:Summary:=⟨[],[],[],[],[],[]⟩
/-- Proof-side original row/orientation interpretation, naming bytes obtained by the actual Reader19 and Orientation19 calls. -/
def step (a:Nat) (s:Summary) (key:List Bool):Summary:=
  let old:=Dict.read s.classes key
  let rows:=SemiprimeD1PacketRows.read (SemiprimeSourceHistogramRows.acquire 64 a) a key
  let out:=SemiprimeD1OrientationBits.acquire rows.left rows.right old
  let next:=Counter.successor s.edge
  let placement:Native.Placement:=⟨key,old,out.key,out.slots,next,rows.valid && out.valid⟩
  ⟨(key,Counter.successor old)::s.classes,(out.key,[true])::s.seen,
    (frame out.key out.slots,next)::s.slots,
    if (Dict.read s.seen out.key).isEmpty then out.key::s.packets else s.packets,
    next,s.placements++[placement]⟩
/-- Actual forward source-vector order, including all repeated and parallel keys. -/
def acquire (a:Nat) (keys:List (List Bool)):Summary:=keys.foldl (step a) empty
/-- Exactly the stopped physical catalogue of the actual frozen alphabet producer. -/
def alphabet (a:Nat):List Bool:=SemiprimeD1StackPacketRowsOriginal.catalogue a
/-- Complete final59-word physical bank, retaining all maps/history records and no hidden work roles. -/
def result (keys alphabet:List Bool) (s:Summary):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (input keys alphabet) classes (Dict.dictionary s.classes)) seen (Dict.dictionary s.seen)) slots (Dict.dictionary s.slots))
    packets (vectorBits s.packets)) output (vectorBits (s.placements.map placementBytes))) edge s.edge) success [true]
/-- Whole actual successful halt, with both transient flags and all real nested return frames clear. -/
def done (keys alphabet:List Bool) (s:Summary):C.State Stack Label:=⟨none,none,none,result keys alphabet s,[]⟩
/-- Runtime source carries actual encoded keys and catalogue only. Width and key list here are proof indices. -/
def source (a:Nat) (keys:List (List Bool)):C.State Stack Label:=initial (vectorBits keys) (alphabet a)
/-- Every placement retains precisely its actual original key and its input order. -/
theorem acquire_sources (a:Nat) (keys:List (List Bool)):
    ((acquire a keys).placements.map (fun p=>p.source))=keys :=by
  have h:∀(keys:List (List Bool)) (s:Summary),((keys.foldl (step a) s).placements.map (fun p=>p.source))=
      s.placements.map (fun p=>p.source)++keys:=by
    intro keys
    induction keys with
    | nil=>intro s;simp only [List.foldl_nil,List.append_nil]
    | cons k ks ih=>
      intro s
      rw [List.foldl_cons,ih]
      simp only [step,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
  exact h keys empty
/-- One actual byte-key override exactly matches a literal trie put at every raw query, including all high-zero prefixes. -/
theorem override_read (rows:Dict.Rows) (key value q:List Bool):
    Dict.read ((key,value)::rows) q=if key=q then value else Dict.read rows q:=Dict.read_cons key value rows q
/-- Compact positive edge is incremented exactly once per physical occurrence. -/
theorem step_edge (a:Nat) (s:Summary) (key:List Bool):
    SemiprimeBitArithmetic.bitValue (step a s key).edge=SemiprimeBitArithmetic.bitValue s.edge+1:=Counter.successor_value _
end RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
