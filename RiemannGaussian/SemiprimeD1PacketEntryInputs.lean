/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortBijection

/-! # Assignment reads from an actual child packet bucket
Each local Boolean assignment is scanned in the literal child-factor port order.
Rows and columns preserve that order and every real endpoint occurrence. Slot
conversion is a native finite-index stage, with physical slot/edge copies paid.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketEntryInputs
open SemiprimeD1ChildGraph SemiprimeBitArithmetic

/-- One actual local endpoint assignment with its cached finite orientation slot. -/
structure Wire (a : ℕ) where
  /-- Original orientation slot, clipped only for malformed external data. -/
  slot : Fin (2^a)
  /-- Literal Boolean assignment at this child port. -/
  bit : Bool
  /-- Copied positive real occurrence ID, retaining parallel occurrences. -/
  edge : List Bool
  deriving Repr

/-- Actual row/column assignment inventory with every producer report. -/
structure Inputs (a : ℕ) where
  /-- Real owner endpoints Y in original local order. -/
  rows : List (Wire a)
  /-- Real factor endpoints X in original local order. -/
  columns : List (Wire a)
  /-- Physical copies, local bit visits and native slot-index/control stages. -/
  clock : ℕ
  deriving Repr

/-- Copy the stored orientation and occurrence words; acquire the literal slot index. -/
def wire {V : ℕ} (a : ℕ) (endpoint : Endpoint V) (bit : Bool) : Wire a × ℕ :=
  let slot := SemiprimeSourceCompactBits.copy endpoint.slot
  let edge := SemiprimeSourceCompactBits.copy endpoint.edge
  let value := bitValue slot.bits
  (⟨⟨value%2^a,Nat.mod_lt _ (by positivity)⟩,bit,edge.bits⟩,
    slot.clock+edge.clock+slot.bits.length+value+2^a+8)

/-- Scan an actual bucket, never a supplied row/column truth list. -/
def gather {V : ℕ} (a : ℕ) : List (Endpoint V)→List Bool→Inputs a
  | [],_ => ⟨[],[],2⟩
  | endpoint::endpoints,bits =>
    let current := wire a endpoint (bits.head?.getD false)
    let tail := gather a endpoints bits.tail
    if endpoint.side then
      ⟨current.1::tail.rows,tail.columns,current.2+tail.clock+6⟩
    else ⟨tail.rows,current.1::tail.columns,current.2+tail.clock+6⟩

/-- Read the retained graph's actual observed-packet factor bucket. -/
def fromCache {n F a : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity)
    (packet : Fin data.source.state.packets.length) (bits : List Bool) : Inputs a :=
  let bucket := (data.graph.factors[packet.val]?).getD []
  let out := gather a bucket bits
  ⟨out.rows,out.columns,data.work+packet.val+out.clock+8⟩

/-- Every acquired wire retains the literal supplied assignment bit and edge. -/
theorem wire_data {V : ℕ} (a : ℕ) (endpoint : Endpoint V) (bit : Bool) :
    (wire a endpoint bit).1.bit=bit ∧ (wire a endpoint bit).1.edge=endpoint.edge := by
  simp only [wire,SemiprimeSourceCompactBits.copy_bits]
  exact ⟨True.intro,True.intro⟩

/-- Valid actual orientation words are not altered by the native finite-index conversion. -/
theorem wire_slot {V : ℕ} (a : ℕ) (endpoint : Endpoint V) (bit : Bool)
    (hs : endpoint.slot.length=a) :
    (wire a endpoint bit).1.slot.val=bitValue endpoint.slot := by
  have h := bitValue_lt_width endpoint.slot
  rw [hs] at h
  simp only [wire,SemiprimeSourceCompactBits.copy_bits,Nat.mod_eq_of_lt h]

/-- Every local endpoint contributes to exactly one side, including duplicate original ports. -/
theorem gather_count {V : ℕ} (a : ℕ) (endpoints : List (Endpoint V)) (bits : List Bool) :
    (gather a endpoints bits).rows.length+(gather a endpoints bits).columns.length=endpoints.length := by
  induction endpoints generalizing bits with
  | nil => rfl
  | cons endpoint endpoints ih =>
    have h := ih bits.tail
    dsimp only [gather]
    split_ifs <;> simp only [List.length_cons] <;> omega

/-- Literal assignment annotation, with high false padding only for malformed inputs. -/
def annotate {V : ℕ} : List (Endpoint V)→List Bool→List (Endpoint V×Bool)
  | [],_ => []
  | endpoint::endpoints,bits => (endpoint,bits.head?.getD false)::annotate endpoints bits.tail

/-- Row selection is exactly the side-filtered literal assignment annotation. -/
theorem gather_rows {V : ℕ} (a : ℕ) (endpoints : List (Endpoint V)) (bits : List Bool) :
    (gather a endpoints bits).rows=
      (annotate endpoints bits).filterMap (fun e => if e.1.side then
        some (wire a e.1 e.2).1 else none) := by
  induction endpoints generalizing bits with
  | nil => rfl
  | cons endpoint endpoints ih =>
    dsimp only [gather]
    split_ifs with hs <;> simp [annotate,hs,ih]

/-- Column selection preserves the complementary original assignment order. -/
theorem gather_columns {V : ℕ} (a : ℕ) (endpoints : List (Endpoint V)) (bits : List Bool) :
    (gather a endpoints bits).columns=
      (annotate endpoints bits).filterMap (fun e => if e.1.side then
        none else some (wire a e.1 e.2).1) := by
  induction endpoints generalizing bits with
  | nil => rfl
  | cons endpoint endpoints ih =>
    dsimp only [gather]
    split_ifs with hs <;> simp [annotate,hs,ih]

end RiemannGaussian.SemiprimeD1PacketEntryInputs
