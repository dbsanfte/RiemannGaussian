/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketEntryValue

/-! # Actual sparse packet entry preparation and eager tables
The source and mode catalogue are acquired once in the header. Per-assignment
execution reads the concrete actual child bucket. New tables contain every
literal coefficient word; no old tensor or packet-entry supplier is invoked.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketTensorTables
open SemiprimeD1JetAxes SemiprimeD1TensorTables

/-- Concrete acquired packet data shared by all entry assignments. -/
structure Header (V : ℕ) where
  /-- Actual retained child-factor port bucket, in literal port order. -/
  endpoints : List (SemiprimeD1ChildGraph.Endpoint V)
  /-- Actual global mode classification, shared by all table entries. -/
  masks : SemiprimeD1PacketModeMask.Cache
  /-- Original source once, actual local graph, mode classification and bucket reads. -/
  clock : ℕ

/-- Prepare from actual OriginalModes, not a supplied mode catalogue or entry list. -/
def prepare {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) : Header (n+F) :=
  let graph := SemiprimeD1ChildGraph.fromReplay owner source.packets i g
  let masks := SemiprimeD1PacketModeMask.fromModes source packet i g
  let endpoints := (graph.factors[packet.val]?).getD []
  ⟨endpoints,masks,masks.clock+(graph.work-source.packets.state.clock)+packet.val+endpoints.length+10⟩

/-- Actual eager materialization, retaining the cached header and affine-node report once. -/
def acquire {V : ℕ} (header : Header V) (ctx : Context)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) : Acquired header.endpoints.length :=
  let out := build header.endpoints.length
    (SemiprimeD1PacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z) a i t
      header.masks header.endpoints beta)
  ⟨out.table,header.clock+z.clock+out.clock+beta.length+12⟩

/-- The literal table read equals the actual assembled physical entry, with no entry oracle. -/
theorem acquire_value {V : ℕ} (header : Header V) (ctx : Context)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (bits : List Bool) (hb : bits.length=header.endpoints.length) :
    (lookup (acquire header ctx z a i t beta).table bits).words=
      (SemiprimeD1PacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z) a i t
        header.masks header.endpoints beta bits).words :=
  build_value _ _ bits hb

/-- Every completed packet table is canonical in the CURRENT child coefficient context. -/
theorem acquire_good {V : ℕ} (header : Header V) (ctx : Context)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    Good ctx (acquire header ctx z a i t beta).table := by
  apply build_good
  intro bits _
  exact SemiprimeD1PacketEntryValue.evaluate_good ctx _ a i t _ _ beta bits

/-- Original catalogue multiplicity/order remains the full actual global catalogue. -/
theorem prepare_catalogue {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) :
    (prepare owner source packet i g).masks.items.map SemiprimeD1PacketModeMask.Item.mode=
      SemiprimeD1ModeCatalog.catalog (source.packets.state.packets.length*2^(i.val+1)) (source.precision-1) :=
  SemiprimeD1PacketModeMask.fromModes_catalogue source packet i g

/-- The original acquired producer is retained once in the table header report. -/
theorem prepare_retains {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) :
    source.work≤(prepare owner source packet i g).clock := by
  dsimp only [prepare,SemiprimeD1PacketModeMask.fromModes]
  omega

/-- Actual original-source entry point: no supplied masks, ports, catalogue or entry values. -/
def acquireOriginal {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :=
  acquire (prepare owner source packet i g) ctx z a i t beta

/-- The eager table degree is the actual acquired packet arity, hence at most 2L. -/
theorem original_degree_bound (n F r a u phase p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1OriginalModeAcquisition.acquire n F r a u phase p arity owner).packets.state.packets.length)
    (i : Fin a) (g : Fin r) :
    (prepare owner (SemiprimeD1OriginalModeAcquisition.acquire n F r a u phase p arity owner) packet i g).endpoints.length≤2*2^a := by
  let graph := SemiprimeD1ChildGraph.acquire n F r a arity owner i g
  have hl : graph.factors.length=
      (SemiprimeD1OriginalModeAcquisition.acquire n F r a u phase p arity owner).packets.state.packets.length :=
    SemiprimeD1ChildGraphSemantics.factors_length owner _ i g
  have hp : packet.val < graph.factors.length := by rw [hl];exact packet.isLt
  have h := SemiprimeD1ChildGraphBounds.packet_arity n F r a arity owner i g ⟨packet.val,hp⟩
  change ((graph.factors[packet.val]?).getD []).length≤_
  rw [List.getElem?_eq_getElem hp]
  exact h

end RiemannGaussian.SemiprimeD1PacketTensorTables
