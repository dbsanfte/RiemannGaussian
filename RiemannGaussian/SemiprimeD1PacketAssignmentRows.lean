/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketRowProducts
import RiemannGaussian.SemiprimeD1OriginalIncidenceIndex
import RiemannGaussian.SemiprimeD1PacketInventoryCoverage

/-! # Original X/Y assignments on physically resolved packet endpoints
The typed occurrence/placement pairing and unique physical ID bank determine
every endpoint bit. No endpoint-to-original-bit correspondence is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace RiemannGaussian.SemiprimeD1PacketAssignmentRows
open SemiprimeD1ChildGraph SemiprimeD1PacketInventory
open SemiprimeD1ChildPortPullbackCorrectness SemiprimeD1ChildAssignmentEquiv
open SemiprimeD1ChildAssignmentEndpoint SemiprimeD1OriginalIncidenceIndex
noncomputable section

/-- The two original occurrence assignments retain their distinct endpoint side. -/
def tagBits (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (x y : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length→Bool)
    (tag : Tag arity) : Bool :=
  if tag.2 then y (position n F r a arity owner tag.1) else x (position n F r a arity owner tag.1)

/-- Exact resolved bits of both endpoints of EVERY actual original paired port. -/
theorem original_pair_bits (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (bits : Tag arity→Bool) (pair : ((e : Fin F)×Fin (arity e))×Placement)
    (hp : pair∈originalPairs n F r a arity owner) :
    originalEndpointBit n F r a arity owner bits (endpoints owner pair.1 pair.2).1=bits (pair.1,true) ∧
    originalEndpointBit n F r a arity owner bits (endpoints owner pair.1 pair.2).2=bits (pair.1,false) := by
  let ids := (originalPairs n F r a arity owner).map (fun p => (p.2.edge,p.1))
  have hn : (ids.map Prod.fst).Nodup := by
    simpa only [ids_value] using ids_nodup n F r a arity owner q g
  have hf := findPort_member ids hn pair.2.edge pair.1 (List.mem_map.mpr ⟨pair,hp,rfl⟩)
  simp only [originalEndpointBit,resolve,endpoints]
  change (((SemiprimeD1ChildPortPullback.findPort pair.2.edge ids).value.map (fun i => (i,true))).map bits).getD false=_ ∧
    (((SemiprimeD1ChildPortPullback.findPort pair.2.edge ids).value.map (fun i => (i,false))).map bits).getD false=_
  rw [hf]
  exact ⟨rfl,rfl⟩

/-- Actual original endpoint reads are exactly the original Y/X coordinate bits
at the computed occurrence position, including repeated parallel incidences. -/
theorem original_pair_xy (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r)
    (x y : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length→Bool)
    (pair : ((e : Fin F)×Fin (arity e))×Placement)
    (hp : pair∈originalPairs n F r a arity owner) :
    originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)
      (endpoints owner pair.1 pair.2).1=y (position n F r a arity owner pair.1) ∧
    originalEndpointBit n F r a arity owner (tagBits n F r a arity owner x y)
      (endpoints owner pair.1 pair.2).2=x (position n F r a arity owner pair.1) := by
  simpa only [tagBits,ite_true,Bool.false_eq_true,ite_false] using
    original_pair_bits n F r a arity owner q g (tagBits n F r a arity owner x y) pair hp

end
end RiemannGaussian.SemiprimeD1PacketAssignmentRows
