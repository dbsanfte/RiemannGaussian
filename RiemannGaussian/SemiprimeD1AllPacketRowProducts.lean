/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalPacketPositions

/-! # All observed packet polynomials reproduce every original row once
The observed partition is computed by actual key index search, with acquisition
coverage and nodup proved. Empty/unobserved orbit buckets are never enumerated.
-/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace RiemannGaussian.SemiprimeD1AllPacketRowProducts
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketRowProducts SemiprimeD1PacketColumnPartition
open SemiprimeD1OriginalPacketPositions SemiprimeD1OriginalIncidenceIndex
open SemiprimeD1PacketSourceVector SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- One original side wire at its computed real occurrence position. -/
def sideWire (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (side : Bool)
    (assignment : Endpoint (n+F)→Bool)
    (j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length) : Wire a :=
  let pair := ((position n F r a arity owner).symm j,
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements[j.val])
  (wire a (chosenEndpoint owner side pair) (assignment (chosenEndpoint owner side pair))).1

/-- Literal original packet filtering equals the computed finite observed
partition in original occurrence order, including repeated parallel ports. -/
theorem originalSideWires_fin (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (side : Bool)
    (assignment : Endpoint (n+F)→Bool)
    (f : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length) :
    originalSideWires n F r a arity owner side f assignment=
      (List.finRange (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length).filterMap
        (fun j => if observed n F r a arity owner j=f then some (sideWire n F r a arity owner side assignment j) else none) := by
  unfold originalSideWires
  rw [pairs_ofFn,List.ofFn_eq_map,List.filterMap_map]
  apply List.filterMap_congr
  intro j _
  dsimp only [Function.comp_def]
  by_cases h : observed n F r a arity owner j=f
  · have hk := (observed_eq_iff n F r a arity owner j f).mp h
    simp only [hk,h,ite_true]
    rfl
  · have hk := (observed_eq_iff n F r a arity owner j f).not.mp h
    simp only [hk,h,ite_false]

/-- Every packet row value can use the row's own computed observed packet,
without changing any selected real occurrence. -/
theorem packet_row_product (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (assignment : Endpoint (n+F)→Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (f : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length) :
    ((originalSideWires n F r a arity owner true f assignment).map
      (wireRowValue ctx z n F r a arity owner f assignment t)).prod=
      ((partitionMap (List.finRange (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length)
        (observed n F r a arity owner) (fun j => some j) f).map
        (fun j => wireRowValue ctx z n F r a arity owner (observed n F r a arity owner j) assignment t
          (sideWire n F r a arity owner true assignment j))).prod := by
  rw [originalSideWires_fin]
  apply congrArg List.prod
  rw [List.map_filterMap]
  unfold partitionMap
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro j _
  by_cases h : observed n F r a arity owner j=f <;> simp only [h,ite_true,ite_false,Option.map_some,Option.map_none]

/-- The actual product over all observed packet/group polynomials evaluates to
all original real-row values once, in their acquired occurrence positions. -/
theorem all_packet_eval (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (assignment : Endpoint (n+F)→Bool) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : ctx.precision=(SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i).precision)
    (hpos : ctx.Positive) (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    MvPolynomial.eval (values ctx n F r a (ctx.precision-1) arity owner i assignment)
      (∏f : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length,
        ∏g : Fin r,packetPolynomial ctx z n F r a u p arity owner i f g assignment t)=
      ∏j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length,
        wireRowValue ctx z n F r a arity owner (observed n F r a arity owner j) assignment t
          (sideWire n F r a arity owner true assignment j) := by
  rw [map_prod]
  simp_rw [packet_groups_eval ctx z n F r a u p arity owner i _ assignment t hprecision hpos hp ht hi,
    packet_row_product]
  let valueFn := fun j : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length =>
    wireRowValue ctx z n F r a arity owner (observed n F r a arity owner j) assignment t
      (sideWire n F r a arity owner true assignment j)
  have h := (partition_perm
    (List.finRange (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length)
    (observed n F r a arity owner) (fun j => some j)).map valueFn
  have hh := h.prod_eq
  rw [prod_flatMap_map,←List.ofFn_eq_map,List.prod_ofFn] at hh
  simp only [List.filterMap_some] at hh
  rw [←List.ofFn_eq_map,List.prod_ofFn] at hh
  exact hh

end
end RiemannGaussian.SemiprimeD1AllPacketRowProducts
