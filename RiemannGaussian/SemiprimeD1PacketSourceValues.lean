/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketCoefficientAlignment

/-! # Original source forms at computed route owners
Every source form below is reconstructed from the actual child column list.
Finite source-group sums collapse using original routing and empty-tile zeros,
without an advised source owner or source-linear-form answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeD1PacketSourceValues
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketGlobalRowForm
open SemiprimeD1PacketRowExpansion SemiprimeD1PacketSourceAlignment
open SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Source group read from the actual physical routing bytes, with its original
palette bound proved from the retained sparse replay. -/
def sourceGroup (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) : Fin r :=
  ⟨SemiprimeBitArithmetic.bitValue (SemiprimeD1ModeRoutingBits.fromReplay
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i tile).source,
    (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner packet i tile).2.1⟩

/-- Computed source group equality is exactly the executed compact-byte equality. -/
theorem sourceGroup_bytes (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (g : Fin r) :
    sourceGroup n F r a arity owner packet i tile=g ↔
      (SemiprimeD1ModeRoutingBits.acquire
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source=
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  have hc := (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner packet i tile).1
  have hd := (SemiprimeD1ModeRoutingBits.fromReplay_data
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i tile).1
  constructor
  · intro h
    rw [←hd]
    apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hc
      (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
    rw [SemiprimeSourceHistogramPortKeys.encodeKey_value]
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    change SemiprimeBitArithmetic.bitValue _=g.val
    rw [hd,h,SemiprimeSourceHistogramPortKeys.encodeKey_value]

/-- Original source form at that computed owner. This is derived from the actual
acquired column list, not an external L-value function. -/
def sourceForm (ctx : Context) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (assignment : Endpoint (n+F)→Bool) (tile : Fin (2^(i.val+1))) (b : ℕ) : Carrier ctx :=
  tilePower ctx a i (columnsOf n F r a arity owner i packet assignment
    (sourceGroup n F r a arity owner packet i tile)) tile.val b

/-- The actual source group sum has exactly one possible nonzero source form.
A local source=target mode contributes zero; empty forms remain literal zero. -/
theorem source_sum (ctx : Context) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (assignment : Endpoint (n+F)→Bool)
    (tile : Fin (2^(i.val+1))) (b : ℕ) (c : Carrier ctx) :
    (∑h : Fin r,if h=g then 0 else
      c*tilePower ctx a i (columnsOf n F r a arity owner i packet assignment h) tile.val b)=
      if sourceGroup n F r a arity owner packet i tile=g then 0
      else c*sourceForm ctx n F r a arity owner packet i assignment tile b := by
  rw [Finset.sum_eq_single (sourceGroup n F r a arity owner packet i tile)]
  · rfl
  · intro h _ hn
    by_cases hg : h=g
    · simp only [hg,ite_true]
    · have hs : (SemiprimeD1ModeRoutingBits.acquire
          (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
          (SemiprimeSourceHistogramPortKeys.encodeKey h.val).bits := by
        intro hb
        exact hn ((sourceGroup_bytes n F r a arity owner packet i tile h).mpr hb).symm
      simp only [hg,ite_false]
      rw [original_tilePower_zero ctx n F r a arity owner packet i h assignment tile b hs,mul_zero]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

/-- The full original row uses exactly one reconstructed source form per tile.
This eliminates the source-group sum using the actual routing palette. -/
theorem full_row_source (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (rowEndpoint : Endpoint (n+F))
    (hr : rowEndpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hrs : rowEndpoint.side=true) (rowBit : Bool) (assignment : Endpoint (n+F)→Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let row := (wire a rowEndpoint rowBit).1
    ((SemiprimeD1PacketColumnPartition.originalSideWires n F r a arity owner false packet assignment).map
      (fun c => interpret ctx (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row c).words)).sum=
      ((columnsOf n F r a arity owner i packet assignment g).map
        (fun c => interpret ctx (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row c).words)).sum+
      ∑tile : Fin (2^(i.val+1)),∑b∈Finset.range (ctx.precision-1),
        if sourceGroup n F r a arity owner packet i tile=g then 0 else
        modeValue ctx z a i t row tile b*sourceForm ctx n F r a arity owner packet i assignment tile b := by
  dsimp only
  rw [full_row_D12 ctx z n F r a arity owner packet i g rowEndpoint hr hrs rowBit assignment t hpos hp ht hi]
  let row := (wire a rowEndpoint rowBit).1
  let localSum := ((columnsOf n F r a arity owner i packet assignment g).map
    (fun c => interpret ctx (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row c).words)).sum
  let expansion := fun h : Fin r => ∑tile : Fin (2^(i.val+1)),∑b∈Finset.range (ctx.precision-1),
    modeValue ctx z a i t row tile b*tilePower ctx a i (columnsOf n F r a arity owner i packet assignment h) tile.val b
  have hsplit : (∑h : Fin r,if h=g then localSum else expansion h)=
      localSum+∑h : Fin r,if h=g then 0 else expansion h := by
    have he (h : Fin r) : (if h=g then localSum else expansion h)=
        (if h=g then localSum else 0)+(if h=g then 0 else expansion h) := by
      by_cases hh : h=g <;> simp only [hh,ite_true,ite_false,add_zero,zero_add]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑h : Fin r,if h=g then _ else expansion h)=_
  have hleft : (∑h : Fin r,if h=g then
      ((columnsOf n F r a arity owner i packet assignment h).map
        (fun c => interpret ctx (SemiprimeD1PacketEntryBits.baseTerm ctx z a t row c).words)).sum else expansion h)=
      ∑h : Fin r,if h=g then localSum else expansion h := by
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : h=g <;> simp only [hh,ite_true,ite_false,localSum]
  rw [hleft,hsplit]
  congr 1
  have hterm (h : Fin r) : (if h=g then 0 else expansion h)=
      ∑tile : Fin (2^(i.val+1)),∑b∈Finset.range (ctx.precision-1),
        if h=g then 0 else modeValue ctx z a i t row tile b*
          tilePower ctx a i (columnsOf n F r a arity owner i packet assignment h) tile.val b := by
    by_cases hh : h=g <;> simp only [hh,ite_true,ite_false,expansion,Finset.sum_const_zero]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tile _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact source_sum ctx n F r a arity owner packet i g assignment tile b (modeValue ctx z a i t row tile b)

end
end RiemannGaussian.SemiprimeD1PacketSourceValues
