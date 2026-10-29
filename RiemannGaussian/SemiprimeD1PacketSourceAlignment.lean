/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketSourceProduct

/-! # Executed source bases and original arithmetic tile coordinates
The physical source terms are identified with literal column-slot powers.
Original D.12 is applied to those same slots, rather than to advised source
linear forms or independently supplied displacement indices.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1PacketSourceAlignment
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketEntryComponents SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The original base column of an arithmetic tile, obtained from the actual slot. -/
def tileBase (a : ℕ) (i : Fin a) (column : Wire a) : Fin (2^a) :=
  ⟨column.slot.val % 2^(i.val+1), (Nat.mod_lt _ (by positivity)).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))⟩

/-- The quotient used by the physical power supplier is exactly the original
D.12 tile displacement. No separate tile-index answer is supplied. -/
theorem column_decomposition (a : ℕ) (i : Fin a) (column : Wire a) :
    column.slot.val=(tileBase a i column).val+2^(i.val+1)*(column.slot.val/2^(i.val+1)) := by
  exact (Nat.mod_add_div _ _).symm

/-- The computed source base is the sum over the actual Boolean-on columns in
its arithmetic tile. Repeated real columns remain repeated summands. -/
def tilePower (ctx : Context) (a : ℕ) (i : Fin a) (columns : List (Wire a))
    (tile order : ℕ) : Carrier ctx :=
  ((columns.filter (fun column => column.bit && (column.slot.val%2^(i.val+1) == tile))).map
    (fun column => (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
      ((column.slot.val/2^(i.val+1):ℕ):ZMod (2^ctx.precision)))^order)).sum

/-- Exact physical source-term sum; the filter is derived from the executed
bit/tile tests, not an externally supplied eligible-column list. -/
theorem source_terms_tilePower (ctx : Context) (a : ℕ) (i : Fin a)
    (columns : List (Wire a)) (item : SemiprimeD1PacketModeMask.Item) (hpos : ctx.Positive) :
    (columns.map (fun column => interpret ctx (sourceTerm ctx a i item column).words)).sum=
      tilePower ctx a i columns item.tile item.mode.order := by
  induction columns with
  | nil => rfl
  | cons column columns ih =>
    rw [List.map_cons,List.sum_cons,sourceTerm_value ctx a i item column hpos,ih]
    unfold tilePower
    by_cases h : (column.bit && (column.slot.val%2^(i.val+1) == item.tile))=true
    · simp only [List.filter_cons,h,ite_true,List.map_cons,List.sum_cons]
    · simp only [List.filter_cons,h,ite_false,Bool.false_eq_true,zero_add]

/-- An actual descriptor-cache source base has exactly its original arithmetic
column form, with no free source-base value parameter. -/
theorem sourceBase_tilePower (ctx : Context) (a : ℕ) (i : Fin a)
    (columns : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache)
    (j : ℕ) (item : SemiprimeD1PacketModeMask.Item) (hj : cache.items[j]?=some item)
    (hpos : ctx.Positive) :
    SemiprimeD1PacketSourceProduct.sourceBase ctx a i columns cache j=
      tilePower ctx a i columns item.tile item.mode.order := by
  simp only [SemiprimeD1PacketSourceProduct.sourceBase,hj]
  exact source_terms_tilePower ctx a i columns item hpos

/-- The original evaluated D.12 expansion of an executed real column term.
The only bit condition is the value of the same physical bit test already used
by the actual coefficient supplier; the displacement is computed internally. -/
theorem baseTerm_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row column : Wire a) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val)
    (hbit : (sameBit row.slot.val (tileBase a i column).val i.val).value=true) :
    interpret ctx (baseTerm ctx z a t row column).words=
      if column.bit then ∑ b∈Finset.range (ctx.precision-1),
        SemiprimeD1UniversalModeData.evaluate ctx.precision
          (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
          (SemiprimeD1UniversalModeData.acquireOriginal ctx.precision a i.val b t row.slot (tileBase a i column))*
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
          ((column.slot.val/2^(i.val+1):ℕ):ZMod (2^ctx.precision)))^b else 0 := by
  rw [baseTerm_value ctx z a t row column hpos hp]
  apply congrArg (fun value : Carrier ctx => if column.bit then value else 0)
  have hb : row.slot.val.testBit i.val=(tileBase a i column).val.testBit i.val := by
    rw [sameBit_value] at hbit
    exact beq_iff_eq.mp hbit
  simpa only [map_pow] using SemiprimeD1UniversalModeData.original_D12 ctx.precision a i.val
    (column.slot.val/2^(i.val+1))
    (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
    t row.slot (tileBase a i column) column.slot ht hi i.isLt hb
    (column_decomposition a i column) hp

/-- Every actual child column belongs to the computed source of its own tile.
The source equality follows from the original physical group test and replay
row dictionary, not from a supplied column owner. -/
theorem original_column_source (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : SemiprimeD1ChildGraph.Endpoint (n+F))
    (he : endpoint∈((SemiprimeD1ChildGraph.acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=false) :
    let tile : Fin (2^(i.val+1)) := ⟨SemiprimeBitArithmetic.bitValue endpoint.slot%2^(i.val+1),
      Nat.mod_lt _ (by positivity)⟩
    (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source=
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  let tile : Fin (2^(i.val+1)) := ⟨SemiprimeBitArithmetic.bitValue endpoint.slot%2^(i.val+1),
    Nat.mod_lt _ (by positivity)⟩
  obtain ⟨port,out,ho,hpacket,horigin⟩ :=
    SemiprimeD1PacketEndpointOriginal.endpoint_origin owner source packet i g endpoint he
  rcases horigin with ⟨heq,hrow⟩|⟨heq,hcolumn⟩
  · rw [heq] at hside
    simp only [SemiprimeD1ChildGraph.endpoints,Bool.true_eq_false] at hside
  · have htile : SemiprimeBitArithmetic.bitValue out.slot%2^(i.val+1)=tile.val := by
      simp only [tile,heq,SemiprimeD1ChildGraph.endpoints]
    have hc := SemiprimeD1ModeRoutingOriginal.column_source_original n F r a arity owner
      packet i tile out ho hpacket htile
    have hn := (SemiprimeD1ChildGraph.testColour_correct
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i.val
      (SemiprimeD1PacketRows.read source.padding.source.selection.cache.rows.source.dictionary a out.source).right).mp hcolumn
    have hcompact := (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner packet i tile).1
    have hsource : (SemiprimeD1ModeRoutingBits.fromReplay source packet i tile).source=
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
      apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hcompact
        (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
      rw [←hc]
      exact hn
    rw [(SemiprimeD1ModeRoutingBits.fromReplay_data source packet i tile).1] at hsource
    exact hsource

end
end RiemannGaussian.SemiprimeD1PacketSourceAlignment
