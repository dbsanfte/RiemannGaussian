/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketColumnPartition

/-! # Original cross-group real-row expansion
Actual child source lists and actual replay routing discharge every crossing
bit test. Global endpoint assignments are restricted by the literal acquired
bucket order; no desired column list, owner map or row form is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeD1PacketGlobalRowForm
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketSourceAlignment SemiprimeD1PacketRowExpansion
open SemiprimeD1PacketColumnPartition SemiprimeD1ChildGraph
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every acquired source-column wire has its literal original endpoint and
assignment bit. This is derived from the actual gather scan. -/
theorem column_origin {V : ℕ} (a : ℕ) (bucket : List (Endpoint V))
    (assignment : Endpoint V→Bool) (column : Wire a)
    (hc : column∈(gather a bucket (bucket.map assignment)).columns) :
    ∃e∈bucket,e.side=false ∧ column=(wire a e (assignment e)).1 := by
  rw [(gather_assignment a bucket assignment).2] at hc
  obtain ⟨e,he,hval⟩ := List.mem_filterMap.mp hc
  cases hs : e.side
  · simp only [hs,Bool.false_eq_true,ite_false,Option.some.injEq] at hval
    exact ⟨e,he,hs,hval.symm⟩
  · simp only [hs,ite_true,reduceCtorEq] at hval

/-- A real row and a real column in different acquired groups meet the original
crossing bit condition. The column's source is proved from the physical group
test, rather than passed as an algebraic owner certificate. -/
theorem original_cross_column_test (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g h : Fin r) (hne : h≠g)
    (rowEndpoint columnEndpoint : Endpoint (n+F))
    (hr : rowEndpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hc : columnEndpoint∈((acquire n F r a arity owner i h).factors[packet.val]?).getD [])
    (hrs : rowEndpoint.side=true) (hcs : columnEndpoint.side=false) (rowBit columnBit : Bool) :
    (sameBit (wire a rowEndpoint rowBit).1.slot.val
      (tileBase a i (wire a columnEndpoint columnBit).1).val i.val).value=true := by
  let tile : Fin (2^(i.val+1)) :=
    ⟨SemiprimeBitArithmetic.bitValue columnEndpoint.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
  have hs := original_column_source n F r a arity owner packet i h columnEndpoint hc hcs
  have hsource : (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
    rw [hs]
    intro he
    have hn := congrArg SemiprimeBitArithmetic.bitValue he
    simp only [SemiprimeSourceHistogramPortKeys.encodeKey_value] at hn
    exact hne (Fin.ext hn)
  have hb := SemiprimeD1PacketModeOriginal.row_test_true n F r a arity owner packet i g tile
    rowEndpoint hr hrs hsource rowBit
  have hlen := SemiprimeD1PacketEndpointOriginal.original_slot_length n F r a arity owner packet i h columnEndpoint hc
  simpa only [tileBase,wire_slot a columnEndpoint columnBit hlen,tile] using hb

/-- Original real-row term expansion for every actual source-column member. -/
theorem original_cross_term_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g h : Fin r) (hne : h≠g) (rowEndpoint : Endpoint (n+F))
    (hr : rowEndpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hrs : rowEndpoint.side=true) (rowBit : Bool) (assignment : Endpoint (n+F)→Bool)
    (column : Wire a)
    (hc : column∈(let bucket := ((acquire n F r a arity owner i h).factors[packet.val]?).getD []
      gather a bucket (bucket.map assignment)).columns)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let row := (wire a rowEndpoint rowBit).1
    interpret ctx (baseTerm ctx z a t row column).words=
      if column.bit then ∑ b∈Finset.range (ctx.precision-1),
        SemiprimeD1UniversalModeData.evaluate ctx.precision
          (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) (interpret ctx z.words)
          (SemiprimeD1UniversalModeData.acquireOriginal ctx.precision a i.val b t row.slot (tileBase a i column))*
        (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)
          ((column.slot.val/2^(i.val+1):ℕ):ZMod (2^ctx.precision)))^b else 0 := by
  obtain ⟨e,he,hs,hwire⟩ := column_origin a _ assignment column hc
  subst column
  exact baseTerm_D12 ctx z a i t _ _ hpos hp ht hi
    (original_cross_column_test n F r a arity owner packet i g h hne rowEndpoint e hr he hrs hs rowBit (assignment e))

/-- Fixed-tile D.12 only needs the bit condition at columns actually contributing
to that tile; empty tiles require no crossing certificate. -/
theorem row_tile_relevant (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (tile : Fin (2^(i.val+1))) (columns : List (Wire a))
    (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val)
    (hb : ∀c∈columns,(c.bit && (c.slot.val%2^(i.val+1) == tile.val))=true →
      (sameBit row.slot.val tile.val i.val).value=true) :
    (columns.map (columnEntry ctx z a i t row tile)).sum=
      ∑b∈Finset.range (ctx.precision-1),modeValue ctx z a i t row tile b*tilePower ctx a i columns tile.val b := by
  simp_rw [tilePower_columns]
  induction columns with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,Finset.sum_const_zero]
  | cons c cs ih =>
    have hc : columnEntry ctx z a i t row tile c=
        ∑b∈Finset.range (ctx.precision-1),modeValue ctx z a i t row tile b*columnPower ctx a i tile c b := by
      by_cases he : (c.bit && (c.slot.val%2^(i.val+1) == tile.val))=true
      · exact column_D12 ctx z a i t row tile c hp ht hi (hb c List.mem_cons_self he)
      · simp only [columnEntry,columnPower,he,Bool.false_eq_true,ite_false,mul_zero,Finset.sum_const_zero]
    simp only [List.map_cons,List.sum_cons]
    rw [hc,ih (fun c hc => hb c (List.mem_cons_of_mem _ hc)),←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    exact (mul_add _ _ _).symm

/-- Every actual source group distinct from the real row's group has the exact
fixed-tile expansion; all relevant bit tests are derived from real endpoints. -/
theorem original_cross_tile_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g h : Fin r) (hne : h≠g) (rowEndpoint : Endpoint (n+F))
    (hr : rowEndpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hrs : rowEndpoint.side=true) (rowBit : Bool) (assignment : Endpoint (n+F)→Bool)
    (tile : Fin (2^(i.val+1))) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let bucket := ((acquire n F r a arity owner i h).factors[packet.val]?).getD []
    let columns := (gather a bucket (bucket.map assignment)).columns
    let row := (wire a rowEndpoint rowBit).1
    (columns.map (columnEntry ctx z a i t row tile)).sum=
      ∑b∈Finset.range (ctx.precision-1),modeValue ctx z a i t row tile b*tilePower ctx a i columns tile.val b := by
  apply row_tile_relevant ctx z a i t _ tile _ hp ht hi
  intro c hc htile
  obtain ⟨e,he,hs,hwire⟩ := column_origin a _ assignment c hc
  have hb := original_cross_column_test n F r a arity owner packet i g h hne rowEndpoint e
    hr he hrs hs rowBit (assignment e)
  have hv : c.slot.val%2^(i.val+1)=tile.val := beq_iff_eq.mp (Bool.and_eq_true_iff.mp htile).2
  rw [←hwire] at hb
  simpa only [tileBase,hv] using hb

/-- The complete finite tile scan contains each original column term exactly
once, including Boolean-off columns and empty tiles. -/
theorem column_tiles (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row column : Wire a) (hpos : ctx.Positive) (hp : 0<ctx.precision) :
    (∑tile : Fin (2^(i.val+1)),columnEntry ctx z a i t row tile column)=
      interpret ctx (baseTerm ctx z a t row column).words := by
  let selected : Fin (2^(i.val+1)) := ⟨column.slot.val%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩
  rw [SemiprimeD1PacketEntryComponents.baseTerm_value ctx z a t row column hpos hp]
  rw [Finset.sum_eq_single selected]
  · simp only [columnEntry,selected,beq_self_eq_true,Bool.and_true]
  · intro tile _ hne
    have hn : column.slot.val%2^(i.val+1)≠tile.val := by
      intro he
      exact hne (Fin.ext he.symm)
    simp only [columnEntry,beq_iff_eq.not.mpr hn,Bool.and_false,Bool.false_eq_true,ite_false]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

/-- A literal column sum splits into the complete arithmetic-tile sum. -/
theorem columns_tiles (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (row : Wire a) (columns : List (Wire a)) (hpos : ctx.Positive) (hp : 0<ctx.precision) :
    (columns.map (fun c => interpret ctx (baseTerm ctx z a t row c).words)).sum=
      ∑tile : Fin (2^(i.val+1)),(columns.map (columnEntry ctx z a i t row tile)).sum := by
  induction columns with
  | nil => simp only [List.map_nil,List.sum_nil,Finset.sum_const_zero]
  | cons c cs ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
    rw [column_tiles ctx z a i t row c hpos hp,ih]

/-- Actual source-group columns under a common global endpoint assignment. -/
def columnsOf (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) (g : Fin r) : List (Wire a) :=
  let bucket := ((acquire n F r a arity owner i g).factors[packet.val]?).getD []
  (gather a bucket (bucket.map assignment)).columns

/-- Distributing a list-valued group scan preserves all additive occurrences. -/
theorem sum_flatMap_map {A B C : Type*} [AddCommMonoid C]
    (xs : List A) (f : A→List B) (value : B→C) :
    ((xs.flatMap f).map value).sum=(xs.map (fun x => ((f x).map value).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

/-- The full original packet-column sum is exactly the sum of the actual
source-group column sums; no partition or coverage premise is supplied. -/
theorem original_column_sum {C : Type*} [AddCommMonoid C]
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) (value : Wire a→C) :
    ((originalSideWires n F r a arity owner false packet assignment).map value).sum=
      ∑g : Fin r,((columnsOf n F r a arity owner i packet assignment g).map value).sum := by
  have hp := original_groups_perm n F r a arity owner i false packet assignment
  have hs := (hp.map value).sum_eq
  simp only [Bool.false_eq_true,ite_false] at hs
  rw [sum_flatMap_map] at hs
  rw [←List.ofFn_eq_map,List.sum_ofFn] at hs
  exact hs.symm

/-- Full original evaluated real-row form: the same-group column contribution
is retained literally, and every other actual source group is expanded over
all original tiles and strict mode orders. All column and crossing hypotheses
are derived from the actual graph, assignment restriction and replay routing. -/
theorem full_row_D12 (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
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
    ((originalSideWires n F r a arity owner false packet assignment).map
      (fun c => interpret ctx (baseTerm ctx z a t row c).words)).sum=
      ∑h : Fin r,if h=g then
        ((columnsOf n F r a arity owner i packet assignment h).map
          (fun c => interpret ctx (baseTerm ctx z a t row c).words)).sum
      else ∑tile : Fin (2^(i.val+1)),∑b∈Finset.range (ctx.precision-1),
        modeValue ctx z a i t row tile b*
          tilePower ctx a i (columnsOf n F r a arity owner i packet assignment h) tile.val b := by
  dsimp only
  rw [original_column_sum n F r a arity owner i packet assignment]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : h=g
  · simp only [hh,ite_true]
  · simp only [hh,ite_false]
    rw [columns_tiles ctx z a i t _ _ hpos hp]
    apply Finset.sum_congr rfl
    intro tile _
    exact original_cross_tile_D12 ctx z n F r a arity owner packet i g h hh rowEndpoint hr hrs
      rowBit assignment tile t hp ht hi

/-- Every actual source form outside its computed source group is zero. Empty
tiles are handled by the literal list sum, without an occupancy hypothesis. -/
theorem original_tilePower_zero (ctx : Context) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (h : Fin r) (assignment : Endpoint (n+F)→Bool)
    (tile : Fin (2^(i.val+1))) (b : ℕ)
    (hn : (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
      (SemiprimeSourceHistogramPortKeys.encodeKey h.val).bits) :
    tilePower ctx a i (columnsOf n F r a arity owner i packet assignment h) tile.val b=0 := by
  rw [tilePower_columns]
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
  by_cases helig : (c.bit && (c.slot.val%2^(i.val+1) == tile.val))=true
  · obtain ⟨e,he,hs,hwire⟩ := column_origin a _ assignment c hc
    have hlen := SemiprimeD1PacketEndpointOriginal.original_slot_length n F r a arity owner packet i h e he
    have hslot : c.slot.val=SemiprimeBitArithmetic.bitValue e.slot := by
      rw [hwire,wire_slot a e (assignment e) hlen]
    have hres : c.slot.val%2^(i.val+1)=tile.val := beq_iff_eq.mp (Bool.and_eq_true_iff.mp helig).2
    rw [hslot] at hres
    have ht : (⟨SemiprimeBitArithmetic.bitValue e.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩ : Fin (2^(i.val+1)))=tile :=
      Fin.ext hres
    have hsource := original_column_source n F r a arity owner packet i h e he hs
    dsimp only at hsource
    rw [ht] at hsource
    exact False.elim (hn hsource)
  · simp only [columnPower,helig,Bool.false_eq_true,ite_false]

/-- The actual other-end route target of a crossing original row is its acquired
group. This closes the target mask from replay data and the executed row test. -/
theorem original_row_target (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (tile : Fin (2^(i.val+1))) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true)
    (hn : (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).source≠
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits) :
    (SemiprimeD1ModeRoutingBits.acquire
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets[packet.val] a i tile).target=
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  obtain ⟨port,out,ho,hpacket,horigin⟩ :=
    SemiprimeD1PacketEndpointOriginal.endpoint_origin owner source packet i g endpoint he
  rcases horigin with ⟨heq,hrow⟩|⟨heq,hcolumn⟩
  · have hnum := (testColour_correct (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits i.val
      (SemiprimeD1PacketRows.read source.padding.source.selection.cache.rows.source.dictionary a out.source).left).mp hrow
    have hsc : SemiprimeSourceCompactBits.Compact (SemiprimeD1ModeRoutingBits.fromReplay source packet i tile).source :=
      (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner packet i tile).1
    have hx : (((SemiprimeD1ModeRoutingOriginal.actualRows source out).left[i.val]?).getD [])≠
        (SemiprimeD1ModeRoutingBits.fromReplay source packet i tile).source := by
      intro heq
      apply hn
      rw [←(SemiprimeD1ModeRoutingBits.fromReplay_data source packet i tile).1]
      apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hsc
        (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
      rw [←heq]
      exact hnum
    have ht := (SemiprimeD1ModeRoutingOriginal.row_target_original n F r a arity owner packet i tile out ho hpacket hx).2
    have htc := (SemiprimeD1ModeRoutingOriginal.route_palette n F r a arity owner packet i tile).2.2.1
    have htarget : (SemiprimeD1ModeRoutingBits.fromReplay source packet i tile).target=
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
      apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ htc
        (SemiprimeSourceHistogramPortKeys.encodeKey_compact g.val)
      rw [←ht]
      exact hnum
    rw [(SemiprimeD1ModeRoutingBits.fromReplay_data source packet i tile).2] at htarget
    exact htarget
  · rw [heq] at hside
    simp only [endpoints,Bool.false_eq_true] at hside

end
end RiemannGaussian.SemiprimeD1PacketGlobalRowForm
