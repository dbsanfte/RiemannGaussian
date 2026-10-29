/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketSourceVector
import RiemannGaussian.SemiprimeD1PacketPolynomialSupport

/-! # Original row modes in the actual global catalogue grid
The computed global source values and actual physical coefficient masks are
aligned at every original packet/tile/order label. These statements bind
executed suppliers; no coefficient or source-value answer is a hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace RiemannGaussian.SemiprimeD1PacketRowCatalogueEvaluation
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketCoefficientAlignment SemiprimeD1PacketSourceVector SemiprimeD1PacketSourceValues
open SemiprimeD1PacketRowExpansion SemiprimeD1PacketGlobalRowForm
open SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- One actual global catalogue coordinate contributes only to its actual
packet, and only when the original source group differs from the row group. -/
theorem coefficient_grid (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet other : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true) (bit : Bool) (tile : Fin (2^(i.val+1))) (b : ℕ)
    (assignment : Endpoint (n+F)→Bool) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
    let mode : SemiprimeD1ModeCatalog.Mode := ⟨tile.val+2^(i.val+1)*other.val,b⟩
    let row := (wire a endpoint bit).1
    interpret ctx (coefficient ctx z a i t row
      (SemiprimeD1PacketModeMask.acquireOne source packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode)).words*
      modeBase ctx n F r a arity owner i assignment mode=
    if other=packet then
      if sourceGroup n F r a arity owner packet i tile=g then 0 else
        (if bit then modeValue ctx z a i t row tile b else -modeValue ctx z a i t row tile b)*
          sourceForm ctx n F r a arity owner packet i assignment tile b
    else 0 := by
  let source := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  let mode : SemiprimeD1ModeCatalog.Mode := ⟨tile.val+2^(i.val+1)*other.val,b⟩
  let row := (wire a endpoint bit).1
  have hd : mode.slot/2^(i.val+1)=other.val := by
    change (tile.val+2^(i.val+1)*other.val)/2^(i.val+1)=other.val
    rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt tile.isLt,Nat.zero_add]
  have hm : mode.slot%2^(i.val+1)=tile.val := by
    change (tile.val+2^(i.val+1)*other.val)%2^(i.val+1)=tile.val
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt tile.isLt]
  change interpret ctx (coefficient ctx z a i t row
    (SemiprimeD1PacketModeMask.acquireOne source packet i _ mode)).words*
      modeBase ctx n F r a arity owner i assignment mode=_
  by_cases heq : other=packet
  · subst other
    have hc := coefficient_in_packet ctx z n F r a arity owner packet i g endpoint he hside bit mode
      hd t hpos hp ht hi
    dsimp only at hc
    have htile : (⟨mode.slot%2^(i.val+1),Nat.mod_lt _ (by positivity)⟩ : Fin (2^(i.val+1)))=tile := Fin.ext hm
    rw [htile] at hc
    rw [hc,modeBase_grid]
    by_cases hs : sourceGroup n F r a arity owner packet i tile=g
    · have hb := (sourceGroup_bytes n F r a arity owner packet i tile g).mp hs
      simp only [hb,hs,ite_true,zero_mul]
    · have hb : (SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).source≠
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
        intro hb
        exact hs ((sourceGroup_bytes n F r a arity owner packet i tile g).mpr hb)
      dsimp only [source] at hb
      have horder : mode.order=b := rfl
      simp only [hb,hs,horder,ite_false,ite_true]
  · have hn : mode.slot/2^(i.val+1)≠packet.val := by
      rw [hd]
      exact fun hv => heq (Fin.ext hv)
    have hf := SemiprimeD1PacketModeMask.acquireOne_other source packet i
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode hn
    have hz : ((SemiprimeD1PacketModeMask.acquireOne source packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode).inPacket &&
      (SemiprimeD1PacketModeMask.acquireOne source packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode).targetHere)=false := by
      rw [hf.1,Bool.false_and]
    rw [SemiprimeD1PacketPolynomialSupport.coefficient_zero ctx z a i t row _ hz,zero_mul]
    simp only [heq,ite_false]

/-- Evaluation in the literal original catalogue order, followed by the exact
packet/tile reindexing. The cache-shape premise is discharged by the actual
fromModes constructor at the original endpoint below. -/
theorem recipe_catalogue (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a P : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true) (bit : Bool) (assignment : Endpoint (n+F)→Bool)
    (cache : SemiprimeD1PacketModeMask.Cache)
    (hcache : cache.items=(SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i).map
      (SemiprimeD1PacketModeMask.acquireOne
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits))
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let row := (wire a endpoint bit).1
    let columns := columnsOf n F r a arity owner i packet assignment g
    MvPolynomial.eval (values ctx n F r a P arity owner i assignment)
      (SemiprimeD1AffineCoefficient.rowPolynomial cache.items.length
        (SemiprimeD1JetAffineCoefficient.rowValue ctx (recipe ctx z a i t row columns cache.items).value))=
      interpret ctx (rowBase ctx z a t row columns).words+
      ∑tile : Fin (2^(i.val+1)),∑b∈Finset.range P,
        if sourceGroup n F r a arity owner packet i tile=g then 0 else
          (if bit then modeValue ctx z a i t row tile b else -modeValue ctx z a i t row tile b)*
            sourceForm ctx n F r a arity owner packet i assignment tile b := by
  dsimp only
  rw [SemiprimeD1PacketAffineRowEvaluation.recipe_eval]
  congr 1
  have hlen : cache.items.length=(SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i).length := by
    rw [hcache,List.length_map]
  have hsum : (∑j : Fin cache.items.length,
      interpret ctx (coefficient ctx z a i t (wire a endpoint bit).1 cache.items[j.val]).words*
        values ctx n F r a P arity owner i assignment j.val)=
      ∑j : Fin (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i).length,
        interpret ctx (coefficient ctx z a i t (wire a endpoint bit).1
          (SemiprimeD1PacketModeMask.acquireOne
            (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
            (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
            (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i)[j.val])).words*
          values ctx n F r a P arity owner i assignment j.val := by
    apply Fintype.sum_equiv (finCongr hlen)
    intro j
    have hj : j.val<(SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i).length := by
      simpa only [←hlen] using j.isLt
    have hget := congrArg (fun xs : List SemiprimeD1PacketModeMask.Item => xs[j.val]?) hcache
    simp only [List.getElem?_eq_getElem j.isLt,List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some,
      Option.some.injEq] at hget
    change interpret ctx (coefficient ctx z a i t (wire a endpoint bit).1 cache.items[j.val]).words*
      values ctx n F r a P arity owner i assignment j.val=_
    rw [hget]
    rfl
  rw [hsum]
  have hv (j : Fin (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i).length) :
      values ctx n F r a P arity owner i assignment j.val=
      modeBase ctx n F r a arity owner i assignment
        (SemiprimeD1GlobalModeOwners.modes n F r a P arity owner i)[j.val] := by
    unfold values
    rw [List.getElem?_eq_getElem j.isLt]
  simp_rw [hv]
  let term := fun mode : SemiprimeD1ModeCatalog.Mode =>
    interpret ctx (coefficient ctx z a i t (wire a endpoint bit).1
      (SemiprimeD1PacketModeMask.acquireOne
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits mode)).words*
      modeBase ctx n F r a arity owner i assignment mode
  change (∑j : Fin (SemiprimeD1ModeCatalog.catalog
    ((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length*2^(i.val+1)) P).length,
    term (SemiprimeD1ModeCatalog.catalog
      ((SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length*2^(i.val+1)) P)[j.val])=_
  rw [SemiprimeD1PacketCatalogueReindex.sum_packet_tiles _ _ _ term]
  dsimp only [term]
  have hgrid : (∑b : Fin P,∑other : Fin
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length,
      ∑tile : Fin (2^(i.val+1)),
      interpret ctx (coefficient ctx z a i t (wire a endpoint bit).1
        (SemiprimeD1PacketModeMask.acquireOne
          (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
          (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
          ⟨tile.val+2^(i.val+1)*other.val,b.val⟩)).words*
        modeBase ctx n F r a arity owner i assignment ⟨tile.val+2^(i.val+1)*other.val,b.val⟩)=
      ∑b : Fin P,∑other : Fin
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length,
        ∑tile : Fin (2^(i.val+1)),if other=packet then
          (if sourceGroup n F r a arity owner packet i tile=g then 0 else
            (if bit then modeValue ctx z a i t (wire a endpoint bit).1 tile b.val else
              -modeValue ctx z a i t (wire a endpoint bit).1 tile b.val)*
              sourceForm ctx n F r a arity owner packet i assignment tile b.val) else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro other _
    apply Finset.sum_congr rfl
    intro tile _
    exact coefficient_grid ctx z n F r a arity owner packet other i g endpoint he hside bit tile b.val
      assignment t hpos hp ht hi
  rw [hgrid]
  have hpacket (b : Fin P) : (∑other : Fin
      (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length,
      ∑tile : Fin (2^(i.val+1)),if other=packet then
        (if sourceGroup n F r a arity owner packet i tile=g then 0 else
          (if bit then modeValue ctx z a i t (wire a endpoint bit).1 tile b.val else
            -modeValue ctx z a i t (wire a endpoint bit).1 tile b.val)*
            sourceForm ctx n F r a arity owner packet i assignment tile b.val) else 0)=
      ∑tile : Fin (2^(i.val+1)),if sourceGroup n F r a arity owner packet i tile=g then 0 else
        (if bit then modeValue ctx z a i t (wire a endpoint bit).1 tile b.val else
          -modeValue ctx z a i t (wire a endpoint bit).1 tile b.val)*
          sourceForm ctx n F r a arity owner packet i assignment tile b.val := by
    rw [Finset.sum_eq_single packet]
    · simp only [ite_true]
    · intro other _ hn
      simp only [hn,ite_false,Finset.sum_const_zero]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  simp_rw [hpacket]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tile _
  exact Fin.sum_univ_eq_sum_range (fun b : ℕ =>
    if sourceGroup n F r a arity owner packet i tile=g then (0 : Carrier ctx) else
      (if bit then modeValue ctx z a i t (wire a endpoint bit).1 tile b else
        -modeValue ctx z a i t (wire a endpoint bit).1 tile b)*
        sourceForm ctx n F r a arity owner packet i assignment tile b) P

end
end RiemannGaussian.SemiprimeD1PacketRowCatalogueEvaluation
