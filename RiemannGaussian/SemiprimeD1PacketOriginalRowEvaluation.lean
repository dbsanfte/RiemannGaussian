/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketRowCatalogueEvaluation

/-! # Original Boolean row equals the acquired affine row evaluation
The source vector is reconstructed from actual original source-group columns.
The false row bit gives the literal complement, including every nonlocal mode
sign. Original descriptor acquisition discharges the cache-shape premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace RiemannGaussian.SemiprimeD1PacketOriginalRowEvaluation
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketSourceValues SemiprimeD1PacketSourceVector SemiprimeD1PacketGlobalRowForm
open SemiprimeD1PacketRowExpansion SemiprimeD1ChildGraph
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual original real-row value under one common endpoint assignment. -/
def originalRow (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (rowEndpoint : Endpoint (n+F)) (bit : Bool) (assignment : Endpoint (n+F)→Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) : Carrier ctx :=
  let row := (wire a rowEndpoint bit).1
  let total := ((SemiprimeD1PacketColumnPartition.originalSideWires n F r a arity owner false packet assignment).map
    (fun c => interpret ctx (baseTerm ctx z a t row c).words)).sum
  if bit then total else 1-total

/-- Pointwise original row/actual affine-recipe identity. The temporary generic
cache equation is discharged by the actual original acquisition endpoint. -/
theorem recipe_matches_original (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true) (bit : Bool) (assignment : Endpoint (n+F)→Bool)
    (cache : SemiprimeD1PacketModeMask.Cache)
    (hcache : cache.items=(SemiprimeD1GlobalModeOwners.modes n F r a (ctx.precision-1) arity owner i).map
      (SemiprimeD1PacketModeMask.acquireOne
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits))
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let row := (wire a endpoint bit).1
    let columns := columnsOf n F r a arity owner i packet assignment g
    MvPolynomial.eval (values ctx n F r a (ctx.precision-1) arity owner i assignment)
      (SemiprimeD1AffineCoefficient.rowPolynomial cache.items.length
        (SemiprimeD1JetAffineCoefficient.rowValue ctx (recipe ctx z a i t row columns cache.items).value))=
      originalRow ctx z n F r a arity owner packet endpoint bit assignment t := by
  dsimp only
  rw [SemiprimeD1PacketRowCatalogueEvaluation.recipe_catalogue ctx z n F r a (ctx.precision-1)
    arity owner packet i g endpoint he hside bit assignment cache hcache t hpos hp ht hi]
  rw [SemiprimeD1PacketEntryComponents.rowBase_value ctx z a t _ _ hpos]
  have hfull := full_row_source ctx z n F r a arity owner packet i g endpoint he hside bit assignment t hpos hp ht hi
  have hbit : (wire a endpoint bit).1.bit=bit := (wire_data a endpoint bit).1
  rw [hbit]
  cases bit
  · simp only [Bool.false_eq_true,ite_false] at hfull ⊢
    unfold originalRow
    simp only [Bool.false_eq_true,ite_false]
    have hneg : (∑tile : Fin (2^(i.val+1)),∑b∈Finset.range (ctx.precision-1),
        if sourceGroup n F r a arity owner packet i tile=g then 0 else
          (-modeValue ctx z a i t (wire a endpoint false).1 tile b)*
            sourceForm ctx n F r a arity owner packet i assignment tile b)=
        -(∑tile : Fin (2^(i.val+1)),∑b∈Finset.range (ctx.precision-1),
          if sourceGroup n F r a arity owner packet i tile=g then 0 else
            modeValue ctx z a i t (wire a endpoint false).1 tile b*
              sourceForm ctx n F r a arity owner packet i assignment tile b) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro tile _
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hs : sourceGroup n F r a arity owner packet i tile=g
      · simp only [hs,ite_true,neg_zero]
      · simp only [hs,ite_false]
        ring
    rw [hneg,hfull]
    ring
  · simp only [ite_true] at hfull ⊢
    unfold originalRow
    simp only [ite_true]
    exact hfull.symm

/-- Closed original acquired-row endpoint. The actual fromModes constructor
supplies the complete descriptor cache; only the actual node precision equality
and original public grid/axis conditions remain. No cache, coefficient,
source-form, mask, or intermediate-fit answer is supplied by the caller. -/
theorem original_recipe_matches (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (i : Fin a) (g : Fin r) (endpoint : Endpoint (n+F))
    (he : endpoint∈((acquire n F r a arity owner i g).factors[packet.val]?).getD [])
    (hside : endpoint.side=true) (bit : Bool) (assignment : Endpoint (n+F)→Bool)
    (hprecision : ctx.precision=(SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i).precision)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (hpos : ctx.Positive) (hp : 0<ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    let source := SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i
    let cache := SemiprimeD1PacketModeMask.fromModes source packet i g
    let row := (wire a endpoint bit).1
    let columns := columnsOf n F r a arity owner i packet assignment g
    MvPolynomial.eval (values ctx n F r a (ctx.precision-1) arity owner i assignment)
      (SemiprimeD1AffineCoefficient.rowPolynomial cache.items.length
        (SemiprimeD1JetAffineCoefficient.rowValue ctx (recipe ctx z a i t row columns cache.items).value))=
      originalRow ctx z n F r a arity owner packet endpoint bit assignment t := by
  let source := SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i
  let cache := SemiprimeD1PacketModeMask.fromModes source packet i g
  have hitems := SemiprimeD1PacketAffineRowEvaluation.fromModes_items source packet i g
  have hprec : source.precision=ctx.precision := hprecision.symm
  have hpackets : source.packets=SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner := rfl
  have hfun : SemiprimeD1PacketModeMask.acquireOne source.packets packet i
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits=
      SemiprimeD1PacketModeMask.acquireOne (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits := by
    funext mode
    rfl
  rw [hfun] at hitems
  have hcache : cache.items=(SemiprimeD1GlobalModeOwners.modes n F r a (ctx.precision-1) arity owner i).map
      (SemiprimeD1PacketModeMask.acquireOne
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner) packet i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits) := by
    simpa only [SemiprimeD1GlobalModeOwners.modes,SemiprimeD1GlobalModeOwners.original,hprec,hpackets] using hitems
  exact recipe_matches_original ctx z n F r a arity owner packet i g endpoint he hside bit assignment
    cache hcache t hpos hp ht hi

end
end RiemannGaussian.SemiprimeD1PacketOriginalRowEvaluation
