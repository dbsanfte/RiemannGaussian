/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketSourceVector

/-! # Actual original source products use the global reconstructed vector
This identifies the executed local source bases, at their computed source
owners, with the same global values used by the actual affine-row evaluation.
-/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace RiemannGaussian.SemiprimeD1PacketSourceProductValues
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketSourceValues SemiprimeD1PacketSourceVector
open SemiprimeD1PacketGlobalRowForm SemiprimeD1PacketSourceAlignment
open SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1GlobalModeOwners SemiprimeD1GlobalModeFibres
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal acquired cache lookup at an original finite catalogue index. -/
theorem original_cache_entry (n F r a u p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r)
    (j : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length) :
    (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g).items[j.val]?=
      some (SemiprimeD1PacketModeMask.acquireOne (original n F r a arity owner) f i
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits
        (mode n F r a (cutoff n F r a u p arity owner i) arity owner i j)) := by
  let acquired := node n F r a u p arity owner i
  have hp : acquired.packets=original n F r a arity owner := rfl
  have hitems := SemiprimeD1PacketAffineRowEvaluation.fromModes_items acquired f i g
  simp only [hp] at hitems
  have hj : j.val<(SemiprimeD1ModeCatalog.catalog
      ((original n F r a arity owner).state.packets.length*2^(i.val+1)) (acquired.precision-1)).length := j.isLt
  have hg := congrArg (fun xs : List SemiprimeD1PacketModeMask.Item => xs[j.val]?) hitems
  simp only [List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some] at hg
  exact hg

/-- At an actual mode's computed source owner, its physically acquired source
base equals the original-derived global source vector, with no equality advice. -/
theorem sourceBase_owner (ctx : Context) (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (assignment : Endpoint (n+F)→Bool)
    (j : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length)
    (hpos : ctx.Positive) :
    let P := cutoff n F r a u p arity owner i
    let f := packet n F r a P arity owner i j
    let g := SemiprimeD1GlobalModeOwners.source n F r a P arity owner i j
    let cache := SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g
    SemiprimeD1PacketSourceProduct.sourceBase ctx a i (columnsOf n F r a arity owner i f assignment g) cache j.val=
      values ctx n F r a P arity owner i assignment j.val := by
  dsimp only
  rw [values_owner]
  rw [sourceBase_tilePower ctx a i _ _ j.val _ (original_cache_entry n F r a u p arity owner i _ _ j) hpos]
  rw [SemiprimeD1PacketCoefficientAlignment.acquireOne_tile,SemiprimeD1PacketModeMask.acquireOne_mode]
  rfl

/-- Every actual owned source base equals that same original global vector;
source-set membership derives both the original packet and colour owner. -/
theorem sourceBase_when_owned (ctx : Context) (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r)
    (assignment : Endpoint (n+F)→Bool) (j : ℕ)
    (hj : j∈SemiprimeD1PacketModeProjection.sourceSet
      (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g))
    (hpos : ctx.Positive) :
    SemiprimeD1PacketSourceProduct.sourceBase ctx a i
      (columnsOf n F r a arity owner i f assignment g)
      (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) j=
      values ctx n F r a (cutoff n F r a u p arity owner i) arity owner i assignment j := by
  have hl := SemiprimeD1PacketModeProjection.sourceSet_lt _ j hj
  rw [SemiprimeD1GlobalModeFamilies.cache_length] at hl
  let index : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length := ⟨j,hl⟩
  have hm := (source_mask n F r a u p arity owner i f g index).mp hj
  have hv := sourceBase_owner ctx n F r a u p arity owner i assignment index hpos
  dsimp only at hv
  rw [hm.1,hm.2] at hv
  exact hv

/-- The actual original-beta physical source product uses exactly the global
source values used in the original affine-row evaluation. No source base or
coefficient-query support/length answer is supplied by the original caller. -/
theorem original_source_product_values (ctx : Context) (n F r a u p : ℕ) [NeZero r]
    (arity : Fin F→ℕ) (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r)
    (assignment : Endpoint (n+F)→Bool) (beta : List ℕ)
    (hb : beta∈(node n F r a u p arity owner i).modes.values) (hpos : ctx.Positive) :
    let cache := SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g
    interpret ctx (SemiprimeD1PacketEntryBits.sourceProduct ctx a i
      (columnsOf n F r a arity owner i f assignment g) beta cache.items 0).words=
      beta.toFinsupp.prod (fun j exponent =>
        if j∈SemiprimeD1PacketModeProjection.sourceSet cache then
          (values ctx n F r a (cutoff n F r a u p arity owner i) arity owner i assignment j)^exponent else 1) := by
  dsimp only
  rw [SemiprimeD1PacketSourceProduct.original_source_product ctx n F r a u p arity owner i f g _ beta hb hpos]
  apply Finsupp.prod_congr
  intro j _
  by_cases hj : j∈SemiprimeD1PacketModeProjection.sourceSet
      (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g)
  · simp only [hj,ite_true]
    rw [sourceBase_when_owned ctx n F r a u p arity owner i f g assignment j hj hpos]
  · simp only [hj,ite_false]

end
end RiemannGaussian.SemiprimeD1PacketSourceProductValues
