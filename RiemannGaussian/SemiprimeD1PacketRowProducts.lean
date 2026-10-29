/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketOriginalRowEvaluation
import RiemannGaussian.SemiprimeD1PacketPolynomialAcquired
import RiemannGaussian.SemiprimeD1ChildAssignmentEndpoint

/-! # Product of actual original packet/group affine rows
All row and column lists come from actual acquired child buckets under one
common endpoint assignment. The original constructor supplies every cache;
no row-polynomial family or source-value vector is a caller input.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace RiemannGaussian.SemiprimeD1PacketRowProducts
open scoped BigOperators
open SemiprimeD1PacketEntryInputs SemiprimeD1PacketEntryBits
open SemiprimeD1PacketGlobalRowForm SemiprimeD1PacketColumnPartition
open SemiprimeD1PacketOriginalRowEvaluation SemiprimeD1PacketSourceVector
open SemiprimeD1ChildGraph SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual target-group row inventory under the common endpoint assignment. -/
def rowsOf (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) (g : Fin r) : List (Wire a) :=
  let bucket := ((acquire n F r a arity owner i g).factors[packet.val]?).getD []
  (gather a bucket (bucket.map assignment)).rows

/-- Original Boolean row value, read at an actual acquired wire. -/
def wireRowValue (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a) : Carrier ctx :=
  let total := ((originalSideWires n F r a arity owner false packet assignment).map
    (fun c => interpret ctx (baseTerm ctx z a t row c).words)).sum
  if row.bit then total else 1-total

/-- The actual original packet/group polynomial, constructed from literal
acquired row recipes, source columns and global descriptor cache. -/
def packetPolynomial (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (g : Fin r) (assignment : Endpoint (n+F)→Bool) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) :
    MvPolynomial ℕ (Carrier ctx) :=
  SemiprimeD1PacketPolynomialAcquired.polynomial ctx z a i t
    (columnsOf n F r a arity owner i packet assignment g)
    (rowsOf n F r a arity owner i packet assignment g)
    (SemiprimeD1PacketModeMask.fromModes (SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i) packet i g)

/-- Every actual acquired row retains its original endpoint and assigned bit. -/
theorem row_origin {V : ℕ} (a : ℕ) (bucket : List (Endpoint V))
    (assignment : Endpoint V→Bool) (row : Wire a)
    (hr : row∈(gather a bucket (bucket.map assignment)).rows) :
    ∃e∈bucket,e.side=true ∧ row=(wire a e (assignment e)).1 := by
  rw [(gather_assignment a bucket assignment).1] at hr
  obtain ⟨e,he,hval⟩ := List.mem_filterMap.mp hr
  cases hs : e.side
  · simp only [hs,Bool.false_eq_true,ite_false,reduceCtorEq] at hval
  · simp only [hs,ite_true,Option.some.injEq] at hval
    exact ⟨e,he,hs,hval.symm⟩

/-- Evaluation of the actual packet/group polynomial is the product of its
actual original real-row values, including false-bit complements. -/
theorem packet_eval (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (g : Fin r) (assignment : Endpoint (n+F)→Bool) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : ctx.precision=(SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i).precision)
    (hpos : ctx.Positive) (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    MvPolynomial.eval (values ctx n F r a (ctx.precision-1) arity owner i assignment)
      (packetPolynomial ctx z n F r a u p arity owner i packet g assignment t)=
      ((rowsOf n F r a arity owner i packet assignment g).map
        (wireRowValue ctx z n F r a arity owner packet assignment t)).prod := by
  unfold packetPolynomial SemiprimeD1PacketPolynomialAcquired.polynomial SemiprimeD1AffineCoefficient.polynomial
  rw [map_list_prod]
  simp only [SemiprimeD1PacketEntryValue.recipes_value,List.map_map,Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro row hr
  obtain ⟨e,he,hs,hrow⟩ := row_origin a _ assignment row hr
  subst row
  have h := original_recipe_matches ctx z n F r a u p arity owner packet i g e he hs (assignment e)
    assignment hprecision t hpos hp ht hi
  simpa only [wireRowValue,originalRow,(wire_data a e (assignment e)).1] using h

/-- Finite products over literal group-list traversals retain all occurrences. -/
theorem prod_flatMap_map {A B C : Type*} [CommMonoid C]
    (xs : List A) (f : A→List B) (value : B→C) :
    ((xs.flatMap f).map value).prod=(xs.map (fun x => ((f x).map value).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons,ih]

/-- All actual group polynomials multiply to the full original packet row
product. The acquired partition preserves every repeated real occurrence. -/
theorem packet_groups_eval (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (i : Fin a)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length)
    (assignment : Endpoint (n+F)→Bool) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : ctx.precision=(SemiprimeD1GlobalModeFibres.node n F r a u p arity owner i).precision)
    (hpos : ctx.Positive) (hp : 0<ctx.precision) (ht : SemiprimeD1WireKernelOriginal.point a t.val≠0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val)=i.val) :
    MvPolynomial.eval (values ctx n F r a (ctx.precision-1) arity owner i assignment)
      (∏g : Fin r,packetPolynomial ctx z n F r a u p arity owner i packet g assignment t)=
      ((originalSideWires n F r a arity owner true packet assignment).map
        (wireRowValue ctx z n F r a arity owner packet assignment t)).prod := by
  rw [map_prod]
  simp_rw [packet_eval ctx z n F r a u p arity owner i packet _ assignment t hprecision hpos hp ht hi]
  have h := (original_groups_perm n F r a arity owner i true packet assignment).map
    (wireRowValue ctx z n F r a arity owner packet assignment t)
  have hh := h.prod_eq
  simp only [ite_true] at hh
  rw [prod_flatMap_map,←List.ofFn_eq_map,List.prod_ofFn] at hh
  exact hh

end
end RiemannGaussian.SemiprimeD1PacketRowProducts
