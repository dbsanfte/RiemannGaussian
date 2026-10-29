/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeLookup
import RiemannGaussian.SemiprimeD1OriginalStateResources

/-! # Actual original-network inventory bounds for tensor tape lookup
The sequential operation is proved first on literal data. Only then is the
actual inherited network inventory used to bound its serialization and scans.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1TensorTapeOriginal
open SemiprimeD1TensorTables SemiprimeD1TensorTapeCodec SemiprimeD1TensorTapeLookup
open SemiprimeD1TensorNetwork SemiprimeD1NetworkStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1OriginalStateResources

/-- A repeated list occurrence still contributes its full nonnegative inventory. -/
theorem member_le_sum {A : Type*} (xs : List A) (f : A → ℕ) (x : A) (hx : x∈xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x; simp only [List.map_cons,List.sum_cons];omega
    · have ht:=ih h
      simp only [List.map_cons,List.sum_cons];omega

/-- Any actual stored tensor's tape fits the actual whole-network inventory. -/
theorem vertex_tape_le (net : Network) (v : SemiprimeD1LeafCounter.Vertex)
    (hv : v∈vertices net) : (tape v.table).length ≤ inventory net := by
  have ht:=tape_le_storage v.table
  have hm:=member_le_sum (vertices net) (fun w => storage w.table+w.ports.length+1) v hv
  unfold inventory
  omega

/-- Literal serialization and sequential reading cost a fixed inventory polynomial. -/
theorem vertex_clock (net : Network) (v : SemiprimeD1LeafCounter.Vertex)
    (hv : v∈vertices net) (bits : List Bool) :
    (fromTable v.table bits).clock ≤ 8*(inventory net+1)*inventory net+4 := by
  apply (fromTable_storage_clock v.table bits).trans
  have h:=vertex_tape_le net v hv
  gcongr

/-- Actual reachable original states supply all storage caps, not a memory oracle. -/
theorem bound_clock (s : ℕ) (call : Call) (hb : Bound s call)
    (v : SemiprimeD1LeafCounter.Vertex) (hv : v∈vertices call.net) (bits : List Bool) :
    (fromTable v.table bits).clock ≤ 8*(inventoryCap s+1)*inventoryCap s+4 := by
  apply (vertex_clock call.net v hv bits).trans
  have h:=hb.inventory
  gcongr

/-- Every original N/prefix reachable literal tensor has the same closed tape path. -/
theorem eventually_original : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0<N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) (next : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) next →
      ∀ (v : SemiprimeD1LeafCounter.Vertex), v∈vertices next.net → ∀ bits : List Bool,
      (fromTable v.table bits).clock ≤
        8*(inventoryCap (SemiprimeD1PublicPackingReady.scale ell)+1)*
          inventoryCap (SemiprimeD1PublicPackingReady.scale ell)+4 := by
  filter_upwards [SemiprimeD1OriginalStateResources.eventually_original] with ell hell
  intro N hN hEll fixed next hr v hv bits
  exact bound_clock _ next (hell N hN hEll fixed next hr) v hv bits

end RiemannGaussian.SemiprimeD1TensorTapeOriginal
