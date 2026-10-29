/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketGlobalRowForm
import RiemannGaussian.SemiprimeD1GlobalModeFamilies

/-! # Finite reindexing of the literal global catalogue
The actual order-major mode catalogue is bijective with its order/slot grid.
This is an erased finite-sum identity, not another catalogue constructor or a
runtime permutation supplied by the caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1PacketCatalogueReindex
open scoped BigOperators
open SemiprimeD1ModeCatalog
noncomputable section

/-- Original catalogue membership gives its explicit order and flattened slot. -/
def memberGrid (slots P : ℕ) : {m : Mode // m∈catalog slots P} ≃ Fin P × Fin slots where
  toFun m := ⟨⟨m.val.order,((mem_catalog slots P m.val).mp m.property).2⟩,
    ⟨m.val.slot,((mem_catalog slots P m.val).mp m.property).1⟩⟩
  invFun q := ⟨⟨q.2.val,q.1.val⟩,(mem_catalog slots P _).mpr ⟨q.2.isLt,q.1.isLt⟩⟩
  left_inv m := by apply Subtype.ext; rfl
  right_inv q := by cases q; rfl

/-- Computed finite position view of every actual global catalogue index. -/
def grid (slots P : ℕ) : Fin (catalog slots P).length ≃ Fin P × Fin slots :=
  (List.Nodup.getEquiv (catalog slots P) (catalog_nodup slots P)).trans (memberGrid slots P)

/-- The finite position view preserves the exact original mode label. -/
theorem grid_label (slots P : ℕ) (j : Fin (catalog slots P).length) :
    (catalog slots P)[j.val]=⟨(grid slots P j).2.val,(grid slots P j).1.val⟩ := by
  rfl

/-- Exact order-major/flattened-slot sum for the actual catalogue, with no
catalogue cardinality or mode lookup supplied as an assumption. -/
theorem sum_grid {A : Type*} [AddCommMonoid A] (slots P : ℕ) (f : Mode→A) :
    (∑j : Fin (catalog slots P).length,f (catalog slots P)[j.val])=
      ∑b : Fin P,∑s : Fin slots,f ⟨s.val,b.val⟩ := by
  calc
    _ = ∑q : Fin P × Fin slots,f ⟨q.2.val,q.1.val⟩ :=
      Fintype.sum_equiv (grid slots P) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

/-- Flattened slot reconstruction uses the same packet-major/tile-minor code
as the actual mode classifier. -/
theorem sum_packet_tiles {A : Type*} [AddCommMonoid A] (packets tiles P : ℕ) (f : Mode→A) :
    (∑j : Fin (catalog (packets*tiles) P).length,f (catalog (packets*tiles) P)[j.val])=
      ∑b : Fin P,∑packet : Fin packets,∑tile : Fin tiles,
        f ⟨tile.val+tiles*packet.val,b.val⟩ := by
  rw [sum_grid]
  apply Finset.sum_congr rfl
  intro b _
  have h := Equiv.sum_comp finProdFinEquiv (fun s : Fin (packets*tiles) => f ⟨s.val,b.val⟩)
  rw [Fintype.sum_prod_type] at h
  exact h.symm

end
end RiemannGaussian.SemiprimeD1PacketCatalogueReindex
