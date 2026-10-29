/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildTableOrder

/-! # Actual cached child table-order metadata scans
The constructor's native finite-tag tests/idxOf scans are all in its literal
report. This is not a unit-bit-cost assumption for arbitrary owner functions.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ChildOrderBudget
open SemiprimeD1ChildPortPullback SemiprimeD1ChildPortBijection

/-- Direct List.product spelling, before inserting concrete dependent metadata. -/
theorem product_length {A B : Type*} (xs : List A) (ys : List B) :
    (xs.product ys).length=xs.length*ys.length := List.length_product xs ys

/-- Resolving the acquired option list cannot create a typed endpoint. -/
theorem permutation_length {n F a : ℕ} {arity : Fin F→ℕ}
    (data : Acquired n F a arity) : (permutation data).value.length ≤ data.links.length := by
  change (resolveCache data.links).value.length ≤ data.links.length
  rw [resolveCache_value]
  exact List.length_filterMap_le _ _

/-- The actual resolved-cache report keeps its prepared source/data work. -/
theorem permutation_work {n F a : ℕ} {arity : Fin F→ℕ}
    (data : Acquired n F a arity) :
    (permutation data).work ≤ data.work+6*data.links.length+5 := by
  have h:=resolveCache_work data.links
  change data.work+(resolveCache data.links).work+3 ≤ _
  omega

/-- Fixed polynomial native scan overhead in original endpoints and acquired links. -/
def overhead (M L : ℕ) : ℕ := 12*L+14*M+(2*M)*(6*L+5)+15

/-- Original-order cache and searched output each have at most two entries per
original occurrence, without a permutation or successful-search assumption. -/
theorem order_length {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : Acquired n F a arity) (v : Fin (n+F)) :
    (SemiprimeD1ChildTableOrder.acquire owner data v).order.length ≤
      2*data.source.padding.source.selection.cache.data.metadata.incidences.length := by
  rw [SemiprimeD1ChildTableOrder.order_length]
  have h:=List.length_filter_le
    (fun t=>decide (SemiprimeD1ChildPortBijection.linkVertex owner t=v))
    (data.source.padding.source.selection.cache.data.metadata.incidences.product [true,false])
  have hp:=product_length data.source.padding.source.selection.cache.data.metadata.incidences [true,false]
  simp only [List.length_cons,List.length_nil] at hp
  change ((data.source.padding.source.selection.cache.data.metadata.incidences.product [true,false]).filter _).length ≤ _
  exact h.trans (by omega)

/-- Actual per-vertex order acquisition, retaining the complete prepared data report. -/
theorem acquire_clock {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : Acquired n F a arity) (v : Fin (n+F)) :
    (SemiprimeD1ChildTableOrder.acquire owner data v).clock ≤ data.work+
      overhead data.source.padding.source.selection.cache.data.metadata.incidences.length data.links.length := by
  let all:=data.source.padding.source.selection.cache.data.metadata.incidences.product [true,false]
  let pulled:=permutation data
  let old:=all.filter (fun t=>decide (linkVertex owner t=v))
  let child:=pulled.value.filter (fun t=>decide (linkVertex owner t=v))
  have hp:=permutation_work data
  have hl:=permutation_length data
  have ha : all.length=2*data.source.padding.source.selection.cache.data.metadata.incidences.length := by
    simp only [all,product_length,List.length_cons,List.length_nil]
    omega
  have ho : old.length ≤ 2*data.source.padding.source.selection.cache.data.metadata.incidences.length :=
    (List.length_filter_le _ _).trans ha.le
  have hc : child.length ≤ data.links.length:=(List.length_filter_le _ _).trans hl
  have hm:=Nat.mul_le_mul ho (show 6*child.length+5 ≤ 6*data.links.length+5 by omega)
  change pulled.work+6*all.length+6*pulled.value.length+
    old.length*(6*child.length+5)+(old.map (fun t=>child.idxOf t)).length+10 ≤ _
  rw [List.length_map,ha]
  change pulled.work ≤ _ at hp
  change pulled.value.length ≤ _ at hl
  unfold overhead
  omega

/-- Increasing the counted metadata dimensions preserves the explicit ledger. -/
theorem overhead_mono {M L M' L' : ℕ} (hm : M ≤ M') (hl : L ≤ L') : overhead M L ≤ overhead M' L' := by
  unfold overhead
  gcongr

end RiemannGaussian.SemiprimeD1ChildOrderBudget
