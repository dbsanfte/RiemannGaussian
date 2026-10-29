/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLayoutCertificates
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutInterface
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutRowSelection
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank

/-!
# Actual integer-row selection and source-layout node certificates

Rows are selected from the supplied integer matrix, preserving literal heights.
Exact kernel locality survives selection, and the explicit box/scan adapter
constructs the counter certificate. This is not a primitive row-selection cost theorem.
-/
namespace RiemannGaussian.SemiprimeLayoutSelection
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LayoutExactBuckets LayoutRowSelection
open RiemannGaussian.SemiprimeLayoutCertificates
open RiemannGaussian.SemiprimeCounterCompose
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A basis chosen among actual integer rows, without coefficient rescaling. -/
structure SelectedRows {J V : Type} [Fintype J] [Fintype V] (C : J → V → ℤ) where
  /-- Finite indices of the selected original rows. -/
  Index : Type
  /-- Actual enumeration of selected indices. -/
  [finite : Fintype Index]
  /-- Index map into the original integer matrix. -/
  select : Index → J
  /-- No row is selected twice. -/
  injective : Function.Injective select
  /-- Every old row is in the rational span of the selected rows. -/
  span : RationalRowSpan C (fun k => C (select k))
  /-- Number of selected rows equals the true rational row rank. -/
  card_eq : Fintype.card Index = LayoutRank.rowRank C

attribute [instance] SelectedRows.finite

/-- Apply the source's actual-row basis theorem, not an assumed rank witness. -/
def selectRows {J V : Type} [Fintype J] [Fintype V] (C : J → V → ℤ) : SelectedRows C := by
  apply Classical.choice
  obtain ⟨K,hK,s,hs,hspan,hcard⟩ := exists_actual_row_basis C
  let _ := hK
  exact ⟨{ Index := K, select := s, injective := hs, span := hspan, card_eq := hcard }⟩

theorem selected_height {J V : Type} [Fintype J] [Fintype V]
    (C : J → V → ℤ) (W : ℕ) (hC : ∀ j v, |C j v| ≤ (W : ℤ)) :
    ∀ k v, |C ((selectRows C).select k) v| ≤ (W : ℤ) := fun k v => hC ((selectRows C).select k) v

theorem selected_locality {J V : Type} [Fintype J] [Fintype V]
    (C : J → V → ℤ) (a : V → ℚ) (ha : KillsIntegerKernel a C) :
    KillsIntegerKernel a (fun k => C ((selectRows C).select k)) :=
  killsIntegerKernel_of_rational_span C _ (selectRows C).span a ha

variable {I V E G : Type} [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G]
variable {owner : I → V} {factor : I → E} {Q R : ℕ}

/-- The selected row family at each actual source head. -/
def headSelection (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (t : Fin Q) (g : G) : SelectedRows (L.constraints t g) := selectRows _

/-- Actual source rows, reindexed by physical tensor ports and evaluated at a node. -/
def nodeRows (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I) (t : Fin Q) :
    (e : E) → Fin (arity e) → V → ℚ :=
  fun e i v => (L.row (incidence e i) v).eval (L.node t)

/-- Full certificate from a source Layout.Data and literal row-height bound.
The off-group row spans are derived from its integer-kernel locality. -/
def nodeCertificate (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i) = e) (t : Fin Q) (W : G → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v| ≤ (W g : ℤ)) :
    NodeCertificate arity (nodeRows L arity incidence t) :=
  ofIntegerConstraints arity (nodeRows L arity incidence t)
    (fun g => {v : V // L.head t v = g}) (Equiv.sigmaFiberEquiv (L.head t)).symm
    (fun e => L.color e t) (fun g => (headSelection L t g).Index)
    (fun g k v => L.constraints t g ((headSelection L t g).select k) v) W
    (fun g k v => hW g _ v)
    (by
      intro e i g hg z hz
      have hloc := selected_locality (L.constraints t g)
        (fun v => (L.row (incidence e i) v.val).eval (L.node t))
        (L.locality t (incidence e i) g (by simpa only [hfactor] using hg))
      exact hloc z hz)

/-- Actual finite enumeration of the selected source row indices. -/
instance nodeCertificateIndexFinite
    (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i) = e) (t : Fin Q) (W : G → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v| ≤ (W g : ℤ)) (g : G) :
    Fintype ((nodeCertificate L arity incidence hfactor t W hW).Index g) :=
  (headSelection L t g).finite

/-- Actual finite signed-box enumeration of one source head. -/
instance nodeCertificateSummaryFinite
    (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i) = e) (t : Fin Q) (W : G → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v| ≤ (W g : ℤ)) (g : G) :
    Fintype ((nodeCertificate L arity incidence hfactor t W hW).Summary g) :=
  inferInstanceAs (Fintype (Summary {v : V // L.head t v=g} (headSelection L t g).Index (W g)))

/-- Explicit product enumeration for the certificate's stored summary types. -/
instance nodeCertificateTupleFinite
    (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i) = e) (t : Fin Q) (W : G → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v| ≤ (W g : ℤ)) :
    Fintype ((g : G) → (nodeCertificate L arity incidence hfactor t W hW).Summary g) :=
  @Pi.instFintype G _ inferInstance inferInstance
    (fun g => nodeCertificateSummaryFinite L arity incidence hfactor t W hW g)

/-- Selected index cardinalities are exactly the source rational ranks. -/
theorem nodeCertificate_index_card
    (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i) = e) (t : Fin Q) (W : G → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v| ≤ (W g : ℤ)) (g : G) :
    Fintype.card ((nodeCertificate L arity incidence hfactor t W hW).Index g) =
      LayoutRank.rowRank (L.constraints t g) := (headSelection L t g).card_eq

/-- Exact whole-summary enumeration bound after actual row selection. -/
theorem nodeCertificate_summary_card
    (L : Layout.Data (O := ℚ) (G := G) owner factor Q R)
    (arity : E → ℕ) (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i) = e) (t : Fin Q) (W : G → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v| ≤ (W g : ℤ)) :
    Fintype.card ((g : G) → (nodeCertificate L arity incidence hfactor t W hW).Summary g) =
      ∏ g, (2*(Fintype.card {v : V // L.head t v = g} * W g)+1)^
        (LayoutRank.rowRank (L.constraints t g)) := by
  have h := grouped_summary_card (fun g => {v : V // L.head t v = g})
    (fun g => (headSelection L t g).Index) W
  calc
    _ = Fintype.card ((g : G) → Summary {v : V // L.head t v = g}
        (headSelection L t g).Index (W g)) := Fintype.card_congr (Equiv.refl _)
    _ = _ := by
      simp_rw [(headSelection L t _).card_eq] at h
      simpa only [← Nat.card_eq_fintype_card] using h

#print axioms nodeCertificate
#print axioms nodeCertificate_index_card
#print axioms nodeCertificate_summary_card
end
end RiemannGaussian.SemiprimeLayoutSelection
