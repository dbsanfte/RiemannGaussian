/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeIndexedNodeCertificate
import RiemannGaussian.SemiprimeMixedRadix
import RiemannGaussian.SemiprimeRowSelectionExecution

/-! # Source node designs with executed original-row selection and representatives -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeExecutedNodeDesign
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open SemiprimeLayoutSelection SemiprimeLayoutCertificates LayoutRowSelection LayoutExactBuckets
open SemiprimeIndexedNodeCertificate SemiprimeRowSelectionExecution
variable {I A E : Type} [Fintype A] [DecidableEq A] [Fintype E]
variable {owner : I → A} {factor : I → E} {r Q R : ℕ}

/-- Literal ordered coordinates of a computed source head. -/
def columns (L : Layout.Data (O := ℚ) (G := Fin r) owner factor Q R)
    (en : FiniteEnumeration A) (t : Fin Q) (g : Fin r) :=
  SemiprimeMixedRadix.filtered en (fun v => L.head t v=g)

/-- Head size from the actual filtered list, with no chosen finite equivalence. -/
def headSize (L : Layout.Data (O := ℚ) (G := Fin r) owner factor Q R)
    (en : FiniteEnumeration A) (t : Fin Q) (g : Fin r) : ℕ :=
  (en.values.filter (fun v => decide (L.head t v=g))).length

/-- Original integer matrix in its supplied ordered column coordinates. -/
def matrix (L : Layout.Data (O := ℚ) (G := Fin r) owner factor Q R)
    (en : FiniteEnumeration A) (t : Fin Q) (g : Fin r) :
    Fin (L.rowCount t g) → Fin (headSize L en t g) → ℤ :=
  fun j v => L.constraints t g j (columns L en t g v)

/-- The original selected integer rows, computed by the row-elimination loop. -/
def selection (L : Layout.Data (O := ℚ) (G := Fin r) owner factor Q R)
    (en : FiniteEnumeration A) (t : Fin Q) (g : Fin r) :=
  selectedRowsWithColumns (L.constraints t g) (columns L en t g)

/-- Actual indexed native design; only row-span proofs are noncomputational.
The selected integer IDs and representative words use the executed algorithms. -/
def data (L : Layout.Data (O := ℚ) (G := Fin r) owner factor Q R)
    (en : FiniteEnumeration A) (arity : E → ℕ)
    (incidence : (e : E) → Fin (arity e) → I)
    (hfactor : ∀ e i, factor (incidence e i)=e) (t : Fin Q) (W : Fin r → ℕ)
    (hW : ∀ g j v, |L.constraints t g j v|≤(W g : ℤ)) :
    Data arity (nodeRows L arity incidence t) where
  r := r
  h := headSize L en t
  m := fun g => (selectedIndices (matrix L en t g)).length
  W := W
  grouping := (Equiv.sigmaFiberEquiv (L.head t)).symm.trans
    (Equiv.sigmaCongrRight (fun g => (columns L en t g).symm))
  assigned := fun e => L.color e t
  C := fun g j v => L.constraints t g ((selection L en t g).select j) (columns L en t g v)
  bounded := fun g j v => hW g _ _
  span := by
    intro e i g hg
    have hl := killsIntegerKernel_of_rational_span (L.constraints t g)
      (fun j => L.constraints t g ((selection L en t g).select j))
      (selection L en t g).span
      (fun v => (L.row (incidence e i) v.val).eval (L.node t))
      (L.locality t (incidence e i) g (by simpa only [hfactor] using hg))
    obtain ⟨c,hc⟩ := row_span_of_integer_kernel _ _ hl
    exact ⟨c, fun v => hc (columns L en t g v)⟩

omit [Fintype E] in
/-- Computed selected counts equal actual original rational row ranks. -/
theorem selected_count (L : Layout.Data (O := ℚ) (G := Fin r) owner factor Q R)
    (en : FiniteEnumeration A) (t : Fin Q) (g : Fin r) :
    (selectedIndices (matrix L en t g)).length = LayoutRank.rowRank (L.constraints t g) := by
  have h := (selection L en t g).card_eq
  change Fintype.card (Fin (selectedIndices (matrix L en t g)).length) = _ at h
  simpa only [Fintype.card_fin] using h

#print axioms data
#print axioms selected_count
end RiemannGaussian.SemiprimeExecutedNodeDesign
