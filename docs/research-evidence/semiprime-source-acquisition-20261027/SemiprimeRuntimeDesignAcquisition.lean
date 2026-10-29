/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNodeArrayExecution
import RiemannGaussian.SemiprimeMixedRadix
import RiemannGaussian.SemiprimeRowSelectionExecution

/-!
# Acquire a runtime node design from raw integer constraints

The runtime input contains no Layout.Data or polynomial-valued index. Selection
uses the existing executed rational pivoting algorithm, retaining original
integer row IDs. All selected integer entries are subsequently cached in arrays.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeRuntimeDesignAcquisition
open scoped BigOperators
open SemiprimeNodeArrayExecution SemiprimeRowSelectionExecution
open SemiprimeIndexedNodeCertificate

/-- Pure raw integer design data produced before row selection. -/
structure RawDesign (n F : ℕ) where
  /-- Number of groups. -/
  r : ℕ
  /-- Public group of every Boolean coordinate. -/
  head : Fin n → Fin r
  /-- Group owning each local factor. -/
  assigned : Fin F → Fin r
  /-- Number of original candidate integer constraints per group. -/
  count : Fin r → ℕ
  /-- Literal global-coordinate integer rows. -/
  rows : (g : Fin r) → Fin (count g) → Fin n → ℤ
  /-- Bounds retained by original selected rows. -/
  W : Fin r → ℕ

/-- The explicit filtered column order of a raw group. -/
def columns {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) :=
  SemiprimeMixedRadix.filtered (SemiprimeFiniteEnumerations.fin n) (fun v => d.head v=g)

/-- Actual number of columns of a raw group. -/
def headSize {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) : ℕ :=
  ((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))).length

/-- The finite integer matrix actually passed to rational pivoting. -/
def matrix {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) :
    Fin (d.count g) → Fin (headSize d g) → ℤ :=
  fun j v => d.rows g j (columns d g v)

/-- Executed original-row selection on the explicit column order. -/
def selection {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) :=
  selectedRowsWithColumns (fun j (v : {v : Fin n // d.head v=g}) => d.rows g j v.val) (columns d g)

/-- Runtime-only design before caching its selected measurement table. -/
def uncache {n F : ℕ} (d : RawDesign n F) : RuntimeDesign n F where
  r := d.r
  h := headSize d
  m := fun g => (selectedIndices (matrix d g)).length
  W := d.W
  grouping := (Equiv.sigmaFiberEquiv d.head).symm.trans
    (Equiv.sigmaCongrRight (fun g => (columns d g).symm))
  assigned := d.assigned
  C := fun g j v => d.rows g ((selection d g).select j) (columns d g v)

/-- Cache every selected integer entry once; callback reads use retained arrays. -/
def cache {n F : ℕ} (d : RuntimeDesign n F) : RuntimeDesign n F :=
  let values := Array.ofFn (fun g : Fin d.r => Array.ofFn (fun j : Fin (d.m g) =>
    Array.ofFn (fun v : Fin (d.h g) => d.C g j v)))
  { d with C := fun g j v =>
      ((values[g.val]'(by simp [values]))[j.val]'(by simp [values]))[v.val]'(by simp [values]) }

/-- Acquired selected measurements have exactly their original integer values. -/
theorem cache_C {n F : ℕ} (d : RuntimeDesign n F) (g : Fin d.r)
    (j : Fin (d.m g)) (v : Fin (d.h g)) : (cache d).C g j v=d.C g j v := by
  simp only [cache, Array.getElem_ofFn]

/-- Raw integer rows to a polynomial-free, selected and cached runtime design. -/
def build {n F : ℕ} (d : RawDesign n F) : RuntimeDesign n F := cache (uncache d)

/-- Selection cardinality is the actual original rational rank on this head. -/
theorem selected_count {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) :
    (build d).m g = OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank
      (fun j (v : {v : Fin n // d.head v=g}) => d.rows g j v.val) := by
  have h := (selection d g).card_eq
  change Fintype.card (Fin (selectedIndices (matrix d g)).length) = _ at h
  change (selectedIndices (matrix d g)).length = _
  simpa only [Fintype.card_fin] using h

/-- Cached rows keep the raw integer entry bound without rational rescaling. -/
theorem build_bounded {n F : ℕ} (d : RawDesign n F)
    (hW : ∀ g j v, |d.rows g j v|≤(d.W g : ℤ))
    (g : Fin d.r) (j : Fin ((build d).m g)) (v : Fin ((build d).h g)) :
    |(build d).C g j v| ≤ ((build d).W g : ℤ) := by
  have hc : (build d).C g j v = (uncache d).C g j v := cache_C (uncache d) g j v
  rw [hc]
  exact hW g _ _

/-- Attach proof-only native row locality to the already acquired runtime data. -/
def certify {n F : ℕ} (d : RawDesign n F) (arity : Fin F → ℕ)
    (rows : (e : Fin F) → Fin (arity e) → Fin n → ℚ)
    (hW : ∀ g j v, |d.rows g j v|≤(d.W g : ℤ))
    (hlocal : ∀ e i g, g ≠ d.assigned e →
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.KillsIntegerKernel
        (fun v : {v : Fin n // d.head v=g} => rows e i v.val)
        (fun j (v : {v : Fin n // d.head v=g}) => d.rows g j v.val)) : Data arity rows where
  r := d.r
  h := (build d).h
  m := (build d).m
  W := d.W
  grouping := (build d).grouping
  assigned := d.assigned
  C := (build d).C
  bounded := build_bounded d hW
  span := by
    intro e i g hg
    have hl := OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.killsIntegerKernel_of_rational_span
      (fun j (v : {v : Fin n // d.head v=g}) => d.rows g j v.val)
      (fun j (v : {v : Fin n // d.head v=g}) => d.rows g ((selection d g).select j) v.val)
      (selection d g).span (fun v => rows e i v.val) (hlocal e i g hg)
    obtain ⟨c,hc⟩ := SemiprimeLayoutCertificates.row_span_of_integer_kernel _ _ hl
    refine ⟨c, fun v => ?_⟩
    have hgroup : (build d).grouping.symm ⟨g,v⟩ = (columns d g v).val := rfl
    have hcache (j) : (build d).C g j v = d.rows g ((selection d g).select j) (columns d g v).val :=
      cache_C (uncache d) g j v
    exact (congrArg (rows e i) hgroup).trans ((hc (columns d g v)).trans
      (Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℤ => c j*(z : ℚ)) (hcache j).symm)))

/-- Erasing the native validity certificate returns exactly the pure acquired design. -/
theorem certify_runtime {n F : ℕ} (d : RawDesign n F) (arity : Fin F → ℕ)
    (rows : (e : Fin F) → Fin (arity e) → Fin n → ℚ)
    (hW : ∀ g j v, |d.rows g j v|≤(d.W g : ℤ))
    (hlocal : ∀ e i g, g ≠ d.assigned e →
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.KillsIntegerKernel
        (fun v : {v : Fin n // d.head v=g} => rows e i v.val)
        (fun j (v : {v : Fin n // d.head v=g}) => d.rows g j v.val)) :
    { r := (certify d arity rows hW hlocal).r
      h := (certify d arity rows hW hlocal).h
      m := (certify d arity rows hW hlocal).m
      W := (certify d arity rows hW hlocal).W
      grouping := (certify d arity rows hW hlocal).grouping
      assigned := (certify d arity rows hW hlocal).assigned
      C := (certify d arity rows hW hlocal).C : RuntimeDesign n F } = build d := rfl

end RiemannGaussian.SemiprimeRuntimeDesignAcquisition
