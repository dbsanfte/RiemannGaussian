/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRuntimeDesignCache
import RiemannGaussian.SemiprimeEncodedRowSelection
import RiemannGaussian.SemiprimePaidPrefixController
import RiemannGaussian.SemiprimeMaterializedSourceWords
import RiemannGaussian.SemiprimePaidConstraintCache

/-!
# Actual physical selection and complete runtime-design caching
Raw metadata accesses use the stated cached-scalar model. Original integer
accesses carry the caller's actual IntRun reports. The runtime has no native
Data, polynomial, logical basis, or selected-row answer parameter.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimePaidRuntimeDesign
open scoped BigOperators
open SemiprimeRuntimeDesignAcquisition SemiprimeNodeArrayExecution
open SemiprimeMaterializedSourceUniversal
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open SemiprimeEncodedRowSelection (IntRun)

/-- Actual finite cached-head filter, with selected scalar/list-cell work. -/
def filterColumns {n r : ℕ} (head : Fin n → Fin r) (g : Fin r) : List (Fin n) → Run (List (Fin n))
  | [] => ⟨[],1⟩
  | v::vs => let rest := filterColumns head g vs
             ⟨if head v=g then v::rest.value else rest.value,rest.work+5⟩

/-- The tracked column scan preserves the old filtered order exactly. -/
theorem filterColumns_value {n r : ℕ} (head : Fin n → Fin r) (g : Fin r) (vs : List (Fin n)) :
    (filterColumns head g vs).value=vs.filter (fun v => decide (head v=g)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [filterColumns,List.filter_cons,ih]

/-- All original head reads, filter branches and cell constructors are paid. -/
theorem filterColumns_work {n r : ℕ} (head : Fin n → Fin r) (g : Fin r) (vs : List (Fin n)) :
    (filterColumns head g vs).work=5*vs.length+1 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [filterColumns,List.length_cons,ih]; omega

/-- A list whose stored order is the exact old group-column order. -/
def columnEquiv {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g)))) :
    Fin (headSize d g) ≃ {v : Fin n // d.head v=g} :=
  (finCongr (congrArg List.length hx).symm).trans
    (listSubtypeEquiv xs (by rw [hx]; exact (List.nodup_finRange n).filter _)
      (fun v => d.head v=g) (by intro v; rw [hx]; simp [SemiprimeFiniteEnumerations.fin]))

/-- Cached columns do not change the original finite coordinate equivalence. -/
theorem columnEquiv_eq {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g)))) :
    columnEquiv d g xs hx=columns d g := by
  subst xs
  apply Equiv.ext
  intro v
  apply Subtype.ext
  rfl

/-- Read a known valid coordinate by an actual Option/list scan, without a fallback oracle. -/
def readIndex {A : Type*} (xs : List A) (i : Fin xs.length) : Run A :=
  let out := SemiprimePaidConstraintCache.getRun xs i.val
  ⟨out.value.get (by
      have h := SemiprimePaidConstraintCache.getRun_value xs i.val
      rw [List.getElem?_eq_getElem i.isLt] at h
      rw [h]
      trivial),out.work+1⟩

/-- The actual list scanner obtains its intended cached coordinate. -/
theorem readIndex_value {A : Type*} (xs : List A) (i : Fin xs.length) :
    (readIndex xs i).value=xs.get i := by
  simp only [readIndex,SemiprimePaidConstraintCache.getRun_value,
    List.getElem?_eq_getElem i.isLt,Option.get_some]
  rfl

/-- Valid finite reads retain every visited list cell. -/
theorem readIndex_work {A : Type*} (xs : List A) (i : Fin xs.length) :
    (readIndex xs i).work≤2*xs.length+2 := by
  have h := SemiprimePaidConstraintCache.getRun_work xs i.val
  change _+1≤_
  omega

/-- One cached group column, including its real list-read report. -/
def readColumn {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (v : Fin (headSize d g)) : Run (Fin n) :=
  readIndex xs (Fin.cast (congrArg List.length hx).symm v)

/-- A tracked column read has the exact original coordinate. -/
theorem readColumn_value {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (v : Fin (headSize d g)) :
    (readColumn d g xs hx v).value=(columns d g v).val := by
  rw [← columnEquiv_eq d g xs hx]
  exact readIndex_value _ _

/-- Acquire the original row-coordinate report through its cached head column. -/
def matrixReader {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun)
    (j : Fin (d.count g)) (v : Fin (headSize d g)) : IntRun :=
  let col := readColumn d g xs hx v
  let out := source g j col.value
  ⟨out.value,col.work+out.work+2⟩

/-- Materialize one ORIGINAL selected row from the selector's retained integer cache. -/
def selectedRow (integers : List (List ℤ)) (j : ℕ) : Run (Array ℤ) :=
  let row := SemiprimePaidConstraintCache.getRun integers j
  let values := row.value.getD []
  ⟨values.toArray,row.work+5*values.length+3⟩

/-- One physical selector call, followed only by reads of its ORIGINAL integer cache. -/
def group {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun) (bits : ℕ) : Run (Array (Array ℤ)) :=
  let selected := SemiprimeEncodedRowSelection.select (matrixReader d g xs hx source) bits
  let reports := selected.selected.map (fun j => selectedRow selected.integers j.val)
  ⟨(reports.map (fun r => r.value)).toArray,
    selected.work+(reports.map (fun r => r.work)).sum+10*selected.selected.length+5⟩

/-- The new group payload is exactly the old selected ORIGINAL integer matrix. -/
theorem group_value {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun) (bits : ℕ)
    (hs : ∀ g j v,(source g j v).value=d.rows g j v)
    (hb : ∀ g j v,|d.rows g j v|≤(2^bits : ℕ)) :
    (group d g xs hx source bits).value =
      Array.ofFn (fun j : Fin (SemiprimeRowSelectionExecution.selectedIndices (matrix d g)).length =>
        Array.ofFn (fun v : Fin (headSize d g) =>
          matrix d g ((SemiprimeRowSelectionExecution.selectedIndices (matrix d g)).get j) v)) := by
  have hv (j : Fin (d.count g)) (v : Fin (headSize d g)) :
      (matrixReader d g xs hx source j v).value=matrix d g j v := by
    simp only [matrixReader,readColumn_value,hs,matrix]
  have hc : (fun j v => (matrixReader d g xs hx source j v).value)=matrix d g := by
    funext j v
    exact hv j v
  have hsel := SemiprimeEncodedRowSelection.select_correct (matrixReader d g xs hx source) bits
    (by intro j v; rw [hv]; exact hb g j _)
  rw [hc] at hsel
  have hints := SemiprimeEncodedRowSelection.select_integers (matrixReader d g xs hx source) bits
  simp only [hv] at hints
  simp only [group,hsel,hints,selectedRow,SemiprimePaidConstraintCache.getRun_value,List.getElem?_ofFn,
    List.map_map,Function.comp_def]
  conv_lhs => rw [← List.ofFn_get (SemiprimeRowSelectionExecution.selectedIndices (matrix d g))]
  simp only [List.map_ofFn,List.toArray_ofFn]
  apply congrArg (fun f : Fin (SemiprimeRowSelectionExecution.selectedIndices (matrix d g)).length → Array ℤ => Array.ofFn f)
  funext j
  simp only [Function.comp_apply,dite_eq_left ((SemiprimeRowSelectionExecution.selectedIndices (matrix d g)).get j).isLt,
    Option.getD_some,List.toArray_ofFn]

/-- Proof-only value equality of the frozen integer-only cache wrapper. -/
theorem old_cache_eq {n F : ℕ} (d : RuntimeDesign n F) : SemiprimeRuntimeDesignAcquisition.cache d=d := by
  simp only [SemiprimeRuntimeDesignAcquisition.cache,Array.getElem_ofFn]

/-- Build a pure provisional design from acquired column and selected-integer caches. -/
def provisional {n F : ℕ} (d : RawDesign n F) (cols : Fin d.r → List (Fin n))
    (hc : ∀ g,cols g=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (values : Fin d.r → Array (Array ℤ)) : RuntimeDesign n F where
  r := d.r
  h := headSize d
  m := fun g => (values g).size
  W := d.W
  grouping := (Equiv.sigmaFiberEquiv d.head).symm.trans
    (Equiv.sigmaCongrRight (fun g => (columnEquiv d g (cols g) (hc g)).symm))
  assigned := d.assigned
  C := fun g j v => ((values g)[j.val]!)[v.val]!

/-- Actual paid design builder; every head selects ONCE. Returned integer and
grouping accessors are cached; finite shape metadata has an explicit scalar model. -/
def build {n F : ℕ} (d : RawDesign n F)
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun) (bits : ℕ) : Run (RuntimeDesign n F) := by
  let indices := SemiprimePaidPrefixController.finIndices n
  let heads := SemiprimeRuntimeDesignCache.function d.head
  let columns := Array.ofFn (fun g : Fin d.r => filterColumns heads g indices.value)
  let cols := fun g : Fin d.r => (columns[g.val]'(by simp [columns])).value
  have hc (g : Fin d.r) : cols g=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))) := by
    simp [cols,columns,indices,filterColumns_value,heads,SemiprimeRuntimeDesignCache.function_eq,
      SemiprimePaidPrefixController.finIndices_value,SemiprimeFiniteEnumerations.fin]
  let groups := Array.ofFn (fun g : Fin d.r => group d g (cols g) (hc g) source bits)
  let values := fun g : Fin d.r => (groups[g.val]'(by simp [groups])).value
  let output := SemiprimeRuntimeDesignCache.acquire (provisional d cols hc values)
  exact ⟨output,indices.work+(∑ g : Fin d.r,(columns[g.val]'(by simp [columns])).work)+
    (∑ g : Fin d.r,(groups[g.val]'(by simp [groups])).work)+
    100*(n+F+d.r+1)^4*(1+(∑ g : Fin d.r,d.count g))⟩

/-- Exact old build value, with no old scalar elimination anywhere in the NEW runtime. -/
theorem build_eq {n F : ℕ} (d : RawDesign n F)
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun) (bits : ℕ)
    (hs : ∀ g j v,(source g j v).value=d.rows g j v)
    (hb : ∀ g j v,|d.rows g j v|≤(2^bits : ℕ)) :
    (build d source bits).value=SemiprimeRuntimeDesignAcquisition.build d := by
  unfold build
  simp only [SemiprimeRuntimeDesignCache.acquire_eq,Array.getElem_ofFn]
  simp only [group_value d _ _ _ source bits hs hb]
  unfold provisional
  simp only [columnEquiv_eq]
  rw [SemiprimeRuntimeDesignAcquisition.build,old_cache_eq]
  simp [SemiprimeRuntimeDesignAcquisition.uncache,SemiprimeRuntimeDesignAcquisition.selection,
    SemiprimeRowSelectionExecution.selectedRowsWithColumns,SemiprimeRowSelectionExecution.selectedRows,
    SemiprimeRowSelectionExecution.selectedIndex,matrix]
  constructor
  · rfl
  · apply Function.hfunext rfl
    intro g g' hg
    cases hg
    apply Function.hfunext (by simp)
    intro j j' hj
    apply Function.hfunext rfl
    intro v v' hv
    cases hv
    have hjval : j.val=j'.val := Fin.val_eq_val_of_heq hj
    apply heq_of_eq
    simp [hjval]
    rfl

/-- A selected-cache read scans at most the acquired matrix and copies one row. -/
theorem selectedRow_work {m h : ℕ} (C : Fin m → Fin h → ℤ) (j : Fin m) :
    (selectedRow (List.ofFn (fun i => List.ofFn (C i))) j.val).work ≤ 2*m+5*h+4 := by
  have hw := SemiprimePaidConstraintCache.getRun_work
    (List.ofFn (fun i => List.ofFn (C i))) j.val
  simp only [List.length_ofFn] at hw
  simp only [selectedRow,SemiprimePaidConstraintCache.getRun_value,List.getElem?_ofFn,
    dite_eq_left j.isLt,Option.getD_some,List.length_ofFn]
  omega

/-- List accumulation pays every callback report, without function memoization. -/
theorem sum_map_le {A : Type*} (xs : List A) (f : A → ℕ) (B : ℕ)
    (hf : ∀ x ∈ xs,f x ≤ B) : (xs.map f).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have hx := hf x (by simp)
    have ht := ih (by intro y hy; exact hf y (by simp [hy]))
    nlinarith

/-- Explicit polynomial group budget, using its ACTUAL row and column dimensions. -/
def groupBudget (m h bits readBudget : ℕ) : ℕ :=
  SemiprimeEncodedRowSelection.budget m h bits (2*h+readBudget+4)+
    m*(2*m+5*h+4)+10*m+5

/-- Source callbacks are charged once per matrix cell; all later selected-row
accesses use the SAME acquired original integer cache. -/
theorem group_work {n F : ℕ} (d : RawDesign n F) (g : Fin d.r) (xs : List (Fin n))
    (hx : xs=((SemiprimeFiniteEnumerations.fin n).values.filter (fun v => decide (d.head v=g))))
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun) (bits readBudget : ℕ)
    (hs : ∀ g j v,(source g j v).value=d.rows g j v)
    (hb : ∀ g j v,|d.rows g j v|≤(2^bits : ℕ))
    (hr : ∀ g j v,(source g j v).work≤readBudget) :
    (group d g xs hx source bits).work≤groupBudget (d.count g) (headSize d g) bits readBudget := by
  have hlen : xs.length=headSize d g := congrArg List.length hx
  have hv (j : Fin (d.count g)) (v : Fin (headSize d g)) :
      (matrixReader d g xs hx source j v).value=matrix d g j v := by
    simp only [matrixReader,readColumn_value,hs,matrix]
  have hc : (fun j v => (matrixReader d g xs hx source j v).value)=matrix d g := by
    funext j v
    exact hv j v
  have hsel := SemiprimeEncodedRowSelection.select_correct (matrixReader d g xs hx source) bits
    (by intro j v; rw [hv]; exact hb g j _)
  rw [hc] at hsel
  have hints := SemiprimeEncodedRowSelection.select_integers (matrixReader d g xs hx source) bits
  simp only [hv] at hints
  have hw := SemiprimeEncodedRowSelection.select_work (matrixReader d g xs hx source) bits
    (2*headSize d g+readBudget+4) (by intro j v; rw [hv]; exact hb g j _)
    (by
      intro j v
      have ha := readIndex_work xs (Fin.cast (congrArg List.length hx).symm v)
      have hb' := hr g j (readColumn d g xs hx v).value
      change _+_+2≤_
      change (readIndex xs _).work+_+2≤_
      omega)
  have hl : (SemiprimeRowSelectionExecution.selectedIndices (matrix d g)).length≤d.count g := by
    simpa using (SemiprimeRowSelectionExecution.selectedIndices_nodup (matrix d g)).length_le_card
  have ha := sum_map_le (SemiprimeRowSelectionExecution.selectedIndices (matrix d g))
    (fun j => (selectedRow (List.ofFn (fun i => List.ofFn (matrix d g i))) j.val).work)
    (2*d.count g+5*headSize d g+4) (by intro j _; exact selectedRow_work _ j)
  simp only [group,hsel,hints,List.map_map,Function.comp_def]
  unfold groupBudget
  nlinarith

/-- Complete retained design ledger. The finite sum has one polynomial
physical-selector budget per head; no selection is hidden in a later closure. -/
def buildBudget {n F : ℕ} (d : RawDesign n F) (bits readBudget : ℕ) : ℕ :=
  3*(n+1)^2+d.r*(5*n+1)+
    (∑ g : Fin d.r,groupBudget (d.count g) (headSize d g) bits readBudget)+
    100*(n+F+d.r+1)^4*(1+(∑ g : Fin d.r,d.count g))

/-- All matrix source-read reports, physical selector work, cached selected
row reads, column scans and stated metadata/cache allowances are retained. -/
theorem build_work {n F : ℕ} (d : RawDesign n F)
    (source : (g : Fin d.r) → Fin (d.count g) → Fin n → IntRun) (bits readBudget : ℕ)
    (hs : ∀ g j v,(source g j v).value=d.rows g j v)
    (hb : ∀ g j v,|d.rows g j v|≤(2^bits : ℕ))
    (hr : ∀ g j v,(source g j v).work≤readBudget) :
    (build d source bits).work≤buildBudget d bits readBudget := by
  have hi := SemiprimePaidPrefixController.finIndices_work n
  unfold build buildBudget
  simp only [Array.getElem_ofFn,filterColumns_work,
    SemiprimePaidPrefixController.finIndices_value,List.length_finRange,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  gcongr
  exact group_work d _ _ _ source bits readBudget hs hb hr

end RiemannGaussian.SemiprimePaidRuntimeDesign
