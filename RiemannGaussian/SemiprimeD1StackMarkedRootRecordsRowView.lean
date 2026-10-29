/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTableView
/-! # Clean actual row boundary views and exact local physical updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsTableView
/-- Only five mutable table/template/cache words survive between paid subcalls. -/
structure TableWork where
  /-- Physically parsed original index word. -/
  indexWord : List Bool := []
  /-- Physically normalized side singleton. -/
  sideWord : List Bool := []
  /-- Original physical port vector. -/
  portsWord : List Bool := []
  /-- Physically counted arity markers. -/
  countWord : List Bool := []
  /-- Physically parsed or reacquired table bytes. -/
  tableWord : List Bool := []
/-- Whole2011 physical bank. Component functions are fixed finite tape-bank views only. -/
def view (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) : Stack → List Bool :=
  data r v (tableWords bits p.indexWord p.sideWord p.portsWord p.countWord p.tableWord) (words w)
/-- Actual complete table projection, including the retained original-N alias. -/
theorem view_table (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (h : r R.originalInput=bits) (k : T.Stack) :
    view r v bits p w (tableStack k)=
      tableWords bits p.indexWord p.sideWord p.portsWord p.countWord p.tableWord k := by
  apply data_table
  exact h
/-- Every private word is exactly its explicit physical payload. -/
@[simp] theorem view_aux (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (k : Aux) : view r v bits p w (aux k)=words w k := rfl
/-- Actual parsed or acquired indexWord word. -/
@[simp] theorem view_indexWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) : view r v bits p w index=p.indexWord := rfl
/-- Actual parsed or acquired sideWord word. -/
@[simp] theorem view_sideWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) : view r v bits p w side=p.sideWord := rfl
/-- Actual parsed or acquired portsWord word. -/
@[simp] theorem view_portsWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) : view r v bits p w ports=p.portsWord := rfl
/-- Actual parsed or acquired countWord word. -/
@[simp] theorem view_countWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) : view r v bits p w count=p.countWord := rfl
/-- Actual parsed or acquired tableWord word. -/
@[simp] theorem view_tableWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) : view r v bits p w table=p.tableWord := rfl
/-- Exact physical indexWord write, retaining all old and fresh source caches. -/
theorem set_indexWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) index word=view r v bits {p with indexWord := word} w := by
  unfold view index
  rw [update_table _ _ _ _ (tableIndex) word (by decide),update_indexWord]
/-- Exact physical sideWord write, retaining all old and fresh source caches. -/
theorem set_sideWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) side word=view r v bits {p with sideWord := word} w := by
  unfold view side
  rw [update_table _ _ _ _ (tableSide) word (by decide),update_sideWord]
/-- Exact physical portsWord write, retaining all old and fresh source caches. -/
theorem set_portsWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) ports word=view r v bits {p with portsWord := word} w := by
  unfold view ports
  rw [update_table _ _ _ _ (G.counter .bank) word (by decide),update_bank]
/-- Exact physical countWord write, retaining all old and fresh source caches. -/
theorem set_countWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) count word=view r v bits {p with countWord := word} w := by
  unfold view count
  rw [update_table _ _ _ _ (G.counter .count) word (by decide),update_countWord]
/-- Exact physical tableWord write, retaining all old and fresh source caches. -/
theorem set_tableWord (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) table word=view r v bits {p with tableWord := word} w := by
  unfold view table
  rw [update_table _ _ _ _ (G.aux .output) word (by decide),update_output]
/-- Exact actual local records write. -/
theorem set_records (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .recordReader) word=view r v bits p {w with records := word} := by
  unfold view
  rw [update_aux,words_records]
/-- Exact actual local descriptors write. -/
theorem set_descriptors (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .descriptorReader) word=view r v bits p {w with descriptors := word} := by
  unfold view
  rw [update_aux,words_descriptors]
/-- Exact actual local tag write. -/
theorem set_tag (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .tag) word=view r v bits p {w with tag := word} := by
  unfold view
  rw [update_aux,words_tag]
/-- Exact actual local coord0 write. -/
theorem set_coord0 (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .coord0) word=view r v bits p {w with coord0 := word} := by
  unfold view
  rw [update_aux,words_coord0]
/-- Exact actual local coord2 write. -/
theorem set_coord2 (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .coord2) word=view r v bits p {w with coord2 := word} := by
  unfold view
  rw [update_aux,words_coord2]
/-- Exact actual local coord3 write. -/
theorem set_coord3 (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .coord3) word=view r v bits p {w with coord3 := word} := by
  unfold view
  rw [update_aux,words_coord3]
/-- Exact actual local scratch write. -/
theorem set_scratch (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .fieldScratch) word=view r v bits p {w with scratch := word} := by
  unfold view
  rw [update_aux,words_scratch]
/-- Exact actual local status write. -/
theorem set_status (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .status) word=view r v bits p {w with status := word} := by
  unfold view
  rw [update_aux,words_status]
/-- Exact actual local history write. -/
theorem set_history (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .history) word=view r v bits p {w with history := word} := by
  unfold view
  rw [update_aux,words_history]
/-- Exact actual local output write. -/
theorem set_output (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (word : List Bool) :
    Function.update (view r v bits p w) (aux .output) word=view r v bits p {w with output := word} := by
  unfold view
  rw [update_aux,words_output]
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
