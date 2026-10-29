/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecords
/-! # Fixed physical bank views and the shared retained original-N word -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecords
/-- Every original source role is literally the same physical retained word. -/
@[simp] theorem data_root (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : R.Stack) : data r v t a (root k)=r k := rfl
/-- Every fresh descriptor-source role has its own physical allocation. -/
@[simp] theorem data_catalogue (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : V.Stack) : data r v t a (catalogue k)=v k := rfl
/-- Every local parse/accumulation word is physically explicit. -/
@[simp] theorem data_aux (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : Aux) : data r v t a (aux k)=a k := rfl
/-- The table sees the actual old original-N cell; its allocated shadow stays empty. -/
theorem data_table (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (h : r R.originalInput=t tableNumber) (k : T.Stack) :
    data r v t a (tableStack k)=t k := by
  by_cases he : k=tableNumber
  · subst k;exact h
  · simp only [tableStack,he,ite_false,tablePrivate,data,Sum.elim_inr,Sum.elim_inl,privateTable]
/-- A local physical update leaves all three acquired component banks intact. -/
theorem update_aux (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : Aux) (word : List Bool) :
    Function.update (data r v t a) (aux k) word=data r v t (Function.update a k word) := by
  unfold data aux
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr]
/-- A physical fresh-catalogue update retains the complete original source bank. -/
theorem update_catalogue (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : V.Stack) (word : List Bool) :
    Function.update (data r v t a) (catalogue k) word=data r (Function.update v k word) t a := by
  unfold data catalogue
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- A borrowed actual original-source work update has its literal whole-bank form. -/
theorem update_root (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : R.Stack) (word : List Bool) :
    Function.update (data r v t a) (root k) word=data (Function.update r k word) v t a := by
  unfold data root
  rw [Sum.update_elim_inl]
/-- Updating a private table role cannot accidentally populate its shared-N shadow. -/
theorem privateTable_update (t : T.Stack → List Bool) (k : T.Stack) (word : List Bool)
    (h : k≠tableNumber) :
    Function.update (privateTable t) k word=privateTable (Function.update t k word) := by
  funext j
  by_cases he : j=tableNumber
  · subst j
    rw [Function.update_of_ne h.symm]
    simp only [privateTable,ite_true]
  · by_cases hj : j=k
    · subst j;simp only [Function.update_self,privateTable,h,ite_false]
    · simp only [Function.update_of_ne hj,privateTable,he,ite_false]
/-- All parser/table updates apart from N have distinct private physical targets. -/
theorem update_table (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) (k : T.Stack) (word : List Bool)
    (h : k≠tableNumber) :
    Function.update (data r v t a) (tableStack k) word=data r v (Function.update t k word) a := by
  simp only [tableStack,h,ite_false,tablePrivate,data]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl,privateTable_update t k word h]
/-- The entire local parse/log state, with no implicit private data words. -/
structure Work where
  /-- Unread actual factor-record suffix. -/
  records : List Bool := []
  /-- Unread actual consecutive five-field descriptor suffix. -/
  descriptors : List Bool := []
  /-- Actual five parsed descriptor fields; coord1 lives in the table template. -/
  tag : List Bool := []
  /-- Physical unary side before its paid normalization. -/
  coord0 : List Bool := []
  /-- Physical coordinate2. -/
  coord2 : List Bool := []
  /-- Physical coordinate3. -/
  coord3 : List Bool := []
  /-- Actual parser reversal scratch. -/
  scratch : List Bool := []
  /-- Physical parser or final success singleton. -/
  status : List Bool := []
  /-- Chronological reverse byte history. -/
  history : List Bool := []
  /-- Physical output seeded with exactly one FALSE. -/
  output : List Bool := []
/-- All ten actual local words; this is a proof view, never a runtime getter. -/
def words (w : Work) : Aux → List Bool
  | .recordReader => w.records | .descriptorReader => w.descriptors | .tag => w.tag
  | .coord0 => w.coord0 | .coord2 => w.coord2 | .coord3 => w.coord3
  | .fieldScratch => w.scratch | .status => w.status | .history => w.history | .output => w.output
/-- Exact physical records update of the ten-word local view. -/
theorem words_records (w : Work) (word : List Bool) :
    Function.update (words w) .recordReader word=words {w with records := word} := by
  funext k;cases k <;> rfl
/-- Exact physical descriptors update of the ten-word local view. -/
theorem words_descriptors (w : Work) (word : List Bool) :
    Function.update (words w) .descriptorReader word=words {w with descriptors := word} := by
  funext k;cases k <;> rfl
/-- Exact physical tag update of the ten-word local view. -/
theorem words_tag (w : Work) (word : List Bool) :
    Function.update (words w) .tag word=words {w with tag := word} := by
  funext k;cases k <;> rfl
/-- Exact physical coord0 update of the ten-word local view. -/
theorem words_coord0 (w : Work) (word : List Bool) :
    Function.update (words w) .coord0 word=words {w with coord0 := word} := by
  funext k;cases k <;> rfl
/-- Exact physical coord2 update of the ten-word local view. -/
theorem words_coord2 (w : Work) (word : List Bool) :
    Function.update (words w) .coord2 word=words {w with coord2 := word} := by
  funext k;cases k <;> rfl
/-- Exact physical coord3 update of the ten-word local view. -/
theorem words_coord3 (w : Work) (word : List Bool) :
    Function.update (words w) .coord3 word=words {w with coord3 := word} := by
  funext k;cases k <;> rfl
/-- Exact physical scratch update of the ten-word local view. -/
theorem words_scratch (w : Work) (word : List Bool) :
    Function.update (words w) .fieldScratch word=words {w with scratch := word} := by
  funext k;cases k <;> rfl
/-- Exact physical status update of the ten-word local view. -/
theorem words_status (w : Work) (word : List Bool) :
    Function.update (words w) .status word=words {w with status := word} := by
  funext k;cases k <;> rfl
/-- Exact physical history update of the ten-word local view. -/
theorem words_history (w : Work) (word : List Bool) :
    Function.update (words w) .history word=words {w with history := word} := by
  funext k;cases k <;> rfl
/-- Exact physical output update of the ten-word local view. -/
theorem words_output (w : Work) (word : List Bool) :
    Function.update (words w) .output word=words {w with output := word} := by
  funext k;cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsView
