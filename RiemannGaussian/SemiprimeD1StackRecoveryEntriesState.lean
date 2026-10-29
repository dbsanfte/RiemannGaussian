/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesEncoding
/-! # Exact all25-role source, parsed-row and logger boundaries
The allocated12-role indexed bank retains its original nested child tape.
Its query/value shadows stay empty; actual calls use the parsed external fields.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntries
open SemiprimeD1StackRecoveryEntriesEncoding (R.Row)
/-- Fixed full indexed bank at an actual stopped-component boundary. -/
def indexedBank (childTape:List Bool):I.Stack → List Bool:=I.input childTape []
/-- Complete actual25-role boundary, retaining every allocated indexed role/shadow. -/
def data (childTape:List Bool) (words:Aux → List Bool):Stack → List Bool:=Sum.elim (indexedBank childTape) words
/-- Actual external word update preserves all12 indexed roles and every other external word. -/
theorem data_update (childTape:List Bool) (words:Aux → List Bool) (k:Aux) (word:List Bool):
    data childTape (Function.update words k word)=Function.update (data childTape words) (aux k) word:=by
  funext p
  rcases p with p|p
  · rfl
  · simp only [data,aux,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- Every external word is its actual physical tape projection. -/
theorem data_aux (childTape:List Bool) (words:Aux → List Bool) (k:Aux):data childTape words (aux k)=words k:=rfl
/-- Shared copy/parser/frame scratch is genuinely empty at all actual component boundaries. -/
theorem data_scratch (childTape:List Bool) (words:Aux → List Bool):data childTape words scratch=[]:=rfl
/-- The original nested child tape remains physically retained, never supplied through a getter. -/
theorem data_children (childTape:List Bool) (words:Aux → List Bool):data childTape words children=childTape:=rfl
/-- Exact actual source-field address inside the parsed five-word row. -/
def fieldAux (part:Fin 5):Aux:=if part=0 then .node else if part=1 then .index else if part=2 then .sign else if part=3 then .magnitude else .denominator
/-- Every field parser writes its declared physical tape. -/
theorem field_address (part:Fin 5):fieldTarget part=aux (fieldAux part):=by fin_cases part <;> rfl
/-- All five actual field addresses are distinct. -/
theorem field_injective:Function.Injective fieldAux:=by decide
/-- Proof-only complete external word view; neither fields nor this view is a runtime argument. -/
def words (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out:List Bool):Aux → List Bool
  | .rows=>rows | .reader=>reader | .node=>fields 0 | .index=>fields 1 | .sign=>fields 2
  | .magnitude=>fields 3 | .denominator=>fields 4 | .selectedRow=>row | .child=>child | .valid=>valid
  | .history=>history | .frameBuffer=>buffer | .output=>out
/-- Current actual field projection from the full external view. -/
theorem words_field (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out:List Bool) (part:Fin 5):
    words rows reader fields row child valid history buffer out (fieldAux part)=fields part:=by fin_cases part <;> rfl
/-- Actual parsed-field update, preserving all original source/logger words. -/
theorem update_field (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out:List Bool) (part:Fin 5) (word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (fieldAux part) word=
      words rows reader (Function.update fields part word) row child valid history buffer out:=by
  funext k;fin_cases part <;> cases k <;> rfl
/-- Literal actual rows tape update. -/
theorem update_rows (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.rows:Aux) word=words word reader fields row child valid history buffer out:=by
  funext k;cases k <;> rfl
/-- Literal actual reader tape update. -/
theorem update_reader (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.reader:Aux) word=words rows word fields row child valid history buffer out:=by
  funext k;cases k <;> rfl
/-- Literal actual row tape update. -/
theorem update_row (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.selectedRow:Aux) word=words rows reader fields word child valid history buffer out:=by
  funext k;cases k <;> rfl
/-- Literal actual child tape update. -/
theorem update_child (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.child:Aux) word=words rows reader fields row word valid history buffer out:=by
  funext k;cases k <;> rfl
/-- Literal actual valid tape update. -/
theorem update_valid (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.valid:Aux) word=words rows reader fields row child word history buffer out:=by
  funext k;cases k <;> rfl
/-- Literal actual history tape update. -/
theorem update_history (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.history:Aux) word=words rows reader fields row child valid word buffer out:=by
  funext k;cases k <;> rfl
/-- Literal actual buffer tape update. -/
theorem update_buffer (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.frameBuffer:Aux) word=words rows reader fields row child valid history word out:=by
  funext k;cases k <;> rfl
/-- Literal actual out tape update. -/
theorem update_out (rows reader:List Bool) (fields:Fin 5 → List Bool)
    (row child valid history buffer out word:List Bool):
    Function.update (words rows reader fields row child valid history buffer out) (.output:Aux) word=words rows reader fields row child valid history buffer word:=by
  funext k;cases k <;> rfl
/-- Only the original two actual tapes are populated at the physical source entry. -/
theorem initial_data (rows childTape:List Bool):
    (initial rows childTape).data=data childTape (words rows [] (fun _=>[]) [] [] [] [] [] []):=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesState
