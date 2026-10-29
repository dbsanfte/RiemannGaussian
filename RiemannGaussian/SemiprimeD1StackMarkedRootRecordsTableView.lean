/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsView
/-! # Exact sparse physical table-template and acquired table/cache views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTableView
open SemiprimeD1StackMarkedRootRecords
/-- Six actually populated table roles at a clean row boundary. -/
def slot (i : Fin 6) : T.Stack :=
  if i=0 then tableNumber else if i=1 then tableIndex else if i=2 then tableSide
  else if i=3 then G.counter .bank else if i=4 then G.counter .count else G.aux .output
/-- All six actual data/cache positions are physically distinct. -/
theorem slot_injective : Function.Injective slot := by decide
/-- Sparse144-role view. Live checker words, DFS words and private shadows are empty. -/
def tableWords (bits indexWord sideWord bank countWord output : List Bool) (k : T.Stack) : List Bool :=
  if k=tableNumber then bits else if k=tableIndex then indexWord else if k=tableSide then sideWord
  else if k=G.counter .bank then bank else if k=G.counter .count then countWord
  else if k=G.aux .output then output else []
/-- Only the physically parsed original index and computed side accompany N and scope bytes. -/
theorem initial_table (bits indexWord : List Bool) (sideBit : Bool) (bank : List Bool) :
    (SemiprimeD1StackMarkedPublicInputTable.initial bits indexWord sideBit bank).data=
      tableWords bits indexWord [sideBit] bank [] [] := by
  funext k
  rcases k with k|k
  · simp [SemiprimeD1StackMarkedPublicInputTable.initial,SemiprimeD1StackStaticWordTable.initial,
      SemiprimeD1StackStaticWordTable.data,SemiprimeD1StackStaticWordTable.store,
      tableWords,tableNumber,tableIndex,tableSide,G.template,G.counter,G.aux]
  · rcases k with k|k
    · change SemiprimeD1StackMarkedPublicInputTable.inputTemplate bits indexWord sideBit k=_
      rw [SemiprimeD1StackMarkedPublicInputTableTrace.template_only]
      simp only [tableWords,tableNumber,tableIndex,tableSide,G.template,G.counter,G.aux,
        Sum.inr.injEq,Sum.inl.injEq,Sum.inl_ne_inr,ite_false]
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
/-- The real completed144 source retains exactly the original scope, template and counted arity. -/
theorem result_table (bits indexWord : List Bool) (sideBit : Bool) (words : List (List Bool)) :
    (SemiprimeD1StackMarkedPublicInputTableExecution.done bits indexWord sideBit words).data=
      tableWords bits indexWord [sideBit] (SemiprimeD1TensorTapeCodec.vectorBits words)
        (List.replicate words.length true)
        (SemiprimeD1StackMarkedPublicInputTableExecution.outputTape bits indexWord sideBit words) := by
  have h := initial_table bits indexWord sideBit (SemiprimeD1TensorTapeCodec.vectorBits words)
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · exact congrFun h (.inr (.inl k))
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
/-- The six physical slot evaluations are independent of every other table word. -/
theorem tableWords_slot (bits indexWord sideWord bank countWord output : List Bool) (i : Fin 6) :
    tableWords bits indexWord sideWord bank countWord output (slot i)=
      (![bits,indexWord,sideWord,bank,countWord,output] : Fin 6 → List Bool) i := by
  fin_cases i <;> rfl
/-- Updating the actual indexWord cell preserves every other table/template word. -/
theorem update_indexWord (bits indexWord sideWord bank countWord output word : List Bool) :
    Function.update (tableWords bits indexWord sideWord bank countWord output) (tableIndex) word=
      tableWords bits word sideWord bank countWord output := by
  funext k
  by_cases h : k=(tableIndex)
  · subst k;rfl
  · simp only [Function.update_of_ne h,tableWords,h,ite_false]
/-- Updating the actual sideWord cell preserves every other table/template word. -/
theorem update_sideWord (bits indexWord sideWord bank countWord output word : List Bool) :
    Function.update (tableWords bits indexWord sideWord bank countWord output) (tableSide) word=
      tableWords bits indexWord word bank countWord output := by
  funext k
  by_cases h : k=(tableSide)
  · subst k;rfl
  · simp only [Function.update_of_ne h,tableWords,h,ite_false]
/-- Updating the actual bank cell preserves every other table/template word. -/
theorem update_bank (bits indexWord sideWord bank countWord output word : List Bool) :
    Function.update (tableWords bits indexWord sideWord bank countWord output) (G.counter .bank) word=
      tableWords bits indexWord sideWord word countWord output := by
  funext k
  by_cases h : k=(G.counter .bank)
  · subst k;rfl
  · simp only [Function.update_of_ne h,tableWords,h,ite_false]
/-- Updating the actual countWord cell preserves every other table/template word. -/
theorem update_countWord (bits indexWord sideWord bank countWord output word : List Bool) :
    Function.update (tableWords bits indexWord sideWord bank countWord output) (G.counter .count) word=
      tableWords bits indexWord sideWord bank word output := by
  funext k
  by_cases h : k=(G.counter .count)
  · subst k;rfl
  · simp only [Function.update_of_ne h,tableWords,h,ite_false]
/-- Updating the actual output cell preserves every other table/template word. -/
theorem update_output (bits indexWord sideWord bank countWord output word : List Bool) :
    Function.update (tableWords bits indexWord sideWord bank countWord output) (G.aux .output) word=
      tableWords bits indexWord sideWord bank countWord word := by
  funext k
  by_cases h : k=(G.aux .output)
  · subst k;rfl
  · simp only [Function.update_of_ne h,tableWords,h,ite_false]
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTableView
