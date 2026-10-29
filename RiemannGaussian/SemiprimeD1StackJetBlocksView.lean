/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksPrimitives
import RiemannGaussian.SemiprimeD1StackJetBlocksEncoding
/-! # Complete actual old-context and clean block-source word boundaries
All contexts below describe actual physical banks; source/ready execution
must acquire that cache through the real context supplier or an actual caller.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksView
open SemiprimeD1StackJetBlocks
/-- Entire context cache plus every live source/block field, with all other private helpers empty. -/
def data (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history:List Bool) :Stack→List Bool :=
  Sum.elim context (fun k=>match k with
    | .coefficients=>coefficients
    | .blocks=>blocks
    | .todo=>todo
    | .reader=>reader
    | .rankTodo=>rankTodo
    | .word=>word
    | .rowHistory=>rowHistory
    | .row=>row
    | .history=>history
    | _=>[])
/-- Update only the actual coefficients word; every old context word is retained. -/
theorem data_coefficients (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .coefficients) xs=data context xs blocks todo reader rankTodo word rowHistory row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual blocks word; every old context word is retained. -/
theorem data_blocks (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .blocks) xs=data context coefficients xs todo reader rankTodo word rowHistory row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual todo word; every old context word is retained. -/
theorem data_todo (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .todo) xs=data context coefficients blocks xs reader rankTodo word rowHistory row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual reader word; every old context word is retained. -/
theorem data_reader (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .reader) xs=data context coefficients blocks todo xs rankTodo word rowHistory row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual rankTodo word; every old context word is retained. -/
theorem data_rankTodo (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .rankTodo) xs=data context coefficients blocks todo reader xs word rowHistory row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual word word; every old context word is retained. -/
theorem data_word (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .word) xs=data context coefficients blocks todo reader rankTodo xs rowHistory row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual rowHistory word; every old context word is retained. -/
theorem data_rowHistory (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .rowHistory) xs=data context coefficients blocks todo reader rankTodo word xs row history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual row word; every old context word is retained. -/
theorem data_row (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .row) xs=data context coefficients blocks todo reader rankTodo word rowHistory xs history :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Update only the actual history word; every old context word is retained. -/
theorem data_history (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history xs:List Bool) :
    Function.update (data context coefficients blocks todo reader rankTodo word rowHistory row history) (aux .history) xs=data context coefficients blocks todo reader rankTodo word rowHistory row xs :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> simp [data,aux,Function.update]
/-- Every actual acquired context/header/rank/width/helper role survives the clean source boundary. -/
theorem data_context (context:X.Stack→List Bool) (coefficients blocks todo reader rankTodo word rowHistory row history:List Bool) (k:X.Stack) :
    data context coefficients blocks todo reader rankTodo word rowHistory row history (contextStack k)=context k :=rfl
/-- Whole original header/precision/q/vector input has exactly its actual physical bank representation. -/
theorem input_data (axes precision q coefficients:List Bool) :
    input axes precision q coefficients=data (X.initial axes precision).data coefficients q [] [] [] [] [] [] [] :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackJetBlocksView
