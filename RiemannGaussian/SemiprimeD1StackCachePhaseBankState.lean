/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBank
/-! # Full246-word physical boundary views
No callee workspace is silently reset: data contains its ENTIRE238-word bank.
The proof-side outer record describes eight real input/parser/logger words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBank
/-- Entire physical246-role bank, including dirty/stopped callee caches. -/
def data (bank:P.Stack→List Bool) (w:Aux→List Bool):Stack→List Bool:=Sum.elim bank w
/-- Every actual callee word retains its literal complete bank value. -/
theorem data_cached (bank:P.Stack→List Bool) (w:Aux→List Bool) (k:P.Stack):data bank w (cached k)=bank k:=rfl
/-- Every actual outer input/parser/logger word is literal. -/
theorem data_aux (bank:P.Stack→List Bool) (w:Aux→List Bool) (k:Aux):data bank w (aux k)=w k:=rfl
/-- Actual callee single-word writes coincide with full physical246-role updates. -/
theorem data_update_cached (bank:P.Stack→List Bool) (w:Aux→List Bool) (k:P.Stack) (word:List Bool):
    data (Function.update bank k word) w=Function.update (data bank w) (cached k) word:=by
  funext r;rcases r with r|r <;> simp [data,cached,Function.update_apply]
/-- Actual outer single-word writes coincide with full physical246-role updates. -/
theorem data_update_aux (bank:P.Stack→List Bool) (w:Aux→List Bool) (k:Aux) (word:List Bool):
    data bank (Function.update w k word)=Function.update (data bank w) (aux k) word:=by
  funext r;rcases r with r|r <;> simp [data,aux,Function.update_apply]
/-- Eight mathematical fields describe eight actual outer tapes only, never runtime objects. -/
structure Words where
  /-- Original retained issued-reference vector. -/
  references:List Bool:=[]
  /-- Original retained per-phase child tape vector. -/
  children:List Bool:=[]
  /-- Actual consuming reference reader. -/
  referenceReader:List Bool:=[]
  /-- Actual consuming child-field reader. -/
  childReader:List Bool:=[]
  /-- Actual field-parser valid bit. -/
  valid:List Bool:=[]
  /-- Actual reversed output chunk history. -/
  history:List Bool:=[]
  /-- Actual one-phase framed chunk buffer. -/
  buffer:List Bool:=[]
  /-- Actual chronological output vector. -/
  output:List Bool:=[]
/-- Literal outer word projection. -/
def words (v:Words):Aux→List Bool
  | .references=>v.references | .children=>v.children | .referenceReader=>v.referenceReader
  | .childReader=>v.childReader | .valid=>v.valid | .history=>v.history | .buffer=>v.buffer | .output=>v.output
/-- Proof-side single outer field update, exactly corresponding to one real physical write. -/
def setWord (v:Words) (k:Aux) (word:List Bool):Words:=match k with
  | .references=>{v with references:=word} | .children=>{v with children:=word}
  | .referenceReader=>{v with referenceReader:=word} | .childReader=>{v with childReader:=word}
  | .valid=>{v with valid:=word} | .history=>{v with history:=word} | .buffer=>{v with buffer:=word}
  | .output=>{v with output:=word}
/-- Every actual outer word update has the exact full physical representation. -/
theorem words_update (v:Words) (k:Aux) (word:List Bool):
    Function.update (words v) k word=words (setWord v k word):=by funext r;cases r <;> cases k <;> rfl
/-- Exactly the real four initial words, with all other242 roles empty. -/
theorem initial_data (hp cn refs children:List Bool):(initial hp cn refs children).data=
    data (P.input hp cn [] []) (words {references:=refs,children:=children}):=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Only heap/counter are persistent: reference and children are acquired afresh each phase. -/
theorem persistent_heap (k:P.Stack):persistent k=true ↔cached k=heap ∨cached k=counter:=by
  simp only [persistent,decide_eq_true_eq]
/-- The scratch/status allocation is not either retained input. -/
theorem scratch_not_persistent:persistent P.copyScratch=false:=by decide
end RiemannGaussian.SemiprimeD1StackCachePhaseBankState
