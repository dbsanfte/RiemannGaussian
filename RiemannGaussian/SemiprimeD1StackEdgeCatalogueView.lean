/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueComponents
import RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding

/-! # Actual edge-transducer store invariants and literal local instructions -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueView
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1EdgeCatalogueEncoding (Record)

/-- Literal old catalogue role physically consumed by the parser. -/
def sourceReader : Cat.Stack := Cat.kernelStack (SemiprimeD1StackCartesian4.aux 2)
/-- Exact physical store; only the actually parsed old tape role is overwritten. -/
def store (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (work:Aux→List Bool) : Stack→List Bool
  | .inl k => if k=sourceReader then tape else base k
  | .inr (.inl part) => words part
  | .inr (.inr role) => work role
/-- All transient component buffers are empty between literal operations. -/
def cleanWork (raw side:List Bool) : Aux→List Bool
  | .reversed => raw
  | .side => side
  | _ => []
/-- Actual clean loop state, retaining parsed fields and reversed emitted tape. -/
def clean (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (raw side:List Bool) : Stack→List Bool :=
  store base tape words (cleanWork raw side)
/-- The actual parser reads precisely the supplied physical tape role. -/
theorem store_reader (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (work:Aux→List Bool) :
    store base tape words work reader=tape := by simp [store,reader,sourceReader,catStack]
/-- A physical tape update preserves every other original metadata role. -/
theorem update_reader (base:Cat.Stack→List Bool) (tape next:List Bool) (words:Record) (work:Aux→List Bool) :
    Function.update (store base tape words work) reader next=store base next words work := by
  funext k
  rcases k with k|k|k
  · by_cases h:k=sourceReader
    · subst k;simp [store,reader,sourceReader,catStack,Function.update]
    · have h':k≠Cat.kernelStack (SemiprimeD1StackCartesian4.aux 2):=h
      simp [store,reader,sourceReader,catStack,Function.update,h']
  · simp [store,reader,catStack,Function.update]
  · simp [store,reader,catStack,Function.update]
/-- A real parsed-field write changes only its finite cache slot. -/
theorem update_cache (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (work:Aux→List Bool)
    (part:Fin 5) (word:List Bool) :
    Function.update (store base tape words work) (cache part) word=
      store base tape (Function.update words part word) work := by
  funext k
  rcases k with k|k|k
  · simp [store,cache,Function.update]
  · by_cases h:k=part
    · subst k;simp [store,cache,Function.update]
    · simp [store,cache,Function.update,h]
  · simp [store,cache,Function.update]
/-- A real work-stack write changes only that physical role. -/
theorem update_aux (base:Cat.Stack→List Bool) (tape:List Bool) (words:Record) (work:Aux→List Bool)
    (role:Aux) (word:List Bool) :
    Function.update (store base tape words work) (aux role) word=
      store base tape words (Function.update work role word) := by
  funext k
  rcases k with k|k|k
  · simp [store,aux,Function.update]
  · simp [store,aux,Function.update]
  · by_cases h:k=role
    · subst k;simp [store,aux,Function.update]
    · simp [store,aux,Function.update,h]

/-- A literal global push, including its actual data-cell allocation. -/
theorem push_run (pc next:Label) (stack:Stack) (bit:Bool) (data:Stack→List Bool)
    (hc:program pc=.base (.push stack bit next)) :
    Runs program 1 pc data next (Function.update data stack (bit::data stack)) := by
  exact one_base program pc next (.push stack bit next) data _ hc rfl rfl

/-- A literal global pop with one continuation, including actual EOF. -/
theorem pop_run (pc next:Label) (stack:Stack) (data:Stack→List Bool)
    (hc:program pc=.base (.pop stack next next next)) :
    Runs program 1 pc data next (Function.update data stack (data stack).tail) := by
  apply one_base program pc next (.pop stack next next next) data _ hc
  · cases h:(data stack).head? with
    | none => simp [B.execute,SemiprimeD1StackBytecode.choose,h]
    | some bit => cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,h]
  · rfl

/-- Every old limit byte is physically cleared; no stale field is discarded for free. -/
theorem clear_run (word:List Bool) (pc next:Label) (stack:Stack) (data:Stack→List Bool)
    (hw:data stack=word) (hc:program pc=.base (.pop stack next pc pc)) :
    Runs program (word.length+1) pc data next (Function.update data stack []) := by
  induction word generalizing data with
  | nil =>
    apply one_base program pc next (.pop stack next pc pc) data _ hc
    · simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
    · change Function.update data stack (data stack).tail=_
      rw [hw,List.tail_nil]
  | cons bit word ih =>
    have h0:Runs program 1 pc data pc (Function.update data stack word):=by
      apply one_base program pc pc (.pop stack next pc pc) data _ hc
      · cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
      · change Function.update data stack (data stack).tail=_
        rw [hw,List.tail_cons]
    have h1:=ih (Function.update data stack word) (Function.update_self _ _ _)
    have h:=h0.trans h1
    rw [Function.update_idem] at h
    simpa only [List.length_cons,show 1+(word.length+1)=word.length+1+1 by omega] using h
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueView
