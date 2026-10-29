/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamPrimitives
/-! # Complete stream banks with four physically immutable header aliases
All functions below describe exact finite stores. They are erased proof views;
the literal program obtains every current operand through physical parsing.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamView
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
/-- Exactly the four displaced header allocations. -/
def Header (k : ChoiceStack) : Prop:=
  k=axesRole false ∨ k=precisionRole false ∨ k=axesRole true ∨ k=precisionRole true
/-- The header-alias predicate concerns only fixed decidable role names. -/
instance headerDecidable (k : ChoiceStack) : Decidable (Header k):=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
/-- Physical raw header shadows are empty, although all169 words remain allocated. -/
def mask (source : ChoiceStack→List Bool) (k : ChoiceStack) : List Bool:=if Header k then [] else source k
/-- Included source reads the immutable caller headers through four literal aliases. -/
def materialize (i : Inputs) (source : ChoiceStack→List Bool) (k : ChoiceStack) : List Bool:=
  if k=axesRole false then i.oldAxes else if k=precisionRole false then i.oldPrecision
  else if k=axesRole true then i.newAxes else if k=precisionRole true then i.newPrecision else source k
/-- All changing words at a stable parser/call boundary. -/
structure Words where
  /-- Entire actual source bank; its four header shadows are masked physically. -/
  source : ChoiceStack→List Bool
  /-- Actual unconsumed parent record suffix. -/
  records : List Bool
  /-- Actual unconsumed activity suffix. -/
  activation : List Bool
  /-- Actual unconsumed canonical scope vector suffix. -/
  scopes : List Bool
  /-- Actual unconsumed canonical order vector suffix. -/
  orders : List Bool
  /-- Acquired old ports, physically disposed after this iteration. -/
  oldPorts : List Bool
  /-- Reversed output row history, without any list EOF. -/
  history : List Bool
  /-- Final chronological record word. -/
  output : List Bool
  /-- Actual final success word. -/
  success : List Bool
/-- Complete17-word caller bank, including unchanged eight inputs and copy scratch. -/
def auxData (i : Inputs) (w : Words) : Aux→List Bool
  | .records=>i.records | .activation=>i.activation | .scopes=>i.scopes | .orders=>i.orders
  | .oldAxes=>i.oldAxes | .oldPrecision=>i.oldPrecision | .newAxes=>i.newAxes | .newPrecision=>i.newPrecision
  | .recordsReader=>w.records | .activationReader=>w.activation | .scopesReader=>w.scopes | .ordersReader=>w.orders
  | .oldPorts=>w.oldPorts | .history=>w.history | .output=>w.output | .success=>w.success | .copyScratch=>[]
/-- Complete190-word stable store: all parser/scratch words and header shadows are present. -/
def data (i : Inputs) (w : Words) : Stack→List Bool:=Sum.elim (mask w.source) (Sum.elim (fun _=>[]) (auxData i w))
/-- No work, reader, history, output or status is supplied at entry. -/
def empty : Words:=⟨fun _=>[],[],[],[],[],[],[],[],[]⟩
/-- The declared eight-input frontdoor is exactly the full stable empty-work bank. -/
theorem initial_data (i : Inputs) : inputData i=data i empty:=by
  funext k
  rcases k with k|k
  · change []=(if Header k then [] else [])
    split <;> rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Every included word reads precisely its actual alias/header or raw work tape. -/
theorem project (i : Inputs) (w : Words) (k : ChoiceStack) : data i w (choice k)=materialize i w.source k:=by
  by_cases h0 : k=axesRole false
  · subst k;rfl
  by_cases h1 : k=precisionRole false
  · subst k;rfl
  by_cases h2 : k=axesRole true
  · subst k;rfl
  by_cases h3 : k=precisionRole true
  · subst k;rfl
  simp only [choice,h0,h1,h2,h3,ite_false,data,work,Sum.elim_inl,mask,Header,
    or_self,materialize]
/-- Raw shadows themselves stay physically empty in every stable bank. -/
theorem shadow_empty (i : Inputs) (w : Words) (k : ChoiceStack) (hk : Header k) : data i w (work k)=[]:=ite_eq_left hk
/-- Updating an ordinary source word commutes with masking the four other literal roles. -/
theorem mask_update (source : ChoiceStack→List Bool) (k : ChoiceStack) (word : List Bool) (hk : ¬Header k) :
    mask (Function.update source k word)=Function.update (mask source) k word:=by
  funext j
  by_cases he : j=k
  · subst j
    simp only [mask,hk,ite_false,Function.update_self]
  · simp only [mask,Function.update_of_ne he]
/-- Parsing directly into a source operand changes no caller input or shadow. -/
theorem update_source (i : Inputs) (w : Words) (k : ChoiceStack) (word : List Bool) (hk : ¬Header k) :
    Function.update (data i w) (choice k) word=data i {w with source:=Function.update w.source k word}:=by
  have h0 : k≠axesRole false:=fun h=>hk (Or.inl h)
  have h1 : k≠precisionRole false:=fun h=>hk (Or.inr (Or.inl h))
  have h2 : k≠axesRole true:=fun h=>hk (Or.inr (Or.inr (Or.inl h)))
  have h3 : k≠precisionRole true:=fun h=>hk (Or.inr (Or.inr (Or.inr h)))
  simp only [choice,h0,h1,h2,h3,ite_false,data,mask_update _ _ _ hk,work]
  exact (SemiprimeD1StackRename.payload_update _ _ k word).symm
/-- Actual parent table, ordinal order, child scope and singleton activity are work operands. -/
theorem operand_not_header : ¬Header parentRole ∧ ¬Header orderRole ∧ ¬Header scopeRole ∧ ¬Header X.activity:=by decide
/-- Physical record-reader update is an exact whole-bank update. -/
theorem update_records (i : Inputs) (w : Words) (word : List Bool) :
    Function.update (data i w) (aux .recordsReader) word=data i {w with records:=word}:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Physical activity-reader update is an exact whole-bank update. -/
theorem update_activation (i : Inputs) (w : Words) (word : List Bool) :
    Function.update (data i w) (aux .activationReader) word=data i {w with activation:=word}:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Physical scope-reader update is an exact whole-bank update. -/
theorem update_scopes (i : Inputs) (w : Words) (word : List Bool) :
    Function.update (data i w) (aux .scopesReader) word=data i {w with scopes:=word}:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Physical order-reader update is an exact whole-bank update. -/
theorem update_orders (i : Inputs) (w : Words) (word : List Bool) :
    Function.update (data i w) (aux .ordersReader) word=data i {w with orders:=word}:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Physical disposal-buffer update is an exact whole-bank update. -/
theorem update_ports (i : Inputs) (w : Words) (word : List Bool) :
    Function.update (data i w) (aux .oldPorts) word=data i {w with oldPorts:=word}:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- The growing history is changed only by actual row splicing or final reversal. -/
theorem update_history (i : Inputs) (w : Words) (word : List Bool) :
    Function.update (data i w) (aux .history) word=data i {w with history:=word}:=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackOldVertexStreamView
