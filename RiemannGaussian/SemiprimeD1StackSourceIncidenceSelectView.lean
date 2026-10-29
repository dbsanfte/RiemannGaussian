/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectPrimitives
/-! # Complete physical selector banks during temporary choice and rollback
The views are theorem-side descriptions of the fixed63 physical stacks. No view,
function, prefix list, result or native counter inhabits machine control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
open SemiprimeD1StackSourceIncidenceSelect
/-- All25 shared environment,22 scorer and16 private selector words, with none omitted. -/
def view (env:E.Stack→List Bool) (scoreWords:SemiprimeD1StackSourceIncidence.Aux→List Bool)
    (words:Aux→List Bool) :Stack→List Bool :=Sum.elim (Sum.elim env scoreWords) words
/-- Any shared environment update changes exactly its actual directly aliased field. -/
theorem update_environment (env:E.Stack→List Bool) (scoreWords:SemiprimeD1StackSourceIncidence.Aux→List Bool)
    (words:Aux→List Bool) (k:E.Stack) (word:List Bool) :
    Function.update (view env scoreWords words) (environmentStack k) word=
      view (Function.update env k word) scoreWords words :=by
  funext i
  rcases i with i|i
  · rcases i with i|i
    · simp only [Function.update_apply,view,environmentStack,queryStack,Q.environmentStack,Sum.elim_inl,Sum.inl.injEq]
    · rfl
  · rfl
/-- Any actual scorer-private update retains the full25 environment and16 caller roles. -/
theorem update_score (env:E.Stack→List Bool) (scoreWords:SemiprimeD1StackSourceIncidence.Aux→List Bool)
    (words:Aux→List Bool) (k:SemiprimeD1StackSourceIncidence.Aux) (word:List Bool) :
    Function.update (view env scoreWords words) (queryStack (Q.aux k)) word=
      view env (Function.update scoreWords k word) words :=by
  funext i
  rcases i with i|i
  · rcases i with i|i
    · rfl
    · simp only [Function.update_apply,view,queryStack,Q.aux,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq]
  · rfl
/-- Every private parser/snapshot/incumbent/compare update retains all47 physical scorer/cache roles. -/
theorem update_private (env:E.Stack→List Bool) (scoreWords:SemiprimeD1StackSourceIncidence.Aux→List Bool)
    (words:Aux→List Bool) (k:Aux) (word:List Bool) :
    Function.update (view env scoreWords words) (aux k) word=
      view env scoreWords (Function.update words k word) :=by
  funext i
  rcases i with i|i
  · rfl
  · simp only [Function.update_apply,view,aux,Sum.elim_inr,Sum.inr.injEq]
/-- Exact original cache projection required by the real query, with arbitrary retained selected-vector bytes. -/
def environment (ids:List (List Bool)) (chosen pfx:List Bool) :E.Stack→List Bool :=
  (SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids chosen [] pfx).data
/-- The only persistent query-private inputs and its physically acquired total score. -/
def scoreWords (stream square cube fourth total:List Bool) :SemiprimeD1StackSourceIncidence.Aux→List Bool
  | .source=>stream | .square=>square | .cube=>cube | .fourth=>fourth | .total=>total | _=>[]
/-- The only persistent selector inputs and physically held variable/candidate state. -/
def privateWords (catalogue owners factors todo reader savedKey bestID bestScore:List Bool) :Aux→List Bool
  | .catalogue=>catalogue | .owners=>owners | .factors=>factors | .todo=>todo | .reader=>reader
  | .savedKey=>savedKey | .bestID=>bestID | .bestScore=>bestScore | _=>[]
/-- Canonical clean bank between actual candidate calls and parser rounds. -/
def clean (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors
    todo reader savedKey bestID bestScore total:List Bool) :Stack→List Bool :=
  view (environment ids chosen pfx) (scoreWords stream square cube fourth total)
    (privateWords catalogue owners factors todo reader savedKey bestID bestScore)
/-- Canonical25-role projection is exact even while a temporary candidate dictionary has an older selected vector. -/
theorem clean_environment (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors
    todo reader savedKey bestID bestScore total:List Bool) (k:E.Stack) :
    clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total
      (environmentStack k)=environment ids chosen pfx k :=rfl
/-- All47 query roles agree with the actual no-total input bank before a real scorer call. -/
theorem clean_query (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors
    todo reader savedKey bestID bestScore:List Bool) (k:Q.Stack) :
    clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore []
      (queryStack k)=Q.data (environment ids chosen pfx) stream square cube fourth k :=by
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Updating the physical chosen role preserves the entire other62-word clean bank. -/
theorem clean_chosen (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (candidate) word=clean ids word pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical pfx role preserves the entire other62-word clean bank. -/
theorem clean_pfx (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (selected) word=clean ids chosen word stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical total role preserves the entire other62-word clean bank. -/
theorem clean_total (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (score) word=clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical todo role preserves the entire other62-word clean bank. -/
theorem clean_todo (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (aux .todo) word=clean ids chosen pfx stream square cube fourth catalogue owners factors word reader savedKey bestID bestScore total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical reader role preserves the entire other62-word clean bank. -/
theorem clean_reader (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (aux .reader) word=clean ids chosen pfx stream square cube fourth catalogue owners factors todo word savedKey bestID bestScore total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical savedKey role preserves the entire other62-word clean bank. -/
theorem clean_savedKey (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (aux .savedKey) word=clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader word bestID bestScore total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical bestID role preserves the entire other62-word clean bank. -/
theorem clean_bestID (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (aux .bestID) word=clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey word bestScore total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Updating the physical bestScore role preserves the entire other62-word clean bank. -/
theorem clean_bestScore (ids:List (List Bool)) (chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total word:List Bool) :
    Function.update (clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID bestScore total) (aux .bestScore) word=clean ids chosen pfx stream square cube fourth catalogue owners factors todo reader savedKey bestID word total :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectView
