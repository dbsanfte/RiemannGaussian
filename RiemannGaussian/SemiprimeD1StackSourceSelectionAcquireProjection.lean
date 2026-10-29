/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireSelectorInput
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireKeyInput
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOriginal
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOccurrences
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysOriginal
/-! # Exact physical selector/key-reader boundaries after actual paid source handoffs
The generic seven-word and three-live-environment-field equalities precede
original graph instantiation. All native graphs, selected IDs and ordered lists
occur solely in these proof interpretations of actual physically copied words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireProjection
open SemiprimeD1StackSourceSelectionAcquire
open SemiprimeD1StackSourceSelectionAcquireSelectorInput SemiprimeD1StackSourceSelectionAcquireKeyInput
attribute [local irreducible] SemiprimeD1IncidenceSearch.run
/-- Seven actual literal writes are precisely the complete fixed63-role selector input, with every other role empty. -/
theorem selector_input_updates (occurrences catalogue square cube fourth owners factors:List Bool) :
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _ :Select.Stack=>[]) (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source)) occurrences)
      (Select.aux .catalogue) catalogue) (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .square)) square)
      (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .cube)) cube)
      (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .fourth)) fourth) (Select.aux .owners) owners)
      (Select.aux .factors) factors)=SemiprimeD1StackSourceIncidenceSelect.input occurrences catalogue square cube fourth owners factors :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Generic paid handoff bank equals the actual selector initializer on exactly the seven acquired source words. -/
theorem selectorReady_eq_initial (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) :
    selectorReady occurrences alphabet=(SemiprimeD1StackSourceIncidenceSelect.initial (occurrences .output)
      (alphabet (Alpha.aux .output)) (alphabet (Alpha.aux .square)) (alphabet (Alpha.aux .cube))
      (alphabet (Alpha.aux .fourth)) (occurrences .number) (occurrences .factors)).data :=
  selector_input_updates _ _ _ _ _ _ _
/-- Exactly dictionary, nextKey and prefix are live in the acquired Env25 boundary; all22 other roles are physically empty. -/
theorem environment_ready (ids:List (List Bool)) (pfx:List Bool) :
    Function.update (Function.update (Function.update (fun _ :Env.Stack=>[])
      (Env.aux .dictionary) (SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids))
      (Env.aux .nextKey) (SemiprimeD1StackSourceEnvironmentEncoding.variableKey ids.length)) (Env.aux .prefix) pfx=
      (SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids [] [] pfx).data :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Generic four-word actual handoff is the complete key-reader input on the identical acquired dictionary/key/prefix and occurrence bytes. -/
theorem keyReady_eq_source (selector:Select.Stack→List Bool) (ids:List (List Bool)) (pfx:List Bool)
    (rows:List (List Bool×List Bool))
    (hD:selector Select.dictionary=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids)
    (hK:selector Select.nextKey=SemiprimeD1StackSourceEnvironmentEncoding.variableKey ids.length)
    (hP:selector Select.selected=pfx)
    (hS:selector (Select.queryStack (SemiprimeD1StackSourceIncidence.aux .source))=SemiprimeD1StackOwnerLookup.records rows []) :
    keyReady selector=(SemiprimeD1StackSourceSelectedKeysEncoding.source ⟨ids,[],[],pfx,rows⟩).data :=by
  unfold keyReady
  rw [hD,hK,hP,hS]
  change _=SemiprimeD1StackSourceSelectedKeys.data (SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids [] [] pfx).data
    (SemiprimeD1StackOwnerLookup.records rows [])
  rw [←environment_ready]
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- The actual Occ21.done bank and actual Alpha30.result produce the exact original selector source, in its proven occurrence order. -/
theorem selectorReady_original (net:SemiprimeD1TensorNetwork.Network) (a:Nat) :
    selectorReady (SemiprimeD1StackSourceOccurrencesExecution.done net.leftCount
      (SemiprimeD1StackSourceOccurrencesEncoding.originalRows net)).data
      (SemiprimeD1StackSourceAlphabet64Encoding.result a)=
      (SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredSource net.leftCount net.rows.length a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).data :=by
  rw [selectorReady_eq_initial]
  have ho:=SemiprimeD1StackSourceOccurrencesOriginal.output_original net
  have hf:=SemiprimeD1StackSourceOccurrencesOriginal.factor_count net
  unfold SemiprimeD1StackSourceOccurrencesOriginal.originalDone at ho hf
  rw [ho,hf]
  rw [←SemiprimeD1StackSourceIncidenceSelectOccurrences.network_original_keys net a]
  rfl
/-- Both frozen original interfaces use the identical acquired metadata incidence list; no new ordering theorem is introduced. -/
theorem original_pairs (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    SemiprimeD1StackSourceSelectedKeysOriginal.originalPairs n F a arity owner=
      SemiprimeD1StackSourceIncidenceSelectMeaning.originalKeys n F a arity owner :=by
  rw [SemiprimeD1StackSourceSelectedKeysOriginal.canonical_namespace]
  rfl
/-- Actual stopped Selector63 supplies the complete actual selected Env25 and identical original occurrence order to Keys39, without replay. -/
theorem keyReady_original (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    keyReady (SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredDone n F a arity owner).data=
      (SemiprimeD1StackSourceSelectedKeysEncoding.source
        (SemiprimeD1StackSourceSelectedKeysOriginal.originalInput n F 64 a arity owner [] []
          (SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1IncidenceSearch.run n F 64 a arity owner).value))).data :=by
  apply keyReady_eq_source
  · change (SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredDone n F a arity owner).data
      (SemiprimeD1StackSourceIncidenceSelect.environmentStack (Env.aux .dictionary))=_
    rw [SemiprimeD1StackSourceIncidenceSelectOriginal.acquired_environment]
    rfl
  · change (SemiprimeD1StackSourceIncidenceSelectOriginal.acquiredDone n F a arity owner).data
      (SemiprimeD1StackSourceIncidenceSelect.environmentStack (Env.aux .nextKey))=_
    rw [SemiprimeD1StackSourceIncidenceSelectOriginal.acquired_environment]
    rfl
  · exact SemiprimeD1StackSourceIncidenceSelectOriginal.acquired_output n F a arity owner
  · rw [original_pairs]
    rfl
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireProjection
