/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexed
/-! # Literal all12-word boundaries for binary-index acquisition -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedState
open SemiprimeD1StackRecoveryEntriesIndexed
/-- Full physical word bank; all addresses remain fixed finite. -/
def store (left right work sum cache query counter reader parser value valid copy:List Bool):Stack → List Bool
  | .inl k=>A.store left right work sum k
  | .inr .cache=>cache | .inr .query=>query | .inr .counter=>counter | .inr .reader=>reader
  | .inr .parser=>parser | .inr .value=>value | .inr .valid=>valid | .inr .copy=>copy
/-- Real scan boundary has every arithmetic/parser/copy work field empty. -/
def view (cache query counter reader value:List Bool):Stack → List Bool:=store [] [] [] [] cache query counter reader [] value [] []
/-- Literal physical left word update. -/
theorem update_left (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inl .left:Stack) word=store word right work sum cache query counter reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical right word update. -/
theorem update_right (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inl .right:Stack) word=store left word work sum cache query counter reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical work word update. -/
theorem update_work (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inl .scratch:Stack) word=store left right word sum cache query counter reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical sum word update. -/
theorem update_sum (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inl .output:Stack) word=store left right work word cache query counter reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical cache word update. -/
theorem update_cache (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .cache:Stack) word=store left right work sum word query counter reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical query word update. -/
theorem update_query (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .query:Stack) word=store left right work sum cache word counter reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical counter word update. -/
theorem update_counter (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .counter:Stack) word=store left right work sum cache query word reader parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical reader word update. -/
theorem update_reader (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .reader:Stack) word=store left right work sum cache query counter word parser value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical parser word update. -/
theorem update_parser (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .parser:Stack) word=store left right work sum cache query counter reader word value valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical value word update. -/
theorem update_value (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .value:Stack) word=store left right work sum cache query counter reader parser word valid copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical valid word update. -/
theorem update_valid (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .valid:Stack) word=store left right work sum cache query counter reader parser value word copy:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Literal physical copy word update. -/
theorem update_copy (left right work sum cache query counter reader parser value valid copy word:List Bool):
    Function.update (store left right work sum cache query counter reader parser value valid copy) (.inr .copy:Stack) word=store left right work sum cache query counter reader parser value valid word:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
/-- Honest prepared two-input bank contains no supplied ordinal or answer. -/
theorem initial_store (cache query:List Bool):(initial cache query).data=view cache query [] [] []:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedState
