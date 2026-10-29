/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhasePrimitives
/-! # Four actual NEW-context handoff copies before the real ordered fold
Every source byte is read from the restored bank. All fifteen actual new
context fields are represented at the destination; eleven are empty at ready.+-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseNewCache
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseView SemiprimeD1StackCachePhasePrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Actual four copied words; no context value is evaluated by the source. -/
def newAxes (restored:Restore.Stack→List Bool) :List Bool :=restored (Restore.freshStack (Fresh.contextStack (Header.childStack X.axesCache)))
/-- Actual restored binary NEW precision. -/
def newPrecision (restored:Restore.Stack→List Bool) :List Bool :=restored (Restore.freshStack (Fresh.contextStack (Header.childStack X.precisionBits)))
/-- Actual restored NEW unary rank. -/
def newRank (restored:Restore.Stack→List Bool) :List Bool :=restored (Restore.freshStack (Fresh.contextStack (Header.childStack X.rankCache)))
/-- Actual restored NEW unary numerical precision width. -/
def newWidth (restored:Restore.Stack→List Bool) :List Bool :=restored (Restore.freshStack (Fresh.contextStack (Header.childStack X.widthCache)))
/-- Full physical111-role bank after four actual cache copies and before the real fold call. -/
def foldReady (restored:Restore.Stack→List Bool) (children:List Bool) :Fold.Stack→List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Fold.initial [] [] children).data Fold.axes (newAxes restored))
    (Fold.aux .precision) (newPrecision restored)) Fold.rank (newRank restored)) Fold.width (newWidth restored)
/-- Exact actual four-copy clock including every restoration loop and real return. -/
def newCopyTime (restored:Restore.Stack→List Bool) :Nat :=
  5*((newAxes restored).length+(newPrecision restored).length+(newRank restored).length+(newWidth restored).length)+16
/-- The literal four NEW-cache copies preserve the entire95-role source and all31 block roles. -/
theorem new_cache_run (restored:Restore.Stack→List Bool) (children:List Bool)
    (blocks:Blocks.Stack→List Bool) :
    Runs program (newCopyTime restored) (ctl (.copy .newAxes))
      (data restored (Fold.initial [] [] children).data blocks []) (ctl .fold)
      (data restored (foldReady restored children) blocks []) :=by
  let f0:=(Fold.initial [] [] children).data
  let f1:=Function.update f0 Fold.axes (newAxes restored)
  let f2:=Function.update f1 (Fold.aux .precision) (newPrecision restored)
  let f3:=Function.update f2 Fold.rank (newRank restored)
  let f4:=Function.update f3 Fold.width (newWidth restored)
  have h0:=copy_call .newAxes (data restored f0 blocks []) (newAxes restored) [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*(newAxes restored).length+4) _ _ _
    (Function.update (data restored f0 blocks []) (foldStack Fold.axes) (newAxes restored)) at h0
  rw [data_fold] at h0
  have h1:=copy_call .newPrecision (data restored f1 blocks []) (newPrecision restored) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(newPrecision restored).length+4) _ _ _
    (Function.update (data restored f1 blocks []) (foldStack (Fold.aux .precision)) (newPrecision restored)) at h1
  rw [data_fold] at h1
  have h2:=copy_call .newRank (data restored f2 blocks []) (newRank restored) [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program (5*(newRank restored).length+4) _ _ _
    (Function.update (data restored f2 blocks []) (foldStack Fold.rank) (newRank restored)) at h2
  rw [data_fold] at h2
  have h3:=copy_call .newWidth (data restored f3 blocks []) (newWidth restored) [] rfl rfl rfl
  simp only [List.append_nil] at h3
  change Runs program (5*(newWidth restored).length+4) _ _ _
    (Function.update (data restored f3 blocks []) (foldStack Fold.width) (newWidth restored)) at h3
  rw [data_fold] at h3
  have h:=join (join (join h0 h1) h2) h3
  change Runs program _ _ _ (ctl .fold) _ at h
  change Runs program _ _ _ _ (data restored f4 blocks [])
  convert h using 1
  unfold newCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseNewCache
