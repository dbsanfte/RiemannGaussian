/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhasePrimitives
/-! # Six actual OLD-cache/q/coefficient copies after the real ordered fold
The raw coefficient vector comes from the actual fold output. OLD precision
and NEW folded coefficient precision remain separate throughout this source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseOldCache
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseView SemiprimeD1StackCachePhasePrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Entire actual OLD context projection, retained in the real restored bank. -/
def oldContext (restored:Restore.Stack→List Bool) (k:X.Stack) :List Bool :=
  restored (Restore.freshStack (Fresh.contextStack (Header.oldStack k)))
/-- Actual P48 q marker word in the SAME restored phase record. -/
def blockWord (restored:Restore.Stack→List Bool) :List Bool :=
  restored (Restore.freshStack (Fresh.contextStack Header.blocks))
/-- Full physical31-role block-ready bank, produced by six actual preserving copies. -/
def blockReady (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool) :Blocks.Stack→List Bool :=
  (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _=>[]) (Blocks.contextStack X.axesCache) (oldContext restored X.axesCache)) (Blocks.contextStack X.precisionBits) (oldContext restored X.precisionBits)) (Blocks.contextStack X.rankCache) (oldContext restored X.rankCache)) (Blocks.contextStack X.widthCache) (oldContext restored X.widthCache)) (Blocks.aux .blocks) (blockWord restored)) (Blocks.aux .coefficients) (fold Fold.output))
/-- Exact six-copy clock, including all actual caller returns. -/
def oldCopyTime (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool) :Nat :=
  5*((oldContext restored X.axesCache).length+(oldContext restored X.precisionBits).length+(oldContext restored X.rankCache).length+(oldContext restored X.widthCache).length+(blockWord restored).length+(fold Fold.output).length)+24
/-- All six actual post-fold handoffs preserve the complete95 and111 preceding component banks. -/
theorem old_cache_run (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool) :
    Runs program (oldCopyTime restored fold) (ctl (.copy .oldAxes))
      (data restored fold (fun _=>[]) []) (ctl .blocks) (data restored fold (blockReady restored fold) []) :=by
  let b0:Blocks.Stack→List Bool:=fun _=>[]
  let b1:=Function.update b0 (Blocks.contextStack X.axesCache) (oldContext restored X.axesCache)
  let b2:=Function.update b1 (Blocks.contextStack X.precisionBits) (oldContext restored X.precisionBits)
  let b3:=Function.update b2 (Blocks.contextStack X.rankCache) (oldContext restored X.rankCache)
  let b4:=Function.update b3 (Blocks.contextStack X.widthCache) (oldContext restored X.widthCache)
  let b5:=Function.update b4 (Blocks.aux .blocks) (blockWord restored)
  let b6:=Function.update b5 (Blocks.aux .coefficients) (fold Fold.output)
  have h0:=copy_call .oldAxes (data restored fold b0 []) (oldContext restored X.axesCache) [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*(oldContext restored X.axesCache).length+4) _ _ _
    (Function.update (data restored fold b0 []) (blockStack (Blocks.contextStack X.axesCache)) (oldContext restored X.axesCache)) at h0
  rw [data_blocks] at h0
  have h1:=copy_call .oldPrecision (data restored fold b1 []) (oldContext restored X.precisionBits) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(oldContext restored X.precisionBits).length+4) _ _ _
    (Function.update (data restored fold b1 []) (blockStack (Blocks.contextStack X.precisionBits)) (oldContext restored X.precisionBits)) at h1
  rw [data_blocks] at h1
  have h2:=copy_call .oldRank (data restored fold b2 []) (oldContext restored X.rankCache) [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program (5*(oldContext restored X.rankCache).length+4) _ _ _
    (Function.update (data restored fold b2 []) (blockStack (Blocks.contextStack X.rankCache)) (oldContext restored X.rankCache)) at h2
  rw [data_blocks] at h2
  have h3:=copy_call .oldWidth (data restored fold b3 []) (oldContext restored X.widthCache) [] rfl rfl rfl
  simp only [List.append_nil] at h3
  change Runs program (5*(oldContext restored X.widthCache).length+4) _ _ _
    (Function.update (data restored fold b3 []) (blockStack (Blocks.contextStack X.widthCache)) (oldContext restored X.widthCache)) at h3
  rw [data_blocks] at h3
  have h4:=copy_call .blocks (data restored fold b4 []) (blockWord restored) [] rfl rfl rfl
  simp only [List.append_nil] at h4
  change Runs program (5*(blockWord restored).length+4) _ _ _
    (Function.update (data restored fold b4 []) (blockStack (Blocks.aux .blocks)) (blockWord restored)) at h4
  rw [data_blocks] at h4
  have h5:=copy_call .coefficients (data restored fold b5 []) (fold Fold.output) [] rfl rfl rfl
  simp only [List.append_nil] at h5
  change Runs program (5*(fold Fold.output).length+4) _ _ _
    (Function.update (data restored fold b5 []) (blockStack (Blocks.aux .coefficients)) (fold Fold.output)) at h5
  rw [data_blocks] at h5
  have h:=(join (join (join (join (join h0 h1) h2) h3) h4) h5)
  change Runs program _ _ _ (ctl .blocks) _ at h
  change Runs program _ _ _ _ (data restored fold b6 [])
  convert h using 1
  unfold oldCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseOldCache

