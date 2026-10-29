/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseMetadataBounds
/-! # All ten actual cache copies and the real block scan fit physical-input bounds -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseCopyBounds
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseInputBounds SemiprimeD1StackCachePhaseMetadataBounds
open SemiprimeD1StackCachePhaseNewCache SemiprimeD1StackCachePhaseOldCache
open SemiprimeD1StackJetFoldWords (Modes)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- The four real NEW-cache handoffs are paid by the actual restored words. -/
theorem newCopyTime_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) :
    newCopyTime (restored banks i) ≤ 1000000*(inputSize banks i modes+1)^2 :=by
  have h0:(newAxes (restored banks i)).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.childStack X.axesCache)))
  have h1:(newPrecision (restored banks i)).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.childStack X.precisionBits)))
  have h2:(newRank (restored banks i)).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.childStack X.rankCache)))
  have h3:(newWidth (restored banks i)).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.childStack X.widthCache)))
  unfold newCopyTime
  nlinarith only [h0,h1,h2,h3]
/-- Four OLD-cache fields, actual q and the actual folded output pay all six post-fold copies. -/
theorem oldCopyTime_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    oldCopyTime (restored banks i) (folded axes q newP modes) ≤ 10000000000*(inputSize banks i modes+1)^2 :=by
  have h0:(oldContext (restored banks i) X.axesCache).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.oldStack X.axesCache)))
  have h1:(oldContext (restored banks i) X.precisionBits).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.oldStack X.precisionBits)))
  have h2:(oldContext (restored banks i) X.rankCache).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.oldStack X.rankCache)))
  have h3:(oldContext (restored banks i) X.widthCache).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack (Header.oldStack X.widthCache)))
  have h4:(blockWord (restored banks i)).length ≤ 1001*inputSize banks i modes :=
    restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack Header.blocks))
  have h5:=folded_length_le banks i axes p q newP modes hv
  unfold oldCopyTime
  nlinarith only [h0,h1,h2,h3,h4,h5]
/-- q times OLD rank is already the physically stored NEW rank; its value is paid once in the real heap. -/
theorem block_rank_markers_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    q*(axes.prod+1) ≤ 10000*(inputSize banks i modes+1) :=by
  have hq:=restored_word_le banks i modes (Restore.freshStack (Fresh.contextStack Header.blocks))
  change (banks[i.val] (Fresh.contextStack Header.blocks)).length ≤ 1001*inputSize banks i modes at hq
  rw [hv.blocks,List.length_replicate] at hq
  have hr:q*axes.prod ≤ 1001*inputSize banks i modes := (child_dimensions banks i axes p q newP modes hv).1
  nlinarith only [hq,hr]
/-- The SAME actual block-ready source is paid by the physical folded vector and acquired rank markers. -/
theorem blockBound_le (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (hv:ValidCache banks[i.val] axes p q newP) :
    SemiprimeD1StackJetBlocksReady.readyBound axes.prod q (coefficients axes q newP modes) ≤
      1000000000000*(inputSize banks i modes+1)^2 :=by
  have h:=SemiprimeD1StackJetBlocksBounds.readyBound_linear axes.prod q (coefficients axes q newP modes)
  have hout:=folded_length_le banks i axes p q newP modes hv
  have he:folded axes q newP modes Fold.output=vectorBits (coefficients axes q newP modes):=
    SemiprimeD1StackJetFoldExecution.output_words (q::axes) newP modes
  rw [he] at hout
  have hq:=block_rank_markers_le banks i axes p q newP modes hv
  nlinarith only [h,hout,hq]
end RiemannGaussian.SemiprimeD1StackCachePhaseCopyBounds

