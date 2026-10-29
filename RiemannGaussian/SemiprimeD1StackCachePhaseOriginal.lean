/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseStorage
/-! # Exact original cache shape and native ascending coefficient readout
All cache validity facts are consequences of the real Fresh producer. Its OLD
precision and NEW working precision stay independent; no native clock is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseOriginal
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseInputBounds
open SemiprimeD1StackJetFoldWords (Modes modeTape)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Every actually accepted Fresh85 bank contains exactly both required context caches and original q. -/
theorem valid_fresh (a u edges:Nat) (t p:List Bool) (axes:List Nat)
    (hg:SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t=true) :
    ValidCache (SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t p axes) axes p
      (SemiprimeD1StackPhaseChildContextPrimitives.count a u edges t)
      (SemiprimeD1StackPhaseChildContextPrimitives.precision a u edges t p) :=by
  constructor
  · change [SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t]=[true]
    rw [hg]
  · intro k
    rw [SemiprimeD1StackPhaseChildContextFreshOriginal.context_retained]
    exact (SemiprimeD1StackPhaseChildContextOriginal.acquired_caches a u edges t p axes hg).1 k
  · intro k
    rw [SemiprimeD1StackPhaseChildContextFreshOriginal.context_retained]
    exact (SemiprimeD1StackPhaseChildContextOriginal.acquired_caches a u edges t p axes hg).2 k
  · exact SemiprimeD1StackJetBlocksOriginal.fresh_q a u edges t p axes hg
/-- The original actual good flag provides positive q, with no external dimension supplier. -/
theorem fresh_q_positive (a u edges:Nat) (t:List Bool)
    (hg:SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t=true) :
    0 < SemiprimeD1StackPhaseChildContextPrimitives.count a u edges t :=
  ((SemiprimeD1StackPhaseChildContextArithmetic.good_true a u edges t).mp hg).2
/-- Whole accepted actual output is exactly the original ascending native block extraction. -/
theorem output_native (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) :
    result banks i axes p q newP modes (blockStack (Blocks.aux .output))=
      vectorBits ((List.range q).map (fun j=>vectorBits
        (SemiprimeD1JetBlockBits.extract (⟨axes,SemiprimeBitArithmetic.bitValue p⟩:SemiprimeD1JetAxes.Context)
          j (coefficients axes q newP modes)).words)) :=
  SemiprimeD1StackJetBlocksOriginal.output_native (SemiprimeD1StackJetBlocksExecution.contextResult axes p)
    ⟨axes,SemiprimeBitArithmetic.bitValue p⟩ q (coefficients axes q newP modes)
/-- The entire95-role cache/heap reader remains retained through actual folding and extraction. -/
theorem restore_retained (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (k:Restore.Stack) :
    result banks i axes p q newP modes (restoreStack k)=restored banks i k :=rfl
/-- Every111-role stopped fold field, including source/output and empty shadows, remains retained. -/
theorem fold_retained (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (p:List Bool) (q:Nat) (newP:List Bool) (modes:Modes) (k:Fold.Stack) :
    result banks i axes p q newP modes (foldStack k)=folded axes q newP modes k :=rfl
/-- Generic physical initial-word bridge, before any original graph/bank expression is instantiated. -/
theorem initial_from (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes)
    (heapBytes counterBytes referenceBytes:List Bool)
    (hh:heapBytes=heap banks) (hc:counterBytes=counter banks) (hr:referenceBytes=reference banks i) :
    initial heapBytes counterBytes referenceBytes (modeTape modes)=source banks i modes :=by
  subst heapBytes;subst counterBytes;subst referenceBytes;rfl
/-- Generic actual bit-length equality avoids expanding the original producer's arithmetic during elaboration. -/
theorem inputSize_from (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes)
    (heapBytes counterBytes referenceBytes:List Bool)
    (hh:heapBytes=heap banks) (hc:counterBytes=counter banks) (hr:referenceBytes=reference banks i) :
    heapBytes.length+counterBytes.length+referenceBytes.length+(modeTape modes).length+1=inputSize banks i modes :=by
  subst heapBytes;subst counterBytes;subst referenceBytes
  unfold inputSize SemiprimeD1StackFreshBankRestoreBounds.inputSize SemiprimeD1StackFreshBankRestoreBounds.resource
    heap counter reference
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseOriginal
