/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseNewCache
import RiemannGaussian.SemiprimeD1StackCachePhaseOldCache
/-! # Exact acquired-cache boundaries after the ten actual preserving copies
The predicates below describe the actual restored bytes. They are proof-only;
the runtime accepts no bank, rank, context, decoded precision or coefficient.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseNewCache SemiprimeD1StackCachePhaseOldCache
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace FS
export SemiprimeD1StackJetFoldState (data address values data_update initial_data)
end FS
/-- The full actual stopped OLD/NEW caches, phase flag and q, supplied by the real restorer in proofs only. -/
structure ValidCache (bank:Fresh.Stack→List Bool) (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool) :Prop where
  guard :bank (Fresh.contextStack (Header.aux .valid))=[true]
  old :∀k,bank (Fresh.contextStack (Header.oldStack k))=SemiprimeD1StackJetContextCorrectness.finalData axes p k
  child :∀k,bank (Fresh.contextStack (Header.childStack k))=SemiprimeD1StackJetContextCorrectness.finalData (q::axes) newP k
  blocks :bank (Fresh.contextStack Header.blocks)=List.replicate q true
/-- Four literal physical word updates are exactly the frozen fold-ready cache. -/
theorem fold_updates (axes:List Nat) (precision children:List Bool) :
    Function.update (Function.update (Function.update (Function.update
      (Fold.initial [] [] children).data Fold.axes (vectorBits (axes.map unary)))
      (Fold.aux .precision) precision) Fold.rank (unary axes.prod)) Fold.width
      (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue precision))=
      (SemiprimeD1StackJetFoldContext.ready axes precision children).data :=by
  rw [FS.initial_data]
  change Function.update (Function.update (Function.update (Function.update
    (FS.data (FS.values [] [] children [] [] [] [] [] [] [] [] [] [] []))
    (FS.address .axes) (vectorBits (axes.map unary))) (FS.address .precision) precision)
    (FS.address .rank) (unary axes.prod)) (FS.address .width)
      (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue precision))=_
  rw [←FS.data_update,←FS.data_update,←FS.data_update,←FS.data_update]
  apply congrArg FS.data
  funext s;cases s <;> rfl
/-- The completed real NEW-cache transfers are the exact acquired fold entry, not a rank/width oracle. -/
theorem foldReady_actual (bank:Fresh.Stack→List Bool) (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool)
    (hv:ValidCache bank axes p q newP) (heap counter reference children:List Bool) :
    foldReady (SemiprimeD1StackFreshBankRestore.result bank heap counter reference) children=
      (SemiprimeD1StackJetFoldContext.ready (q::axes) newP children).data :=by
  unfold foldReady
  have ha:newAxes (SemiprimeD1StackFreshBankRestore.result bank heap counter reference)=vectorBits ((q::axes).map unary):=hv.child X.axesCache
  have hp:newPrecision (SemiprimeD1StackFreshBankRestore.result bank heap counter reference)=newP:=hv.child X.precisionBits
  have hr:newRank (SemiprimeD1StackFreshBankRestore.result bank heap counter reference)=unary (q::axes).prod:=hv.child X.rankCache
  have hw:newWidth (SemiprimeD1StackFreshBankRestore.result bank heap counter reference)=
      SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue newP):=hv.child X.widthCache
  rw [ha,hp,hr,hw]
  exact fold_updates (q::axes) newP children
/-- Six literal word updates fill every actually live block-ready cache/input field. -/
theorem block_updates (axes:List Nat) (p:List Bool) (q:Nat) (words:List (List Bool)) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (fun _=>[]) (Blocks.contextStack X.axesCache) (vectorBits (axes.map unary)))
      (Blocks.contextStack X.precisionBits) p) (Blocks.contextStack X.rankCache) (unary axes.prod))
      (Blocks.contextStack X.widthCache) (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue p)))
      (Blocks.aux .blocks) (List.replicate q true)) (Blocks.aux .coefficients) (vectorBits words)=
      (SemiprimeD1StackJetBlocksReady.ready (SemiprimeD1StackJetBlocksExecution.contextResult axes p) q words).data :=by
  funext k;rcases k with k|k
  · fin_cases k <;> rfl
  · cases k <;> rfl
/-- OLD cache/q plus ACTUAL fold output form exactly the frozen block-ready boundary. -/
theorem blockReady_actual (bank:Fresh.Stack→List Bool) (axes:List Nat) (p:List Bool) (q:Nat) (newP:List Bool)
    (hv:ValidCache bank axes p q newP) (heap counter reference:List Bool) (fold:Fold.Stack→List Bool)
    (words:List (List Bool)) (hc:fold Fold.output=vectorBits words) :
    blockReady (SemiprimeD1StackFreshBankRestore.result bank heap counter reference) fold=
      (SemiprimeD1StackJetBlocksReady.ready (SemiprimeD1StackJetBlocksExecution.contextResult axes p) q words).data :=by
  unfold blockReady
  have ha:oldContext (SemiprimeD1StackFreshBankRestore.result bank heap counter reference) X.axesCache=vectorBits (axes.map unary):=hv.old X.axesCache
  have hp:oldContext (SemiprimeD1StackFreshBankRestore.result bank heap counter reference) X.precisionBits=p:=hv.old X.precisionBits
  have hr:oldContext (SemiprimeD1StackFreshBankRestore.result bank heap counter reference) X.rankCache=unary axes.prod:=hv.old X.rankCache
  have hw:oldContext (SemiprimeD1StackFreshBankRestore.result bank heap counter reference) X.widthCache=
      SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue p):=hv.old X.widthCache
  have hq:blockWord (SemiprimeD1StackFreshBankRestore.result bank heap counter reference)=List.replicate q true:=hv.blocks
  rw [ha,hp,hr,hw,hq,hc]
  exact block_updates axes p q words
end RiemannGaussian.SemiprimeD1StackCachePhaseProjection
