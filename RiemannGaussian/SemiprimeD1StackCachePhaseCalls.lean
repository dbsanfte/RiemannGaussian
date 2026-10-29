/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhasePrimitives
/-! # Three real whole-source calls, preserving all other allocated component words -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseCalls
open SemiprimeD1StackCachePhase SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- The actual heap/counter/issued reference drive one real complete restore, with child and block banks untouched. -/
theorem restore_call (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length)
    (fold:Fold.Stack→List Bool) (blocks:Blocks.Stack→List Bool) (scratch:List Bool) :
    ∃t≤SemiprimeD1StackFreshBankRestoreExecution.runBound banks i+1,
      Runs program t (ctl .start)
        (data (SemiprimeD1StackFreshBankRestoreExecution.source banks i).data fold blocks scratch)
        (ctl .check) (data (SemiprimeD1StackFreshBankRestoreExecution.target banks i).data fold blocks scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackFreshBankRestoreExecution.source_run banks i
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program restoreStack Label.restore
    (fun _ _ h=>Sum.inl.inj h) Restore.program (.inl .start) (fun _=>rfl)
    (ctl .start) (ctl .check) rfl t
    (SemiprimeD1StackFreshBankRestoreExecution.source banks i)
    (SemiprimeD1StackFreshBankRestoreExecution.target banks i) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The actual111-role ready fold, with all95 restored/cache words and all31 block words retained. -/
theorem fold_call (axes:List Nat) (hp:∀q∈axes,0<q) (precision:List Bool)
    (modes:SemiprimeD1StackJetFoldWords.Modes) (restored:Restore.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch:List Bool) :
    ∃t≤SemiprimeD1StackJetFoldBounds.runBound axes precision modes+1,
      Runs program t (ctl .fold)
        (data restored (SemiprimeD1StackJetFoldContext.ready axes precision
          (SemiprimeD1StackJetFoldWords.modeTape modes)).data blocks scratch)
        (ctl (.copy .oldAxes)) (data restored (SemiprimeD1StackJetFoldExecution.done axes precision modes).data blocks scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackJetFoldBounds.ready_run_bounded axes hp precision modes
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program foldStack Label.fold
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj h)) Fold.program (.local .prepared) (fun _=>rfl)
    (ctl .fold) (ctl (.copy .oldAxes)) rfl t
    (SemiprimeD1StackJetFoldContext.ready axes precision (SemiprimeD1StackJetFoldWords.modeTape modes))
    (SemiprimeD1StackJetFoldExecution.done axes precision modes) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- The actual31-role ready block scan, preserving both complete preceding physical source banks. -/
theorem blocks_call (context:X.Stack→List Bool) (rank q:Nat)
    (hrank:context X.rankCache=List.replicate rank true) (words:List (List Bool))
    (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool) (scratch:List Bool) :
    ∃t≤SemiprimeD1StackJetBlocksReady.readyBound rank q words+1,
      Runs program t (ctl .blocks)
        (data restored fold (SemiprimeD1StackJetBlocksReady.ready context q words).data scratch)
        (ctl .done) (data restored fold (SemiprimeD1StackJetBlocksReady.done context rank q words).data scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackJetBlocksReady.ready_run context rank q hrank words
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program blockStack Label.blocks
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))) Blocks.program (.local .ready) (fun _=>rfl)
    (ctl .blocks) (ctl .done) rfl t
    (SemiprimeD1StackJetBlocksReady.ready context q words)
    (SemiprimeD1StackJetBlocksReady.done context rank q words) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact (hk k rfl).elim
          · rfl
end RiemannGaussian.SemiprimeD1StackCachePhaseCalls
