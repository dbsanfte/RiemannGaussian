/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksStorage
import RiemannGaussian.SemiprimeD1StackJetFoldOriginal
/-! # Exact original phase blocks and distinct old/new acquired-cache bridges
Old precision can differ from the precision of the folded coefficient source.
The extractor copies the actual binary words unchanged, using only old rank.
These are exact physical cache/payload bridges, not a native-clock transport.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksOriginal
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksView SemiprimeD1StackJetBlocksEncoding
open SemiprimeD1StackJetBlocksReady SemiprimeD1StackJetBlocksExecution SemiprimeD1StackJetBlocksBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Every actual old context word is retained through the whole block traversal. -/
theorem context_retained (context:X.Stack→List Bool) (rank q:Nat) (words:List (List Bool)) (k:X.Stack) :
    (done context rank q words).data (contextStack k)=context k :=rfl
/-- Both actual q markers and the entire original coefficient vector remain available to the caller. -/
theorem inputs_retained (context:X.Stack→List Bool) (rank q:Nat) (words:List (List Bool)) :
    (done context rank q words).data (aux .coefficients)=vectorBits words ∧
    (done context rank q words).data (aux .blocks)=List.replicate q true :=⟨rfl,rfl⟩
/-- Literal output ABI is the original ascending offset extraction, including raw padded coefficient bytes. -/
theorem output_native (context:X.Stack→List Bool) (old:SemiprimeD1JetAxes.Context) (q:Nat)
    (words:List (List Bool)) :
    (done context old.rank q words).data (aux .output)=
      vectorBits ((List.range q).map (fun j=>vectorBits (SemiprimeD1JetBlockBits.extract old j words).words)) :=by
  change tape old.rank q words=_
  rw [tape,chunks_native,List.map_map]
  rfl
/-- The ENTIREactual15-role OLDcache in Fresh85 is exactly the extractor's reached ready cache. -/
theorem fresh_old_cache (a u edges:Nat) (t p:List Bool) (axes:List Nat)
    (hg:SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t=true) (q:Nat)
    (words:List (List Bool)) (k:X.Stack) :
    SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t p axes
      (SemiprimeD1StackPhaseChildContextFresh.contextStack (SemiprimeD1StackPhaseChildContext.oldStack k))=
      (ready (contextResult axes p) q words).data (contextStack k) :=by
  change _=contextResult axes p k
  rw [SemiprimeD1StackPhaseChildContextFreshOriginal.context_retained]
  exact (SemiprimeD1StackPhaseChildContextOriginal.acquired_caches a u edges t p axes hg).1 k
/-- q comes from the SAMEactual retained P48 phase cache, without a supplied dimension evaluator. -/
theorem fresh_q (a u edges:Nat) (t p:List Bool) (axes:List Nat)
    (hg:SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t=true) :
    SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t p axes
      (SemiprimeD1StackPhaseChildContextFresh.contextStack SemiprimeD1StackPhaseChildContext.blocks)=
      List.replicate (SemiprimeD1StackPhaseChildContextPrimitives.count a u edges t) true :=by
  have ha:SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives.accepted a u t=true:=
    ((SemiprimeD1StackPhaseChildContextArithmetic.good_true a u edges t).mp hg).1
  exact SemiprimeD1StackPhaseChildContextArithmetic.count_word a u edges t p ha
/-- Fold111's ACTUALoutput is the exact physical coefficient input of the block-ready program.
The old binary precision p and the folded child precision newP stay independent. -/
theorem fold_input (axes:List Nat) (p newP:List Bool) (q:Nat)
    (modes:SemiprimeD1StackJetFoldWords.Modes) :
    (SemiprimeD1StackJetFoldExecution.done (q::axes) newP modes).data SemiprimeD1StackJetFold.output=
      (ready (contextResult axes p) q
        (SemiprimeD1StackJetFoldWords.sumWords (SemiprimeD1StackJetFoldContext.context (q::axes) newP) modes)).data
        (aux .coefficients) :=
  SemiprimeD1StackJetFoldExecution.output_words (q::axes) newP modes
/-- The unchanged native block vector is obtained by the SAMEactual ready source with a linear own cap. -/
theorem ready_original (axes:List Nat) (p:List Bool) (q:Nat) (words:List (List Bool)) :
    ∃t≤1000*((vectorBits words).length+q*(axes.prod+1)+1),
      SemiprimeD1StackCalls.run program t (ready (contextResult axes p) q words)=
        some (done (contextResult axes p) axes.prod q words) :=
  ready_run_linear (contextResult axes p) axes.prod q rfl words
/-- Whole four-input acquisition still pays its real old context source, rather than assuming its rank/width. -/
theorem source_original (axes:List Nat) (hp:∀r∈axes,0<r) (p:List Bool) (q:Nat)
    (words:List (List Bool)) :
    ∃t≤10000*(resource axes p q words+1)^2,
      SemiprimeD1StackCalls.run program t (source axes p q words)=
        some (done (contextResult axes p) axes.prod q words) :=source_run_bounded axes hp p q words
end RiemannGaussian.SemiprimeD1StackJetBlocksOriginal
