/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFreshBankRestoreOriginal
import RiemannGaussian.SemiprimeD1StackJetBlocksOriginal
/-! # Actual cached-phase coefficient consumer: restore, guard, fold and blocks
Only the physical heap, counter, issued reference and nested child-result tape
enter. The real restorer supplies both distinct contexts and q. Ten real
preserving copies feed the actual fold-ready and block-ready programs. Every
allocated component/shadow/work role is counted; no bank/value/solver is a
runtime operand. Recursive child acquisition remains an upstream obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhase
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Restore
export SemiprimeD1StackFreshBankRestore
  (Stack Label program initial freshStack heapStack originalInput stack_card)
end Restore
namespace Fold
export SemiprimeD1StackJetFold
  (Stack Label program initial axes rank width aux output stack_card)
end Fold
namespace Blocks
export SemiprimeD1StackJetBlocks (Stack Label program contextStack aux stack_card)
end Blocks
namespace Fresh
export SemiprimeD1StackPhaseChildContextFresh (Stack contextStack)
end Fresh
namespace Header
export SemiprimeD1StackPhaseChildContext (oldStack childStack aux blocks)
end Header
namespace X
export SemiprimeD1StackJetContext (Stack axesCache precisionBits rankCache widthCache)
end X
/-- All95 restored/cache/read roles, all111 fold roles, all31 block roles and one copy scratch. -/
abbrev Stack :=Restore.Stack⊕(Fold.Stack⊕(Blocks.Stack⊕Unit))
/-- Complete physical restore bank inclusion, retained after its real call. -/
def restoreStack :Restore.Stack→Stack :=Sum.inl
/-- Complete physical ordered-fold bank inclusion. -/
def foldStack (k:Fold.Stack) :Stack :=.inr (.inl k)
/-- Complete physical block-source bank inclusion. -/
def blockStack (k:Blocks.Stack) :Stack :=.inr (.inr (.inl k))
/-- One actual preserving-copy scratch, cleared after every copy. -/
def copyScratch :Stack :=.inr (.inr (.inr ()))
/-- Actual restored old/new context role, with neither cache regenerated. -/
def restoredContext (child:Bool) (k:X.Stack) :Stack :=
  restoreStack (Restore.freshStack (Fresh.contextStack (if child then Header.childStack k else Header.oldStack k)))
/-- Actual restored phase success marker; it is peeked and retained. -/
def phaseValid :Stack :=restoreStack (Restore.freshStack (Fresh.contextStack (Header.aux .valid)))
/-- Actual restored q marker word, acquired originally by P48. -/
def blockCount :Stack :=restoreStack (Restore.freshStack (Fresh.contextStack Header.blocks))
/-- Ten fixed code sites, never a data-dependent offset or supplied index. -/
inductive Copy where
  | newAxes | newPrecision | newRank | newWidth | oldAxes | oldPrecision | oldRank | oldWidth | blocks | coefficients
  deriving DecidableEq,Repr
instance :Fintype Copy :=Fintype.ofList
  [.newAxes,.newPrecision,.newRank,.newWidth,.oldAxes,.oldPrecision,.oldRank,.oldWidth,.blocks,.coefficients]
  (by intro k;cases k <;> simp)
/-- Each source is a physically restored word or the actual folded coefficient output. -/
def copySource :Copy→Stack
  | .newAxes=>restoredContext true X.axesCache
  | .newPrecision=>restoredContext true X.precisionBits
  | .newRank=>restoredContext true X.rankCache
  | .newWidth=>restoredContext true X.widthCache
  | .oldAxes=>restoredContext false X.axesCache
  | .oldPrecision=>restoredContext false X.precisionBits
  | .oldRank=>restoredContext false X.rankCache
  | .oldWidth=>restoredContext false X.widthCache
  | .blocks=>blockCount
  | .coefficients=>foldStack Fold.output
/-- The actual visible cache/input words, with every other component word initially empty. -/
def copyTarget :Copy→Stack
  | .newAxes=>foldStack Fold.axes
  | .newPrecision=>foldStack (Fold.aux .precision)
  | .newRank=>foldStack Fold.rank
  | .newWidth=>foldStack Fold.width
  | .oldAxes=>blockStack (Blocks.contextStack X.axesCache)
  | .oldPrecision=>blockStack (Blocks.contextStack X.precisionBits)
  | .oldRank=>blockStack (Blocks.contextStack X.rankCache)
  | .oldWidth=>blockStack (Blocks.contextStack X.widthCache)
  | .blocks=>blockStack (Blocks.aux .blocks)
  | .coefficients=>blockStack (Blocks.aux .coefficients)
/-- All three real copy operands are concrete distinct physical words. -/
def copyStack (site:Copy) (k:Fin 3) :Stack :=
  if k=0 then copySource site else if k=1 then copyTarget site else copyScratch
/-- Fixed literal call/copy/guard/rejection/halt control. -/
inductive Control where | start | check | copy (site:Copy) | fold | blocks | reject | done
  deriving DecidableEq,Fintype
/-- All actual component return addresses remain fixed finite before every operand family. -/
inductive Label where
  | local (pc:Control) | restore (pc:Restore.Label) | fold (pc:Fold.Label)
  | blocks (pc:Blocks.Label) | copy (site:Copy) (pc:Fin 9)
  deriving Fintype
local notation "ctl" => Label.local
/-- Literal next code address at each of the ten physical copy sites. -/
def copyNext :Copy→Label
  | .newAxes=>ctl (.copy .newPrecision)
  | .newPrecision=>ctl (.copy .newRank)
  | .newRank=>ctl (.copy .newWidth)
  | .newWidth=>ctl .fold
  | .oldAxes=>ctl (.copy .oldPrecision)
  | .oldPrecision=>ctl (.copy .oldRank)
  | .oldRank=>ctl (.copy .oldWidth)
  | .oldWidth=>ctl (.copy .blocks)
  | .blocks=>ctl (.copy .coefficients)
  | .coefficients=>ctl .blocks
/-- One actual program, with real cache access, original phase guard and paid component handoffs. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.restore (.inl .start)) (ctl .check)
  | .local .check=>.base (.peek phaseValid (ctl .reject) (ctl .reject) (ctl (.copy .newAxes)))
  | .local (.copy site)=>.call (.copy site 0) (copyNext site)
  | .local .fold=>.call (.fold (.local .prepared)) (ctl (.copy .oldAxes))
  | .local .blocks=>.call (.blocks (.local .ready)) (ctl .done)
  | .local .reject=>.base (.push (blockStack (Blocks.aux .output)) false (ctl .done))
  | .local .done=>.base .halt
  | .restore pc=>SemiprimeD1StackValidationLink.instruction restoreStack Label.restore (Restore.program pc)
  | .fold pc=>SemiprimeD1StackValidationLink.instruction foldStack Label.fold (Fold.program pc)
  | .blocks pc=>SemiprimeD1StackValidationLink.instruction blockStack Label.blocks (Blocks.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
/-- Entire actual component banks plus the actual copy scratch. Functions are proof notation only. -/
def data (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch:List Bool) :Stack→List Bool :=
  Sum.elim restored (Sum.elim fold (Sum.elim blocks (fun _=>scratch)))
/-- Four original physical words; every other238-role field is empty. -/
def input (heap counter reference children:List Bool) :Stack→List Bool :=
  data (Restore.initial heap counter reference).data (Fold.initial [] [] children).data (fun _=>[]) []
/-- Literal issued-cache and prepared-child input, before the one real restore call. -/
def initial (heap counter reference children:List Bool) :C.State Stack Label :=
  ⟨some (ctl .start),none,none,input heap counter reference children,[]⟩
/-- Fixed finite238-role cached-phase consumer, with no original-input factoring claim at this boundary. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine
  (restoreStack Restore.originalInput) (blockStack (Blocks.aux .output)) (ctl .start) program
/-- Every actual copy source, target and scratch remains distinct. -/
theorem copy_injective (site:Copy) :Function.Injective (copyStack site) :=by cases site <;> decide
/-- All238 allocated data roles, including every unused component shadow, are included. -/
theorem stack_card :Fintype.card Stack=238 :=by
  rw [Fintype.card_sum,Restore.stack_card,Fintype.card_sum,Fold.stack_card,Fintype.card_sum,Blocks.stack_card]
  decide
/-- Actual runtime flags have only finite Boolean/read/return-label information. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every data and actual return alphabet is fixed finite before every physical heap and child tape. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackCachePhase
