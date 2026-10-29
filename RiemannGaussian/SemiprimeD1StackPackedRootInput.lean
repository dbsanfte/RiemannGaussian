/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryOriginal
import RiemannGaussian.SemiprimeD1PackedRootRetained
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsOriginal
import RiemannGaussian.SemiprimeD1StackPackedRootContextOriginal
/-! # One original-input root source with marked records and the actual2ell header
The real2270-role source runs once. The marked source continues at its honest
ready entry over the SAME retained1804-role bank. All207 new marked-source
words and all28 context-source words are allocated, including every shadow.
Only original binary N is supplied. Old table-bearing catalogues are retained
as old data; downstream table reads must use the new marked record operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInput
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootPacketInventory (Stack Label program input initial originalInput copyScratch)
end R
namespace W
export SemiprimeD1StackMarkedRootRecords (Stack Label Aux program ctl originalInput aux)
end W
namespace J
export SemiprimeD1StackPackedRootContext (Stack Label program input originalInput context precision width rank)
end J
namespace Old
export SemiprimeD1StackRootNetworkRecords (Stack originalInput)
end Old
/-- Only the genuinely new207 marked-source roles; the old1804 bank is shared. -/
abbrev Private := SemiprimeD1StackVertexCatalogue.Stack⊕
  (SemiprimeD1StackMarkedPublicInputTable.Stack⊕W.Aux)
/-- Every retained2270, new207 and complete28 context word is physically counted. -/
abbrev Stack := R.Stack⊕(Private⊕J.Stack)
/-- The entire acquired root source remains present. -/
def rootStack : R.Stack→Stack := Sum.inl
/-- Actual retained1804 subbank inside Root2270, by static source inclusions only. -/
def retainedRoot (k : Old.Stack) : R.Stack :=
  SemiprimeD1PackedRootRetained.embed k
/-- A static inverse with an unused outside-bank default; no data-dependent address lookup. -/
def retainedRootInverse : R.Stack→Old.Stack
  | .inl (.inl (.inl (.inl (.inl (.inl k))))) => k
  | _ => Old.originalInput
/-- Real2011 program operands alias exactly the old bank plus fresh207 private words. -/
def markedStack : W.Stack→Stack
  | .inl k => rootStack (retainedRoot k)
  | .inr k => .inr (.inl k)
/-- Static marked-bank inverse, independent of every source word or acquired value. -/
def markedInverse : Stack→W.Stack
  | .inl k => .inl (retainedRootInverse k)
  | .inr (.inl k) => .inr k
  | .inr (.inr _) => .inl Old.originalInput
/-- All28 real context-source words have their own physical allocation. -/
def contextStack (k : J.Stack) : Stack := .inr (.inr k)
/-- Sole actual original binary-input role. -/
def originalInput : Stack := rootStack R.originalInput
/-- NEW weighted complete owner/factor records, separate from all old payloads. -/
def output : Stack := markedStack (W.aux .output)
/-- Physically retained rational-grid width; it depends only on acquired a/M. -/
def rationalWidth : Stack := rootStack SemiprimeD1StackRootPacketInventory.template
/-- Actual newly acquired binary tensor precision. -/
def precision : Stack := contextStack J.precision
/-- Actual newly acquired TRUE context width. -/
def width : Stack := contextStack J.width
/-- Actual newly acquired root rank. -/
def rank : Stack := contextStack J.rank
/-- One real preserving N handoff, using the stopped root's actual empty scratch. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then originalInput else if k=1 then contextStack J.originalInput else rootStack R.copyScratch
/-- Fixed source/ready/copy/context/halt stages only. -/
inductive Control where | start | marked | copyNumber | context | done
  deriving DecidableEq,Repr
/-- Literal five-stage enumeration, independent of every source value. -/
instance controlFintype : Fintype Control := Fintype.ofList [.start,.marked,.copyNumber,.context,.done]
  (by intro k;cases k <;> simp)
/-- Complete finite component and saved-return label bank, before every N. -/
inductive Label where
  | local (pc : Control) | root (pc : R.Label) | marked (pc : W.Label)
  | context (pc : J.Label) | copy (pc : Fin 9)
  deriving Fintype
/-- One genuine original-input source with no table, context, width or coefficient advice. -/
def program : Label→C.Instruction Stack Label
  | .local .start => .call (.root (.local .start)) (.local .marked)
  | .local .marked => .call (.marked (W.ctl .ready)) (.local .copyNumber)
  | .local .copyNumber => .call (.copy 0) (.local .context)
  | .local .context => .call (.context (.inl .start)) (.local .done)
  | .local .done => .base .halt
  | .root pc => SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .marked pc => SemiprimeD1StackValidationLink.instruction markedStack Label.marked (W.program pc)
  | .context pc => SemiprimeD1StackValidationLink.instruction contextStack Label.context (J.program pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
/-- Literal complete three-bank view, with no omitted unused role. -/
def bank (root : R.Stack→List Bool) (marked : Private→List Bool) (context : J.Stack→List Bool) :
    Stack→List Bool := Sum.elim root (Sum.elim marked context)
/-- Exactly original binary N is initially populated. -/
def input (bits : List Bool) : Stack→List Bool := bank (R.input bits) (fun _ => []) (fun _ => [])
/-- Genuine N-only front door, before all actual acquisition calls. -/
def initial (bits : List Bool) : C.State Stack Label :=
  ⟨some (.local .start),none,none,input bits,[]⟩
/-- One fixed finite original-input machine with NEW marked records as its output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput output (.local .start) program
/-- Every retained original-source operand has its exact static inverse. -/
theorem retainedRoot_inverse (k : Old.Stack) : retainedRootInverse (retainedRoot k)=k := rfl
/-- Sharing the retained old source never aliases its distinct words. -/
theorem retainedRoot_injective : Function.Injective retainedRoot := by
  intro a b h
  exact congrArg retainedRootInverse h
/-- Every real marked-source word retains an exact static inverse. -/
theorem marked_inverse (k : W.Stack) : markedInverse (markedStack k)=k := by cases k <;> rfl
/-- No marked-source operands alias each other. -/
theorem marked_injective : Function.Injective markedStack := by
  intro a b h
  have he:=congrArg markedInverse h
  simpa only [marked_inverse] using he
/-- Every actual context-source word is distinct. -/
theorem context_injective : Function.Injective contextStack := by
  intro a b h
  exact Sum.inr_injective (Sum.inr_injective h)
/-- The true N source, context input and restoring scratch are physically distinct. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- All2505 roles count the original cache, new marked shadows and full context bank. -/
theorem stack_card : Fintype.card Stack=2505 := by
  have hp : Fintype.card Private=207 := by
    have hs : Fintype.card (Old.Stack⊕Private)=Fintype.card Old.Stack+Fintype.card Private :=
      Fintype.card_sum
    have h : Fintype.card Old.Stack+Fintype.card Private=2011 :=
      hs.symm.trans SemiprimeD1StackMarkedRootRecords.stack_card
    rw [SemiprimeD1StackRootNetworkRecords.stack_card] at h
    omega
  change Fintype.card R.Stack+Fintype.card (Private⊕J.Stack)=2505
  rw [SemiprimeD1StackRootPacketInventory.stack_card,Fintype.card_sum,hp,
    SemiprimeD1StackPackedRootContext.stack_card]
/-- Runtime control contains finite flags and fixed labels only. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every Boolean and actual saved-return alphabet is fixed finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPackedRootInput
