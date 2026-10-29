/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexOriginal
import RiemannGaussian.SemiprimeD1StackNetworkRowsOriginal
/-! # Original binary N to exact original network rows and n/F/M
The real1821-role original source acquires the records and owner index once.
The real row source starts at its actual acquired-index entry. All seventeen
index roles alias that retained bank; only its thirty-one private roles are
newly allocated. No records, owner map, count, rows or routing getter enter
runtime control. Both actual source banks remain available after acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRows
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootOwnerIndex (Stack Label program input initial initialPrefix originalInput indexStack indexInverse index_inverse)
export SemiprimeD1StackRootOwnerIndexExecution (done)
end R
namespace Q
export SemiprimeD1StackNetworkRows (Stack Label program Aux)
end Q
/-- Exactly the fourteen fibre and seventeen parser/row/tally words that the acquired index does not provide. -/
abbrev Private :=SemiprimeD1StackOwnerFibre.Stack⊕Q.Aux
/-- All1821retained source words plus thirty-one actually new words; no duplicate index bank. -/
abbrev Stack :=R.Stack⊕Private
/-- Every actual original-N record/index/source role remains physically present. -/
def rootStack :R.Stack→Stack :=Sum.inl
/-- All actual index operands reuse the same acquired physical bank; every private row operand has its own word. -/
def rowsStack :Q.Stack→Stack
  | .inl k=>rootStack (R.indexStack k)
  | .inr k=>.inr k
/-- Static inverse only, independent of every original input, count or output. -/
def rowsInverse :Stack→Q.Stack
  | .inl k=>.inl (R.indexInverse k)
  | .inr k=>.inr k
/-- Exact source and new private row store; the shared seventeen index roles remain in the source bank. -/
def data (root:R.Stack→List Bool) (rows:Q.Stack→List Bool) :Stack→List Bool :=
  Sum.elim root (fun k=>rows (.inr k))
/-- The standard source and actual caller-prefix source both continue directly at the row-ready entry. -/
inductive Control where | start | prescribed | rows | done deriving DecidableEq
instance :Fintype Control :=Fintype.ofList [.start,.prescribed,.rows,.done] (by intro k;cases k <;> simp)
/-- All real called source and row labels are fixed finite before N. -/
abbrev Label :=Control⊕(R.Label⊕Q.Label)
/-- Actual included original-N source labels. -/
def rootLabel (pc:R.Label) :Label :=.inr (.inl pc)
/-- Actual included row parser/lookup/logger labels. -/
def rowsLabel (pc:Q.Label) :Label :=.inr (.inr pc)
local notation "ctl" => (Sum.inl :Control→Label)
/-- One fixed source program; the index is acquired ONCEand the actual row-ready entry reuses it. -/
def program :Label→C.Instruction Stack Label
  | .inl .start=>.call (rootLabel (.inl .start)) (ctl .rows)
  | .inl .prescribed=>.call (rootLabel (.inl .prescribed)) (ctl .rows)
  | .inl .rows=>.call (rowsLabel (.local .copyFactors)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction rootStack rootLabel (R.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction rowsStack rowsLabel (Q.program pc)
/-- Binary N is the sole standard physical input; all derived records/index/rows/tallies start empty. -/
def input (bits:List Bool) :Stack→List Bool :=data (R.input bits) (fun _=>[])
/-- Literal original-binary-N entry. -/
def initial (bits:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Literal actual-prescription entry, with no derived graph/count/owner advice. -/
def initialPrefix (bits pre:List Bool) :C.State Stack Label :=
  ⟨some (ctl .prescribed),none,none,data (R.initialPrefix bits pre).data (fun _=>[]),[]⟩
/-- Genuine sole binary-input address inherited from the original source. -/
def originalInput :Stack :=rootStack R.originalInput
/-- Actual physical original factor-major owner-row tape. -/
def output :Stack :=rowsStack (SemiprimeD1StackNetworkRows.aux .output)
/-- One actual fixed finite1852-role machine, including every retained source cache and every row helper. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- Every used physical row role has its exact static inverse. -/
theorem rows_inverse (k:Q.Stack) :rowsInverse (rowsStack k)=k :=by
  rcases k with k|k
  · change Sum.inl (R.indexInverse (R.indexStack k))=Sum.inl k
    rw [R.index_inverse]
  · rfl
/-- Sharing the actual acquired index never aliases distinct row operands. -/
theorem rows_injective :Function.Injective rowsStack :=by
  intro a b h
  have he:=congrArg rowsInverse h
  simpa only [rows_inverse] using he
/-- All1852physical words are counted, including the original two index-input shadows and the row query shadow. -/
theorem stack_card :Fintype.card Stack=1852 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootOwnerIndex.stack_card,Fintype.card_sum,
    SemiprimeD1StackOwnerFibre.stack_card]
  decide
/-- Runtime control contains only finite flags and actual fixed return labels. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All allocated data/return alphabets are fixed finite before every N. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootNetworkRows
