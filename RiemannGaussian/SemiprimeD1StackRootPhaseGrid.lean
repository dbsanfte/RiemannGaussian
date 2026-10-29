/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecursiveControlOriginal
import RiemannGaussian.SemiprimeD1StackAssignmentEnumerationBounds
/-! # Actual original-input conditional binary phase-index grid
The complete root source executes once. Its actual guard bit controls whether
its retained exponent is physically copied and consumed to build one binary
zero word. Actual fixed-width increments then enumerate the chronological grid.
No width, activity bit, exponent, phase body or enumeration count is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseGrid
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootRecursiveControl
  (Stack Label program input initial originalInput sourceStack output)
export SemiprimeD1StackRootRecursiveControlEncoding (result done)
export SemiprimeD1StackRootRecursiveControlExecution (runBound)
end R
namespace A
export SemiprimeD1StackAssignmentLoop (Stack Label code data control)
end A
/-- All126 physical Boolean roles, retaining every119 acquired root cell. -/
abbrev Stack :=R.Stack⊕(A.Stack⊕Fin 2)
/-- Actual retained original-input root source. -/
def rootStack (k:R.Stack) : Stack :=.inl k
/-- Actual five-word fixed-width binary assignment enumerator. -/
def enumStack (k:A.Stack) : Stack :=.inr (.inl k)
/-- Two disjoint physical copy/count work words, fixed before N. -/
def aux (i:Fin 2) : Stack :=.inr (.inr i)
/-- Actual consumed copy of the physically acquired parent exponent tally. -/
def count : Stack :=aux 0
/-- Actual preserving-copy scratch. -/
def scratch : Stack :=aux 1
/-- Original binary N is the sole initial payload. -/
def originalInput : Stack :=rootStack R.originalInput
/-- Actual root guard output, read physically by the branch instruction. -/
def guard : Stack :=rootStack R.output
/-- Actual acquired root exponent; its source word is retained literally. -/
def exponent : Stack :=rootStack (R.sourceStack SemiprimeD1StackRootParameters.exponent)
/-- Physically emitted chronological binary phase-index vector, empty if inactive. -/
def output : Stack :=enumStack .output
/-- Eight fixed physical source, guard, zero-word and enumeration phases. -/
inductive Control where | start | branch | copy | seed | fill | zero | enumerate | done
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems:={.start,.branch,.copy,.seed,.fill,.zero,.enumerate,.done}
  complete:=by intro k;cases k <;> simp
/-- Every included component and real return label is fixed before N. -/
abbrev Label :=Control⊕(R.Label⊕(Fin 9⊕A.Label))
/-- Actual whole original-input root-controller inclusion. -/
def rootLabel (pc:R.Label) : Label :=.inr (.inl pc)
/-- Actual preserving-copy inclusion. -/
def copyLabel (pc:Fin 9) : Label :=.inr (.inr (.inl pc))
/-- Actual binary increment/overflow enumeration inclusion. -/
def enumLabel (pc:A.Label) : Label :=.inr (.inr (.inr pc))
/-- Three distinct actual operands of the paid exponent copy. -/
def copyStack (i:Fin 3) : Stack :=if i=0 then exponent else if i=1 then count else scratch
local notation "ctl" => (Sum.inl : Control→Label)
/-- One fixed N-only program: actual guard, actual unary-byte consumption to
binary zero, then actual wrapped binary increments and one final vector reversal. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (rootLabel (.inl .start)) (ctl .branch)
  | .inl .branch=>.base (.peek guard (ctl .done) (ctl .done) (ctl .copy))
  | .inl .copy=>.call (copyLabel 0) (ctl .seed)
  | .inl .seed=>.base (.push (enumStack .word) false (ctl .fill))
  | .inl .fill=>.base (.pop count (ctl .enumerate) (ctl .zero) (ctl .zero))
  | .inl .zero=>.base (.push (enumStack .word) false (ctl .fill))
  | .inl .enumerate=>.call (enumLabel (A.control .bodyCall)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction rootStack rootLabel (R.program pc)
  | .inr (.inr (.inl pc))=>SemiprimeD1StackMultiplierLink.instruction copyStack copyLabel (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inr pc))=>SemiprimeD1StackValidationLink.instruction enumStack enumLabel (A.code pc)
/-- Exact complete physical payload, with no operand/value evaluator in the program. -/
def data (root:R.Stack→List Bool) (enumeration:A.Stack→List Bool) (counts work:List Bool) : Stack→List Bool :=
  Sum.elim root (Sum.elim enumeration (fun i=>if i=0 then counts else work))
/-- Original binary N alone; all seven genuinely new roles are physically empty. -/
def input (bits:List Bool) : Stack→List Bool :=data (R.input bits) (fun _=>[]) [] []
/-- Actual original-input entry before any root acquisition or activity decision. -/
def initial (bits:List Bool) : C.State Stack Label :=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual stage boundary after the complete original root program has returned. -/
def afterRoot (bits:List Bool) : Stack→List Bool :=data (R.result bits) (fun _=>[]) [] []
/-- Genuine fixed126-role finite machine, with binary N as its only designated input. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- Paid copy source, counter and scratch never alias. -/
theorem copy_injective : Function.Injective copyStack :=by decide
/-- Retained119 plus binary enumerator5 plus count/scratch2 are all counted. -/
theorem stack_card : Fintype.card Stack=126 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootRecursiveControl.stack_card,Fintype.card_sum]
  decide
/-- All actual Boolean and real-return alphabets are finite before N. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Actual read and remembered-return flags contain only fixed finite labels. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootPhaseGrid
