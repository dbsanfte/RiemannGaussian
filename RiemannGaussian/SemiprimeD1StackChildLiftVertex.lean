/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTableStorage
import RiemannGaussian.SemiprimeD1StackVertexProduct
/-! # Literal whole lifted-child vertex record acquisition
The real134-word table source runs once. Two preserving physical frames then
emit its acquired table and retained canonical scope, followed by the vertex
tag. All134 source words remain present and two additional words are paid.
The seven source words are caller operands, not an original-N-only entry.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertex
namespace T
export SemiprimeD1StackChildLiftTable (Stack Label program initial stack_card)
end T
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
/-- Exactly two new physical words; neither contains a prepared answer. -/
inductive Aux where | record | scratch deriving DecidableEq,Repr
instance auxFintype : Fintype Aux := Fintype.ofList [.record,.scratch] (by intro k;cases k <;> simp)
/-- Every134 table-source word, including its template and all shadows, is retained. -/
abbrev Stack := T.Stack⊕Aux
/-- Literal whole-table source inclusion. -/
def table (k : T.Stack) : Stack := .inl k
/-- Literal record/framing-work address. -/
def aux (k : Aux) : Stack := .inr k
/-- Actual whole-table output, acquired by the included source. -/
def tableOutput : Stack := table (SemiprimeD1StackVectorTable.aux .output)
/-- Actual retained canonical scope; its record count was acquired physically. -/
def scopeInput : Stack := table (SemiprimeD1StackVectorTable.counter .bank)
/-- Two fixed frame sites: table first, then scope. -/
def frameStack (scope : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if scope then scopeInput else tableOutput)
  else if k=1 then aux .record else aux .scratch
/-- Finite literal caller stages. -/
inductive Control where | start | seed | tableFrame | scopeFrame | tag | done deriving DecidableEq
instance controlFintype : Fintype Control := Fintype.ofList
  [.start,.seed,.tableFrame,.scopeFrame,.tag,.done] (by intro k;cases k <;> simp)
/-- Included source/frame labels contain no data-valued controls. -/
inductive Label where
  | local (pc : Control) | source (pc : T.Label) | frame (scope : Bool) (pc : Fin 11)
  deriving Fintype
/-- One literal call, two literal frames and literal record/EOF tags. -/
def program : Label→C.Instruction Stack Label
  | .local .start => .call (.source .start) (.local .seed)
  | .local .seed => .base (.push (aux .record) false (.local .tableFrame))
  | .local .tableFrame => .call (.frame false 0) (.local .scopeFrame)
  | .local .scopeFrame => .call (.frame true 0) (.local .tag)
  | .local .tag => .base (.push (aux .record) true (.local .done))
  | .local .done => .base .halt
  | .source pc => SemiprimeD1StackValidationLink.instruction table Label.source (T.program pc)
  | .frame scope pc => SemiprimeD1StackMultiplierLink.instruction (frameStack scope) (Label.frame scope)
      (SemiprimeD1StackFrame.code pc)
/-- All actual data, including both new scratch words. -/
def bank (source : T.Stack→List Bool) (record scratch : List Bool) : Stack→List Bool :=
  Sum.elim source (fun k => match k with | .record=>record | .scratch=>scratch)
/-- Only the actual original seven table-source words enter; both new words are empty. -/
def input (parent order oldAxes oldp newAxes newp scope : List Bool) : Stack→List Bool :=
  bank (T.initial parent order oldAxes oldp newAxes newp scope).data [] []
/-- Actual prepared entry precedes both the whole table call and all record acquisition. -/
def initial (parent order oldAxes oldp newAxes newp scope : List Bool) : C.State Stack Label :=
  ⟨some (.local .start),none,none,input parent order oldAxes oldp newAxes newp scope,[]⟩
/-- Fixed136-role compiled source; no native record/table constructor is an opcode. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine scopeInput (aux .record) (.local .start) program
/-- Whole source inclusion aliases no physical word. -/
theorem table_injective : Function.Injective table := Sum.inl_injective
/-- Each real frame has separate source, output and restoration scratch. -/
theorem frame_injective (scope : Bool) : Function.Injective (frameStack scope) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> cases scope <;> simp_all [frameStack,scopeInput,tableOutput,table,aux]
/-- No omitted source/template/scanner/DFS or framing shadow. -/
theorem stack_card : Fintype.card Stack=136 := by
  rw [Fintype.card_sum,T.stack_card]
  rfl
/-- The finite machine state contains only literal labels and Boolean flags. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackChildLiftVertex
