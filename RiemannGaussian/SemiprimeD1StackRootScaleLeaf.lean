/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleOriginal
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Exact physical original-root scale and leaf threshold acquisition
The ready entry reuses an ACTUALLY acquired RootSchedule cache and preserves
ALL15 of its fields. Only ten fresh work/output roles are allocated. The whole
entry first executes that SAME original-N source. Twenty real doublings,
physical odd subtraction, and the actual unary divider compute the threshold;
no square-root, product, quotient or prepared-answer opcode is present.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeaf
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootSchedule (Stack Label program input initial boot aux)
end R
namespace D
export SemiprimeD1StackUnaryDivmod (Stack contents unary)
end D
namespace Div
export SemiprimeD1StackUnaryDivmodBytecode (Label code entry)
end Div
/-- Actual scale/square-root/leaf outputs and real copy-restoration scratch. -/
inductive Aux where | scale | root | leaf | scratch
  deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList [.scale,.root,.leaf,.scratch] (by intro k;cases k <;> simp)
/-- Entire old15-role cache is disjoint from the six real work roles and four outputs. -/
abbrev Stack :=R.Stack⊕(D.Stack⊕Aux)
/-- Read-only inclusion of the entire acquired N/root-schedule cache. -/
def rootStack : R.Stack→Stack :=Sum.inl
/-- Fresh six-role divider bank, reused for doubling and exact odd subtraction. -/
def divStack (k : D.Stack) : Stack :=.inr (.inl k)
/-- Literal output and copy-restoration role inclusion. -/
def aux (k : Aux) : Stack :=.inr (.inr k)
/-- Finite source labels, including exactly twenty static doubling rounds. -/
inductive Label where
  | start | ready | double (position : Fin 21) | doublePush1 (position : Fin 20)
  | doublePush2 (position : Fin 20) | restore (position : Fin 20) | restorePush (position : Fin 20)
  | seedOdd | squareCopy | popOdd | popRemaining | advance (position : Fin 3)
  | clearWork | clearOdd | copyRoot | seedDenominator | copyScale | divide | clearRemainder
  | moveLeaf | pushLeaf | plusOne | done
  | root (pc : R.Label) | copy (kind : Fin 5) (pc : Fin 9) | division (pc : Div.Label)
  deriving Fintype
/-- Five fixed preserving-copy source sites, before N. -/
def copySource (kind : Fin 5) : Stack :=
  if kind=0 then rootStack (R.boot .width) else if kind=1 then rootStack (R.aux .lambda)
  else if kind=2 then divStack .divisor else if kind=3 then aux .root else aux .scale
/-- Copies deliver actual width/lambda/odd/root/scale words to their physical consumers. -/
def copyTarget (kind : Fin 5) : Stack :=
  if kind=0 then aux .scale else if kind=2 then divStack .copied
  else if kind=3 then divStack .divisor else divStack .input
/-- Every included copy uses a separate actual restoration stack. -/
def copyStack (kind : Fin 5) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .scratch
/-- One literal finite program independent of every original number and metadata value. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.root .start) .ready
  | .ready=>.call (.copy 0 0) (.double 0)
  | .double p=>if h:p.val<20 then
      .base (.pop (aux .scale) (.restore ⟨p.val,h⟩) (.doublePush1 ⟨p.val,h⟩) (.doublePush1 ⟨p.val,h⟩))
      else .call (.copy 1 0) .seedOdd
  | .doublePush1 p=>.base (.push (divStack .quotient) true (.doublePush2 p))
  | .doublePush2 p=>.base (.push (divStack .quotient) true (.double ⟨p.val,by omega⟩))
  | .restore p=>.base (.pop (divStack .quotient) (.double ⟨p.val+1,by omega⟩) (.restorePush p) (.restorePush p))
  | .restorePush p=>.base (.push (aux .scale) true (.restore p))
  | .seedOdd=>.base (.push (divStack .divisor) true .squareCopy)
  | .squareCopy=>.call (.copy 2 0) .popOdd
  | .popOdd=>.base (.pop (divStack .copied) (.advance 0) .popRemaining .popRemaining)
  | .popRemaining=>.base (.pop (divStack .input) .clearWork .popOdd .popOdd)
  | .advance p=>.base (.push (if p=0 then aux .root else divStack .divisor) true
      (if h:p.val<2 then .advance ⟨p.val+1,by omega⟩ else .squareCopy))
  | .clearWork=>.base (.pop (divStack .copied) .clearOdd .clearWork .clearWork)
  | .clearOdd=>.base (.pop (divStack .divisor) .copyRoot .clearOdd .clearOdd)
  | .copyRoot=>.call (.copy 3 0) .seedDenominator
  | .seedDenominator=>.base (.push (divStack .divisor) true .copyScale)
  | .copyScale=>.call (.copy 4 0) .divide
  | .divide=>.call (.division Div.entry) .clearRemainder
  | .clearRemainder=>.base (.pop (divStack .remainder) .moveLeaf .clearRemainder .clearRemainder)
  | .moveLeaf=>.base (.pop (divStack .quotient) .plusOne .pushLeaf .pushLeaf)
  | .pushLeaf=>.base (.push (aux .leaf) true .moveLeaf)
  | .plusOne=>.base (.push (aux .leaf) true .done)
  | .done=>.base .halt
  | .root pc=>SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .division pc=>SemiprimeD1StackMultiplierLink.instruction divStack Label.division (Div.code pc)
/-- Exact fixed physical bank; every old root-cache field is retained separately. -/
def store (root : R.Stack→List Bool) (work : D.Stack→List Bool) (out : Aux→List Bool) : Stack→List Bool :=
  Sum.elim root (Sum.elim work out)
/-- Actual output words and actual restoration scratch, not runtime result suppliers. -/
def metadata (scale root leaf scratch : List Bool) : Aux→List Bool
  | .scale=>scale | .root=>root | .leaf=>leaf | .scratch=>scratch
/-- Only original N is populated before the complete real original-input source. -/
def input (bits : List Bool) : Stack→List Bool :=store (R.input bits) (fun _=>[]) (fun _=>[])
/-- Whole N-only entry, before root metadata has been acquired. -/
def initial (bits : List Bool) : C.State Stack Label :=⟨some .start,none,none,input bits,[]⟩
/-- Ready entry reuses exactly the ACTUALLY acquired RootSchedule.done cache;
all ten fresh work/output roles are empty. No N/root acquisition is repeated. -/
def ready (bits : List Bool) : C.State Stack Label :=
  ⟨some .ready,none,none,store (SemiprimeD1StackRootScheduleExecution.result bits) (fun _=>[]) (fun _=>[]),[]⟩
/-- One genuine finite machine with the original N stack as its sole input. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (rootStack (R.boot .input)) (aux .leaf) .start program
/-- Every old and fresh physical role is counted, before N. -/
theorem stack_card : Fintype.card Stack=25 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootSchedule.stack_card,Fintype.card_sum]
  decide
/-- Actual root source and fresh divider role inclusions are injective. -/
theorem root_injective : Function.Injective rootStack :=Sum.inl_injective
/-- Actual fresh divider has no internal operand aliases. -/
theorem div_injective : Function.Injective divStack :=fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)
/-- Every fixed preserving-copy site has three separate actual roles. -/
theorem copy_injective (kind : Fin 5) : Function.Injective (copyStack kind) :=by fin_cases kind <;> decide
/-- Internal control has only finite Boolean/return-label flags, never native counters. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data and return alphabet is fixed and finite before all N. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackRootScaleLeaf
