/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryBootstrap
import RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Fixed original-binary root schedule acquisition
Only N starts populated. Actual bootstrap width, repeated real unary division
by two, literal marker writes and preserving copies acquire lambda, root
levels/exponent and minimumLevels. N remains binary throughout. Materialized
s and the square-root leaf threshold are separate acquisition obligations.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRootSchedule
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Boot
export SemiprimeD1BinaryBootstrap (Stack Label code payload done seenOne)
end Boot
namespace D
export SemiprimeD1StackUnaryDivmod (Stack contents unary)
end D
namespace Div
export SemiprimeD1StackUnaryDivmodBytecode (Label code entry)
end Div
/-- Four actual schedule words and one physically empty copy-restoration role. -/
inductive Aux where | lambda | levels | exponent | minimum | scratch
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList [.lambda,.levels,.exponent,.minimum,.scratch]
  (by intro k;cases k <;> simp)
/-- Fifteen fixed physical roles, including all divisor/copy/remainder work. -/
abbrev Stack := Boot.Stack⊕(D.Stack⊕Aux)
/-- Static roles for retaining the original word and width. -/
def boot (k : Boot.Stack) : Stack := .inl k
/-- Literal six-role real divider inclusion. -/
def divStack (k : D.Stack) : Stack := .inr (.inl k)
/-- Literal auxiliary metadata/work inclusion. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- One fixed metadata-size phase or one of exactly seventeen quotient calls. -/
inductive Job where | size (minimum : Bool) | half (position : Fin 17)
  deriving DecidableEq,Fintype
/-- Literal fixed source labels; counters never occur in internal control. -/
inductive Label where
  | start | choose | zeroLambda | seedLambda (position : Fin 20) | seedTwo (position : Fin 2)
  | copyWidth | probe (minimum : Bool) | divide (minimum : Bool)
  | clearRemainder (job : Job) | move (job : Job) | movePush (job : Job)
  | emitSize (minimum : Bool) (position : Fin 4) | seedMinimum (position : Fin 8)
  | copyMinimum | copyLevels | halve (position : Fin 18) | pushLevel | copyFirst | copySecond | done
  | bootstrap (pc : Boot.Label) | copy (kind : Fin 3) (pc : Fin 9) | division (pc : Div.Label)
  deriving Fintype
/-- Real copy sites: retained width, acquired lambda, acquired levels. -/
def copySource (kind : Fin 3) : Stack :=
  if kind=0 then boot .width else if kind=1 then aux .lambda else aux .levels
/-- Width/lambda initialize actual divider input; levels append to exponent. -/
def copyTarget (kind : Fin 3) : Stack :=if kind=2 then aux .exponent else divStack .input
/-- Every preserving copy uses three separate physical operands. -/
def copyStack (kind : Fin 3) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .scratch
/-- The actual counted destination, selected by one fixed phase Boolean. -/
def sizeOutput (minimum : Bool) : Stack :=aux (if minimum then .minimum else .lambda)
/-- The next literal phase after physically moving the acquired quotient. -/
def afterMove : Job→Label
  | .size minimum=>.emitSize minimum 0
  | .half p=>.halve ⟨p.val+1,by omega⟩
/-- One constant finite instruction table before ALL N. No arithmetic opcode,
AST, decoded N, supplied count, evaluator, answer or clock belongs to control. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.bootstrap (.scan,false)) .choose
  | .choose=>.base (.peek (boot .width) .zeroLambda (.seedLambda 0) (.seedLambda 0))
  | .zeroLambda=>.base (.push (aux .lambda) true (.seedTwo 0))
  | .seedLambda p=>.base (.push (aux .lambda) true
      (if h:p.val<19 then .seedLambda ⟨p.val+1,by omega⟩ else .seedTwo 0))
  | .seedTwo p=>.base (.push (divStack .divisor) true (if p=0 then .seedTwo 1 else .copyWidth))
  | .copyWidth=>.call (.copy 0 0) (.probe false)
  | .probe minimum=>.base (.peek (divStack .input)
      (if minimum then .copyLevels else .seedMinimum 0) (.divide minimum) (.divide minimum))
  | .divide minimum=>.call (.division Div.entry) (.clearRemainder (.size minimum))
  | .clearRemainder job=>.base (.pop (divStack .remainder) (.move job) (.clearRemainder job) (.clearRemainder job))
  | .move job=>.base (.pop (divStack .quotient) (afterMove job) (.movePush job) (.movePush job))
  | .movePush job=>.base (.push (divStack .input) true (.move job))
  | .emitSize minimum p=>.base (.push (sizeOutput minimum) true
      (if minimum then if h:p.val<3 then .emitSize true ⟨p.val+1,by omega⟩ else .probe true else .probe false))
  | .seedMinimum p=>.base (.push (aux .minimum) true
      (if h:p.val<7 then .seedMinimum ⟨p.val+1,by omega⟩ else .copyMinimum))
  | .copyMinimum=>.call (.copy 1 0) (.probe true)
  | .copyLevels=>.call (.copy 1 0) (.halve 0)
  | .halve p=>if h:p.val<17 then .call (.division Div.entry) (.clearRemainder (.half ⟨p.val,h⟩))
      else .base (.pop (divStack .input) .copyFirst .pushLevel .pushLevel)
  | .pushLevel=>.base (.push (aux .levels) true (.halve 17))
  | .copyFirst=>.call (.copy 2 0) .copySecond
  | .copySecond=>.call (.copy 2 0) .done
  | .done=>.base .halt
  | .bootstrap pc=>SemiprimeD1StackMultiplierLink.instruction boot Label.bootstrap (Boot.code pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .division pc=>SemiprimeD1StackMultiplierLink.instruction divStack Label.division (Div.code pc)
/-- Exact physical view; all functions here index a fixed finite tape bank. -/
def store (b : Boot.Stack→List Bool) (d : D.Stack→List Bool) (a : Aux→List Bool) : Stack→List Bool :=
  Sum.elim b (Sum.elim d a)
/-- Four actual metadata words and actual scratch, never native encoded answers. -/
def metadata (lam levels exponent minimum scratch : List Bool) : Aux→List Bool
  | .lambda=>lam | .levels=>levels | .exponent=>exponent | .minimum=>minimum | .scratch=>scratch
/-- Exactly original binary N initially; every derived role is EMPTY. -/
def input (bits : List Bool) : Stack→List Bool :=store (Boot.payload bits [] [] []) (fun _=>[]) (fun _=>[])
/-- The source starts before even the real original-word bootstrap. -/
def initial (bits : List Bool) : C.State Stack Label :=⟨some .start,none,none,input bits,[]⟩
/-- Genuine fixed finite machine, with original binary input and root exponent output. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine (boot .input) (aux .exponent) .start program
/-- Complete fixed physical inventory. -/
theorem stack_card : Fintype.card Stack=15 := by decide
/-- No N, size, decoded metadata, predicate or budget inhabits internal control. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Actual return and Boolean alphabets are finite before every N. -/
theorem alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
/-- Bootstrap and complete divider use injective physical role maps. -/
theorem boot_injective : Function.Injective boot :=Sum.inl_injective
/-- All six actual divider operands are distinct. -/
theorem div_injective : Function.Injective divStack :=fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)
/-- Every actual preserving copy has three distinct operands. -/
theorem copy_injective (kind : Fin 3) : Function.Injective (copyStack kind) := by fin_cases kind <;> decide
end RiemannGaussian.SemiprimeD1StackRootSchedule
