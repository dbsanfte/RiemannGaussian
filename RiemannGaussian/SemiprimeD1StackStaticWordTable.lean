/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCountExecution
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackProcedureReturns
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1StackFrame
/-! # Static finite checker to an actual whole truth-table compiler
The checker code and complete finite role inventory are fixed before every
input. Runtime data consist of original checker input words in a read-only
template and a physical scope-ID bank. A real scanner acquires its record
count. Every DFS leaf copies the template, reverses the real assignment,
executes the fixed checker, frames its actual binary coefficient and clears every role.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackStaticWordTable
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace D
export SemiprimeD1StackDigitCount (Stack Label program data)
end D
/-- Compile-time parameters only. Neither the checker nor its role list belongs
to a runtime configuration. Concrete clients instantiate one constant value. -/
structure Static (K L : Type) where
  /-- Literal finite source program, fixed before input. -/
  code : L→C.Instruction K L
  /-- Fixed actual checker entry label. -/
  entry : L
  /-- Physical raw-assignment operand. -/
  raw : K
  /-- Physical binary coefficient output operand. -/
  output : K
  /-- Computable literal inventory of all physical checker roles. -/
  roles : List K
  /-- Every role, including dormant private shadows, is visited. -/
  complete : ∀k,k∈roles
  /-- Every static role occurs exactly once. -/
  nodup : roles.Nodup
/-- Private DFS roles; physical scope counter.count is used directly as depth. -/
inductive Aux where | prefix | work | scratch | reversed | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.prefix,.work,.scratch,.reversed,.output]
  (by intro k;cases k <;> simp)
/-- All physical roles: real checker, read-only input template, real scope
counter and five DFS words. Every type is fixed before the original input. -/
abbrev Stack (K : Type) := K⊕(K⊕(D.Stack⊕Aux))
/-- Literal checker-bank role. -/
def checker {K : Type} (k : K) : Stack K := .inl k
/-- Literal read-only original-input template role. -/
def template {K : Type} (k : K) : Stack K := .inr (.inl k)
/-- Literal physical scanner/counting role. -/
def counter {K : Type} (k : D.Stack) : Stack K := .inr (.inr (.inl k))
/-- Literal DFS-private physical role. -/
def aux {K : Type} (k : Aux) : Stack K := .inr (.inr (.inr k))
/-- Fixed finite source labels. The role indices range over the STATIC role
inventory only; no input number, template, assignment or count enters control. -/
inductive Label (L : Type) (size : Nat) where
  | start | build | finish | done | bad
  | visit | fork | low | high | afterLow | setHigh | afterHigh | restore | returnDone
  | leaf | prefixCopy | reversePrefix | check | emitSentinel | emitFrame | emitTag | emitLeaf | emitReverse | leafCleanup | leafReturn
  | load (position : Fin (size+1)) | loadCopy (position : Fin size)
  | clear (position : Fin (size+1))
  | checker (pc : L) | counter (pc : D.Label)
  | copy (position : Option (Fin size)) (pc : Fin 9)
  | reverse (table : Bool) (pc : Fin 4)
  | frame (pc : Fin 11) | recordReverse (pc : Fin 4)
  deriving Fintype
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Exactly one role at a fixed position of the compile-time inventory. -/
def role (position : Fin s.roles.length) : K := s.roles[position.val]
/-- Actual preserving-copy wiring; none copies the reverse assignment prefix,
some copies one complete template word into its checker operand. -/
def copyStack (position : Option (Fin s.roles.length)) (k : Fin 3) : Stack K :=
  if k=0 then position.elim (aux .prefix) (fun p=>template (role s p))
  else if k=1 then position.elim (aux .work) (fun p=>checker (role s p)) else aux .scratch
/-- Both actual consuming reversals, including direct raw-assignment delivery. -/
def reverseStack (table : Bool) (k : Fin 2) : Stack K :=
  if k=0 then aux (if table then .reversed else .work)
  else if table then aux .output else checker s.raw
/-- Next static bank-copy position. -/
def loadNext (p : Fin s.roles.length) : Label L s.roles.length := .load ⟨p.val+1,by omega⟩
/-- Actual physical binary coefficient framing into the existing private buffer. -/
def frameStack (k : Fin 3) : Stack K :=
  if k=0 then checker s.output else if k=1 then aux .work else aux .scratch
/-- Physical leaf-record reversal prepends its exact reversed bytes to DFS history. -/
def recordReverseStack (k : Fin 2) : Stack K := if k=0 then aux .work else aux .reversed
/-- The entire compiler program depends ONLY on the static checker. In
particular no N, template bytes, predicate, arity or budget is a parameter. -/
def program : Label L s.roles.length→C.Instruction (Stack K) (Label L s.roles.length)
  | .start=>.call (.counter (.inl .main)) .build
  | .build=>.call .visit .finish
  | .finish=>.call (.reverse true 0) .done
  | .done | .bad=>.base .halt
  | .visit=>.base (.pop (counter .count) .leaf .fork .fork)
  | .fork=>.base (.push (aux .reversed) true .low)
  | .low=>.base (.push (aux .prefix) false .high)
  | .high=>.call .visit .afterLow
  | .afterLow=>.base (.pop (aux .prefix) .bad .setHigh .setHigh)
  | .setHigh=>.base (.push (aux .prefix) true .afterHigh)
  | .afterHigh=>.call .visit .restore
  | .restore=>.base (.pop (aux .prefix) .bad .returnDone .returnDone)
  | .returnDone=>.base (.push (counter .count) true .leafReturn)
  | .leaf=>.call (.load 0) .prefixCopy
  | .load pos=>if h:pos.val<s.roles.length then
      .base (.pop (checker (role s ⟨pos.val,h⟩)) (.loadCopy ⟨pos.val,h⟩) (.load pos) (.load pos))
      else .ret
  | .loadCopy pos=>.call (.copy (some pos) 0) (loadNext s pos)
  | .prefixCopy=>.call (.copy none 0) .reversePrefix
  | .reversePrefix=>.call (.reverse false 0) .check
  | .check=>.call (.checker s.entry) .emitSentinel
  | .emitSentinel=>.base (.push (aux .work) false .emitFrame)
  | .emitFrame=>.call (.frame 0) .emitTag
  | .emitTag=>.base (.push (aux .work) true .emitLeaf)
  | .emitLeaf=>.base (.push (aux .work) false .emitReverse)
  | .emitReverse=>.call (.recordReverse 0) .leafCleanup
  | .leafCleanup=>.call (.clear 0) .leafReturn
  | .leafReturn=>.ret
  | .clear pos=>if h:pos.val<s.roles.length then
      .base (.pop (checker (role s ⟨pos.val,h⟩)) (.clear ⟨pos.val+1,by omega⟩) (.clear pos) (.clear pos))
      else .ret
  | .checker pc=>SemiprimeD1StackValidationLink.instruction checker Label.checker (s.code pc)
  | .counter pc=>SemiprimeD1StackValidationLink.instruction counter Label.counter (D.program pc)
  | .copy pos pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack s pos) (Label.copy pos)
      (SemiprimeD1StackCopy.code pc)
  | .reverse table pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack s table) (Label.reverse table)
      (SemiprimeD1StackReverseWord.code pc)
  | .frame pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack s) Label.frame
      (SemiprimeD1StackFrame.code pc)
  | .recordReverse pc=>SemiprimeD1StackMultiplierLink.instruction recordReverseStack Label.recordReverse
      (SemiprimeD1StackReverseWord.code pc)
/-- Complete data view. Functions here describe only fixed finite physical banks. -/
def store (live original : K→List Bool) (count : D.Stack→List Bool) (front work scratch hist out : List Bool) :
    Stack K→List Bool := Sum.elim live (Sum.elim original (Sum.elim count (fun k=>match k with
      | .prefix=>front | .work=>work | .scratch=>scratch | .reversed=>hist | .output=>out)))
/-- Stable DFS view: checker empty, entire original input template and scope
bank retained, actual unary count restored after each recursive visit. -/
def data (original : K→List Bool) (bank : List Bool) (depth : Nat) (front hist : List Bool) : Stack K→List Bool :=
  store (fun _=>[]) original (D.data bank [] (List.replicate depth true) [] [] [] []) front [] [] hist []
/-- The only initial data are actual checker-input template bytes and actual
scope-bank bytes. No unary count, raw assignment, result or table is supplied. -/
def initial (original : K→List Bool) (bank : List Bool) : C.State (Stack K) (Label L s.roles.length) :=
  ⟨some .start,none,none,data original bank 0 [] [],[]⟩
/-- Fixed genuine finite machine for this one static checker. -/
def machine [Fintype K] [Fintype L] : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine (counter .bank) (aux .output) .start (program s)
omit [DecidableEq K] in
/-- Complete role count, including BOTH actual checker and original-template banks. -/
theorem stack_card [Fintype K] : Fintype.card (Stack K)=2*Fintype.card K+12 := by
  simp only [Stack,Fintype.card_sum,SemiprimeD1StackDigitCount.stack_card]
  have ha:Fintype.card Aux=5:=by decide
  omega
/-- All actual finite flags and return-label control are fixed before input. -/
theorem control_finite [Fintype K] [Fintype L] : Finite (machine s).σ :=
  SemiprimeD1StackCalls.control_finite (counter .bank) (aux .output) .start (program s)
end RiemannGaussian.SemiprimeD1StackStaticWordTable
