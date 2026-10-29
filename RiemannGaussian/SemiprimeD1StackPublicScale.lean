/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceBounds
import RiemannGaussian.SemiprimeD1StackInputDotBounds
import RiemannGaussian.SemiprimeD1StackWordEqualBounds
/-! # Closed physical public scale caller
Original binary N, raw assignment, physical j/k marker caches and a singleton
forward/inverse selector are the only initial data. Root source acquisition,
zero-word padding, dot acquisition/guard/evaluation and output equality are
literal included procedures, not supplied truth or evaluator callbacks.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScale
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace R
export SemiprimeD1StackRootSources (Stack Label program input initial modulusKey)
end R
namespace I
export SemiprimeD1StackInputDotEvaluate (Stack Label Args program initial output status rawRole suffixRole)
end I
namespace W
export SemiprimeD1StackWordBlock (Stack Label program initial)
end W
namespace E
export SemiprimeD1StackWordEqual (Label code)
end E
/-- Seven physical original-input, padding, output and scratch roles. -/
inductive Aux where
  | raw | selector | padding | scratch | count | word | output
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList [.raw,.selector,.padding,.scratch,.count,.word,.output]
  (by intro k;cases k <;> simp)
/-- Original root bank, full executed dot backend and private finite work roles. -/
abbrev Stack := R.Stack⊕(I.Stack⊕Aux)
/-- Literal auxiliary role embedding. -/
def auxRole (k : Aux) : Stack := .inr (.inr k)
/-- Acquired original binary modulus word; no separate prepared modulus input. -/
def modulusRole : Stack := .inl (.inl R.modulusKey)
/-- Actual dot base/stride/frequency/count physical cache roles. -/
def baseRole : I.Stack := .inl (.inl (.inl .base))
/-- Actual shared source/word-vector count cache. -/
def countRole : I.Stack := .inl SemiprimeD1StackInputDotEvaluate.countRole
/-- Literal whole-dot role embedding; its modulus is acquired by a real preserving copy. -/
def dotStack (k : I.Stack) : Stack := .inr (.inl k)
/-- Five real preserving copies: original raw, modulus-width, forward/inverse code, and actual dot modulus. -/
def copyStack (site : Fin 5) (k : Fin 3) : Stack :=
  if k=0 then
    if site=0 then auxRole .raw else if site=1 ∨ site=4 then modulusRole
    else .inl (.inr (if site=2 then .forwardRoot else .root))
  else if k=1 then
    if site=0 then dotStack I.rawRole else if site=1 then auxRole .padding
    else if site=4 then dotStack (.inl SemiprimeD1StackInputDotEvaluate.modulusRole) else dotStack baseRole
  else auxRole .scratch
/-- Output block is read from the actual unread raw suffix using actual M width. -/
def blockStack (k : Fin 5) : Stack :=
  if k=0 then dotStack I.suffixRole else if k=1 then modulusRole else if k=2 then auxRole .count
  else if k=3 then auxRole .scratch else auxRole .word
/-- Direct physical equality consumes the actual numerical result and output word. -/
def equalStack : SemiprimeD1StackAdder.Stack→Stack
  | .left=>dotStack I.output
  | .right=>auxRole .word
  | .scratch=>auxRole .scratch
  | .output=>auxRole .output
/-- Fixed labels; selector and every unbounded operand live only on Bool stacks. -/
inductive Label where
  | start | select | chooseForward | chooseInverse | copyModulus | copyRaw | copyWidth | zeroPop | zeroPush
  | seed (position : Fin 2) | compute | branch | readOutput | equal | reject | done | bad
  | roots (pc : R.Label) | copy (site : Fin 5) (pc : Fin 9) | dot (pc : I.Label)
  | block (pc : W.Label) | compare (pc : E.Label)
  deriving Fintype
/-- ONE fixed actual public scale instruction table. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.roots .start) .select
  | .select=>.base (.pop (auxRole .selector) .bad .chooseForward .chooseInverse)
  | .chooseForward=>.call (.copy 2 0) .copyModulus
  | .chooseInverse=>.call (.copy 3 0) .copyModulus
  | .copyModulus=>.call (.copy 4 0) .copyRaw
  | .copyRaw=>.call (.copy 0 0) .copyWidth
  | .copyWidth=>.call (.copy 1 0) .zeroPop
  | .zeroPop=>.base (.pop (auxRole .padding) (.seed 0) .zeroPush .zeroPush)
  | .zeroPush=>.base (.push (dotStack I.rawRole) false .zeroPop)
  | .seed pos=>.base (.push (dotStack countRole) true (if pos=0 then .seed 1 else .compute))
  | .compute=>.call (.dot .start) .branch
  | .branch=>.base (.pop (dotStack I.status) .bad .reject .readOutput)
  | .readOutput=>.call (.block .start) .equal
  | .equal=>.call (.compare .loop) .done
  | .reject=>.base (.push (auxRole .output) false .done)
  | .done | .bad=>.base .halt
  | .roots pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.roots (R.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .dot pc=>SemiprimeD1StackValidationLink.instruction dotStack Label.dot (I.program pc)
  | .block pc=>SemiprimeD1StackValidationLink.instruction blockStack Label.block (W.program pc)
  | .compare pc=>SemiprimeD1StackMultiplierLink.instruction equalStack Label.compare (E.code pc)
/-- Literal seven-role private store. -/
def aux (raw selector padding scratch count word output : List Bool) : Aux→List Bool
  | .raw=>raw | .selector=>selector | .padding=>padding | .scratch=>scratch
  | .count=>count | .word=>word | .output=>output
/-- Physical combined data, a specification view rather than a runtime supplier. -/
def store (roots : R.Stack→List Bool) (dot : I.Stack→List Bool)
    (raw selector padding scratch count word output : List Bool) : Stack→List Bool :=
  Sum.elim roots (Sum.elim dot (aux raw selector padding scratch count word output))
/-- Original N/raw assignment and physical descriptor fields ONLY. No root,
modulus, input/output word, vector, guard or expected verdict is initially supplied. -/
def initial (bits raw stride frequency : List Bool) (inverse : Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store (R.input bits)
    (I.initial [] ⟨[],stride,frequency,[]⟩ [] []).data raw [inverse] [] [] [] [] [],[]⟩
/-- Whole real dot-component role embedding is injective despite shared modulus. -/
theorem dot_injective : Function.Injective dotStack := by
  intro i j h;exact Sum.inl_injective (Sum.inr_injective h)
/-- Every actual copy's roles are physically disjoint. -/
theorem copy_injective (site : Fin 5) : Function.Injective (copyStack site) := by fin_cases site <;> decide
/-- Full output read has five distinct physical roles. -/
theorem block_injective : Function.Injective blockStack := by decide
/-- Numeric equality has four distinct physical roles. -/
theorem equal_injective : Function.Injective equalStack := by decide
/-- One fixed whole scale machine, with descriptor inputs explicitly physical. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inl (.inl (SemiprimeD1BinaryPublicAcquisition.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))))
  (auxRole .output) .start program
/-- Every stack alphabet is finite before N, j/k and the assignment. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- Control contains finite flags only, never native N/words/expressions/counts. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- Every physical data role, including private unused shadows, is counted. -/
theorem stack_card : Fintype.card Stack=160 := by decide
end RiemannGaussian.SemiprimeD1StackPublicScale
