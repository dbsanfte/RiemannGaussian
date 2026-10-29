/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprCodec
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops

/-! # Actual physical acquisition of power-expression syntax
The already acquired base byte stream is copied once per physical exponent
marker. Literal one and multiplication tags are emitted by fixed pushes. Two
real exponent copies preserve its cache; no runtime AST or power opcode exists.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprPower
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Five fixed Boolean data roles, independent of both syntax and exponent. -/
abbrev Stack := Fin 5
/-- Physical base syntax, retained by every real copy. -/
def base : Stack := 0
/-- Cached physical exponent markers; their values are never decoded. -/
def exponent : Stack := 1
/-- Disposable physical copy of the exponent marker word. -/
def counter : Stack := 2
/-- Actual Copy restoration scratch, empty between every call. -/
def scratch : Stack := 3
/-- Output code, with an actual already acquired suffix retained at its tail. -/
def output : Stack := 4
/-- Both fixed Copy sites: exponent→counter or encoded base→output. -/
def copyStack (isBase : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if isBase then base else exponent)
  else if k=1 then (if isBase then output else counter) else scratch

/-- Constant syntax-building labels and real Copy instructions. -/
inductive Label where
  | start | baseLoop | baseCopy | one0 | one1 | one2 | one3 | one4
  | copyAgain | mulLoop | mul0 | mul1 | done | copy (isBase : Bool) (pc : Fin 9)
  deriving DecidableEq,Fintype,Repr

/-- Complete fixed code. The five literal-one pushes are its REVERSED encoded
word; each later marker prepends exactly two actual multiplication-tag bits. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.copy false 0) .baseLoop
  | .baseLoop => .base (.pop counter .one0 .baseCopy .baseCopy)
  | .baseCopy => .call (.copy true 0) .baseLoop
  | .one0 => .base (.push output false .one1)
  | .one1 => .base (.push output true .one2)
  | .one2 => .base (.push output true .one3)
  | .one3 => .base (.push output false .one4)
  | .one4 => .base (.push output false .copyAgain)
  | .copyAgain => .call (.copy false 0) .mulLoop
  | .mulLoop => .base (.pop counter .done .mul0 .mul0)
  | .mul0 => .base (.push output true .mul1)
  | .mul1 => .base (.push output true .mulLoop)
  | .done => .base .halt
  | .copy isBase pc => SemiprimeD1StackMultiplierLink.instruction (copyStack isBase)
      (Label.copy isBase) (SemiprimeD1StackCopy.code pc)

/-- Exact physical syntax/cache/counter/work/output payload. -/
def store (baseCode cached count work out : List Bool) : Stack→List Bool := fun k=>
  if k=0 then baseCode else if k=1 then cached else if k=2 then count else if k=3 then work else out
/-- Actual source entry; base and exponent syntax acquisition are caller work. -/
def initial (baseCode cached tail : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store baseCode cached [] [] tail,[]⟩
/-- Both real copy operand maps have distinct physical roles. -/
theorem copyStack_injective (isBase : Bool) : Function.Injective (copyStack isBase) := by
  cases isBase <;> decide
/-- One fixed actual finite machine, never an input-sized program factory. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine base output .start program
/-- Every data and return-tag alphabet is fixed and finite before the input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite base output .start program
/-- Transient control carries no exponent value, encoded base or syntax tree. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite base output .start program

end RiemannGaussian.SemiprimeD1StackExprPower
