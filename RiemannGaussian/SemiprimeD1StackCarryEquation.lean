/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordEqualBounds
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
import RiemannGaussian.SemiprimeD1StackCopy
/-! # Physical INTEGER carry equation from one framed operand record
The offset is the LENGTH of the physically retained template. No congruence,
decoded integer, expected shift, sum or accepted Boolean is a runtime input.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCarryEquation
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace A
export SemiprimeD1StackAdder (Stack Label code state store)
end A
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial)
end F
/-- Fixed physical data roles, including all parser/shift/arithmetic work. -/
inductive Stack where
  | input | cached | count | scratch | valid | coefficient | previous | target | next | left | right | output
  deriving DecidableEq,Repr
instance : Fintype Stack := Fintype.ofList
  [.input,.cached,.count,.scratch,.valid,.coefficient,.previous,.target,.next,.left,.right,.output]
  (by intro k;cases k <;> simp)
/-- The actual four framed operand destinations. -/
def operand (k : Fin 4) : Stack := if k=0 then .coefficient else if k=1 then .previous else if k=2 then .target else .next
/-- Static field parser wiring; source bytes and work are all physical. -/
def fieldStack (k : Fin 4) : F.Stack→Stack
  | .inl .input=>.input
  | .inl .scratch=>.scratch
  | .inl .output=>operand k
  | .inr _=>.valid
/-- Actual preserving cached-template copy. -/
def copyStack (k : Fin 3) : Stack := if k=0 then .cached else if k=1 then .count else .scratch
/-- The TWO actual integer ripple-adders, sharing only empty work. -/
def addStack (right : Bool) : A.Stack→Stack
  | .left=>if right then .target else .coefficient
  | .right=>if right then .next else .previous
  | .scratch=>.scratch
  | .output=>if right then .right else .left
/-- Actual final numeric comparison wiring. -/
def equalStack : A.Stack→Stack
  | .left=>.left | .right=>.right | .scratch=>.scratch | .output=>.output
/-- Fixed finite control and literal component locations. -/
inductive Label where
  | read (k : Fin 4) | check (k : Fin 4) | copyCache | shift | prepend | addLeft | addRight | compare | done | bad
  | field (k : Fin 4) (pc : F.Label) | copy (pc : Fin 9)
  | add (right : Bool) (pc : A.Label) | equal (pc : SemiprimeD1StackWordEqual.Label)
  deriving DecidableEq,Fintype
/-- After each parsed field, consume the actual parser validity Boolean. -/
def afterField (k : Fin 4) : Label := if k=0 then .read 1 else if k=1 then .read 2 else if k=2 then .read 3 else .copyCache
/-- ONE fixed code table. Every arithmetic/parser subroutine is actual included code. -/
def program : Label→C.Instruction Stack Label
  | .read k=>.call (.field k (F.active .tagPop (none,false))) (.check k)
  | .check k=>.base (.pop .valid .bad .bad (afterField k))
  | .copyCache=>.call (.copy 0) .shift
  | .shift=>.base (.pop .count .addLeft .prepend .prepend)
  | .prepend=>.base (.push .next false .shift)
  | .addLeft=>.call (.add false (.start false)) .addRight
  | .addRight=>.call (.add true (.start false)) .compare
  | .compare=>.call (.equal .loop) .done
  | .done | .bad=>.base .halt
  | .field k pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack k) (Label.field k) (F.code pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .add right pc=>SemiprimeD1StackMultiplierLink.instruction (addStack right) (Label.add right) (A.code pc)
  | .equal pc=>SemiprimeD1StackMultiplierLink.instruction equalStack Label.equal (SemiprimeD1StackWordEqual.code pc)
/-- Literal physical payload view, never a decoded arithmetic input. -/
def store (input cached count scratch valid coefficient previous target next left right output : List Bool) : Stack→List Bool
  | .input=>input | .cached=>cached | .count=>count | .scratch=>scratch | .valid=>valid
  | .coefficient=>coefficient | .previous=>previous | .target=>target | .next=>next
  | .left=>left | .right=>right | .output=>output
/-- One physical framed record, with arbitrary unconsumed suffix. -/
def record (coefficient previous target next tail : List Bool) : List Bool :=
  SemiprimeSourceHistogramKeyBits.frame coefficient
    (SemiprimeSourceHistogramKeyBits.frame previous
      (SemiprimeSourceHistogramKeyBits.frame target (SemiprimeSourceHistogramKeyBits.frame next tail)))
/-- Only original physical record and offset template are supplied. -/
def input (code cached : List Bool) : Stack→List Bool := store code cached [] [] [] [] [] [] [] [] [] []
/-- Literal source entry with every temporary and return stack empty. -/
def initial (code cached : List Bool) : C.State Stack Label := ⟨some (.read 0),none,none,input code cached,[]⟩
/-- All four parser roles are distinct for every actual operand field. -/
theorem field_injective (k : Fin 4) : Function.Injective (fieldStack k) := by
  fin_cases k <;> intro i j h <;> rcases i with i|i <;> rcases j with j|j <;>
    cases i <;> cases j <;> simp_all [fieldStack,operand]
/-- Preserving copy has genuinely separate source/destination/scratch. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- Both ripple-add calls have separate actual operands, scratch and output. -/
theorem add_injective (right : Bool) : Function.Injective (addStack right) := by
  cases right <;> intro i j h <;> cases i <;> cases j <;> simp_all [addStack]
/-- Actual comparator roles are distinct. -/
theorem equal_injective : Function.Injective equalStack := by
  intro i j h;cases i <;> cases j <;> simp_all [equalStack]
/-- Actual finite INTEGER checker; syntax/record acquisition remains caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.input Stack.output (.read 0) program
/-- Every actual data and return alphabet is fixed and finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.input Stack.output (Label.read 0) program
/-- No integer/list/function appears in finite control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.input Stack.output (Label.read 0) program
/-- Exact physical data-role count. -/
theorem stack_card : Fintype.card Stack=12 := by decide
end RiemannGaussian.SemiprimeD1StackCarryEquation
