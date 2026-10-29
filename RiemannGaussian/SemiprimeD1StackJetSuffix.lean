/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryProduct
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackProcedureTrace

/-! # Physical acquisition of original mixed-radix suffix records
The first pass parses/reverses the actual axis fields. The second pass starts
from product one and physically acquires every suffix product with UnaryProduct.
Framing/copying/parser work is part of the fixed included program. Rank is an
actual retained product output, not an input bound or supplied value.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetSuffix
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
namespace P
export SemiprimeD1StackUnaryProduct (Stack Label code entry)
end P

/-- Fixed physical Boolean argument/cache/work stacks. -/
inductive Stack | axes | reverseAxes | axis | radix | product | records | scratch | valid
  deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.axes,.reverseAxes,.axis,.radix,.product,.records,.scratch,.valid}
  complete := by intro k; cases k <;> simp

/-- Finite control stages; failure cleanup enumerates only the fixed stack bank. -/
inductive Control
  | vector | readAxis | axisRead | positive | reverseFrame | clearAxis | startSuffix
  | suffixPeek | readReverse | reverseRead | frameRadix | frameAxis | productCall
  | clearRadix | moveProduct | movePush | success | fail (stage : Fin 8) | failure | halt
  deriving DecidableEq,Inhabited,Repr
instance : Fintype Control := Fintype.ofList
  ([.vector,.readAxis,.axisRead,.positive,.reverseFrame,.clearAxis,.startSuffix,
    .suffixPeek,.readReverse,.reverseRead,.frameRadix,.frameAxis,.productCall,
    .clearRadix,.moveProduct,.movePush,.success,.failure,.halt]++(List.finRange 8).map .fail)
  (by intro k; cases k <;> simp)

/-- Fixed disjoint copies of Field, Frame and actual UnaryProduct instruction tables. -/
abbrev Label := F.Label ⊕ (F.Label ⊕ (Fin 11 ⊕ (Fin 11 ⊕ (Fin 11 ⊕ (P.Label ⊕ Control)))))

/-- Literal control label. -/
def control (c : Control) : Label := .inr (.inr (.inr (.inr (.inr (.inr c)))))
/-- Axis-input field-parser label. -/
def axesField (l : F.Label) : Label := .inl l
/-- Reverse-axis field-parser label. -/
def reverseField (l : F.Label) : Label := .inr (.inl l)
/-- Actual reverse-axis framing label. -/
def reverseFrame (l : Fin 11) : Label := .inr (.inr (.inl l))
/-- Actual suffix-divisor framing label. -/
def radixFrame (l : Fin 11) : Label := .inr (.inr (.inr (.inl l)))
/-- Actual axis framing label. -/
def axisFrame (l : Fin 11) : Label := .inr (.inr (.inr (.inr (.inl l))))
/-- Actual metadata-product label. -/
def productLabel (l : P.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inl l)))))

/-- Original axis parser reads actual source tape, with physical validity bit. -/
def axesFieldStack : F.Stack → Stack
  | .inl .input => .axes
  | .inl .scratch => .scratch
  | .inl .output => .axis
  | .inr _ => .valid
/-- Reverse parser reads actual acquired reverse-axis records. -/
def reverseFieldStack : F.Stack → Stack
  | .inl .input => .reverseAxes
  | .inl .scratch => .scratch
  | .inl .output => .axis
  | .inr _ => .valid
/-- Axis-framing acquisition retains the original counter while prepending its field. -/
def reverseFrameStack : Fin 3 → Stack := fun k => if k=0 then .axis else if k=1 then .reverseAxes else .scratch
/-- Suffix-radix framing retains the actual acquired product. -/
def radixFrameStack : Fin 3 → Stack := fun k => if k=0 then .radix else if k=1 then .records else .scratch
/-- Axis-framing prepends the first field of each actual (q,d) record. -/
def axisFrameStack : Fin 3 → Stack := fun k => if k=0 then .axis else if k=1 then .records else .scratch
/-- Product consumes the actual axis counter and copies/restores the actual radix. -/
def productStack : P.Stack → Stack
  | .multiplier => .axis
  | .multiplicand => .radix
  | .scratch => .scratch
  | .product => .product

/-- Fixed failure-clearing catalogue, with no input-sized control address. -/
def clearStack (k : Fin 8) : Stack :=
  if k=0 then .axes else if k=1 then .reverseAxes else if k=2 then .axis else if k=3 then .radix
  else if k=4 then .product else if k=5 then .records else if k=6 then .scratch else .valid

/-- Actual closed finite program: all suffix products are physically acquired. -/
def code : Label → C.Instruction Stack Label
  | .inl l => SemiprimeD1StackMultiplierLink.instruction axesFieldStack axesField (F.code l)
  | .inr (.inl l) => SemiprimeD1StackMultiplierLink.instruction reverseFieldStack reverseField (F.code l)
  | .inr (.inr (.inl l)) => SemiprimeD1StackMultiplierLink.instruction reverseFrameStack reverseFrame
      (SemiprimeD1StackFrame.code l)
  | .inr (.inr (.inr (.inl l))) => SemiprimeD1StackMultiplierLink.instruction radixFrameStack radixFrame
      (SemiprimeD1StackFrame.code l)
  | .inr (.inr (.inr (.inr (.inl l)))) => SemiprimeD1StackMultiplierLink.instruction axisFrameStack axisFrame
      (SemiprimeD1StackFrame.code l)
  | .inr (.inr (.inr (.inr (.inr (.inl l))))) =>
      SemiprimeD1StackMultiplierLink.instruction productStack productLabel (P.code l)
  | .inr (.inr (.inr (.inr (.inr (.inr c))))) => match c with
    | .vector => .base (.pop .axes (control (.fail 0)) (control .startSuffix) (control .readAxis))
    | .readAxis => .call (axesField (F.active .tagPop (none,false))) (control .axisRead)
    | .axisRead => .base (.pop .valid (control (.fail 0)) (control (.fail 0)) (control .positive))
    | .positive => .base (.peek .axis (control (.fail 0)) (control .reverseFrame) (control .reverseFrame))
    | .reverseFrame => .call (reverseFrame 0) (control .clearAxis)
    | .clearAxis => .base (.pop .axis (control .vector) (control .clearAxis) (control .clearAxis))
    | .startSuffix => .base (.push .radix true (control .suffixPeek))
    | .suffixPeek => .base (.peek .reverseAxes (control .success) (control .readReverse) (control .readReverse))
    | .readReverse => .call (reverseField (F.active .tagPop (none,false))) (control .reverseRead)
    | .reverseRead => .base (.pop .valid (control (.fail 0)) (control (.fail 0)) (control .frameRadix))
    | .frameRadix => .call (radixFrame 0) (control .frameAxis)
    | .frameAxis => .call (axisFrame 0) (control .productCall)
    | .productCall => .call (productLabel P.entry) (control .clearRadix)
    | .clearRadix => .base (.pop .radix (control .moveProduct) (control .clearRadix) (control .clearRadix))
    | .moveProduct => .base (.pop .product (control .suffixPeek) (control .movePush) (control .movePush))
    | .movePush => .base (.push .radix true (control .moveProduct))
    | .success => .base (.push .valid true (control .halt))
    | .fail k => .base (.pop (clearStack k)
        (if h : k.val<7 then control (.fail ⟨k.val+1,by omega⟩) else control .failure)
        (control (.fail k)) (control (.fail k)))
    | .failure => .base (.push .valid false (control .halt))
    | .halt => .base .halt

/-- Actual fixed finite machine. Prepared physical axes are its sole argument stack. -/
def machine := SemiprimeD1StackCalls.machine Stack.axes Stack.records (control .vector) code

/-- Explicit physical data bank. -/
def data (axes reverseAxes axis radix product records scratch valid : List Bool) : Stack → List Bool
  | .axes => axes
  | .reverseAxes => reverseAxes
  | .axis => axis
  | .radix => radix
  | .product => product
  | .records => records
  | .scratch => scratch
  | .valid => valid

end RiemannGaussian.SemiprimeD1StackJetSuffix
