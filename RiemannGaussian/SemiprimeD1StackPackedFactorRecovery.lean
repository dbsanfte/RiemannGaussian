/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutOriginal
import RiemannGaussian.SemiprimeD1StackBinarySquareRootOriginal
import RiemannGaussian.SemiprimeD1StackSubtractorExecution

/-! # A literal binary packed-scalar factor recovery source
The only two original words are N and the actually acquired packed scalar.
Real readout, binary arithmetic, a whole binary square-root call and physical
factor checks acquire the outputs. Scalar acquisition remains a caller duty.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecovery
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackPackedMomentReadout (Stack Label program input originalInput scalarInput aux digit)
end R
namespace S
export SemiprimeD1StackBinarySquareRoot (Stack Label program input originalInput power adder multiply compare aux clearStack)
end S
namespace A
export SemiprimeD1StackAdder (Stack Label code store)
end A
namespace X
export SemiprimeD1StackMultiplier (Stack Label code input factor payload)
end X
namespace W
export SemiprimeD1StackWordLess (Stack Label program output store)
end W
/-- Dedicated physical factor outputs, status/parser word and restoring scratch. -/
inductive Aux where | small | large | status | scratch deriving DecidableEq,Repr
/-- Four literal extra words, independent of N and the scalar. -/
instance auxFintype : Fintype Aux := Fintype.ofList [.small,.large,.status,.scratch] (by intro k;cases k <;> simp)
/-- The complete readout22 and square-root33 banks plus four explicit words. -/
abbrev Stack := R.Stack⊕(S.Stack⊕Aux)
/-- Whole actual readout bank, retained exactly after acquisition. -/
def readout (k : R.Stack) : Stack := .inl k
/-- Whole binary square-root allocation; its18 arithmetic words are reused between calls. -/
def squareRoot (k : S.Stack) : Stack := .inr (.inl k)
/-- Explicit new physical words; no private role is hidden in control. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- Original binary N. -/
def originalInput : Stack := readout R.originalInput
/-- Actual acquired packed scalar, never supplied moments or factors. -/
def scalarInput : Stack := readout R.scalarInput
/-- Actual binary factor sum, acquired by the real readout. -/
def sum : Stack := readout (R.aux .sum)
/-- Actual binary model count, acquired by the real readout. -/
def count : Stack := readout (R.aux .count)
/-- Shared four-word addition/subtraction map. -/
def adder (k : A.Stack) : Stack := squareRoot (S.adder k)
/-- Shared nine-word real multiplication map. -/
def multiply (k : X.Stack) : Stack := squareRoot (S.multiply k)
/-- Shared five-word real numeric comparison map. -/
def compare (k : W.Stack) : Stack := squareRoot (S.compare k)
/-- Fixed sites for every preserving copy; all values stay on Boolean stacks. -/
inductive Copy where
  | count | squareSmall | squareLarge | squareLeft | squareRight | squareResult | number | discriminant
  | minusLeft | minusRight | small | plusLeft | plusRight | large | checkSmall | checkLarge
  | productLeft | productRight | productCompare | numberCompare | reverseNumber | reverseProduct
  deriving DecidableEq,Repr
/-- Complete fixed copy inventory. -/
def copies : List Copy := [.count,.squareSmall,.squareLarge,.squareLeft,.squareRight,.squareResult,.number,
  .discriminant,.minusLeft,.minusRight,.small,.plusLeft,.plusRight,.large,.checkSmall,.checkLarge,
  .productLeft,.productRight,.productCompare,.numberCompare,.reverseNumber,.reverseProduct]
/-- Every fixed copy site is listed literally. -/
instance copyFintype : Fintype Copy := Fintype.ofList copies (by intro k;cases k <;> simp [copies])
/-- Literal source addresses for all preserving copies. -/
def copySource : Copy→Stack
  | .count => count
  | .squareSmall | .squareLarge | .squareLeft | .squareRight | .minusLeft | .plusLeft => sum
  | .squareResult | .productCompare | .reverseProduct => multiply (.inl .right)
  | .number | .numberCompare | .reverseNumber => originalInput
  | .discriminant | .small | .large => adder .output
  | .minusRight | .plusRight => squareRoot (S.aux .output)
  | .checkSmall | .productLeft => aux .small
  | .checkLarge | .productRight => aux .large
/-- Literal destination addresses for all preserving copies. -/
def copyTarget : Copy→Stack
  | .count => aux .status
  | .squareSmall | .small => aux .small
  | .squareLarge | .large => aux .large
  | .squareLeft | .productLeft => multiply X.input
  | .squareRight | .productRight => multiply X.factor
  | .squareResult | .minusLeft | .plusLeft => adder .left
  | .number | .minusRight | .plusRight => adder .right
  | .discriminant => squareRoot S.originalInput
  | .checkSmall | .checkLarge | .productCompare | .reverseNumber => compare (.inl .left)
  | .numberCompare | .reverseProduct => compare (.inl .right)
/-- Every actual copy restores the same separate physical scratch. -/
def copyStack (site : Copy) (k : Fin 3) : Stack :=
  if k=0 then copySource site else if k=1 then copyTarget site else aux .scratch
/-- Consuming reversal for a selected factor borrows the empty square-root power word. -/
def reverseStack (large : Bool) (k : Fin 2) : Stack :=
  if k=0 then aux (if large then .large else .small) else squareRoot S.power
/-- Real high-zero trimming restores the borrowed power and both empty adder operands. -/
def trimStack (large : Bool) : A.Stack→Stack
  | .left => adder .left | .right => adder .right
  | .scratch => squareRoot S.power | .output => aux (if large then .large else .small)
/-- Every possible arithmetic/temporary payload is physically drained on rejection. -/
def abortStack (k : Fin 22) : Stack :=
  if h:k.val<18 then squareRoot (S.clearStack ⟨k.val,h⟩)
  else match k.val with | 18 => aux .small | 19 => aux .large | 20 => aux .status | _ => aux .scratch
/-- Fixed finite stages; no operand, unbounded counter or evaluator lives in labels. -/
inductive Control where
  | start | copy (site : Copy) | countHead | countOneEof | countTwoTrue | countTwoEof
  | square | times4a | times4b | subtractD | borrowD | clearD | clearSquare | root
  | minus | minusBorrow | minusParity | clearMinus | plus | plusParity | clearPlus
  | reverse (large : Bool) | trim (large : Bool)
  | seed2a (large : Bool) | seed2b (large : Bool) | lessFactor (large : Bool) | factorFlag (large : Bool)
  | product | lessProduct | productFlag | lessNumber | numberFlag | clearProduct | success | done
  | abort (k : Fin 22) | reject
  deriving DecidableEq,Repr
/-- Explicit complete literal stage inventory. -/
instance controlFintype : Fintype Control := Fintype.ofList
  ([.start,.countHead,.countOneEof,.countTwoTrue,.countTwoEof,.square,.times4a,.times4b,.subtractD,.borrowD,
    .clearD,.clearSquare,.root,.minus,.minusBorrow,.minusParity,.clearMinus,.plus,.plusParity,.clearPlus,
    .reverse false,.reverse true,.trim false,.trim true,.seed2a false,.seed2a true,.seed2b false,.seed2b true,
    .lessFactor false,.lessFactor true,.factorFlag false,.factorFlag true,.product,.lessProduct,.productFlag,
    .lessNumber,.numberFlag,.clearProduct,.success,.done,.reject]++copies.map Control.copy++List.ofFn Control.abort)
  (by intro k;cases k <;> simp [copies];all_goals rename_i k;fin_cases k <;> simp)
/-- All actual included labels and finite source-specific copy/reverse sites. -/
abbrev Label := Control⊕(R.Label⊕(S.Label⊕(A.Label⊕(SemiprimeD1StackSubtractor.Label⊕
  (X.Label⊕(W.Label⊕((Copy×Fin 9)⊕((Bool×Fin 4)⊕(Bool×SemiprimeD1StackReduce.Label)))))))))
/-- Literal enclosing stage. -/
def ctl : Control→Label := Sum.inl
/-- Whole actual readout labels. -/
def readoutLabel (pc : R.Label) : Label := .inr (.inl pc)
/-- Whole actual binary square-root labels. -/
def squareRootLabel (pc : S.Label) : Label := .inr (.inr (.inl pc))
/-- Actual shared adder labels. -/
def adderLabel (pc : A.Label) : Label := .inr (.inr (.inr (.inl pc)))
/-- Actual shared subtractor labels, including its physical borrow prefix. -/
def subtractLabel (pc : SemiprimeD1StackSubtractor.Label) : Label := .inr (.inr (.inr (.inr (.inl pc))))
/-- Actual shared multiplier labels. -/
def multiplyLabel (pc : X.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inl pc)))))
/-- Actual shared numeric-comparison labels. -/
def compareLabel (pc : W.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inl pc))))))
/-- Actual restoring-copy labels. -/
def copyLabel (site : Copy) (pc : Fin 9) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (site,pc))))))))
/-- Actual consuming-reversal labels. -/
def reverseLabel (large : Bool) (pc : Fin 4) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (large,pc)))))))))
/-- Actual consuming-trim labels. -/
def trimLabel (large : Bool) (pc : SemiprimeD1StackReduce.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (large,pc)))))))))
/-- Fixed next stage after each real preserving copy. -/
def afterCopy : Copy→Label
  | .count => ctl .countHead
  | .squareSmall => ctl (.copy .squareLarge) | .squareLarge => ctl (.copy .checkSmall)
  | .squareLeft => ctl (.copy .squareRight) | .squareRight => ctl .square
  | .squareResult => ctl (.copy .number) | .number => ctl .times4a | .discriminant => ctl .clearD
  | .minusLeft => ctl (.copy .minusRight) | .minusRight => ctl .minus | .small => ctl .clearMinus
  | .plusLeft => ctl (.copy .plusRight) | .plusRight => ctl .plus | .large => ctl .clearPlus
  | .checkSmall => ctl (.seed2a false) | .checkLarge => ctl (.seed2a true)
  | .productLeft => ctl (.copy .productRight) | .productRight => ctl .product
  | .productCompare => ctl (.copy .numberCompare) | .numberCompare => ctl .lessProduct
  | .reverseNumber => ctl (.copy .reverseProduct) | .reverseProduct => ctl .lessNumber
/-- The next physical reject drain, then a literal FALSE status. -/
def abortNext (k : Fin 22) : Label := if h:k.val+1<22 then ctl (.abort ⟨k.val+1,h⟩) else ctl .reject
/-- One constant literal source with real acquisition, arithmetic and final factor validation. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (readoutLabel (SemiprimeD1StackPackedMomentReadout.ctl .start)) (ctl (.copy .count))
  | .inl (.copy site) => .call (copyLabel site 0) (afterCopy site)
  | .inl .countHead => .base (.pop (aux .status) (ctl (.abort 0)) (ctl .countTwoTrue) (ctl .countOneEof))
  | .inl .countOneEof => .base (.pop (aux .status) (ctl (.copy .squareSmall)) (ctl (.abort 0)) (ctl (.abort 0)))
  | .inl .countTwoTrue => .base (.pop (aux .status) (ctl (.abort 0)) (ctl (.abort 0)) (ctl .countTwoEof))
  | .inl .countTwoEof => .base (.pop (aux .status) (ctl (.copy .squareLeft)) (ctl (.abort 0)) (ctl (.abort 0)))
  | .inl .square => .call (multiplyLabel (.control .start)) (ctl (.copy .squareResult))
  | .inl .times4a => .base (.push (adder .right) false (ctl .times4b))
  | .inl .times4b => .base (.push (adder .right) false (ctl .subtractD))
  | .inl .subtractD => .call (subtractLabel (.start false)) (ctl .borrowD)
  | .inl .borrowD => .base (.pop (adder .output) (ctl (.abort 0)) (ctl (.copy .discriminant)) (ctl (.abort 0)))
  | .inl .clearD => .base (.pop (adder .output) (ctl .clearSquare) (ctl .clearD) (ctl .clearD))
  | .inl .clearSquare => .base (.pop (multiply (.inl .right)) (ctl .root) (ctl .clearSquare) (ctl .clearSquare))
  | .inl .root => .call (squareRootLabel (SemiprimeD1StackBinarySquareRoot.ctl .start)) (ctl (.copy .minusLeft))
  | .inl .minus => .call (subtractLabel (.start false)) (ctl .minusBorrow)
  | .inl .minusBorrow => .base (.pop (adder .output) (ctl (.abort 0)) (ctl .minusParity) (ctl (.abort 0)))
  | .inl .minusParity => .base (.pop (adder .output) (ctl (.abort 0)) (ctl (.copy .small)) (ctl (.abort 0)))
  | .inl .clearMinus => .base (.pop (adder .output) (ctl (.copy .plusLeft)) (ctl .clearMinus) (ctl .clearMinus))
  | .inl .plus => .call (adderLabel (.start false)) (ctl .plusParity)
  | .inl .plusParity => .base (.pop (adder .output) (ctl (.abort 0)) (ctl (.copy .large)) (ctl (.abort 0)))
  | .inl .clearPlus => .base (.pop (adder .output) (ctl (.reverse false)) (ctl .clearPlus) (ctl .clearPlus))
  | .inl (.reverse large) => .call (reverseLabel large 0) (ctl (.trim large))
  | .inl (.trim large) => .call (trimLabel large .trim) (if large then ctl (.copy .checkSmall) else ctl (.reverse true))
  | .inl (.seed2a large) => .base (.push (compare (.inl .right)) true (ctl (.seed2b large)))
  | .inl (.seed2b large) => .base (.push (compare (.inl .right)) false (ctl (.lessFactor large)))
  | .inl (.lessFactor large) => .call (compareLabel .start) (ctl (.factorFlag large))
  | .inl (.factorFlag large) => .base (.pop (compare W.output) (ctl (.abort 0))
      (if large then ctl (.copy .productLeft) else ctl (.copy .checkLarge)) (ctl (.abort 0)))
  | .inl .product => .call (multiplyLabel (.control .start)) (ctl (.copy .productCompare))
  | .inl .lessProduct => .call (compareLabel .start) (ctl .productFlag)
  | .inl .productFlag => .base (.pop (compare W.output) (ctl (.abort 0)) (ctl (.copy .reverseNumber)) (ctl (.abort 0)))
  | .inl .lessNumber => .call (compareLabel .start) (ctl .numberFlag)
  | .inl .numberFlag => .base (.pop (compare W.output) (ctl (.abort 0)) (ctl .clearProduct) (ctl (.abort 0)))
  | .inl .clearProduct => .base (.pop (multiply (.inl .right)) (ctl .success) (ctl .clearProduct) (ctl .clearProduct))
  | .inl .success => .base (.push (aux .status) true (ctl .done))
  | .inl .done => .base .halt
  | .inl (.abort k) => .base (.pop (abortStack k) (abortNext k) (ctl (.abort k)) (ctl (.abort k)))
  | .inl .reject => .base (.push (aux .status) false (ctl .done))
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction readout readoutLabel (R.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction squareRoot squareRootLabel (S.program pc)
  | .inr (.inr (.inr (.inl pc))) => SemiprimeD1StackMultiplierLink.instruction adder adderLabel (A.code pc)
  | .inr (.inr (.inr (.inr (.inl pc)))) => SemiprimeD1StackMultiplierLink.instruction adder subtractLabel (SemiprimeD1StackSubtractor.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inl pc))))) => SemiprimeD1StackValidationLink.instruction multiply multiplyLabel (X.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl pc)))))) => SemiprimeD1StackValidationLink.instruction compare compareLabel (W.program pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (site,pc)))))))) =>
    SemiprimeD1StackMultiplierLink.instruction (copyStack site) (copyLabel site) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (large,pc))))))))) =>
    SemiprimeD1StackMultiplierLink.instruction (reverseStack large) (reverseLabel large) (SemiprimeD1StackReverseWord.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (large,pc))))))))) =>
    SemiprimeD1StackMultiplierLink.instruction (trimStack large) (trimLabel large) (SemiprimeD1StackReduce.code pc)
/-- Full physical bank, with no discarded foreign or scratch roles. -/
def bank (r : R.Stack→List Bool) (s : S.Stack→List Bool) (u : Aux→List Bool) : Stack→List Bool := Sum.elim r (Sum.elim s u)
/-- Precisely binary N and its actual packed scalar are initially present. -/
def input (bits scalar : List Bool) : Stack→List Bool := bank (R.input bits scalar) (fun _=>[]) (fun _=>[])
/-- True prepared front door; no moment, discriminant, root or factor input. -/
def initial (bits scalar : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input bits scalar,[]⟩
/-- One fixed finite physical machine, before every N/scalar choice. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .small) (ctl .start) program
/-- Every physical word is counted. -/
theorem stack_card : Fintype.card Stack=59 := by decide
/-- Whole readout bank has distinct physical addresses. -/
theorem readout_injective : Function.Injective readout := Sum.inl_injective
/-- Whole binary square-root bank has distinct physical addresses. -/
theorem squareRoot_injective : Function.Injective squareRoot := by intro a b h;exact Sum.inl_injective (Sum.inr_injective h)
/-- Every copy restores a third distinct physical word. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site) := by cases site <;> decide
/-- Both consuming reversal operands are distinct. -/
theorem reverse_injective (large : Bool) : Function.Injective (reverseStack large) := by cases large <;> decide
/-- Every trim call has four distinct actual operands. -/
theorem trim_injective (large : Bool) : Function.Injective (trimStack large) := by cases large <;> decide
/-- Data and saved-return alphabets are fixed finite. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Internal control is finite and contains no unbounded arithmetic state. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPackedFactorRecovery
