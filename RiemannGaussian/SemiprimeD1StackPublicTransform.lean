/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleFinite
import RiemannGaussian.SemiprimeD1StackResidueMulBounds
/-! # Closed original public first/second transform instruction table
Only original binary N, raw assignment and TWO physical descriptor Booleans
enter. Original axes, root code, modulus, normalization, vectors, guards and
all output queries are acquired/executed by literal included procedures.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransform
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace R
export SemiprimeD1StackRootSources (Stack Label program initial input modulusKey)
end R
namespace D
export SemiprimeD1StackDotEvaluate (Stack Label program initial modulus output)
end D
namespace M
export SemiprimeD1StackResidueMul (Stack Label program initial modulus output)
end M
namespace W
export SemiprimeD1StackWordVector (Stack Label program initial original countCache output)
end W
namespace V
export SemiprimeD1StackVectorCanonical (Stack Label program initial)
end V
namespace J
export SemiprimeD1StackJetRead (Stack Label program)
end J
namespace E
export SemiprimeD1StackWordEqual (Label code)
end E
/-- Seven fixed original-input/control/cache/work data roles. -/
inductive Aux where
  | raw | second | inverse | normalizer | remaining | scratch | output
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList [.raw,.second,.inverse,.normalizer,.remaining,.scratch,.output]
  (by intro k;cases k <;> simp)
/-- A fixed disjoint physical role catalogue; none of its fields depends on N. -/
inductive Stack where
  | roots (k : R.Stack) | dot (k : D.Stack) | multiply (k : M.Stack)
  | inputVector (k : W.Stack) | outputVector (k : W.Stack)
  | guard (k : V.Stack) | read (k : J.Stack) | equal (k : SemiprimeD1StackAdder.Stack) | aux (k : Aux)
  deriving DecidableEq,Fintype
/-- Literal copied metadata sites, all finite before original N. -/
inductive CopyKind where
  | root (inverse : Bool) | modulus (destination : Fin 5) | axis (second : Bool) (destination : Fin 4)
  | normalizer | rawInput | rawOutput | vector (fromOutput : Bool) (destination : Fin 3)
  | remaining | frequency | index | normOperand | dotOperand | productResult | outputWord
  deriving DecidableEq,Fintype
/-- Actual original acquired n axis: t for first, r for second. -/
def axisRole (second : Bool) : R.Stack := .inl (SemiprimeD1BinaryPublicAcquisition.axesStack (.inr (if second then 0 else 1)))
/-- Actual three-role copy sources; original normalization is a REAL acquired word. -/
def copySource : CopyKind→Stack
  | .root inverse=>.roots (.inr (if inverse then .root else .forwardRoot))
  | .modulus _=>.roots (.inl R.modulusKey)
  | .axis second destination=>.roots (axisRole (if destination=3 then !second else second))
  | .normalizer=>.roots (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true)))
  | .rawInput=>.aux .raw
  | .rawOutput=>.inputVector (.inl 0)
  | .vector fromOutput _=>if fromOutput then .outputVector W.output else .inputVector W.output
  | .remaining=>.dot (.inl .count)
  | .frequency | .index=>.aux .remaining
  | .normOperand=>.aux .normalizer
  | .dotOperand=>.dot D.output
  | .productResult=>.multiply M.output
  | .outputWord=>.read .output
/-- Actual copy destinations; every physical copy is explicitly included. -/
def copyDestination : CopyKind→Stack
  | .root _=>.dot (.inl .base)
  | .modulus destination=>if destination=0 then .dot D.modulus else if destination=1 then .multiply M.modulus
      else if destination=2 then .inputVector (.inl 1) else if destination=3 then .outputVector (.inl 1) else .guard .modulus
  | .axis _ destination=>if destination=0 then .dot (.inl .count) else if destination=1 then .inputVector W.countCache
      else if destination=2 then .outputVector W.countCache else .dot (.inl .stride)
  | .normalizer=>.aux .normalizer
  | .rawInput=>.inputVector W.original
  | .rawOutput=>.outputVector W.original
  | .vector _ destination=>if destination=0 then .dot (.inl .cache) else if destination=1 then .guard .cache else .read .cache
  | .remaining=>.aux .remaining
  | .frequency=>.dot (.inl .frequency)
  | .index=>.read .index
  | .normOperand=>.multiply (.inl SemiprimeD1StackMultiplier.input)
  | .dotOperand=>.multiply (.inl SemiprimeD1StackMultiplier.factor)
  | .productResult=>.equal .left
  | .outputWord=>.equal .right
/-- Literal actual preserving-copy role mapping. -/
def copyStack (kind : CopyKind) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyDestination kind else .aux .scratch
/-- Fixed whole-controller and actual nested-component labels. -/
inductive Label where
  | start | selectSecond | selectInverse (second : Bool) | rootCode (second inverse : Bool)
  | moduli (second inverse : Bool) (position : Fin 5) | axes (second inverse : Bool) (position : Fin 4)
  | normalization (second inverse : Bool) | copyRawInput | acquireInput | copyRawOutput | acquireOutput
  | copyInputDot | copyGuardInput | guardInput | branchInput | clearGuard | copyGuardOutput | guardOutput | branchOutput
  | copyOutputCache | copyLoop | loop | clearFrequency | copyFrequency | evaluate | copyDot | clearDot | copyNorm
  | multiply | copyProduct | clearProduct | copyIndex | readOutput | copyOutput | clearOutput | compare | branchEqual
  | accept | reject | clearRemaining | clearFinalFrequency | done | bad
  | roots (pc : R.Label) | dot (pc : D.Label) | multiplication (pc : M.Label)
  | inputWords (pc : W.Label) | outputWords (pc : W.Label) | check (pc : V.Label)
  | read (pc : J.Label) | equal (pc : E.Label) | copy (kind : CopyKind) (pc : Fin 9)
  deriving Fintype
/-- ONE actual closed instruction table. Loop count/frequency live only as
physical marker cells; normalization is copied from the N-only acquired bank. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.roots .start) .selectSecond
  | .selectSecond=>.base (.pop (.aux .second) .bad (.selectInverse false) (.selectInverse true))
  | .selectInverse second=>.base (.pop (.aux .inverse) .bad (.rootCode second false) (.rootCode second true))
  | .rootCode second inverse=>.call (.copy (.root inverse) 0) (.moduli second inverse 0)
  | .moduli second inverse pos=>.call (.copy (.modulus pos) 0)
      (if h : pos.val<4 then .moduli second inverse ⟨pos.val+1,by omega⟩ else .axes second inverse 0)
  | .axes second inverse pos=>.call (.copy (.axis second pos) 0)
      (if h : pos.val<3 then .axes second inverse ⟨pos.val+1,by omega⟩ else .normalization second inverse)
  | .normalization second inverse=>if second && inverse then .call (.copy .normalizer 0) .copyRawInput
      else .base (.push (.aux .normalizer) true .copyRawInput)
  | .copyRawInput=>.call (.copy .rawInput 0) .acquireInput
  | .acquireInput=>.call (.inputWords (.control .start)) .copyRawOutput
  | .copyRawOutput=>.call (.copy .rawOutput 0) .acquireOutput
  | .acquireOutput=>.call (.outputWords (.control .start)) .copyInputDot
  | .copyInputDot=>.call (.copy (.vector false 0) 0) .copyGuardInput
  | .copyGuardInput=>.call (.copy (.vector false 1) 0) .guardInput
  | .guardInput=>.call (.check .start) .branchInput
  | .branchInput=>.base (.pop (.guard .output) .bad .reject .clearGuard)
  | .clearGuard=>.base (.pop (.guard .cache) .copyGuardOutput .clearGuard .clearGuard)
  | .copyGuardOutput=>.call (.copy (.vector true 1) 0) .guardOutput
  | .guardOutput=>.call (.check .start) .branchOutput
  | .branchOutput=>.base (.pop (.guard .output) .bad .reject .copyOutputCache)
  | .copyOutputCache=>.call (.copy (.vector true 2) 0) .copyLoop
  | .copyLoop=>.call (.copy .remaining 0) .loop
  | .loop=>.base (.pop (.aux .remaining) .accept .clearFrequency .clearFrequency)
  | .clearFrequency=>.base (.pop (.dot (.inl .frequency)) .copyFrequency .clearFrequency .clearFrequency)
  | .copyFrequency=>.call (.copy .frequency 0) .evaluate
  | .evaluate=>.call (.dot .start) .copyDot
  | .copyDot=>.call (.copy .dotOperand 0) .clearDot
  | .clearDot=>.base (.pop (.dot D.output) .copyNorm .clearDot .clearDot)
  | .copyNorm=>.call (.copy .normOperand 0) .multiply
  | .multiply=>.call (.multiplication .start) .copyProduct
  | .copyProduct=>.call (.copy .productResult 0) .clearProduct
  | .clearProduct=>.base (.pop (.multiply M.output) .copyIndex .clearProduct .clearProduct)
  | .copyIndex=>.call (.copy .index 0) .readOutput
  | .readOutput=>.call (.read .start) .copyOutput
  | .copyOutput=>.call (.copy .outputWord 0) .clearOutput
  | .clearOutput=>.base (.pop (.read .output) .compare .clearOutput .clearOutput)
  | .compare=>.call (.equal .loop) .branchEqual
  | .branchEqual=>.base (.pop (.equal .output) .bad .reject .loop)
  | .accept=>.base (.push (.aux .output) true .clearRemaining)
  | .reject=>.base (.push (.aux .output) false .clearRemaining)
  | .clearRemaining=>.base (.pop (.aux .remaining) .clearFinalFrequency .clearRemaining .clearRemaining)
  | .clearFinalFrequency=>.base (.pop (.dot (.inl .frequency)) .done .clearFinalFrequency .clearFinalFrequency)
  | .done | .bad=>.base .halt
  | .roots pc=>SemiprimeD1StackValidationLink.instruction Stack.roots Label.roots (R.program pc)
  | .dot pc=>SemiprimeD1StackValidationLink.instruction Stack.dot Label.dot (D.program pc)
  | .multiplication pc=>SemiprimeD1StackValidationLink.instruction Stack.multiply Label.multiplication (M.program pc)
  | .inputWords pc=>SemiprimeD1StackValidationLink.instruction Stack.inputVector Label.inputWords (W.program pc)
  | .outputWords pc=>SemiprimeD1StackValidationLink.instruction Stack.outputVector Label.outputWords (W.program pc)
  | .check pc=>SemiprimeD1StackValidationLink.instruction Stack.guard Label.check (V.program pc)
  | .read pc=>SemiprimeD1StackValidationLink.instruction Stack.read Label.read (J.program pc)
  | .equal pc=>SemiprimeD1StackMultiplierLink.instruction Stack.equal Label.equal (E.code pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
/-- Original N/raw plus two singleton descriptor flags ONLY; no n/stride/root/
normalizer/modulus/vector/canonicality/evaluator/count/verdict input occurs. -/
def initial (bits raw : List Bool) (second inverse : Bool) : C.State Stack Label :=
  ⟨some .start,none,none,(fun k=>match k with
    | .roots j=>R.input bits j
    | .aux .raw=>raw
    | .aux .second=>[second]
    | .aux .inverse=>[inverse]
    | _=>[]),[]⟩
/-- One fixed finite whole transform machine, independent of original dimensions. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.roots (.inl (SemiprimeD1BinaryPublicAcquisition.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))))
  (.aux .output) .start program
/-- Every physical stack and return alphabet is fixed finite before N. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- No native number/list/AST/getter occurs in finite machine control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- Complete disjoint role inventory, including every actual component cache. -/
theorem stack_card : Fintype.card Stack=204 := by decide
end RiemannGaussian.SemiprimeD1StackPublicTransform
