/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootArithmetic
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataOriginal
import RiemannGaussian.SemiprimeD1StackMultiplierExecution
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # A fixed33-word finite source for binary integer square root
The sole original operand is binary D. A real metadata call obtains a binary
power of two. Actual add, multiply and compare calls test descending bits.
All arithmetic/private words are physically swept after every iteration.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRoot
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace M
export SemiprimeD1StackPackedRootMetadata (Stack Label program input boot aux)
end M
namespace A
export SemiprimeD1StackAdder (Stack Label code store)
end A
namespace X
export SemiprimeD1StackMultiplier (Stack Label code input factor payload)
end X
namespace W
export SemiprimeD1StackWordLess (Stack Label program output store)
end W
/-- The only two additional physical data words. -/
inductive Aux where | root | output deriving DecidableEq,Repr
/-- Literal two-word enumeration, independent of the original operand. -/
instance auxFintype : Fintype Aux := Fintype.ofList [.root,.output] (by intro k;cases k <;> simp)
/-- All33 allocated words, including every retained metadata/private word. -/
abbrev Stack := M.Stack⊕(A.Stack⊕(X.Stack⊕(W.Stack⊕Aux)))
/-- Whole retained metadata-source inclusion. -/
def metadata (k : M.Stack) : Stack := .inl k
/-- Four actual candidate-adder words. -/
def adder (k : A.Stack) : Stack := .inr (.inl k)
/-- Nine actual square-multiplier words. -/
def multiply (k : X.Stack) : Stack := .inr (.inr (.inl k))
/-- Five actual numeric-comparison words. -/
def compare (k : W.Stack) : Stack := .inr (.inr (.inr (.inl k)))
/-- Additional candidate-root and compact-output words. -/
def aux (k : Aux) : Stack := .inr (.inr (.inr (.inr k)))
/-- Original input always remains binary and is preserved by all trial calls. -/
def originalInput : Stack := metadata (M.boot .input)
/-- Physically acquired binary2^L, shifted right by one actual pop per trial. -/
def power : Stack := metadata (M.aux .base)
/-- Borrowed restoring scratch is proven empty after every actual copy. -/
def copyScratch : Stack := metadata (M.aux .copyScratch)
/-- Seven fixed preserving-copy sites, independent of all operands. -/
inductive Copy where
  | root | power | trialInput | trialFactor | discriminant | square | accepted
  deriving DecidableEq,Repr
/-- Literal seven-site copy enumeration. -/
instance copyFintype : Fintype Copy := Fintype.ofList [.root,.power,.trialInput,.trialFactor,.discriminant,.square,.accepted]
  (by intro k;cases k <;> simp)
/-- Literal source/destination/restoring-scratch mapping for all actual copies. -/
def copyStack (site : Copy) (k : Fin 3) : Stack :=
  if k=0 then match site with
    | .root => aux .root | .power => power
    | .trialInput | .trialFactor | .accepted => adder .output
    | .discriminant => originalInput | .square => multiply (.inl .right)
  else if k=1 then match site with
    | .root => adder .left | .power => adder .right
    | .trialInput => multiply X.input | .trialFactor => multiply X.factor
    | .discriminant => compare (.inl .left) | .square => compare (.inl .right)
    | .accepted => aux .root
  else copyScratch
/-- All18 trial-work roles in one fixed literal physical sweep order. -/
def clearStack (k : Fin 18) : Stack := match k.val with
  | 0 => adder .left | 1 => adder .right | 2 => adder .scratch | 3 => adder .output
  | 4 => multiply (.inl .left) | 5 => multiply (.inl .right)
  | 6 => multiply (.inl .scratch) | 7 => multiply (.inl .output)
  | 8 => multiply X.factor | 9 => multiply SemiprimeD1StackMultiplier.copied
  | 10 => multiply SemiprimeD1StackMultiplier.copyScratch
  | 11 => multiply X.input | 12 => multiply SemiprimeD1StackMultiplier.digits
  | 13 => compare (.inl .left) | 14 => compare (.inl .right)
  | 15 => compare (.inl .scratch) | 16 => compare (.inl .output)
  | _ => compare W.output
/-- Consuming final reversal borrows the now-empty descending-power word. -/
def reverseStack (k : Fin 2) : Stack := if k=0 then aux .root else power
/-- Actual high-zero trimming uses four distinct and actually empty work roles. -/
def trimStack : A.Stack→Stack
  | .left => adder .left | .right => adder .right
  | .scratch => power | .output => aux .output
/-- Finite phases and sweep positions; no numeric operand is stored in control. -/
inductive Control where
  | start | rootCopy | powerCopy | add | trialInputCopy | trialFactorCopy | square
  | discriminantCopy | squareCopy | compare | decide | clearRoot | acceptCopy
  | clear (k : Fin 18) | shift | reverse | trim | done
  deriving DecidableEq,Repr
/-- All fixed stages and all eighteen actual sweep positions. -/
instance controlFintype : Fintype Control := Fintype.ofList
  ([.start,.rootCopy,.powerCopy,.add,.trialInputCopy,.trialFactorCopy,.square,.discriminantCopy,
    .squareCopy,.compare,.decide,.clearRoot,.acceptCopy,.shift,.reverse,.trim,.done]++List.ofFn Control.clear)
  (by intro k;cases k <;> simp;rename_i k;fin_cases k <;> simp)
/-- The complete fixed control and included source label bank. -/
abbrev Label := Control⊕(M.Label⊕(A.Label⊕(X.Label⊕(W.Label⊕((Copy×Fin 9)⊕(Fin 4⊕SemiprimeD1StackReduce.Label))))))
/-- Fixed outer program stage. -/
def ctl : Control→Label := Sum.inl
/-- Real metadata-source labels. -/
def metadataLabel (pc : M.Label) : Label := .inr (.inl pc)
/-- Real candidate-adder labels. -/
def adderLabel (pc : A.Label) : Label := .inr (.inr (.inl pc))
/-- Real square-multiplier labels. -/
def multiplyLabel (pc : X.Label) : Label := .inr (.inr (.inr (.inl pc)))
/-- Real numeric-less-than labels. -/
def compareLabel (pc : W.Label) : Label := .inr (.inr (.inr (.inr (.inl pc))))
/-- Real restoring-copy labels. -/
def copyLabel (site : Copy) (pc : Fin 9) : Label := .inr (.inr (.inr (.inr (.inr (.inl (site,pc))))))
/-- Real final-reversal labels. -/
def reverseLabel (pc : Fin 4) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inl pc))))))
/-- Real high-zero-trim labels. -/
def trimLabel (pc : SemiprimeD1StackReduce.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inr pc))))))
/-- The next one of eighteen fixed clear sites, then the actual power shift. -/
def clearNext (k : Fin 18) : Label :=
  if h:k.val+1 < 18 then ctl (.clear ⟨k.val+1,h⟩) else ctl .shift
/-- One literal source: acquire, test descending binary powers, trim, halt. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (metadataLabel (.local .start)) (ctl .rootCopy)
  | .inl .rootCopy => .call (copyLabel .root 0) (ctl .powerCopy)
  | .inl .powerCopy => .call (copyLabel .power 0) (ctl .add)
  | .inl .add => .call (adderLabel (.start false)) (ctl .trialInputCopy)
  | .inl .trialInputCopy => .call (copyLabel .trialInput 0) (ctl .trialFactorCopy)
  | .inl .trialFactorCopy => .call (copyLabel .trialFactor 0) (ctl .square)
  | .inl .square => .call (multiplyLabel (.control .start)) (ctl .discriminantCopy)
  | .inl .discriminantCopy => .call (copyLabel .discriminant 0) (ctl .squareCopy)
  | .inl .squareCopy => .call (copyLabel .square 0) (ctl .compare)
  | .inl .compare => .call (compareLabel .start) (ctl .decide)
  | .inl .decide => .base (.pop (compare W.output) (ctl (.clear 0)) (ctl .clearRoot) (ctl (.clear 0)))
  | .inl .clearRoot => .base (.pop (aux .root) (ctl .acceptCopy) (ctl .clearRoot) (ctl .clearRoot))
  | .inl .acceptCopy => .call (copyLabel .accepted 0) (ctl (.clear 0))
  | .inl (.clear k) => .base (.pop (clearStack k) (clearNext k) (ctl (.clear k)) (ctl (.clear k)))
  | .inl .shift => .base (.pop power (ctl .reverse) (ctl .rootCopy) (ctl .reverse))
  | .inl .reverse => .call (reverseLabel 0) (ctl .trim)
  | .inl .trim => .call (trimLabel .trim) (ctl .done)
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction metadata metadataLabel (M.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackMultiplierLink.instruction adder adderLabel (A.code pc)
  | .inr (.inr (.inr (.inl pc))) => SemiprimeD1StackValidationLink.instruction multiply multiplyLabel (X.code pc)
  | .inr (.inr (.inr (.inr (.inl pc)))) => SemiprimeD1StackValidationLink.instruction compare compareLabel (W.program pc)
  | .inr (.inr (.inr (.inr (.inr (.inl (site,pc)))))) =>
    SemiprimeD1StackMultiplierLink.instruction (copyStack site) (copyLabel site) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl pc)))))) =>
    SemiprimeD1StackMultiplierLink.instruction reverseStack reverseLabel (SemiprimeD1StackReverseWord.code pc)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr pc)))))) =>
    SemiprimeD1StackMultiplierLink.instruction trimStack trimLabel (SemiprimeD1StackReduce.code pc)
/-- Exact whole-bank view, including every retained and work word. -/
def bank (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (w : W.Stack→List Bool) (u : Aux→List Bool) : Stack→List Bool :=
  Sum.elim m (Sum.elim a (Sum.elim x (Sum.elim w u)))
/-- Only original binary D is initially supplied. -/
def input (bits : List Bool) : Stack→List Bool := bank (M.input bits) (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => [])
/-- Actual original-input entry, before the real metadata source. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Genuine finite original-binary square-root machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .output) (ctl .start) program
/-- Every retained and private allocated word is included in the count. -/
theorem stack_card : Fintype.card Stack=33 := by decide
/-- Complete metadata-bank inclusion is injective. -/
theorem metadata_injective : Function.Injective metadata := Sum.inl_injective
/-- Every real candidate-adder operand is distinct. -/
theorem adder_injective : Function.Injective adder := by intro a b h;exact Sum.inl_injective (Sum.inr_injective h)
/-- Every real square-multiplier word is distinct. -/
theorem multiply_injective : Function.Injective multiply := by intro a b h;exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
/-- Every real numeric-comparison word is distinct. -/
theorem compare_injective : Function.Injective compare := by intro a b h;exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
/-- All seven real copies have distinct source, destination and scratch. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site) := by cases site <;> decide
/-- The physical final reversal never aliases its two operands. -/
theorem reverse_injective : Function.Injective reverseStack := by decide
/-- The four actual final-trim operands are distinct. -/
theorem trim_injective : Function.Injective trimStack := by decide
/-- The eighteen swept private roles are pairwise distinct. -/
theorem clear_injective : Function.Injective clearStack := by decide
/-- All data and saved-return alphabets are finite before every binary D. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Internal state carries only finite flags and fixed labels. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackBinarySquareRoot
