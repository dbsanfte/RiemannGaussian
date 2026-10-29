/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadCall
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationCall
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFinalCleanup
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsIncluded
/-! # Fixed60-role complete local-weight source from six actual words
Only actual inverse/power arrays, actual scalar signed numerator/denominator,
paid unary q and paid W enter. Reused finite read/operation helpers physically
parse and multiply/add every field; the inverse WHOLE source is never replayed.
The old prefixReverse role is the IMMUTABLE power tape in THIS program, and is
therefore excluded from THIS source's dedicated53-role final cleanup.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeights
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace I
export SemiprimeD1StackNormalizedInverse (Stack Label program Reg Aux ReadSite)
end I
/-- The original actual Ezero scalar remains retained in two additional tapes. -/
inductive Scalar where | signed | den deriving DecidableEq,Repr
/-- Literal two-word scalar inventory before every input. -/
instance :Fintype Scalar:=Fintype.ofList [.signed,.den] (by intro k;cases k <;> simp)
/-- ALL58 reused words, including unused shadows, plus actual scalar2. -/
abbrev Stack:=I.Stack⊕Scalar
/-- Injective complete actual helper-bank inclusion. -/
def helper:I.Stack→Stack:=Sum.inl
/-- Both actual retained scalar inputs. -/
def scalar:Scalar→Stack:=Sum.inr
/-- Actual helper controller address; powers are retained at prefixReverse. -/
def aux (slot:I.Aux):Stack:=helper (SemiprimeD1StackNormalizedInverse.aux slot)
/-- Actual two-field coefficient cache address. -/
def reg (slot:I.Reg) (den:Bool):Stack:=helper (SemiprimeD1StackNormalizedInverse.reg slot den)
/-- Actual retained paid W, with no width shadow. -/
def template:Stack:=helper SemiprimeD1StackNormalizedInverse.template
/-- Literal actual53-role inventory: all helper work EXCEPT immutable powers. -/
def workRole (i:Fin 53):Stack:=helper (SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩)
/-- Paid preserving copies initialize actual counters or final scalar/total operands. -/
inductive Copy where | count | terms | subtract | aIndex | bIndex | scalar (den:Bool) | total (den:Bool)
  deriving DecidableEq,Repr,Fintype
/-- Sources are physically acquired inputs, current j/count or the actual sum. -/
def copySource:Copy→Stack
  | .count|.terms|.bIndex=>aux .originalQ | .subtract=>aux .remaining | .aIndex=>aux .terms
  | .scalar false=>scalar .signed | .scalar true=>scalar .den | .total den=>reg .acc den
/-- Every copy destination is a distinct physically emptied counter/cache word. -/
def copyTarget:Copy→Stack
  | .count=>aux .remaining | .terms=>aux .terms | .subtract=>aux .readTodo
  | .aIndex=>aux .aIndex | .bIndex=>aux .bIndex | .scalar den=>reg .left den | .total den=>reg .right den
/-- Real restoring-copy operands retain the original source and restore helper scratch. -/
def copyStack (site:Copy) (i:Fin 3):Stack:=if i=0 then copySource site else if i=1 then copyTarget site else aux .copyScratch
/-- Final scalar product is framed directly BEFORE all coefficient fields are drained. -/
def frameStack (den:Bool) (i:Fin 3):Stack:=if i=0 then reg .product den else if i=1 then aux .output else aux .fieldFrameScratch
/-- All literal outer/pair/cleanup stages are finite before the actual q/W. -/
inductive Control where
  | start | copyCount | outer | seedZero (den:Bool) | copyTerms | copySubtract | subtract | removeTerm
  | copyA | predecessorA | copyB | predecessorB | terms
  | readInverse | checkedInverse | readPower | checkedPower | product | checkedProduct | sum | checkedSum
  | clearPair (i:Fin 6) | decrementA | decrementB | clearIndices (second:Bool)
  | scalar (den:Bool) | total (den:Bool) | finalProduct | checkedFinalProduct
  | frame (den:Bool) | tag | clearCoefficient (i:Fin 8) | clean (reject:Bool) (i:Fin 53)
  | abortOutput | abortTerminal | done
  deriving DecidableEq,Repr,Fintype
/-- Reused finite helper labels and actual caller labels, never numerical indices. -/
inductive Label where
  | local (pc:Control) | helper (pc:I.Label) | copy (site:Copy) (pc:Fin 9) | frame (den:Bool) (pc:Fin 11)
  deriving Fintype
/-- Literal rejection cleanup entry; every retained input is preserved. -/
def abort:Label:=.local (.clean true 0)
/-- ONE fixed actual source; no coefficient/array/Fits/result/clock evaluator operand. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.base (.push (aux .output) false (.local .copyCount))
  | .local .copyCount=>.call (.copy .count 0) (.local .outer)
  | .local .outer=>.base (.pop (aux .remaining) (.local (.clean false 0)) abort (.local (.seedZero false)))
  | .local (.seedZero den)=>.base (.push (reg .acc den) den (.local (if den then .copyTerms else .seedZero true)))
  | .local .copyTerms=>.call (.copy .terms 0) (.local .copySubtract)
  | .local .copySubtract=>.call (.copy .subtract 0) (.local .subtract)
  | .local .subtract=>.base (.pop (aux .readTodo) (.local .copyA) abort (.local .removeTerm))
  | .local .removeTerm=>.base (.pop (aux .terms) abort abort (.local .subtract))
  | .local .copyA=>.call (.copy .aIndex 0) (.local .predecessorA)
  | .local .predecessorA=>.base (.pop (aux .aIndex) abort abort (.local .copyB))
  | .local .copyB=>.call (.copy .bIndex 0) (.local .predecessorB)
  | .local .predecessorB=>.base (.pop (aux .bIndex) abort abort (.local .terms))
  | .local .terms=>.base (.pop (aux .terms) (.local (.clearIndices false)) abort (.local .readInverse))
  | .local .readInverse=>.call (.helper (.read .denominator .copyArray)) (.local .checkedInverse)
  | .local .checkedInverse=>.base (.pop (aux .valid) abort abort (.local .readPower))
  | .local .readPower=>.call (.helper (.read .prefix .copyArray)) (.local .checkedPower)
  | .local .checkedPower=>.base (.pop (aux .valid) abort abort (.local .product))
  | .local .product=>.call (.helper (.operation .product (.copyInput false false))) (.local .checkedProduct)
  | .local .checkedProduct=>.base (.pop (aux .valid) abort abort (.local .sum))
  | .local .sum=>.call (.helper (.operation .sum (.copyInput false false))) (.local .checkedSum)
  | .local .checkedSum=>.base (.pop (aux .valid) abort abort (.local (.clearPair 0)))
  | .local (.clearPair i)=>.base (.pop (helper (SemiprimeD1StackNormalizedInverse.regRole ⟨i.val,by omega⟩))
      (if h:i.val<5 then .local (.clearPair ⟨i.val+1,by omega⟩) else .local .decrementA)
      (.local (.clearPair i)) (.local (.clearPair i)))
  | .local .decrementA=>.base (.pop (aux .aIndex) (.local .decrementB) abort (.local .decrementB))
  | .local .decrementB=>.base (.pop (aux .bIndex) (.local .terms) abort (.local .terms))
  | .local (.clearIndices second)=>.base (.pop (aux (if second then .bIndex else .aIndex))
      (.local (if second then .scalar false else .clearIndices true))
      (.local (.clearIndices second)) (.local (.clearIndices second)))
  | .local (.scalar den)=>.call (.copy (.scalar den) 0) (.local (if den then .total false else .scalar true))
  | .local (.total den)=>.call (.copy (.total den) 0) (.local (if den then .finalProduct else .total true))
  | .local .finalProduct=>.call (.helper (.operation .product (.copyInput false false))) (.local .checkedFinalProduct)
  | .local .checkedFinalProduct=>.base (.pop (aux .valid) abort abort (.local (.frame true)))
  | .local (.frame den)=>.call (.frame den 0) (.local (if den then .frame false else .tag))
  | .local .tag=>.base (.push (aux .output) true (.local (.clearCoefficient 0)))
  | .local (.clearCoefficient i)=>.base (.pop (helper (SemiprimeD1StackNormalizedInverse.regRole i))
      (if h:i.val<7 then .local (.clearCoefficient ⟨i.val+1,by omega⟩) else .local .outer)
      (.local (.clearCoefficient i)) (.local (.clearCoefficient i)))
  | .local (.clean reject i)=>.base (.pop (workRole i)
      (if h:i.val<52 then .local (.clean reject ⟨i.val+1,by omega⟩) else .local (if reject then .abortOutput else .done))
      (.local (.clean reject i)) (.local (.clean reject i)))
  | .local .abortOutput=>.base (.pop (aux .output) (.local .abortTerminal) (.local .abortOutput) (.local .abortOutput))
  | .local .abortTerminal=>.base (.push (aux .output) false (.local .done))
  | .local .done=>.base .halt
  | .helper pc=>SemiprimeD1StackValidationLink.instruction helper Label.helper (I.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .frame den pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack den) (Label.frame den) (SemiprimeD1StackFrame.code pc)
/-- Six actual original words ONLY; every other54 tape, including all helper shadows, is EMPTY. -/
def input (inverse powers signed den q width:List Bool):Stack→List Bool:=
  Sum.elim (SemiprimeD1StackNormalizedInverse.bank (fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then width else [])
    (fun _=>[]) (fun k=>match k with | .denominator=>inverse | .prefixReverse=>powers | .originalQ=>q | _=>[]))
    (fun k=>match k with | .signed=>signed | .den=>den)
/-- Honest whole prepared entry, before any row/count/current/array acquisition. -/
def initial (inverse powers signed den q width:List Bool):C.State Stack Label:=
  ⟨some (.local .start),none,none,input inverse powers signed den q width,[]⟩
/-- One fixed finite60-role source with no numerical/evaluator/clock control operands. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .denominator) (aux .output) (.local .start) program
/-- Every helper word, private unused shadow, scalar tape and real data role is counted. -/
theorem stack_card:Fintype.card Stack=60:=by simp only [Stack,Fintype.card_sum];decide
/-- Every actual preserving copy has three distinct operands. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by
  cases site <;> first | decide | (rename_i den;cases den <;> decide)
/-- Both preserving Frames have three distinct physical operands. -/
theorem frame_injective (den:Bool):Function.Injective (frameStack den):=by cases den <;> decide
/-- All transient states are finite before the actual six inputs. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All data and genuine saved-return alphabets are finite. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryWeights
