/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputWidthOriginal
import RiemannGaussian.SemiprimeD1StackWordBlockBounds
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeD1StackWordEqualBounds

/-! # Literal original public input-word/flag checker
The actual N+physical-index bound producer runs once. A real raw-word copy and
block acquisition precede an actual low-bound-bit activity test. Active inputs
execute the strict width guard and the original first/nonfirst flag rule;
inactive inputs execute real numeric zero comparison. Original raw and public
cache bytes survive, all disposable bound/word work is physically drained.

This module defines the whole literal runtime. Its complete source trace,
original-family semantic transport and whole-clock proofs are successor work;
the frozen bound supplier's clock alone is NOT this caller's clock.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPublicInput
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace H
export SemiprimeD1StackPublicInputWidth (Stack Label program initial original output)
end H
namespace B
export SemiprimeD1StackWordBlock (Stack Label program)
end B
namespace L
export SemiprimeD1StackWordLess (Stack Label program output)
end L
namespace E
export SemiprimeD1StackAdder (Stack)
export SemiprimeD1StackWordEqual (Label code)
end E
/-- All52 Boolean roles, fixed before all original N/index/raw assignments. -/
abbrev Stack := H.Stack⊕(B.Stack⊕(L.Stack⊕(E.Stack⊕Unit)))
/-- The actually produced bound, used directly as the strict comparator's right. -/
def bound : Stack := .inl H.output
/-- Actual caller-supplied descriptor index retained by the bound producer. -/
def index : Stack := .inl (.inr .indexCache)
/-- Actual binary modulus template, acquired by the SAME bound producer. -/
def modulusKey : H.Stack := .inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr false))
/-- The original raw assignment is retained by an actual physical copy. -/
def assignment : Stack := .inr (.inr (.inr (.inr ())))
/-- Word extraction directly shares the actual acquired binary width template. -/
def blockStack (k : B.Stack) : Stack := if k=1 then .inl modulusKey else .inr (.inl k)
/-- Strict comparison shares the produced bound, never a supplied bound value. -/
def lessStack : L.Stack→Stack
  | .inl .right=>bound
  | k=>.inr (.inr (.inl k))
/-- Actual computed Boolean of every real numeric comparison. -/
def comparison : Stack := lessStack L.output
/-- Private right/result roles; comparator left/scratch shadows remain counted. -/
def equalPrivate (k : E.Stack) : Stack := .inr (.inr (.inr (.inl k)))
/-- Zero comparisons consume the physically acquired word directly. -/
def equalStack : E.Stack→Stack
  | .left=>blockStack 4
  | .scratch=>blockStack 3
  | .output=>comparison
  | k=>equalPrivate k
/-- Actual final input-table verdict has a separate physical singleton cell. -/
def output : Stack := equalPrivate .output
/-- Two real preserving-copy sites: raw assignment and acquired word for less. -/
def copyStack (kind : Fin 2) (k : Fin 3) : Stack :=
  if k=0 then (if kind=0 then assignment else blockStack 4)
  else if k=1 then (if kind=0 then blockStack 0 else lessStack (.inl .left)) else blockStack 3
/-- Fixed finite program labels; only individual Boolean bits occur in control. -/
inductive Label where
  | start | copyRaw | block | activity | guardCopy | guard | readGuard | indexCase
  | firstCopy | twoHigh | twoLow | firstCheck | nonzero | zero | readTest | flag (test : Bool)
  | readZero | write (bit : Bool) | clearWord | clearBound | done | bad
  | header (pc : H.Label) | copy (kind : Fin 2) (pc : Fin 9)
  | extract (pc : B.Label) | less (pc : L.Label) | equality (pc : E.Label)
  deriving Fintype
/-- ONE closed literal program; all arithmetic operands and verdicts are
acquired by actual procedures and actual Boolean branches on real tape cells. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.header .start) .copyRaw
  | .copyRaw=>.call (.copy 0 0) .block
  | .block=>.call (.extract RiemannGaussian.SemiprimeD1StackWordFit.Label.start) .activity
  | .activity=>.base (.peek bound .zero .guardCopy .zero)
  | .guardCopy=>.call (.copy 1 0) .guard
  | .guard=>.call (.less .start) .readGuard
  | .readGuard=>.base (.pop comparison .bad (.write false) .indexCase)
  | .indexCase=>.base (.peek index .firstCopy .nonzero .nonzero)
  | .firstCopy=>.call (.copy 1 0) .twoHigh
  | .twoHigh=>.base (.push bound true .twoLow)
  | .twoLow=>.base (.push bound false .firstCheck)
  | .firstCheck=>.call (.less .start) .readTest
  | .nonzero=>.call (.equality .loop) .readTest
  | .zero=>.call (.equality .loop) .readZero
  | .readTest=>.base (.pop comparison .bad (.flag false) (.flag true))
  | .flag test=>.base (.peek (blockStack 0) (.write ((!test)==false))
      (.write ((!test)==false)) (.write ((!test)==true)))
  | .readZero=>.base (.pop comparison .bad (.write false) (.write true))
  | .write bit=>.base (.push output bit .clearWord)
  | .clearWord=>.base (.pop (blockStack 4) .clearBound .clearWord .clearWord)
  | .clearBound=>.base (.pop bound .done .clearBound .clearBound)
  | .done | .bad=>.base .halt
  | .header pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.header (H.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .extract pc=>SemiprimeD1StackValidationLink.instruction blockStack Label.extract (B.program pc)
  | .less pc=>SemiprimeD1StackValidationLink.instruction lessStack Label.less (L.program pc)
  | .equality pc=>SemiprimeD1StackMultiplierLink.instruction equalStack Label.equality (E.code pc)
/-- Initial private cells contain only actual raw assignment bits. -/
def privateInput (raw : List Bool) : B.Stack⊕(L.Stack⊕(E.Stack⊕Unit))→List Bool
  | .inr (.inr (.inr _))=>raw
  | _=>[]
/-- Original binary N, physical index and actual raw assignment are the only
inputs. No width, guard, flag-rule answer, word or clock is initialized. -/
def initial (bits raw indexWord : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,Sum.elim (SemiprimeD1StackPublicInputWidth.input bits indexWord) (privateInput raw),[]⟩
/-- Each physical extractor role stays distinct despite direct template sharing. -/
theorem block_injective : Function.Injective blockStack := by decide
/-- Strict comparison roles stay distinct despite direct actual-bound sharing. -/
theorem less_injective : Function.Injective lessStack := by decide
/-- Every zero-comparison role remains physically distinct. -/
theorem equal_injective : Function.Injective equalStack := by decide
/-- Both actual preserving-copy inclusions are physically injective. -/
theorem copy_injective (kind : Fin 2) : Function.Injective (copyStack kind) := by fin_cases kind <;> decide
/-- Fixed genuine bit machine; the full original-input trace is a successor task. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl H.original) output .start program
/-- All real data and return-label alphabets are finite before the original input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite (.inl H.original) output Label.start program
/-- No original integer, list, width, guard predicate or clock enters control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite (.inl H.original) output Label.start program
/-- All data and private shadow roles are included in this complete inventory. -/
theorem stack_card : Fintype.card Stack=52 := by decide
end RiemannGaussian.SemiprimeD1StackPublicInput
