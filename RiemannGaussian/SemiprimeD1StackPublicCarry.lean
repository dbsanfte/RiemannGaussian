/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTargetBounds
import RiemannGaussian.SemiprimeD1StackWordVectorFinite
import RiemannGaussian.SemiprimeD1StackCarryEquationBounds
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeMacroEntryBitCheck
/-! # Whole original-input INTEGER carry checker
Original binary N, RAW local assignment and a physical query index are the only
inputs. Target, modulus, radix, operand words, guards, carry record and verdict
are acquired by actual included finite procedures, never supplied as advice.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarry
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace T
export SemiprimeD1StackPublicTarget (Stack Label program initial input)
end T
namespace P
export SemiprimeD1BinaryPublicAcquisition (digitStack fermatStack)
end P
namespace W
export SemiprimeD1StackWordVector (Stack Label program initial original countCache output)
end W
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial)
end F
namespace L
export SemiprimeD1StackWordLess (Stack Label program initial)
end L
namespace Q
export SemiprimeD1StackCarryEquation (Stack Label program initial)
end Q
/-- Fifteen finite physical roles, with disjoint work reused only between phases. -/
inductive Aux where
  | raw | reader | three | todo | history | vector | blockCount | blockOut | scratch
  | coefficient | previous | next | valid | bound | output
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList
  [.raw,.reader,.three,.todo,.history,.vector,.blockCount,.blockOut,.scratch,
    .coefficient,.previous,.next,.valid,.bound,.output] (by intro k;cases k <;> simp)
/-- ALL51 Boolean data roles, before all original input sizes. -/
abbrev Stack := T.Stack⊕Aux
/-- The actually acquired modulus WORD. -/
def modulusRole : T.Stack := .inl (P.fermatStack (.inr false))
/-- Actual acquired radix-width template, never numeric exponent advice. -/
def radixRole : T.Stack := .inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .radix))
/-- Actual acquired public target-word cache. -/
def targetRole : T.Stack := .inr .output
/-- Original input N occupies its actual public-preprocessing input stack. -/
def inputRole : Stack := .inl (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input)))
/-- Actual accepted Boolean output, not an expected verdict operand. -/
def output : Stack := .inr .output
/-- The three actual original raw-word cache roles, in graph order. -/
def wordRole (k : Fin 3) : Stack := .inr (if k=0 then .coefficient else if k=1 then .previous else .next)
/-- Direct physical assignment grouping with SAME acquired modulus width. -/
def vectorStack : W.Stack→Stack
  | .inl k=>if k=0 then .inr .reader else if k=1 then .inl modulusRole else
      if k=2 then .inr .blockCount else if k=3 then .inr .scratch else .inr .blockOut
  | .inr k=>if k=0 then .inr .three else if k=1 then .inr .todo else if k=2 then .inr .history
      else if k=3 then .inr .vector else .inr .raw
/-- Actual field parsing of the physically acquired vector. -/
def fieldStack (k : Fin 3) : F.Stack→Stack
  | .inl .input=>.inr .vector | .inl .scratch=>.inr .scratch
  | .inl .output=>wordRole k | .inr _=>.inr .valid
/-- Only fixed preserving-copy purposes occur in finite control. -/
inductive CopyKind where | bound | operand (k : Fin 3) | guardBound (k : Fin 3)
  deriving DecidableEq,Fintype
/-- Actual preserving copies for bound construction and every destructive guard. -/
def copyStack (kind : CopyKind) (k : Fin 3) : Stack :=
  if k=0 then match kind with
    | .bound=>.inl modulusRole | .operand j=>wordRole j
    | .guardBound j=>if j=0 then .inl modulusRole else .inr .bound
  else if k=1 then match kind with
    | .bound=>.inr .bound | .operand _=>.inr .blockOut | .guardBound _=>.inr .blockCount
  else .inr .scratch
/-- Complete numeric guard uses actual copied operands; work is physically drained. -/
def lessStack : L.Stack→Stack
  | .inl .left=>.inr .blockOut | .inl .right=>.inr .blockCount | .inl .scratch=>.inr .scratch
  | .inl .output=>.inr .history | .inr _=>.inr .valid
/-- Carry record fields are original coefficient, previous, ACTUAL target, next. -/
def frameWord (field : Fin 4) : Stack :=
  if field=0 then wordRole 0 else if field=1 then wordRole 1 else if field=2 then .inl targetRole else wordRole 2
/-- Real word-to-record framing, preserving every actual source cache. -/
def frameStack (field : Fin 4) (k : Fin 3) : Stack :=
  if k=0 then frameWord field else if k=1 then .inr .vector else .inr .scratch
/-- Whole actual INTEGER carry-equation procedure; only the actual radix cache is shared. -/
def carryStack : Q.Stack→Stack
  | .input=>.inr .vector | .cached=>.inl radixRole | .count=>.inr .todo | .scratch=>.inr .scratch
  | .valid=>.inr .valid | .coefficient=>wordRole 0 | .previous=>wordRole 1 | .target=>.inr .blockOut
  | .next=>wordRole 2 | .left=>.inr .history | .right=>.inr .blockCount | .output=>output
/-- Fixed literal pipeline and all real procedure locations. -/
inductive Label where
  | start | seed (k : Fin 3) | vectorCall | tag (k : Fin 3) | fieldCall (k : Fin 3) | parsed (k : Fin 3)
  | vectorEnd | copyBound | boundPop | boundPush | guardOperand (k : Fin 3) | guardBound (k : Fin 3)
  | compare (k : Fin 3) | tested (k : Fin 3) | frame (field : Fin 4) | clear (pass : Bool) (k : Fin 3)
  | equation | reject | done | bad
  | target (pc : T.Label) | words (pc : W.Label) | fields (k : Fin 3) (pc : F.Label)
  | copy (kind : CopyKind) (pc : Fin 9) | less (pc : L.Label) | framer (field : Fin 4) (pc : Fin 11)
  | carry (pc : Q.Label)
  deriving Fintype
/-- After a parsed word, move to its literal successor tag or vector terminator. -/
def afterField (k : Fin 3) : Label := if k=0 then .tag 1 else if k=1 then .tag 2 else .vectorEnd
/-- Successful guards proceed only via actual verdict pops. -/
def afterGuard (k : Fin 3) : Label := if k=0 then .guardOperand 1 else if k=1 then .guardOperand 2 else .frame 3
/-- Reverse field construction gives the exact coefficient/previous/target/next record. -/
def afterFrame (field : Fin 4) : Label :=
  if field=3 then .frame 2 else if field=2 then .frame 1 else if field=1 then .frame 0 else .clear true 0
/-- Both computed branches really clear every retained operand cache. -/
def afterClear (pass : Bool) (k : Fin 3) : Label :=
  if k=0 then .clear pass 1 else if k=1 then .clear pass 2 else if pass then .equation else .done
/-- ONE complete fixed finite program. Every target/word/guard/record/equation
step is a real included call or literal push/pop, not an evaluator opcode. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.target .start) (.seed 0)
  | .seed k=>.base (.push (.inr .three) true (if k=0 then .seed 1 else if k=1 then .seed 2 else .vectorCall))
  | .vectorCall=>.call (.words (.control .start)) (.tag 0)
  | .tag k=>.base (.pop (.inr .vector) .bad .bad (.fieldCall k))
  | .fieldCall k=>.call (.fields k (F.active .tagPop (none,false))) (.parsed k)
  | .parsed k=>.base (.pop (.inr .valid) .bad .bad (afterField k))
  | .vectorEnd=>.base (.pop (.inr .vector) .bad .copyBound .bad)
  | .copyBound=>.call (.copy .bound 0) .boundPop
  | .boundPop=>.base (.pop (.inr .bound) .boundPush .boundPush .boundPush)
  | .boundPush=>.base (.push (.inr .bound) false (.guardOperand 0))
  | .guardOperand k=>.call (.copy (.operand k) 0) (.guardBound k)
  | .guardBound k=>.call (.copy (.guardBound k) 0) (.compare k)
  | .compare k=>.call (.less .start) (.tested k)
  | .tested k=>.base (.pop (.inr .valid) .bad .reject (afterGuard k))
  | .frame field=>.call (.framer field 0) (afterFrame field)
  | .clear pass k=>.base (.pop (wordRole k) (afterClear pass k) (.clear pass k) (.clear pass k))
  | .equation=>.call (.carry (.read 0)) .done
  | .reject=>.base (.push output false (.clear false 0))
  | .done | .bad=>.base .halt
  | .target pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.target (T.program pc)
  | .words pc=>SemiprimeD1StackValidationLink.instruction vectorStack Label.words (W.program pc)
  | .fields k pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack k) (Label.fields k) (F.code pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .less pc=>SemiprimeD1StackValidationLink.instruction lessStack Label.less (L.program pc)
  | .framer field pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack field) (Label.framer field) (SemiprimeD1StackFrame.code pc)
  | .carry pc=>SemiprimeD1StackValidationLink.instruction carryStack Label.carry (Q.program pc)
/-- All auxiliary cells, with phase work explicit. -/
def aux (raw reader three todo history vector blockCount blockOut scratch coefficient previous next valid bound output : List Bool) : Aux→List Bool
  | .raw=>raw | .reader=>reader | .three=>three | .todo=>todo | .history=>history | .vector=>vector
  | .blockCount=>blockCount | .blockOut=>blockOut | .scratch=>scratch | .coefficient=>coefficient
  | .previous=>previous | .next=>next | .valid=>valid | .bound=>bound | .output=>output
/-- Literal complete store; the context is finite physical target/public stacks. -/
def store (context : T.Stack→List Bool)
    (raw reader three todo history vector blockCount blockOut scratch coefficient previous next valid bound output : List Bool) : Stack→List Bool :=
  Sum.elim context (aux raw reader three todo history vector blockCount blockOut scratch coefficient previous next valid bound output)
/-- Original N, raw local assignment and physical query index ONLY. -/
def initial (bits raw index : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store (T.input bits index) raw [] [] [] [] [] [] [] [] [] [] [] [] [] [],[]⟩
/-- All ten actual word-vector roles remain distinct under direct width sharing. -/
theorem vector_injective : Function.Injective vectorStack := by decide
/-- Actual parser destinations/work are disjoint. -/
theorem field_injective (k : Fin 3) : Function.Injective (fieldStack k) := by
  fin_cases k <;> intro i j h <;> rcases i with i|i <;> rcases j with j|j <;> cases i <;> cases j <;> simp_all [fieldStack,wordRole]
/-- Every actual preserving copy has separate source/destination/scratch. -/
theorem copy_injective (kind : CopyKind) : Function.Injective (copyStack kind) := by cases kind with
  | bound=>decide
  | operand k=>fin_cases k <;> decide
  | guardBound k=>fin_cases k <;> decide
/-- Real comparator roles are all distinct. -/
theorem less_injective : Function.Injective lessStack := by
  intro i j h;rcases i with i|i <;> rcases j with j|j <;> cases i <;> cases j <;> simp_all [lessStack]
/-- Real record framing cannot alias the source word with output/scratch. -/
theorem frame_injective (field : Fin 4) : Function.Injective (frameStack field) := by fin_cases field <;> decide
/-- The twelve actual integer-equation roles have no physical alias. -/
theorem carry_injective : Function.Injective carryStack := by decide
/-- One fixed finite whole public carry machine. Index acquisition remains caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine inputRole output .start program
/-- ALL data and actual return alphabets are finite before original N. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- No N, target, word, exponent, record or verdict occurs as unbounded control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- Every one of the physical data roles is counted. -/
theorem stack_card : Fintype.card Stack=51 := by decide
end RiemannGaussian.SemiprimeD1StackPublicCarry
