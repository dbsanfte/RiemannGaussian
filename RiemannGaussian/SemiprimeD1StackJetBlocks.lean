/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetContextBounds
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1StackAssignmentBody
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1JetBlockBits
/-! # Sequential actual fresh-axis coefficient blocks from an acquired context
The whole source REAL-acquires the old context from its unary-axis header and
binary precision. The same ready entry reuses the EXACTactual context cache.
Actual q markers and the actual retained rank word drive the outer/inner loops;
coefficient fields are copied in one forward scan, with literal empty-word
padding after source EOF. No rank, offset, block getter or coefficient answer
is a control operand. Old/new precision equality is never required: coefficients
are copied unchanged and extraction uses only the old axes/rank.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocks
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace X
export SemiprimeD1StackJetContext (Stack Label program initial axesCache precisionBits rankCache)
end X
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
/-- All actual retained vector/q inputs and per-field/per-block/logging words. -/
inductive Aux where
  | coefficients | blocks | todo | reader | rankTodo | word | fieldScratch | valid | copyScratch
  | frameBuffer | frameScratch | rowHistory | row | logScratch | history | output
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.coefficients,.blocks,.todo,.reader,.rankTodo,.word,.fieldScratch,.valid,.copyScratch,.frameBuffer,
    .frameScratch,.rowHistory,.row,.logScratch,.history,.output] (by intro k;cases k <;> simp)
/-- All15actual context words and16actual new source/loop/output words. -/
abbrev Stack :=X.Stack⊕Aux
/-- Actual old-context cache inclusion, retained literally during the entire block traversal. -/
def contextStack :X.Stack→Stack :=Sum.inl
/-- Actual local word inclusion. -/
def aux :Aux→Stack :=Sum.inr
/-- Three real preserving-copy operand choices. -/
inductive Copy where | blocks | vector | rank deriving DecidableEq
instance :Fintype Copy :=Fintype.ofList [.blocks,.vector,.rank] (by intro k;cases k <;> simp)
/-- q is copied once, coefficients once, and the ACTUALacquired rank markers once per emitted block. -/
def copyStack (part:Copy) (k:Fin 3) :Stack :=
  if k=0 then match part with | .blocks=>aux .blocks | .vector=>aux .coefficients | .rank=>contextStack X.rankCache
  else if k=1 then match part with | .blocks=>aux .todo | .vector=>aux .reader | .rank=>aux .rankTodo
  else aux .copyScratch
/-- Real coefficient field parsing; a zero coefficient is still a tagged empty field. -/
def fieldStack :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .fieldScratch | .inl .output=>aux .word | .inr _=>aux .valid
/-- Every coefficient's raw binary bytes are preserved by the real Frame routine. -/
def frameStack (k:Fin 3) :Stack :=if k=0 then aux .word else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Actual field-to-block, block-completion and final chronological-output reversals. -/
inductive Reverse where | field | row | output deriving DecidableEq
instance :Fintype Reverse :=Fintype.ofList [.field,.row,.output] (by intro k;cases k <;> simp)
/-- All actual source/destination reversal pairs are distinct. -/
def reverseStack (part:Reverse) (k:Fin 2) :Stack :=
  if k=0 then match part with | .field=>aux .frameBuffer | .row=>aux .rowHistory | .output=>aux .history
  else match part with | .field=>aux .rowHistory | .row=>aux .row | .output=>aux .output
/-- The real outer row logger preserves and frames the actual completed block vector. -/
def bodyStack :Body.Stack→Stack
  | .word=>aux .row | .scratch=>aux .logScratch | .history=>aux .history
/-- Fixed actual context/copy/q/rank/parser/frame/log/cleanup control. -/
inductive Control where
  | start | ready | copyVector | outer | copyRank | inner | peek | tag | field | valid | frame | fieldTag | fieldReverse
  | clearWord | rowSeed | rowReverse | logRow | clearRow | finishSeed | outputReverse | clearReader | done | abort
  deriving DecidableEq
instance :Fintype Control :=Fintype.ofList
  [.start,.ready,.copyVector,.outer,.copyRank,.inner,.peek,.tag,.field,.valid,.frame,.fieldTag,.fieldReverse,
    .clearWord,.rowSeed,.rowReverse,.logRow,.clearRow,.finishSeed,.outputReverse,.clearReader,.done,.abort]
  (by intro k;cases k <;> simp)
/-- All actual context/primitive return labels are fixed finite before every operand family. -/
inductive Label where
  | local (pc:Control) | context (pc:X.Label) | copy (part:Copy) (pc:Fin 9) | field (pc:Field.Label)
  | frame (pc:Fin 11) | reverse (part:Reverse) (pc:Fin 4) | body (pc:Body.Label)
  deriving Fintype
local notation "ctl" => Label.local
/-- One literal source: real context once, then an actual q-by-rank field scan with no numeric offset evaluator. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.context .start) (ctl .ready)
  | .local .ready=>.call (.copy .blocks 0) (ctl .copyVector)
  | .local .copyVector=>.call (.copy .vector 0) (ctl .outer)
  | .local .outer=>.base (.pop (aux .todo) (ctl .finishSeed) (ctl .abort) (ctl .copyRank))
  | .local .copyRank=>.call (.copy .rank 0) (ctl .inner)
  | .local .inner=>.base (.pop (aux .rankTodo) (ctl .rowSeed) (ctl .abort) (ctl .peek))
  | .local .peek=>.base (.peek (aux .reader) (ctl .frame) (ctl .frame) (ctl .tag))
  | .local .tag=>.base (.pop (aux .reader) (ctl .abort) (ctl .abort) (ctl .field))
  | .local .field=>.call (.field (Field.active .tagPop (none,false))) (ctl .valid)
  | .local .valid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .frame))
  | .local .frame=>.call (.frame 0) (ctl .fieldTag)
  | .local .fieldTag=>.base (.push (aux .frameBuffer) true (ctl .fieldReverse))
  | .local .fieldReverse=>.call (.reverse .field 0) (ctl .clearWord)
  | .local .clearWord=>.base (.pop (aux .word) (ctl .inner) (ctl .clearWord) (ctl .clearWord))
  | .local .rowSeed=>.base (.push (aux .row) false (ctl .rowReverse))
  | .local .rowReverse=>.call (.reverse .row 0) (ctl .logRow)
  | .local .logRow=>.call (.body Body.entry) (ctl .clearRow)
  | .local .clearRow=>.base (.pop (aux .row) (ctl .outer) (ctl .clearRow) (ctl .clearRow))
  | .local .finishSeed=>.base (.push (aux .output) false (ctl .outputReverse))
  | .local .outputReverse=>.call (.reverse .output 0) (ctl .clearReader)
  | .local .clearReader=>.base (.pop (aux .reader) (ctl .done) (ctl .clearReader) (ctl .clearReader))
  | .local .done|.local .abort=>.base .halt
  | .context pc=>SemiprimeD1StackValidationLink.instruction contextStack Label.context (X.program pc)
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (Field.code pc)
  | .frame pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)
  | .reverse part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reverse part) (SemiprimeD1StackReverseWord.code pc)
  | .body pc=>SemiprimeD1StackMultiplierLink.instruction bodyStack Label.body (Body.code pc)
/-- Only the actual q word and actual coefficient vector are installed in the new private input bank. -/
def privateInput (q coefficients:List Bool) :Aux→List Bool :=fun k=>if k=.blocks then q else if k=.coefficients then coefficients else []
/-- The actual whole source has four physical operands: old header, binary precision, q markers and coefficient vector. -/
def input (axes precision q coefficients:List Bool) :Stack→List Bool :=Sum.elim (X.initial axes precision).data (privateInput q coefficients)
/-- Whole actual context-acquiring front door, before any rank/width supplier result. -/
def initial (axes precision q coefficients:List Bool) :C.State Stack Label :=
  ⟨some (ctl .start),none,none,input axes precision q coefficients,[]⟩
/-- One fixed finite31-role prepared-input block source. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine (aux .coefficients) (aux .output) (ctl .start) program
/-- All actual preserving-copy operands are separate. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part) :=by cases part <;> decide
/-- The real parser input/output/scratch/valid addresses are distinct. -/
theorem field_injective :Function.Injective fieldStack :=by decide
/-- Real framing preserves a distinct coefficient source with separate output/restoration scratch. -/
theorem frame_injective :Function.Injective frameStack :=by decide
/-- All actual reversals have distinct operands. -/
theorem reverse_injective (part:Reverse) :Function.Injective (reverseStack part) :=by cases part <;> decide
/-- Real block logger input/scratch/history are distinct. -/
theorem body_injective :Function.Injective bodyStack :=by decide
/-- Every31actual context/private word and helper is included in allocation. -/
theorem stack_card :Fintype.card Stack=31 :=by rw [Fintype.card_sum];decide
/-- All runtime control is finite Boolean/read/return flags, never numeric offsets or evaluators. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All31data and actual return alphabets are fixed finite before every input. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackJetBlocks
