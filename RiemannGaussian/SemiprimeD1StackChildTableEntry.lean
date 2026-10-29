/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetContextBounds
import RiemannGaussian.SemiprimeD1StackGatherBytecode
import RiemannGaussian.SemiprimeD1StackTreeBytecode
import RiemannGaussian.SemiprimeD1StackPrecisionReduceBounds
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Literal individual child-table integer entry source
Only actual table, unary port vector, assignment and old/new context headers
enter. Both ranks and precision widths are acquired by real context calls.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntry
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace J
export SemiprimeD1StackJetContext (Stack Label program initial axesCache precisionBits rankCache widthCache)
end J
namespace G
export SemiprimeD1StackBitGather (Stack contents)
export SemiprimeD1StackGatherBytecode (Label code entry)
end G
namespace T
export SemiprimeD1TensorTapeTreeMachine (Stack contents)
export SemiprimeD1StackTreeBytecode (Label code entry)
end T
namespace R
export SemiprimeD1StackPrecisionReduce (Stack Label program store)
end R
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Twelve actual retained-source, acquired-count, parser and logger roles. -/
inductive Aux where
  | parentTable | order | remaining | oldRemaining | coefficient | valid | scratch
  | buffer | history | output | success | parentEntry
  deriving DecidableEq,Repr
/-- Literal complete auxiliary inventory. -/
instance :Fintype Aux:=Fintype.ofList [.parentTable,.order,.remaining,.oldRemaining,.coefficient,.valid,.scratch,
  .buffer,.history,.output,.success,.parentEntry] (by intro k;cases k <;> simp)
/-- Every allocated old/new context, gather, tree, scalar reducer and helper word is counted. -/
abbrev Stack:=J.Stack⊕(J.Stack⊕(G.Stack⊕(T.Stack⊕(R.Stack⊕Aux))))
/-- Actual old or new full fifteen-word context cache. -/
def context (child:Bool) (k:J.Stack):Stack:=if child then .inr (.inl k) else .inl k
/-- Six actual gather allocations, including retained assignment. -/
def gather (k:G.Stack):Stack:=.inr (.inr (.inl k))
/-- All five tree allocations; its allocated path is an explicitly unused shadow. -/
def treeAllocation (k:T.Stack):Stack:=.inr (.inr (.inr (.inl k)))
/-- Eight actual precision-reducer words, all cleared between coefficients. -/
def reduce (k:R.Stack):Stack:=.inr (.inr (.inr (.inr (.inl k))))
/-- Actual twelve-helper inclusion. -/
def aux (k:Aux):Stack:=.inr (.inr (.inr (.inr (.inr k))))
/-- Gathered raw assignment is consumed DIRECTLY by the real serialized parent lookup. -/
def tree:T.Stack→Stack | .path=>gather .output | k=>treeAllocation k
/-- Five literal paid preserving copies. -/
inductive Copy where | oldRank | newRank | order | table | entry deriving DecidableEq
/-- Literal complete paid-copy site inventory. -/
instance :Fintype Copy:=Fintype.ofList [.oldRank,.newRank,.order,.table,.entry] (by intro k;cases k <;> simp)
/-- Only fixed physical source/destination/scratch triples enter preserving copy calls. -/
def copyStack (site:Copy) (k:Fin 3):Stack:=
  if k=0 then match site with
    | .oldRank=>context false J.rankCache | .newRank=>context true J.rankCache
    | .order=>aux .order | .table=>aux .parentTable | .entry=>tree .output
  else if k=1 then match site with
    | .oldRank=>aux .oldRemaining | .newRank=>aux .remaining
    | .order=>gather .input | .table=>tree .input | .entry=>aux .parentEntry
  else aux .scratch
/-- Every actual parent coefficient is parsed from the stopped real lookup vector. -/
def fieldStack:F.Stack→Stack
  | .inl .input=>tree .output | .inl .scratch=>aux .scratch
  | .inl .output=>aux .coefficient | .inr ()=>aux .valid
/-- Three real frames: actual binary NEWp, actual old/zero coefficient, actual reduced output. -/
inductive Frame where | precision | scalar | log deriving DecidableEq
/-- Literal complete scalar-framing and logging inventory. -/
instance :Fintype Frame:=Fintype.ofList [.precision,.scalar,.log] (by intro k;cases k <;> simp)
/-- Every scalar framed pair and output coefficient uses separate restoring scratch. -/
def frameStack (site:Frame) (k:Fin 3):Stack:=
  if k=0 then match site with | .precision=>context true J.precisionBits | .scalar=>aux .coefficient | .log=>reduce .result
  else if k=1 then match site with | .precision|.scalar=>reduce .input | .log=>aux .buffer
  else aux .scratch
/-- Two literal real reversals: one row fragment and one complete final history. -/
def reverseStack (finish:Bool) (k:Fin 2):Stack:=
  if k=0 then if finish then aux .history else aux .buffer
  else if finish then aux .output else aux .history
/-- All31 allocated non-context words participate in the physical abort sweep. -/
inductive Work where
  | gather (k:G.Stack) | tree (k:T.Stack) | reduce (k:R.Stack) | aux (k:Aux)
  deriving DecidableEq,Fintype
/-- Abort sweeps actual allocations, including the unused tree-path shadow. -/
def work:Work→Stack | .gather k=>gather k | .tree k=>treeAllocation k | .reduce k=>reduce k | .aux k=>aux k
/-- Fixed finite sweep successor, independent of every input. -/
def nextWork:Work→Option Work
  | .gather .input=>some (.gather .assignment) | .gather .assignment=>some (.gather .reader)
  | .gather .reader=>some (.gather .scratch) | .gather .scratch=>some (.gather .accumulator)
  | .gather .accumulator=>some (.gather .output) | .gather .output=>some (.tree .input)
  | .tree .input=>some (.tree .tasks) | .tree .tasks=>some (.tree .path)
  | .tree .path=>some (.tree .scratch) | .tree .scratch=>some (.tree .output)
  | .tree .output=>some (.reduce .input) | .reduce .input=>some (.reduce .word)
  | .reduce .word=>some (.reduce .precision) | .reduce .precision=>some (.reduce .width)
  | .reduce .width=>some (.reduce .work) | .reduce .work=>some (.reduce .temporary)
  | .reduce .temporary=>some (.reduce .result) | .reduce .result=>some (.reduce .valid)
  | .reduce .valid=>some (.aux .parentTable) | .aux .parentTable=>some (.aux .order)
  | .aux .order=>some (.aux .remaining) | .aux .remaining=>some (.aux .oldRemaining)
  | .aux .oldRemaining=>some (.aux .coefficient) | .aux .coefficient=>some (.aux .valid)
  | .aux .valid=>some (.aux .scratch) | .aux .scratch=>some (.aux .buffer)
  | .aux .buffer=>some (.aux .history) | .aux .history=>some (.aux .output)
  | .aux .output=>some (.aux .success) | .aux .success=>some (.aux .parentEntry) | .aux .parentEntry=>none
/-- Literal context/gather/lookup/coefficient/zero-extension control. -/
inductive Control where
  | start | childContext | ready | newPositive | copyOldRank | copyNewRank | copyOrder | gather | copyTable | lookup | copyEntry
  | header | parse | valid | oldCount | newCount | inputEOF | oldEOF | zeros | clearPath
  | precision (zero:Bool) | scalar (zero:Bool) | reduce (zero:Bool) | frame (zero:Bool) | tag (zero:Bool)
  | reverse (zero:Bool) | clearCoefficient (zero:Bool) | clearReduced (zero:Bool)
  | seedOutput | reverseOutput | accept | done | abort | sweep (part:Work) | rejected
  deriving DecidableEq,Fintype
/-- Every callee and return label is fixed finite before all data and contexts. -/
inductive Label where
  | local (pc:Control) | context (child:Bool) (pc:J.Label) | gather (pc:G.Label) | tree (pc:T.Label)
  | reduce (pc:R.Label) | copy (site:Copy) (pc:Fin 9) | field (pc:F.Label)
  | frame (site:Frame) (pc:Fin 11) | reverse (finish:Bool) (pc:Fin 4)
  deriving DecidableEq,Fintype
local notation "ctl"=>Label.local
/-- ONE fixed source with real whole/ready entries and no rank, product, q, getter or lift opcode. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.context false .start) (ctl .childContext)
  | .local .childContext=>.call (.context true .start) (ctl .ready)
  | .local .ready=>.base (.peek (context false J.rankCache) (ctl .abort) (ctl .abort) (ctl .newPositive))
  | .local .newPositive=>.base (.peek (context true J.rankCache) (ctl .abort) (ctl .abort) (ctl .copyOldRank))
  | .local .copyOldRank=>.call (.copy .oldRank 0) (ctl .copyNewRank)
  | .local .copyNewRank=>.call (.copy .newRank 0) (ctl .copyOrder)
  | .local .copyOrder=>.call (.copy .order 0) (ctl .gather)
  | .local .gather=>.call (.gather G.entry) (ctl .copyTable)
  | .local .copyTable=>.call (.copy .table 0) (ctl .lookup)
  | .local .lookup=>.call (.tree T.entry) (ctl .copyEntry)
  | .local .copyEntry=>.call (.copy .entry 0) (ctl .header)
  | .local .header=>.base (.pop (tree .output) (ctl .abort) (ctl .inputEOF) (ctl .parse))
  | .local .parse=>.call (.field (F.active .tagPop (none,false))) (ctl .valid)
  | .local .valid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .oldCount))
  | .local .oldCount=>.base (.pop (aux .oldRemaining) (ctl .abort) (ctl .abort) (ctl .newCount))
  | .local .newCount=>.base (.pop (aux .remaining) (ctl .abort) (ctl .abort) (ctl (.precision false)))
  | .local .inputEOF=>.base (.peek (tree .output) (ctl .oldEOF) (ctl .abort) (ctl .abort))
  | .local .oldEOF=>.base (.peek (aux .oldRemaining) (ctl .zeros) (ctl .abort) (ctl .abort))
  | .local .zeros=>.base (.pop (aux .remaining) (ctl .clearPath) (ctl .abort) (ctl (.precision true)))
  | .local (.precision z)=>.call (.frame .precision 0) (ctl (.scalar z))
  | .local (.scalar z)=>.call (.frame .scalar 0) (ctl (.reduce z))
  | .local (.reduce z)=>.call (.reduce .start) (ctl (.frame z))
  | .local (.frame z)=>.call (.frame .log 0) (ctl (.tag z))
  | .local (.tag z)=>.base (.push (aux .buffer) true (ctl (.reverse z)))
  | .local (.reverse z)=>.call (.reverse false 0) (ctl (.clearCoefficient z))
  | .local (.clearCoefficient z)=>.base (.pop (aux .coefficient) (ctl (.clearReduced z)) (ctl (.clearCoefficient z)) (ctl (.clearCoefficient z)))
  | .local (.clearReduced z)=>.base (.pop (reduce .result) (ctl (if z then .zeros else .header)) (ctl (.clearReduced z)) (ctl (.clearReduced z)))
  | .local .clearPath=>.base (.pop (gather .output) (ctl .seedOutput) (ctl .clearPath) (ctl .clearPath))
  | .local .seedOutput=>.base (.push (aux .output) false (ctl .reverseOutput))
  | .local .reverseOutput=>.call (.reverse true 0) (ctl .accept)
  | .local .accept=>.base (.push (aux .success) true (ctl .done))
  | .local .done=>.base .halt
  | .local .abort=>.base (.jump (ctl (.sweep (.gather .input))))
  | .local (.sweep p)=>
    let next:=ctl (match nextWork p with | some q=>.sweep q | none=>.rejected)
    if work p=gather .assignment ∨work p=aux .parentTable ∨work p=aux .order then .base (.jump next)
    else .base (.pop (work p) next (ctl (.sweep p)) (ctl (.sweep p)))
  | .local .rejected=>.base (.push (aux .success) false (ctl .done))
  | .context child pc=>SemiprimeD1StackValidationLink.instruction (context child) (Label.context child) (J.program pc)
  | .gather pc=>SemiprimeD1StackMultiplierLink.instruction gather Label.gather (G.code pc)
  | .tree pc=>SemiprimeD1StackMultiplierLink.instruction tree Label.tree (T.code pc)
  | .reduce pc=>SemiprimeD1StackValidationLink.instruction reduce Label.reduce (R.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (F.code pc)
  | .frame site pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack site) (Label.frame site) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
/-- Literal full allocated bank, a view of fixed physical tape addresses only. -/
def bank (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool)
    (r:R.Stack→List Bool) (a:Aux→List Bool):Stack→List Bool:=
  Sum.elim old (Sum.elim child (Sum.elim g (Sum.elim t (Sum.elim r a))))
/-- Exactly seven actual source words; no rank, width, old entry or product is preloaded. -/
def input (parentTable order assignment oldAxes oldp newAxes newp:List Bool):Stack→List Bool:=
  bank (J.initial oldAxes oldp).data (J.initial newAxes newp).data (G.contents [] assignment [] [] [] [])
    (T.contents [] [] [] [] []) (R.store [] [] [] [] [] [] [] [])
    (fun k=>match k with | .parentTable=>parentTable | .order=>order | _=>[])
/-- Whole front door precedes both physically paid context acquisitions. -/
def initial (parentTable order assignment oldAxes oldp newAxes newp:List Bool):C.State Stack Label:=
  ⟨some (ctl .start),none,none,input parentTable order assignment oldAxes oldp newAxes newp,[]⟩
/-- Genuine finite fixed source machine. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .parentTable) (aux .output) (ctl .start) program
/-- All61 roles, including the unused allocated Tree.path shadow, are counted. -/
theorem stack_card:Fintype.card Stack=61:=by decide
/-- Each actual context inclusion has distinct physical addresses. -/
theorem context_injective (child:Bool):Function.Injective (context child):=by
  cases child <;> intro a b h <;> simpa only [context,Bool.false_eq_true,ite_false,ite_true,Sum.inl.injEq,Sum.inr.injEq] using h
/-- Each real gather role is a distinct physical word. -/
theorem gather_injective:Function.Injective gather:=fun _ _ h=>Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
/-- Tree path aliases gathered bits while all other tree operands remain distinct. -/
theorem tree_injective:Function.Injective tree:=by intro a b h;cases a <;> cases b <;> simp_all [tree,treeAllocation,gather]
/-- The scalar reducer inclusion has eight distinct actual roles. -/
theorem reduce_injective:Function.Injective reduce:=fun _ _ h=>Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h))))
/-- Every copy restores separate scratch and preserves its real source. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by cases site <;> decide
/-- The actual coefficient parser has separate source/output/scratch/valid fields. -/
theorem field_injective:Function.Injective fieldStack:=by decide
/-- Scalar framing and coefficient logging never alias their restoring scratch. -/
theorem frame_injective (site:Frame):Function.Injective (frameStack site):=by cases site <;> decide
/-- Both real reversals consume separate source and output tapes. -/
theorem reverse_injective (finish:Bool):Function.Injective (reverseStack finish):=by cases finish <;> decide
/-- Every data and actual return alphabet is finite before all inputs. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Runtime sigma carries only fixed finite flags and labels. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackChildTableEntry
