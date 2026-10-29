/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetUnitBounds
import RiemannGaussian.SemiprimeD1StackJetMulBounds
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackFrame
/-! # Actual ordered child-product and mode-sum controller
Only original unary-axis headers, binary precision and a physical nested vector
of binary child-result vectors enter the full source. Real context acquisition
precedes two genuine right-fold procedures. Saved heads are framed Boolean tape
data; recursion uses the real fixed-label return stack. No solver, rank, result,
function or clock is an instruction operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFold
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace M
export SemiprimeD1StackJetMul (Stack Label program output inputData initial)
end M
namespace X
export SemiprimeD1StackJetContext (Stack Label program axesCache precisionBits rankCache widthCache)
end X
namespace U
export SemiprimeD1StackJetUnit (Stack Label program widthCache rankCache output)
end U
namespace A
export SemiprimeD1StackJetAdd (Stack Label program store)
end A
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Eleven actual caller words; saved activations are ordinary Boolean data. -/
inductive Aux where
  | children | modes | group | frames | fieldScratch | valid | copyScratch | frameScratch
  | precision | tailSum | sum
  deriving DecidableEq,Repr
instance :Fintype Aux where
  elems:={.children,.modes,.group,.frames,.fieldScratch,.valid,.copyScratch,.frameScratch,.precision,.tailSum,.sum}
  complete:=by intro k;cases k <;> simp
/-- All111roles remain allocated, including every unused shared-cache/input shadow. -/
abbrev Stack:=M.Stack⊕(X.Stack⊕(U.Stack⊕(A.Stack⊕Aux)))
/-- Literal dense-multiplication bank inclusion. -/
def main (k:M.Stack):Stack:=.inl k
/-- Dedicated context-role shadow inclusion. -/
def contextWork (k:X.Stack):Stack:=.inr (.inl k)
/-- Dedicated unit-role shadow inclusion. -/
def unitWork (k:U.Stack):Stack:=.inr (.inr (.inl k))
/-- Dedicated addition-role shadow inclusion. -/
def addWork (k:A.Stack):Stack:=.inr (.inr (.inr (.inl k)))
/-- Literal caller word address. -/
def aux (k:Aux):Stack:=.inr (.inr (.inr (.inr k)))
/-- The actual current binary child-result vector, restored from one real frame. -/
def left:Stack:=main (.inl (SemiprimeD1StackJetPoint.aux .a))
/-- The actual recursively acquired right product. -/
def product:Stack:=main (.inl (SemiprimeD1StackJetPoint.aux .b))
/-- Actual acquired axis tape shared by context and every multiplier call. -/
def axes:Stack:=main (.inl (SemiprimeD1StackJetPoint.aux .axes))
/-- Actual acquired unary rank counter shared by all real operators. -/
def rank:Stack:=main (.inl (SemiprimeD1StackJetPoint.aux .rank))
/-- Actual acquired unary precision count; coefficients and original precision remain binary. -/
def width:Stack:=main (.inl SemiprimeD1StackJetPoint.precision)
/-- Temporary whole-multiplication output, physically copied then drained. -/
def mulOutput:Stack:=main M.output
/-- Actual full mode sum, also the public stopped output address. -/
def output:Stack:=aux .sum
/-- Actual acquired context cache aliases, with every unused shadow counted. -/
def contextStack (k:X.Stack):Stack:=
  if k=X.axesCache then axes else if k=X.rankCache then rank else if k=X.widthCache then width
  else if k=X.precisionBits then aux .precision else contextWork k
/-- The actual unit result becomes the right-fold empty product; its private inputs stay separate from the saved sum. -/
def unitStack (k:U.Stack):Stack:=
  if k=U.widthCache then width else if k=U.rankCache then rank else if k=U.output then product else unitWork k
/-- Real addition consumes the current product and saved tail sum, and writes the actual sum output. -/
def addStack (k:A.Stack):Stack:=
  if k=U.widthCache then width else if k=U.rankCache then rank
  else if k=.inr .leftTape then product else if k=.inr .rightTape then aux .tailSum
  else if k=.inr .output then output else addWork k
/-- Three fixed preserving-copy sites, independent of every numerical input. -/
inductive Copy where | children | sum | product deriving DecidableEq,Repr
instance :Fintype Copy where
  elems:={.children,.sum,.product}
  complete:=by intro k;cases k <;> simp
/-- Four literal field-parser sites: two input fields and their two saved-head restores. -/
inductive Parse where | mode | child | restoreMode | restoreChild deriving DecidableEq,Repr
instance :Fintype Parse where
  elems:={.mode,.child,.restoreMode,.restoreChild}
  complete:=by intro k;cases k <;> simp
/-- Fixed finite fold, framing and cleanup locations. -/
inductive Control where
  | start | prepared | sumCall | sumVisit | sumRead | sumValid | sumSave | sumClear | sumChild
  | sumRestore | sumRestored | copySum | clearSum | productCall | add | zeroLeft | zeroRight
  | productVisit | productRead | productValid | productSave | productClear | productChild
  | productRestore | productRestored | multiply | clearLeft | clearRight | copyProduct | clearOutput
  | unit | returning | done | abort
  deriving DecidableEq,Repr
instance :Fintype Control where
  elems:={.start,.prepared,.sumCall,.sumVisit,.sumRead,.sumValid,.sumSave,.sumClear,.sumChild,
    .sumRestore,.sumRestored,.copySum,.clearSum,.productCall,.add,.zeroLeft,.zeroRight,
    .productVisit,.productRead,.productValid,.productSave,.productClear,.productChild,
    .productRestore,.productRestored,.multiply,.clearLeft,.clearRight,.copyProduct,.clearOutput,
    .unit,.returning,.done,.abort}
  complete:=by intro k;cases k <;> simp
/-- Only finite labels and flags enter actual control and real return symbols. -/
inductive Label where
  | local (pc:Control) | context (pc:X.Label) | unit (pc:U.Label) | multiply (pc:M.Label) | add (pc:A.Label)
  | copy (site:Copy) (pc:Fin 9) | field (site:Parse) (pc:F.Label) | save (child:Bool) (pc:Fin 11)
  deriving DecidableEq,Fintype
/-- Actual source, destination and restoring scratch for every preserving copy. -/
def copyStack (site:Copy) (k:Fin 3):Stack:=
  if k=0 then match site with | .children=>aux .children | .sum=>output | .product=>mulOutput
  else if k=1 then match site with | .children=>aux .modes | .sum=>aux .tailSum | .product=>product
  else aux .copyScratch
/-- Each complete head is physically saved before the recursive tail is consumed. -/
def saveStack (child:Bool) (k:Fin 3):Stack:=
  if k=0 then (if child then left else aux .group) else if k=1 then aux .frames else aux .frameScratch
/-- Actual input readers and saved activation words use the same real four-role parser. -/
def fieldStack (site:Parse):F.Stack→Stack
  | .inl .input=>match site with | .mode=>aux .modes | .child=>aux .group | .restoreMode|.restoreChild=>aux .frames
  | .inl .output=>match site with | .mode|.restoreMode=>aux .group | .child|.restoreChild=>left
  | .inl .scratch=>aux .fieldScratch
  | .inr _=>aux .valid
/-- One literal finite source: real context acquisition, exact right products, then exact right sums. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.context .start) (.local .prepared)
  | .local .prepared=>.call (.copy .children 0) (.local .sumCall)
  | .local .sumCall=>.call (.local .sumVisit) (.local .done)
  | .local .sumVisit=>.base (.pop (aux .modes) (.local .abort) (.local .zeroLeft) (.local .sumRead))
  | .local .sumRead=>.call (.field .mode (F.active .tagPop (none,false))) (.local .sumValid)
  | .local .sumValid=>.base (.pop (aux .valid) (.local .abort) (.local .abort) (.local .sumSave))
  | .local .sumSave=>.call (.save false 0) (.local .sumClear)
  | .local .sumClear=>.base (.pop (aux .group) (.local .sumChild) (.local .sumClear) (.local .sumClear))
  | .local .sumChild=>.call (.local .sumVisit) (.local .sumRestore)
  | .local .sumRestore=>.call (.field .restoreMode (F.active .tagPop (none,false))) (.local .sumRestored)
  | .local .sumRestored=>.base (.pop (aux .valid) (.local .abort) (.local .abort) (.local .copySum))
  | .local .copySum=>.call (.copy .sum 0) (.local .clearSum)
  | .local .clearSum=>.base (.pop output (.local .productCall) (.local .clearSum) (.local .clearSum))
  | .local .productCall=>.call (.local .productVisit) (.local .add)
  | .local .add=>.call (.add .start) (.local .returning)
  | .local .zeroLeft=>.base (.push product false (.local .zeroRight))
  | .local .zeroRight=>.base (.push (aux .tailSum) false (.local .add))
  | .local .productVisit=>.base (.pop (aux .group) (.local .abort) (.local .unit) (.local .productRead))
  | .local .productRead=>.call (.field .child (F.active .tagPop (none,false))) (.local .productValid)
  | .local .productValid=>.base (.pop (aux .valid) (.local .abort) (.local .abort) (.local .productSave))
  | .local .productSave=>.call (.save true 0) (.local .productClear)
  | .local .productClear=>.base (.pop left (.local .productChild) (.local .productClear) (.local .productClear))
  | .local .productChild=>.call (.local .productVisit) (.local .productRestore)
  | .local .productRestore=>.call (.field .restoreChild (F.active .tagPop (none,false))) (.local .productRestored)
  | .local .productRestored=>.base (.pop (aux .valid) (.local .abort) (.local .abort) (.local .multiply))
  | .local .multiply=>.call (.multiply .start) (.local .clearLeft)
  | .local .clearLeft=>.base (.pop left (.local .clearRight) (.local .clearLeft) (.local .clearLeft))
  | .local .clearRight=>.base (.pop product (.local .copyProduct) (.local .clearRight) (.local .clearRight))
  | .local .copyProduct=>.call (.copy .product 0) (.local .clearOutput)
  | .local .clearOutput=>.base (.pop mulOutput (.local .returning) (.local .clearOutput) (.local .clearOutput))
  | .local .unit=>.call (.unit .seed0) (.local .returning)
  | .local .returning=>.ret
  | .local .done|.local .abort=>.base .halt
  | .context pc=>SemiprimeD1StackValidationLink.instruction contextStack Label.context (X.program pc)
  | .unit pc=>SemiprimeD1StackValidationLink.instruction unitStack Label.unit (U.program pc)
  | .multiply pc=>SemiprimeD1StackValidationLink.instruction main Label.multiply (M.program pc)
  | .add pc=>SemiprimeD1StackValidationLink.instruction addStack Label.add (A.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field site pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack site) (Label.field site) (F.code pc)
  | .save child pc=>SemiprimeD1StackMultiplierLink.instruction (saveStack child) (Label.save child) (SemiprimeD1StackFrame.code pc)
/-- The three actual external input words; every counter and arithmetic/result word is initially empty. -/
def input (axisTape precision children:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (fun _=>[]) axes axisTape) (aux .precision) precision) (aux .children) children
/-- Actual three-input start acquires its own complete context before any arithmetic. -/
def initial (axisTape precision children:List Bool):C.State Stack Label:=
  ⟨some (.local .start),none,none,input axisTape precision children,[]⟩
/-- One genuine finite machine; physical multiword source initialization remains explicit. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .children) output (.local .start) program
/-- All111data roles, including every shared-role shadow, remain counted. -/
theorem stack_card:Fintype.card Stack=111:=by decide
/-- Real context aliases keep all component roles distinct. -/
theorem context_injective:Function.Injective contextStack:=by decide
/-- Real unit aliases keep all component roles distinct. -/
theorem unit_injective:Function.Injective unitStack:=by decide
/-- Real addition aliases keep all component roles distinct. -/
theorem add_injective:Function.Injective addStack:=by decide
/-- Every preserving-copy site has three distinct actual roles. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by cases site <;> decide
/-- Both saved-head frame sites have three distinct actual roles. -/
theorem save_injective (child:Bool):Function.Injective (saveStack child):=by cases child <;> decide
/-- All four real field parsers have distinct input, output, scratch and validity roles. -/
theorem field_injective (site:Parse):Function.Injective (fieldStack site):=by cases site <;> decide
/-- Runtime control is fixed finite before every original context and child tape. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data/return alphabet is finite before every original input. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackJetFold
