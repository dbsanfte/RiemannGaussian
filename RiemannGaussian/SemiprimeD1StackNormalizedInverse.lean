/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationOriginal
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackNormalizedInverseSpec
/-! # A fixed58-word source for the entire normalized inverse
Only the actual denominator array, derived unary q and physical W template enter.
All array reads, descending indices, fitted rational operations, prefix records,
cleanup and final chronological reversal execute as literal Boolean-stack code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverse
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRationalOperation (Stack Label program aux signOutput Op)
end R
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Four actual signed/denominator coefficient caches. -/
inductive Reg where | left | right | product | acc deriving DecidableEq,Repr
/-- Literal four-register inventory. -/
instance regFintype : Fintype Reg := Fintype.ofList [.left,.right,.product,.acc] (by intro k;cases k <;> simp)
/-- The actual three-source controller's additional physical tapes. -/
inductive Aux where
  | denominator | originalQ | remaining | built | aIndex | bIndex | terms
  | reader | readTodo | fieldFrameScratch | valid | copyScratch | prefixReverse | output
  deriving DecidableEq,Repr
/-- All14 tapes are fixed before every array, q and W. -/
instance auxFintype : Fintype Aux := Fintype.ofList
  [.denominator,.originalQ,.remaining,.built,.aIndex,.bIndex,.terms,.reader,.readTodo,
    .fieldFrameScratch,.valid,.copyScratch,.prefixReverse,.output] (by intro k;cases k <;> simp)
/-- All36 source roles plus eight coefficient fields plus14 controller words. -/
abbrev Stack := R.Stack⊕((Reg×Bool)⊕Aux)
/-- The complete real36-word normalized/twice-fitted operation source. -/
def rational (k : R.Stack) : Stack := .inl k
/-- Actual signed numerator when den=FALSE; actual unsigned denominator when TRUE. -/
def reg (r : Reg) (den : Bool) : Stack := .inr (.inl (r,den))
/-- Actual finite controller tape. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- W remains at the actual included operation's retained physical input word. -/
def template : Stack := rational (R.aux .template)
/-- Two finite array read sites; numerical indices stay on physical unary tapes. -/
inductive ReadSite where | denominator | prefix deriving DecidableEq,Repr
/-- Complete literal read-site inventory. -/
instance readSiteFintype : Fintype ReadSite := Fintype.ofList [.denominator,.prefix] (by intro k;cases k <;> simp)
/-- The actual retained source of each zero-extended read. -/
def readSource : ReadSite→Stack | .denominator=>aux .denominator | .prefix=>aux .prefixReverse
/-- The actual acquired decreasing index of each source read. -/
def readIndex : ReadSite→Stack | .denominator=>aux .aIndex | .prefix=>aux .bIndex
/-- The physically acquired rational-cache destination of each read. -/
def readReg : ReadSite→Reg | .denominator=>.left | .prefix=>.right
/-- Three real scalar sites, preserving the original raw operand orientation. -/
inductive Site where | product | sum | negate deriving DecidableEq,Repr
/-- Complete literal scalar-site inventory. -/
instance siteFintype : Fintype Site := Fintype.ofList [.product,.sum,.negate] (by intro k;cases k <;> simp)
/-- Actual frozen operation selected only by a finite literal call site. -/
def operation : Site→R.Op | .product=>.mul | .sum=>.add | .negate=>.neg
/-- Product FIRST and suffix SECOND is essential for byte-exact native right-fold order. -/
def operand : Site→Bool→Reg
  | .product,false=>.left | .product,true=>.right
  | .sum,false=>.product | .sum,true=>.acc
  | .negate,false=>.acc | .negate,true=>.right
/-- The sum and negation overwrite their old accumulator only AFTER four physical operand copies. -/
def destination : Site→Reg | .product=>.product | .sum|.negate=>.acc
/-- Every preserving-copy route is fixed before any source values are chosen. -/
inductive Copy where
  | remaining | terms | aIndex | bIndex | reader (site : ReadSite) | readIndex (site : ReadSite)
  | input (site : Site) (right den : Bool) | output (site : Site) (den : Bool)
  deriving DecidableEq,Repr,Fintype
/-- Actual source of a restoring copy. -/
def copySource : Copy→Stack
  | .remaining=>aux .originalQ | .terms|.aIndex|.bIndex=>aux .built
  | .reader site=>readSource site | .readIndex site=>readIndex site
  | .input site right den=>reg (operand site right) den
  | .output _ den=>rational (R.aux (if den then .denominatorOutput else .numeratorOutput))
/-- Actual empty destination of a restoring copy. -/
def copyTarget : Copy→Stack
  | .remaining=>aux .remaining | .terms=>aux .terms | .aIndex=>aux .aIndex | .bIndex=>aux .bIndex
  | .reader _=>aux .reader | .readIndex _=>aux .readTodo
  | .input _ right den=>rational (R.aux (if right then (if den then .rightDen else .rightSigned) else (if den then .leftDen else .leftSigned)))
  | .output site den=>reg (destination site) den
/-- Every paid copy restores the same separate actual scratch. -/
def copyStack (site : Copy) (k : Fin 3) : Stack := if k=0 then copySource site else if k=1 then copyTarget site else aux .copyScratch
/-- Either an actual array row field or the final consumed-prefix row field. -/
inductive Field where | read (site : ReadSite) (den : Bool) | finish (den : Bool) deriving DecidableEq,Repr,Fintype
/-- Actual four-role Field parser injection; no source word is decoded by a getter. -/
def fieldStack (site : Field) : F.Stack→Stack
  | .inl .input=>match site with | .read _ _=>aux .reader | .finish _=>aux .prefixReverse
  | .inl .scratch=>aux .fieldFrameScratch
  | .inl .output=>match site with | .read part den=>reg (readReg part) den | .finish den=>reg .left den
  | .inr ()=>aux .valid
/-- Framing either appends a new logical coefficient or reverses one physical row at the end. -/
inductive Frame where | coefficient (den : Bool) | finish (den : Bool) deriving DecidableEq,Repr,Fintype
/-- Every frame preserves its signed/denominator source and restores the shared empty parser scratch. -/
def frameStack (site : Frame) (k : Fin 3) : Stack :=
  if k=0 then match site with | .coefficient den=>reg .acc den | .finish den=>reg .left den
  else if k=1 then match site with | .coefficient _=>aux .prefixReverse | .finish _=>aux .output
  else aux .fieldFrameScratch
/-- The literal35 non-template operation roles, including every displaced/shared/private word. -/
def rationalRole (k:Fin 35) :R.Stack:=match k.val with
  | 0=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.x)
  | 1=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.y)
  | 2=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inr .digits))
  | 3=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .left))
  | 4=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .right))
  | 5=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .scratch))
  | 6=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .output))
  | 7=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.remainder)
  | 8=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.quotient)
  | 9=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.copyScratch)
  | 10=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inr .template))
  | 11=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.numerator)
  | 12=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.denominator)
  | 13=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack (SemiprimeD1StackEuclidGCD.aux .fuel))
  | 14=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.scan)
  | 15=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack (SemiprimeD1StackEuclidGCD.aux .next))
  | 16=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack (SemiprimeD1StackEuclidGCD.aux .trimScratch))
  | 17=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.gcdOutput)
  | 18=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)
  | 19=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.aux .numeratorOutput)
  | 20=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.aux .denominatorOutput)
  | 21=>SemiprimeD1StackRationalOperation.normalizeStack (SemiprimeD1StackRationalNormalize.aux .signOutput)
  | 22=>SemiprimeD1StackRationalOperation.multiplierStack SemiprimeD1StackMultiplier.factor
  | 23=>SemiprimeD1StackRationalOperation.multiplierStack SemiprimeD1StackMultiplier.copied
  | 24=>SemiprimeD1StackRationalOperation.multiplierStack SemiprimeD1StackMultiplier.copyScratch
  | 25=>SemiprimeD1StackRationalOperation.multiplierStack SemiprimeD1StackMultiplier.input
  | 26=>SemiprimeD1StackRationalOperation.multiplierStack SemiprimeD1StackMultiplier.digits
  | 27=>SemiprimeD1StackRationalOperation.aux .leftSigned
  | 28=>SemiprimeD1StackRationalOperation.aux .leftDen
  | 29=>SemiprimeD1StackRationalOperation.aux .rightSigned
  | 30=>SemiprimeD1StackRationalOperation.aux .rightDen
  | 31=>SemiprimeD1StackRationalOperation.aux .leftMagnitude
  | 32=>SemiprimeD1StackRationalOperation.aux .rightMagnitude
  | 33=>SemiprimeD1StackRationalOperation.aux .numeratorOutput
  | _=>SemiprimeD1StackRationalOperation.aux .denominatorOutput
/-- Every literal coefficient-cache field occurs exactly once. -/
def regRole (i : Fin 8) : Stack := match i.val with
  | 0=>reg .left false | 1=>reg .left true | 2=>reg .right false | 3=>reg .right true
  | 4=>reg .product false | 5=>reg .product true | 6=>reg .acc false | _=>reg .acc true
/-- Every controller word other than the two readonly inputs and output is paid by the final sweep. -/
def auxRole (i : Fin 11) : Stack := aux (match i.val with
  | 0=>.remaining | 1=>.built | 2=>.aIndex | 3=>.bIndex | 4=>.terms | 5=>.reader
  | 6=>.readTodo | 7=>.fieldFrameScratch | 8=>.valid | 9=>.copyScratch | _=>.prefixReverse)
/-- All54 private physical words, including all35 operation roles and all eight caches. -/
def workRole (i : Fin 54) : Stack :=
  if h:i.val<35 then rational (rationalRole ⟨i.val,h⟩)
  else if h:i.val<43 then regRole ⟨i.val-35,by omega⟩ else auxRole ⟨i.val-43,by omega⟩
/-- A malformed physical source also drains its partial output before true halt. -/
def abortRole (i : Fin 55) : Stack := if h:i.val<54 then workRole ⟨i.val,h⟩ else aux .output
/-- Exact sign-prefixed binary rational field, used only by proof/codec specifications. -/
def signed (word : SemiprimeRationalBits.RationalWord) : List Bool := word.numerator.negative::word.numerator.magnitude
/-- The shared original two-field rational-row ABI. -/
def row (word : SemiprimeRationalBits.RationalWord) (tail : List Bool) : List Bool :=
  true::SemiprimeSourceHistogramKeyBits.frame (signed word) (SemiprimeSourceHistogramKeyBits.frame word.denominator tail)
/-- A chronological physical array has ONE actual FALSE terminator. -/
def tape (words : List SemiprimeRationalBits.RationalWord) : List Bool := words.foldr row [false]
/-- Literal ONE row; it is deliberately NOT fitted to W. -/
def oneRow : List Bool := [true,true,false,true,true,false,true,true,false]
/-- These fixed nine pushes are exactly the native oneWord row, even when W=0. -/
theorem oneRow_eq : oneRow=row SemiprimeJetBits.oneWord [] := rfl
/-- One finite literal bit, fixed before every source input. -/
def seedBit (i : Fin 9) : Bool := oneRow.reverse[i.val]'(by change i.val<9;exact i.isLt)
/-- Real zero-extended array read stages. -/
inductive ReadControl where
  | copyArray | copyIndex | count | tag (take : Bool) | field (take den : Bool) | valid (take den : Bool)
  | clearSigned | clearDen | drainReader | drainTodo | missingReader | missingTodo
  | zeroSigned | zeroDen | success | failed | return
  deriving DecidableEq,Repr,Fintype
/-- Literal full arithmetic-site stages, not an operation stream input. -/
inductive OperationControl where
  | copyInput (right den : Bool) | run | clearDestination (den : Bool) | copyOutput (den : Bool)
  | sign | writeSign (bit : Bool) | clear (i : Fin 35) | success | failed | return
  deriving DecidableEq,Repr,Fintype
/-- Fixed source phases and finite physical cleanup positions. -/
inductive Control where
  | start | seedPrefix | copyRemaining | first | seedOne (i : Fin 9) | bump | outer
  | copyTerms | copyAIndex | copyBIndex | predecessor | seedZero (den : Bool) | terms
  | readA | checkedA | readB | checkedB | operate (site : Site) | operated (site : Site)
  | clearPair (i : Fin 6) | decrementA | decrementB | seedNeg (den : Bool)
  | frameCoefficient (den : Bool) | tagCoefficient | clearCoefficient (i : Fin 8)
  | finalTag | finalField (den : Bool) | finalValid (den : Bool) | finalFrame (den : Bool)
  | finalRowTag | clearFinalReg (den : Bool) | finalEnd | clearFinal (i : Fin 54)
  | abort (i : Fin 55) | done
  deriving DecidableEq,Repr,Fintype
/-- All control and actual nested-source return labels are fixed finite. -/
inductive Label where
  | local (pc : Control) | rational (pc : R.Label) | copy (site : Copy) (pc : Fin 9)
  | field (site : Field) (pc : F.Label) | frame (site : Frame) (pc : Fin 11)
  | read (site : ReadSite) (pc : ReadControl) | operation (site : Site) (pc : OperationControl)
  deriving Fintype
/-- Literal enclosing stage constructor. -/
def ctl : Control→Label := Label.local
/-- Literal predecessor after fixed ONE-row seed bytes. -/
def seedNext (i : Fin 9) : Label := if h:i.val+1<9 then ctl (.seedOne ⟨i.val+1,h⟩) else ctl .bump
/-- Literal next pair-field drain. -/
def pairNext (i : Fin 6) : Label := if h:i.val+1<6 then ctl (.clearPair ⟨i.val+1,h⟩) else ctl .decrementA
/-- Literal next coefficient-cache drain. -/
def coefficientNext (i : Fin 8) : Label := if h:i.val+1<8 then ctl (.clearCoefficient ⟨i.val+1,h⟩) else ctl .bump
/-- Literal next final private-word drain. -/
def finalNext (i : Fin 54) : Label := if h:i.val+1<54 then ctl (.clearFinal ⟨i.val+1,h⟩) else ctl .done
/-- Literal next malformed-source private/output drain. -/
def abortNext (i : Fin 55) : Label := if h:i.val+1<55 then ctl (.abort ⟨i.val+1,h⟩) else ctl .done
/-- Literal next normalized-operation cleanup position. -/
def operationNext (site : Site) (i : Fin 35) : Label :=
  if h:i.val+1<35 then .operation site (.clear ⟨i.val+1,h⟩) else .operation site .success
/-- The old suffix accumulator is retained until every input has been physically copied. -/
def afterInput (site : Site) (right den : Bool) : Label :=
  if !den then .operation site (.copyInput right true)
  else if !right then .operation site (.copyInput true false) else .operation site .run
/-- The exact finite continuation after one fully normalized/twice-fitted scalar site. -/
def afterOperation : Site→Label
  | .product=>ctl (.operate .sum) | .sum=>ctl (.clearPair 0) | .negate=>ctl (.frameCoefficient true)
/-- ONE fixed full array source: actual parsing, arithmetic, prefix construction and final row reversal. -/
def program : Label→C.Instruction Stack Label
  | .local .start=>.base (.push (aux .output) false (ctl .seedPrefix))
  | .local .seedPrefix=>.base (.push (aux .prefixReverse) false (ctl .copyRemaining))
  | .local .copyRemaining=>.call (.copy .remaining 0) (ctl .first)
  | .local .first=>.base (.pop (aux .remaining) (ctl .finalTag) (ctl (.abort 0)) (ctl (.seedOne 0)))
  | .local (.seedOne i)=>.base (.push (aux .prefixReverse) (seedBit i) (seedNext i))
  | .local .bump=>.base (.push (aux .built) true (ctl .outer))
  | .local .outer=>.base (.pop (aux .remaining) (ctl .finalTag) (ctl (.abort 0)) (ctl .copyTerms))
  | .local .copyTerms=>.call (.copy .terms 0) (ctl .copyAIndex)
  | .local .copyAIndex=>.call (.copy .aIndex 0) (ctl .copyBIndex)
  | .local .copyBIndex=>.call (.copy .bIndex 0) (ctl .predecessor)
  | .local .predecessor=>.base (.pop (aux .bIndex) (ctl (.abort 0)) (ctl (.abort 0)) (ctl (.seedZero false)))
  | .local (.seedZero den)=>.base (.push (reg .acc den) den (if den then ctl .terms else ctl (.seedZero true)))
  | .local .terms=>.base (.pop (aux .terms) (ctl (.seedNeg false)) (ctl (.abort 0)) (ctl .readA))
  | .local .readA=>.call (.read .denominator .copyArray) (ctl .checkedA)
  | .local .checkedA=>.base (.pop (aux .valid) (ctl (.abort 0)) (ctl (.abort 0)) (ctl .readB))
  | .local .readB=>.call (.read .prefix .copyArray) (ctl .checkedB)
  | .local .checkedB=>.base (.pop (aux .valid) (ctl (.abort 0)) (ctl (.abort 0)) (ctl (.operate .product)))
  | .local (.operate site)=>.call (.operation site (.copyInput false false)) (ctl (.operated site))
  | .local (.operated site)=>.base (.pop (aux .valid) (ctl (.abort 0)) (ctl (.abort 0)) (afterOperation site))
  | .local (.clearPair i)=>.base (.pop (regRole ⟨i.val,by omega⟩) (pairNext i) (ctl (.clearPair i)) (ctl (.clearPair i)))
  | .local .decrementA=>.base (.pop (aux .aIndex) (ctl (.abort 0)) (ctl (.abort 0)) (ctl .decrementB))
  | .local .decrementB=>.base (.pop (aux .bIndex) (ctl .terms) (ctl (.abort 0)) (ctl .terms))
  | .local (.seedNeg den)=>.base (.push (reg .right den) den (if den then ctl (.operate .negate) else ctl (.seedNeg true)))
  | .local (.frameCoefficient den)=>.call (.frame (.coefficient den) 0)
      (if den then ctl (.frameCoefficient false) else ctl .tagCoefficient)
  | .local .tagCoefficient=>.base (.push (aux .prefixReverse) true (ctl (.clearCoefficient 0)))
  | .local (.clearCoefficient i)=>.base (.pop (regRole i) (coefficientNext i) (ctl (.clearCoefficient i)) (ctl (.clearCoefficient i)))
  | .local .finalTag=>.base (.pop (aux .prefixReverse) (ctl (.abort 0)) (ctl .finalEnd) (ctl (.finalField false)))
  | .local (.finalField den)=>.call (.field (.finish den) (F.active .tagPop (none,false))) (ctl (.finalValid den))
  | .local (.finalValid den)=>.base (.pop (aux .valid) (ctl (.abort 0)) (ctl (.abort 0))
      (if den then ctl (.finalFrame true) else ctl (.finalField true)))
  | .local (.finalFrame den)=>.call (.frame (.finish den) 0) (if den then ctl (.finalFrame false) else ctl .finalRowTag)
  | .local .finalRowTag=>.base (.push (aux .output) true (ctl (.clearFinalReg false)))
  | .local (.clearFinalReg den)=>.base (.pop (reg .left den)
      (if den then ctl .finalTag else ctl (.clearFinalReg true)) (ctl (.clearFinalReg den)) (ctl (.clearFinalReg den)))
  | .local .finalEnd=>.base (.peek (aux .prefixReverse) (ctl (.clearFinal 0)) (ctl (.abort 0)) (ctl (.abort 0)))
  | .local (.clearFinal i)=>.base (.pop (workRole i) (finalNext i) (ctl (.clearFinal i)) (ctl (.clearFinal i)))
  | .local (.abort i)=>.base (.pop (abortRole i) (abortNext i) (ctl (.abort i)) (ctl (.abort i)))
  | .local .done=>.base .halt
  | .rational pc=>SemiprimeD1StackValidationLink.instruction rational Label.rational (R.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field site pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack site) (Label.field site) (F.code pc)
  | .frame site pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack site) (Label.frame site) (SemiprimeD1StackFrame.code pc)
  | .read site pc=>
    let go:=Label.read site
    let cache:=readReg site
    match pc with
    | .copyArray=>.call (.copy (.reader site) 0) (go .copyIndex)
    | .copyIndex=>.call (.copy (.readIndex site) 0) (go .count)
    | .count=>.base (.pop (aux .readTodo) (go (.tag true)) (go .failed) (go (.tag false)))
    | .tag take=>.base (.pop (aux .reader) (go .missingReader) (go .missingReader) (go (.field take false)))
    | .field take den=>.call (.field (.read site den) (F.active .tagPop (none,false))) (go (.valid take den))
    | .valid take den=>.base (.pop (aux .valid) (go .failed) (go .failed)
        (if !den then go (.field take true) else if take then go .drainReader else go .clearSigned))
    | .clearSigned=>.base (.pop (reg cache false) (go .clearDen) (go .clearSigned) (go .clearSigned))
    | .clearDen=>.base (.pop (reg cache true) (go .count) (go .clearDen) (go .clearDen))
    | .drainReader=>.base (.pop (aux .reader) (go .drainTodo) (go .drainReader) (go .drainReader))
    | .drainTodo=>.base (.pop (aux .readTodo) (go .success) (go .drainTodo) (go .drainTodo))
    | .missingReader=>.base (.pop (aux .reader) (go .missingTodo) (go .missingReader) (go .missingReader))
    | .missingTodo=>.base (.pop (aux .readTodo) (go .zeroSigned) (go .missingTodo) (go .missingTodo))
    | .zeroSigned=>.base (.push (reg cache false) false (go .zeroDen))
    | .zeroDen=>.base (.push (reg cache true) true (go .success))
    | .success=>.base (.push (aux .valid) true (go .return))
    | .failed=>.base (.push (aux .valid) false (go .return))
    | .return=>.ret
  | .operation site pc=>
    let go:=Label.operation site
    let dest:=destination site
    match pc with
    | .copyInput right den=>.call (.copy (.input site right den) 0) (afterInput site right den)
    | .run=>.call (.rational (SemiprimeD1StackRationalOperation.localLabel .start (operation site) false false))
        (go (.clearDestination false))
    | .clearDestination den=>.base (.pop (reg dest den)
        (if den then go (.copyOutput false) else go (.clearDestination true)) (go (.clearDestination den)) (go (.clearDestination den)))
    | .copyOutput den=>.call (.copy (.output site den) 0) (if den then go .sign else go (.copyOutput true))
    | .sign=>.base (.pop (rational R.signOutput) (go .failed) (go (.writeSign false)) (go (.writeSign true)))
    | .writeSign bit=>.base (.push (reg dest false) bit (go (.clear 0)))
    | .clear i=>.base (.pop (rational (rationalRole i)) (operationNext site i) (go (.clear i)) (go (.clear i)))
    | .success=>.base (.push (aux .valid) true (go .return))
    | .failed=>.base (.push (aux .valid) false (go .return))
    | .return=>.ret
/-- Actual complete three-bank data view, with no omitted physical shadow. -/
def bank (r : R.Stack→List Bool) (registers : Reg×Bool→List Bool) (u : Aux→List Bool) : Stack→List Bool :=
  Sum.elim r (Sum.elim registers u)
/-- Original physical array/q words; every other controller field is empty. -/
def originalAux (array q : List Bool) : Aux→List Bool
  | .denominator=>array | .originalQ=>q | _=>[]
/-- Only array, actual unary q, and W are initially populated. -/
def input (array q width : List Bool) : Stack→List Bool :=
  bank (fun k=>if k=R.aux .template then width else []) (fun _=>[]) (originalAux array q)
/-- Honest prepared three-word front door, before all real parsing/counting/arithmetic. -/
def initial (array q width : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input array q width,[]⟩
/-- One fixed finite prepared-array source; no coefficient or mode program is supplied at runtime. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (aux .denominator) (aux .output) (ctl .start) program
/-- Every actual physical role is included. -/
theorem stack_card : Fintype.card Stack=58 := by decide
/-- Whole normalized-operation inclusion is physically injective. -/
theorem rational_injective : Function.Injective rational := Sum.inl_injective
/-- Every Boolean data and actual saved-return alphabet is fixed finite before all inputs. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Internal state has only finite flags and static literal labels. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackNormalizedInverse
