/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationOriginal
import RiemannGaussian.SemiprimeD1StackPhaseGeometryOriginal
import RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
import RiemannGaussian.SemiprimeD1StackUnaryProduct
import RiemannGaussian.SemiprimeD1StackWordEqualExecution
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1RecoveryGridBits
/-! # Actual whole original recovery grid from five physical words
True geometry and acquired multiplicities drive a descending physical index
fold, independently of fitted rational values. Every coefficient operation is
the actual normalized/twice-fitted source. No slope, value, multiplicity,
geometry, operation stream or numeric dimension answer is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGrid
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRationalOperation (Stack Label program Op)
end R
namespace G
export SemiprimeD1StackPhaseGeometry (Stack Aux Label program)
end G
namespace D
export SemiprimeD1StackUnaryDivmod (Stack)
export SemiprimeD1StackUnaryDivmodBytecode (Label code entry)
end D
namespace P
export SemiprimeD1StackUnaryProduct (Stack Label code entry)
end P
namespace A
export SemiprimeD1StackAdder (Stack)
end A
namespace S
export SemiprimeD1StackSubtractor (Label code)
end S
namespace E
export SemiprimeD1StackWordEqual (Label code)
end E
namespace F
export SemiprimeD1StackWordFit (Label program)
end F
/-- Sixteen actual rational caches; each has a sign-prefixed numerator and unsigned denominator. -/
inductive Reg where | two | center | alpha | node | index | negative | numBase | denBase | numPower | denPower | reciprocal | slope | gridNum | gridDen | scalar | argument deriving DecidableEq,Repr
/-- Complete literal Reg inventory. -/
instance :Fintype Reg:=Fintype.ofList [.two,.center,.alpha,.node,.index,.negative,.numBase,.denBase,.numPower,.denPower,.reciprocal,.slope,.gridNum,.gridDen,.scalar,.argument] (by intro k;cases k <;> simp)
/-- Four original metadata/index tapes and twelve actual counter/framing/copy work words. -/
inductive Aux where | originalA | originalM | originalU | originalT | q | indexTemplate | todo | doubleWork | copyScratch | scan | powerTodo | repeatTodo | slopes | frameScratch | moveScratch | orderTodo deriving DecidableEq,Repr
/-- Complete literal Aux inventory. -/
instance :Fintype Aux:=Fintype.ofList [.originalA,.originalM,.originalU,.originalT,.q,.indexTemplate,.todo,.doubleWork,.copyScratch,.scan,.powerTodo,.repeatTodo,.slopes,.frameScratch,.moveScratch,.orderTodo] (by intro k;cases k <;> simp)
/-- All104 physical words, including both displaced geometry shadows and every arithmetic/cache word. -/
abbrev Stack:=R.Stack⊕(G.Aux⊕(D.Stack⊕(P.Stack⊕((Reg×Bool)⊕Aux))))
/-- Complete real rational-operation bank. -/
def rationalStack :R.Stack→Stack:=Sum.inl
/-- Every separately allocated geometry word, including two empty displaced shadows. -/
def geometryAux (k:G.Aux) :Stack:=.inr (.inl k)
/-- Six actual unary height-divider words. -/
def divisionStack (k:D.Stack) :Stack:=.inr (.inr (.inl k))
/-- Four actual multiplicity-product words. -/
def productStack (k:P.Stack) :Stack:=.inr (.inr (.inr (.inl k)))
/-- False selects an actual sign-prefixed numerator; true selects actual denominator bytes. -/
def reg (r:Reg) (den:Bool) :Stack:=.inr (.inr (.inr (.inr (.inl (r,den)))))
/-- Actual source and counter/scratch addresses. -/
def aux (k:Aux) :Stack:=.inr (.inr (.inr (.inr (.inr k))))
/-- Original physical width template directly aliases the real operation source's retained template. -/
def template :Stack:=rationalStack (SemiprimeD1StackRationalOperation.aux .template)
/-- Shared real subtractor/equality/rational ripple words, with all lifetimes serial. -/
def rippleStack (k:A.Stack) :Stack:=rationalStack (SemiprimeD1StackRationalOperation.adderStack k)
/-- Actual geometry: ripple words share cleared arithmetic, exponent/index directly alias the true source/counter. -/
def geometryStack :G.Stack→Stack
  | .inl k=>rippleStack k
  | .inr .exponent=>aux .originalA | .inr .index=>aux .q
  | .inr k=>geometryAux k
/-- Real index fitting uses the acquired a+2 template, independent of rational W. -/
def fitStack (k:Fin 5) :Stack:=if k=0 then aux .moveScratch else if k=1 then aux .indexTemplate
  else if k=2 then aux .orderTodo else if k=3 then aux .scan else reg .node false
/-- Four literal power uses; no base, result or exponent evaluator enters control. -/
inductive PowerSite where | center | alpha | numerator | denominator deriving DecidableEq,Repr
/-- Complete literal PowerSite inventory. -/
instance :Fintype PowerSite:=Fintype.ofList [.center,.alpha,.numerator,.denominator] (by intro k;cases k <;> simp)
/-- Actual power destination/accumulator cache. -/
def powerDestination :PowerSite→Reg
  | .center=>.center | .alpha=>.alpha | .numerator=>.numPower | .denominator=>.denPower
/-- Actual retained power base cache; accumulator is always the first multiply operand. -/
def powerBase :PowerSite→Reg
  | .center|.alpha=>.two | .numerator=>.numBase | .denominator=>.denBase
/-- Every power count is physically copied from original a or actual multiplicity. -/
def powerCount :PowerSite→Stack
  | .center|.alpha=>aux .originalA | .numerator|.denominator=>productStack .product
/-- Static rational operation sites are fixed before all original words. -/
inductive Site where
  | power (part:PowerSite) | negativeIndex | numeratorBase | denominatorBase | reciprocal | slope
  | numeratorFold | denominatorFold | scalarInverse | scalar | negativeNode | point | inverseAlpha | argument
  deriving Fintype
/-- Actual finite arithmetic entry for each fixed site. -/
def operation :Site→R.Op
  | .negativeIndex|.negativeNode=>.neg | .numeratorBase|.denominatorBase|.point=>.add
  | .reciprocal|.scalarInverse|.inverseAlpha=>.inv | _=>.mul
/-- Actual cached source operands, preserving both legacy multiplication orientations. -/
def operand (site:Site) (right:Bool) :Reg:=match site,right with
  | .power p,false=>powerDestination p | .power p,true=>powerBase p
  | .negativeIndex,_=>.index
  | .numeratorBase,false|.point,false=>.center
  | .numeratorBase,true|.denominatorBase,true|.point,true=>.negative
  | .denominatorBase,false|.negativeNode,_=>.node
  | .reciprocal,_=>.denBase
  | .slope,false|.inverseAlpha,_=>.alpha
  | .slope,true|.scalar,true|.argument,true=>.reciprocal
  | .numeratorFold,false=>.numPower | .numeratorFold,true|.scalar,false=>.gridNum
  | .denominatorFold,false=>.denPower | .denominatorFold,true|.scalarInverse,_=>.gridDen
  | .argument,false=>.numBase
/-- Actual cache overwritten only AFTER both inputs are physically acquired by R36. -/
def destination :Site→Reg
  | .power p=>powerDestination p | .negativeIndex|.negativeNode=>.negative
  | .numeratorBase|.point=>.numBase | .denominatorBase=>.denBase
  | .reciprocal|.scalarInverse|.inverseAlpha=>.reciprocal | .slope=>.slope
  | .numeratorFold=>.gridNum | .denominatorFold=>.gridDen | .scalar=>.scalar | .argument=>.argument
/-- True geometry-alpha initialization and actual decreasing binary-grid counter. -/
inductive Decrement where | initial | next deriving DecidableEq,Repr
/-- Complete literal Decrement inventory. -/
instance :Fintype Decrement:=Fintype.ofList [.initial,.next] (by intro k;cases k <;> simp)
/-- Two actual geometry cleanup continuations. -/
inductive ClearSite where | initial | row deriving DecidableEq,Repr
/-- Complete literal ClearSite inventory. -/
instance :Fintype ClearSite:=Fintype.ofList [.initial,.row] (by intro k;cases k <;> simp)
/-- Every actual copy route is static, with only finite register/site selection. -/
inductive Copy where
  | originalA | originalT | node | heightM | heightU | divisor | qOperand (part:Decrement) | qResult
  | equalQ | equalT | levels | order | height | power (part:PowerSite) | repeat | index
  | operationInput (site:Site) (right den:Bool) | operationOutput (site:Site) (den:Bool)
  deriving Fintype
/-- Source address of each genuinely paid preserving copy. -/
def copySource :Copy→Stack
  | .originalA=>aux .originalA | .originalT|.node|.equalT=>aux .originalT
  | .heightM=>aux .originalM | .heightU|.divisor|.levels=>aux .originalU
  | .qOperand .initial=>geometryAux .alpha | .qOperand .next|.equalQ|.index=>aux .q
  | .qResult=>rippleStack .output | .order=>geometryAux .order | .height=>divisionStack .quotient
  | .power p=>powerCount p | .repeat=>productStack .product
  | .operationInput site right den=>reg (operand site right) den
  | .operationOutput _ den=>rationalStack (SemiprimeD1StackRationalOperation.aux (if den then .denominatorOutput else .numeratorOutput))
/-- Acquired destination of each actual copy; no whole-store alias is used. -/
def copyTarget :Copy→Stack
  | .originalA=>aux .scan | .originalT|.qResult=>aux .q | .node=>aux .moveScratch
  | .heightM|.heightU=>divisionStack .input | .divisor=>divisionStack .divisor
  | .qOperand _|.equalQ=>rippleStack .left | .equalT=>rippleStack .right
  | .levels=>productStack .multiplicand | .order=>aux .orderTodo | .height=>productStack .multiplier
  | .power _=>aux .powerTodo | .repeat=>aux .repeatTodo | .index=>reg .index false
  | .operationInput _ right den=>rationalStack (SemiprimeD1StackRationalOperation.aux
      (if right then (if den then .rightDen else .rightSigned) else (if den then .leftDen else .leftSigned)))
  | .operationOutput site den=>reg (destination site) den
/-- Three distinct physical operands at every real copy call. -/
def copyStack (part:Copy) (k:Fin 3) :Stack:=if k=0 then copySource part else if k=1 then copyTarget part else aux .copyScratch
/-- Real preserving frames prepend one signed numerator/denominator slope record. -/
def frameStack (den:Bool) (k:Fin 3) :Stack:=if k=0 then reg .slope den else if k=1 then aux .slopes else aux .frameScratch
/-- Exactly the35 actual operation roles other than retained W; every allocated private word is physically visited. -/
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
/-- Every separately allocated geometry word, including two actual empty shadows, is physically visited. -/
def geometryRole (k:Fin 10) :G.Aux:=match k.val with
  | 0=>.exponent
  | 1=>.index
  | 2=>.counter
  | 3=>.center
  | 4=>.alpha
  | 5=>.sign
  | 6=>.zero
  | 7=>.order
  | 8=>.scan
  | _=>.scratch
/-- The16 transient rational words are cleared after each row and final argument construction. -/
def transientRole (k:Fin 16) :Stack:=match k.val with
  | 0=>reg .index false
  | 1=>reg .index true
  | 2=>reg .negative false
  | 3=>reg .negative true
  | 4=>reg .numBase false
  | 5=>reg .numBase true
  | 6=>reg .denBase false
  | 7=>reg .denBase true
  | 8=>reg .numPower false
  | 9=>reg .numPower true
  | 10=>reg .denPower false
  | 11=>reg .denPower true
  | 12=>reg .reciprocal false
  | 13=>reg .reciprocal true
  | 14=>reg .slope false
  | _=>reg .slope true
/-- Literal rational power loop; zero count returns unpadded literal oneWord even W0. -/
inductive PowerPhase where | clearSigned | clearDen | oneMagnitude | oneSign | oneDen | loop | multiply | done deriving DecidableEq,Repr
/-- Complete literal PowerPhase inventory. -/
instance :Fintype PowerPhase:=Fintype.ofList [.clearSigned,.clearDen,.oneMagnitude,.oneSign,.oneDen,.loop,.multiply,.done] (by intro k;cases k <;> simp)
/-- Literal source-operation stages, retaining no mathematical operand/result in control. -/
inductive OperationPhase where
  | copyInput (right den:Bool) | call | clearSigned | clearDen | save (den:Bool)
  | readSign | pushSign (negative:Bool) | clear (k:Fin 35) | done
  deriving Fintype
/-- Whole fixed grid-source phases, with only finite loop positions and just-read bits. -/
inductive Phase where
  | start | seed (k:Fin 15) | copyA | grow | indexBit | doubleDrain | doubleFirst | doubleSecond | doubleRestore | doubleSave
  | heightCheck | heightM (k:Fin 3) | heightU | minusOne | divisor | divide | clearRemainder | clearDivisor
  | node | fitNode | nodeSign | nodeDen | originalT | initialGeometry | initialClearPoint
  | decrement (part:Decrement) | subtractOne (part:Decrement) | subtract (part:Decrement) | borrow (part:Decrement)
  | clearQ (part:Decrement) | qResult (part:Decrement) | clearDifference (part:Decrement)
  | clearGeometry (part:ClearSite) (k:Fin 10)
  | powerCount (part:PowerSite) | alphaMarker | powerCall (part:PowerSite)
  | row | rowGeometry | rowClearPoint | center | equalQ | equalT | equal | equalRead
  | index | indexSign | indexDen | levels | order | subtractOrder | removeLevel | clearOrder | height | multiplicity | clearLevels
  | negative | numeratorBase | denominatorBase | reciprocal | slope | repeat | repeats | frameDen | frameSigned | frameTag
  | numeratorFold | denominatorFold | clearTransient (finish:Bool) (k:Fin 16) | clearMultiplicity | advance
  | scalarInverse | scalar | negativeNode | point | inverseAlpha | argument | clearFinalQ | done | abort
  deriving Fintype
/-- Every real callee, local stage and continuation symbol is fixed before original inputs. -/
inductive Label where
  | local (phase:Phase) | operation (site:Site) (phase:OperationPhase) | power (part:PowerSite) (phase:PowerPhase)
  | rational (pc:R.Label) | geometry (pc:G.Label) | division (pc:D.Label) | product (pc:P.Label)
  | copier (part:Copy) (pc:Fin 9) | frame (den:Bool) (pc:Fin 11)
  | equal (pc:E.Label) | subtract (pc:S.Label) | fit (pc:F.Label)
  deriving Fintype
local notation "ctl"=>Label.local
/-- Fifteen physical literal initializations include two, both right-fold oneWords, rowtodo2 and slope nil. -/
def seed (k:Fin 15) :Stack×Bool:=match k.val with
  | 0=>(aux .slopes,false)
  | 1=>(aux .todo,true)
  | 2=>(aux .todo,true)
  | 3=>(aux .indexTemplate,false)
  | 4=>(aux .indexTemplate,false)
  | 5=>(reg .two false,true)
  | 6=>(reg .two false,false)
  | 7=>(reg .two false,false)
  | 8=>(reg .two true,true)
  | 9=>(reg .gridNum false,true)
  | 10=>(reg .gridNum false,false)
  | 11=>(reg .gridNum true,true)
  | 12=>(reg .gridDen false,true)
  | 13=>(reg .gridDen false,false)
  | _=>(reg .gridDen true,true)
/-- One real arithmetic operation acquires operands before replacing an aliased cache, then clears every operation-private role. -/
def operationProgram (site:Site) :OperationPhase→C.Instruction Stack Label
  | .copyInput right den=>.call (.copier (.operationInput site right den) 0)
      (.operation site (if den then (if right then .call else .copyInput true false) else .copyInput right true))
  | .call=>.call (.rational (SemiprimeD1StackRationalOperation.localLabel .start (operation site) false false)) (.operation site .clearSigned)
  | .clearSigned=>.base (.pop (reg (destination site) false) (.operation site .clearDen) (.operation site .clearSigned) (.operation site .clearSigned))
  | .clearDen=>.base (.pop (reg (destination site) true) (.operation site (.save false)) (.operation site .clearDen) (.operation site .clearDen))
  | .save den=>.call (.copier (.operationOutput site den) 0) (.operation site (if den then .readSign else .save true))
  | .readSign=>.base (.pop (rationalStack SemiprimeD1StackRationalOperation.signOutput) (ctl .abort)
      (.operation site (.pushSign false)) (.operation site (.pushSign true)))
  | .pushSign negative=>.base (.push (reg (destination site) false) negative (.operation site (.clear 0)))
  | .clear k=>.base (.pop (rationalStack (rationalRole k))
      (if h:k.val<34 then .operation site (.clear ⟨k.val+1,by omega⟩) else .operation site .done)
      (.operation site (.clear k)) (.operation site (.clear k)))
  | .done=>.ret
/-- Actual repeated multiplication: literal one seed, actual unary-counter pop, accumulator FIRST/base SECOND, real returns. -/
def powerProgram (part:PowerSite) :PowerPhase→C.Instruction Stack Label
  | .clearSigned=>.base (.pop (reg (powerDestination part) false) (.power part .clearDen) (.power part .clearSigned) (.power part .clearSigned))
  | .clearDen=>.base (.pop (reg (powerDestination part) true) (.power part .oneMagnitude) (.power part .clearDen) (.power part .clearDen))
  | .oneMagnitude=>.base (.push (reg (powerDestination part) false) true (.power part .oneSign))
  | .oneSign=>.base (.push (reg (powerDestination part) false) false (.power part .oneDen))
  | .oneDen=>.base (.push (reg (powerDestination part) true) true (.power part .loop))
  | .loop=>.base (.pop (aux .powerTodo) (.power part .done) (ctl .abort) (.power part .multiply))
  | .multiply=>.call (.operation (.power part) (.copyInput false false)) (.power part .loop)
  | .done=>.ret
/-- Only four original metadata/index words and the physically supplied rational-width template are initialized. -/
def input (a M u t width:List Bool) :Stack→List Bool:=
  Sum.elim (fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then width else [])
    (Sum.elim (fun _=>[]) (Sum.elim (fun _=>[]) (Sum.elim (fun _=>[]) (Sum.elim (fun _=>[]) (fun k=>match k with
      | .originalA=>a | .originalM=>M | .originalU=>u | .originalT=>t | _=>[])))))
/-- All actual acquisition/geometry/multiplicity/index loops and exact descending grid fold execute here. -/
def mainProgram :Phase→C.Instruction Stack Label
  | .start=>.base (.jump (ctl (.seed 0)))
  | .seed k=>.base (.push (seed k).1 (seed k).2 (if h:k.val<14 then ctl (.seed ⟨k.val+1,by omega⟩) else ctl .copyA))
  | .copyA=>.call (.copier .originalA 0) (ctl .grow)
  | .grow=>.base (.pop (aux .scan) (ctl .heightCheck) (ctl .abort) (ctl .indexBit))
  | .indexBit=>.base (.push (aux .indexTemplate) false (ctl .doubleDrain))
  | .doubleDrain=>.base (.pop (aux .todo) (ctl .doubleRestore) (ctl .abort) (ctl .doubleFirst))
  | .doubleFirst=>.base (.push (aux .doubleWork) true (ctl .doubleSecond))
  | .doubleSecond=>.base (.push (aux .doubleWork) true (ctl .doubleDrain))
  | .doubleRestore=>.base (.pop (aux .doubleWork) (ctl .grow) (ctl .abort) (ctl .doubleSave))
  | .doubleSave=>.base (.push (aux .todo) true (ctl .doubleRestore))
  | .heightCheck=>.base (.peek (aux .originalU) (ctl .node) (ctl .abort) (ctl (.heightM 0)))
  | .heightM k=>.call (.copier .heightM 0) (if h:k.val<2 then ctl (.heightM ⟨k.val+1,by omega⟩) else ctl .heightU)
  | .heightU=>.call (.copier .heightU 0) (ctl .minusOne)
  | .minusOne=>.base (.pop (divisionStack .input) (ctl .abort) (ctl .abort) (ctl .divisor))
  | .divisor=>.call (.copier .divisor 0) (ctl .divide)
  | .divide=>.call (.division D.entry) (ctl .clearRemainder)
  | .clearRemainder=>.base (.pop (divisionStack .remainder) (ctl .clearDivisor) (ctl .clearRemainder) (ctl .clearRemainder))
  | .clearDivisor=>.base (.pop (divisionStack .divisor) (ctl .node) (ctl .clearDivisor) (ctl .clearDivisor))
  | .node=>.call (.copier .node 0) (ctl .fitNode)
  | .fitNode=>.call (.fit .start) (ctl .nodeSign)
  | .nodeSign=>.base (.push (reg .node false) false (ctl .nodeDen))
  | .nodeDen=>.base (.push (reg .node true) true (ctl .originalT))
  | .originalT=>.call (.copier .originalT 0) (ctl .initialGeometry)
  | .initialGeometry=>.call (.geometry .start) (ctl .initialClearPoint)
  | .initialClearPoint=>.base (.pop (rippleStack .output) (ctl (.decrement .initial)) (ctl .initialClearPoint) (ctl .initialClearPoint))
  | .decrement part=>.call (.copier (.qOperand part) 0) (ctl (.subtractOne part))
  | .subtractOne part=>.base (.push (rippleStack .right) true (ctl (.subtract part)))
  | .subtract part=>.call (.subtract (.start false)) (ctl (.borrow part))
  | .borrow part=>.base (.pop (rippleStack .output) (ctl .abort) (ctl (.clearQ part)) (ctl .abort))
  | .clearQ part=>.base (.pop (aux .q) (ctl (.qResult part)) (ctl (.clearQ part)) (ctl (.clearQ part)))
  | .qResult part=>.call (.copier .qResult 0) (ctl (.clearDifference part))
  | .clearDifference part=>.base (.pop (rippleStack .output) (if part=.initial then ctl (.clearGeometry .initial 0) else ctl .row) (ctl (.clearDifference part)) (ctl (.clearDifference part)))
  | .clearGeometry part k=>.base (.pop (geometryAux (geometryRole k)) (if h:k.val<9 then ctl (.clearGeometry part ⟨k.val+1,by omega⟩) else if part=.initial then ctl (.powerCount .center) else ctl .advance) (ctl (.clearGeometry part k)) (ctl (.clearGeometry part k)))
  | .powerCount part=>.call (.copier (.power part) 0) (if part=.alpha then ctl .alphaMarker else ctl (.powerCall part))
  | .alphaMarker=>.base (.push (aux .powerTodo) true (ctl (.powerCall .alpha)))
  | .powerCall part=>.call (.power part .clearSigned) (match part with | .center=>ctl (.powerCount .alpha) | .alpha=>ctl .row | .numerator=>ctl (.powerCount .denominator) | .denominator=>ctl .reciprocal)
  | .row=>.base (.pop (aux .todo) (ctl .scalarInverse) (ctl .abort) (ctl .rowGeometry))
  | .rowGeometry=>.call (.geometry .start) (ctl .rowClearPoint)
  | .rowClearPoint=>.base (.pop (rippleStack .output) (ctl .center) (ctl .rowClearPoint) (ctl .rowClearPoint))
  | .center=>.base (.peek (geometryAux .zero) (ctl .abort) (ctl .equalQ) (ctl (.clearTransient false 0)))
  | .equalQ=>.call (.copier .equalQ 0) (ctl .equalT)
  | .equalT=>.call (.copier .equalT 0) (ctl .equal)
  | .equal=>.call (.equal .loop) (ctl .equalRead)
  | .equalRead=>.base (.pop (rippleStack .output) (ctl .abort) (ctl .index) (ctl (.clearTransient false 0)))
  | .index=>.call (.copier .index 0) (ctl .indexSign)
  | .indexSign=>.base (.push (reg .index false) false (ctl .indexDen))
  | .indexDen=>.base (.push (reg .index true) true (ctl .levels))
  | .levels=>.call (.copier .levels 0) (ctl .order)
  | .order=>.call (.copier .order 0) (ctl .subtractOrder)
  | .subtractOrder=>.base (.pop (aux .orderTodo) (ctl .height) (ctl .abort) (ctl .removeLevel))
  | .removeLevel=>.base (.pop (productStack .multiplicand) (ctl .clearOrder) (ctl .abort) (ctl .subtractOrder))
  | .clearOrder=>.base (.pop (aux .orderTodo) (ctl .height) (ctl .clearOrder) (ctl .clearOrder))
  | .height=>.call (.copier .height 0) (ctl .multiplicity)
  | .multiplicity=>.call (.product P.entry) (ctl .clearLevels)
  | .clearLevels=>.base (.pop (productStack .multiplicand) (ctl .negative) (ctl .clearLevels) (ctl .clearLevels))
  | .negative=>.call (.operation .negativeIndex (.copyInput false false)) (ctl .numeratorBase)
  | .numeratorBase=>.call (.operation .numeratorBase (.copyInput false false)) (ctl .denominatorBase)
  | .denominatorBase=>.call (.operation .denominatorBase (.copyInput false false)) (ctl (.powerCount .numerator))
  | .reciprocal=>.call (.operation .reciprocal (.copyInput false false)) (ctl .slope)
  | .slope=>.call (.operation .slope (.copyInput false false)) (ctl .repeat)
  | .repeat=>.call (.copier .repeat 0) (ctl .repeats)
  | .repeats=>.base (.pop (aux .repeatTodo) (ctl .numeratorFold) (ctl .abort) (ctl .frameDen))
  | .frameDen=>.call (.frame true 0) (ctl .frameSigned)
  | .frameSigned=>.call (.frame false 0) (ctl .frameTag)
  | .frameTag=>.base (.push (aux .slopes) true (ctl .repeats))
  | .numeratorFold=>.call (.operation .numeratorFold (.copyInput false false)) (ctl .denominatorFold)
  | .denominatorFold=>.call (.operation .denominatorFold (.copyInput false false)) (ctl (.clearTransient false 0))
  | .clearTransient finish k=>.base (.pop (transientRole k) (if h:k.val<15 then ctl (.clearTransient finish ⟨k.val+1,by omega⟩) else if finish then ctl .clearFinalQ else ctl .clearMultiplicity) (ctl (.clearTransient finish k)) (ctl (.clearTransient finish k)))
  | .clearMultiplicity=>.base (.pop (productStack .product) (ctl (.clearGeometry .row 0)) (ctl .clearMultiplicity) (ctl .clearMultiplicity))
  | .advance=>.base (.peek (aux .todo) (ctl .scalarInverse) (ctl .abort) (ctl (.decrement .next)))
  | .scalarInverse=>.call (.operation .scalarInverse (.copyInput false false)) (ctl .scalar)
  | .scalar=>.call (.operation .scalar (.copyInput false false)) (ctl .negativeNode)
  | .negativeNode=>.call (.operation .negativeNode (.copyInput false false)) (ctl .point)
  | .point=>.call (.operation .point (.copyInput false false)) (ctl .inverseAlpha)
  | .inverseAlpha=>.call (.operation .inverseAlpha (.copyInput false false)) (ctl .argument)
  | .argument=>.call (.operation .argument (.copyInput false false)) (ctl (.clearTransient true 0))
  | .clearFinalQ=>.base (.pop (aux .q) (ctl .done) (ctl .clearFinalQ) (ctl .clearFinalQ))
  | .done|.abort=>.base .halt
/-- One fixed finite whole source; included instructions are literal actual subprograms. -/
def program :Label→C.Instruction Stack Label
  | .local pc=>mainProgram pc
  | .operation site pc=>operationProgram site pc
  | .power part pc=>powerProgram part pc
  | .rational pc=>SemiprimeD1StackValidationLink.instruction rationalStack Label.rational (R.program pc)
  | .geometry pc=>SemiprimeD1StackValidationLink.instruction geometryStack Label.geometry (G.program pc)
  | .division pc=>SemiprimeD1StackMultiplierLink.instruction divisionStack Label.division (D.code pc)
  | .product pc=>SemiprimeD1StackMultiplierLink.instruction productStack Label.product (P.code pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .frame den pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack den) (Label.frame den) (SemiprimeD1StackFrame.code pc)
  | .equal pc=>SemiprimeD1StackMultiplierLink.instruction rippleStack Label.equal (E.code pc)
  | .subtract pc=>SemiprimeD1StackMultiplierLink.instruction rippleStack Label.subtract (S.code pc)
  | .fit pc=>SemiprimeD1StackValidationLink.instruction fitStack Label.fit (F.program pc)
/-- Honest five-tape whole-grid front door. -/
def initial (a M u t width:List Bool) :C.State Stack Label:=⟨some (ctl .start),none,none,input a M u t width,[]⟩
/-- Genuine fixed finite source; a/M/u are actual unary metadata, t and all coefficients stay binary. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .originalA) (aux .slopes) (ctl .start) program
/-- Every original, cache, shadow, counter and arithmetic field is counted. -/
theorem stack_card :Fintype.card Stack=104:=by
  simp only [Stack,Fintype.card_sum,Fintype.card_prod]
  decide
/-- Complete actual rational bank has no alias collision. -/
theorem rational_injective :Function.Injective rationalStack:=Sum.inl_injective
/-- Shared actual ripple words remain four distinct roles. -/
theorem ripple_injective :Function.Injective rippleStack:=rational_injective.comp SemiprimeD1StackRationalOperation.adder_injective
/-- Geometry aliases retain true originala/currentq and share only the serial ripple bank. -/
theorem geometry_injective :Function.Injective geometryStack:=by decide
/-- Actual height-divider inclusion is injective. -/
theorem division_injective :Function.Injective divisionStack:=by intro a b h;exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
/-- Actual multiplicity-product inclusion is injective. -/
theorem product_injective :Function.Injective productStack:=by intro a b h;exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
/-- The five physical index-fit fields are distinct. -/
theorem fit_injective :Function.Injective fitStack:=by decide
/-- Both actual preserving slope frames have distinct physical operands. -/
theorem frame_injective (den:Bool) :Function.Injective (frameStack den):=by cases den <;> decide
/-- Finite control is fixed before all original inputs, grid dimensions and widths. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data and real continuation alphabet is finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryGrid
