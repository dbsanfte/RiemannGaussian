/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalResources
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1RecoveryAffineBits
/-! # Actual original recovery affine array after the actual whole grid
Five physical words enter. The same whole Grid104 runs once; actual true
geometry and height determine retained q. All original framed slopes are
physically reversed by rows, then every original convolution product/add is
executed by real normalized/twice-fitted R36 calls, including zero extensions.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffine
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Q
export SemiprimeD1StackRecoveryGrid (Stack Label program input aux reg template rationalStack geometryStack geometryAux divisionStack productStack rationalRole geometryRole)
end Q
namespace R
export SemiprimeD1StackRationalOperation (Stack Label program aux signOutput)
end R
namespace G
export SemiprimeD1StackPhaseGeometry (Stack Label program)
end G
namespace P
export SemiprimeD1StackUnaryProduct (Stack Label code entry)
end P
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Eight additional actual retained/count/reader/array words, all empty before Grid104. -/
inductive Aux where | retainedQ | reader | reverseSlopes | array | nextArray | remaining | k | readTodo
  deriving DecidableEq,Repr
/-- Complete literal additional-role inventory. -/
instance :Fintype Aux:=Fintype.ofList [.retainedQ,.reader,.reverseSlopes,.array,.nextArray,.remaining,.k,.readTodo]
  (by intro slot;cases slot <;> simp)
/-- All112 allocated roles; proven-empty Grid work is borrowed serially and restored. -/
abbrev Stack:=Q.Stack⊕Aux
/-- Entire retained actual Grid104 bank, including every original, output and displaced shadow. -/
def grid:Q.Stack→Stack:=Sum.inl
/-- New actual retained affine-array/counter word. -/
def aux:Aux→Stack:=Sum.inr
/-- Actual original metadata/width word, readonly outside its acquired grid source. -/
def oldAux (k:SemiprimeD1StackRecoveryGrid.Aux):Stack:=grid (Q.aux k)
/-- Actual transient signed rational field borrowed from the cleared Grid register bank. -/
def reg (r:SemiprimeD1StackRecoveryGrid.Reg) (den:Bool):Stack:=grid (Q.reg r den)
/-- Actual R36 inclusion shares the same retained physical W template. -/
def rational (k:R.Stack):Stack:=grid (Q.rationalStack k)
/-- True geometry aliases actuala/currentt and the serial cleared ripple bank. -/
def geometry (k:G.Stack):Stack:=grid (Q.geometryStack k)
/-- Actual retained height divider word. -/
def height:Stack:=grid (Q.divisionStack .quotient)
/-- Actual unary-product role used ONLY for q acquisition. -/
def product (k:P.Stack):Stack:=grid (Q.productStack k)
/-- Zero, first-order and all-higher affine factor cases are finite control, not a numeric gap operand. -/
inductive Part where | unit | slope | zero deriving DecidableEq,Repr
/-- Literal finite factor-class inventory. -/
instance :Fintype Part:=Fintype.ofList [.unit,.slope,.zero] (by intro slot;cases slot <;> simp)
/-- Actual k decrement advances the finite affine coefficient class. -/
def nextPart:Part→Part | .unit=>.slope | .slope|.zero=>.zero
/-- Two real scalar operations per original convolution pair. -/
inductive Site where | product | sum deriving DecidableEq,Repr
/-- Literal finite operation-site inventory. -/
instance :Fintype Site:=Fintype.ofList [.product,.sum] (by intro slot;cases slot <;> simp)
/-- The finite R36 entry selected by the literal convolution stage. -/
def operation:Site→SemiprimeD1StackRationalOperation.Op | .product=>.mul | .sum=>.add
/-- Each actual operation reads the required FIRST/SECOND physical cache. -/
def operand:Site→Bool→SemiprimeD1StackRecoveryGrid.Reg
  | .product,false=>.numBase | .product,true=>.denBase | .sum,false=>.numPower | .sum,true=>.denPower
/-- The sum destination aliases its SECOND operand only after all four real input copies. -/
def destination:Site→SemiprimeD1StackRecoveryGrid.Reg | .product=>.numPower | .sum=>.denPower
/-- All preserving-copy sites are fixed before dimensions, slopes and coefficients. -/
inductive Copy where
  | originalT | levels | order | height | retained | slopes | count | index | array | readIndex
  | slope (den:Bool) | input (site:Site) (right den:Bool) | output (site:Site) (den:Bool)
  deriving DecidableEq,Repr,Fintype
/-- Actual source of a fixed restoring copy. -/
def copySource:Copy→Stack
  | .originalT=>oldAux .originalT | .levels=>oldAux .originalU
  | .order=>grid (Q.geometryAux .order) | .height=>height | .retained=>product .product
  | .slopes=>oldAux .slopes | .count=>aux .retainedQ | .index=>aux .remaining
  | .array=>aux .array | .readIndex=>aux .k | .slope den=>reg .slope den
  | .input site right den=>reg (operand site right) den
  | .output _ den=>rational (R.aux (if den then .denominatorOutput else .numeratorOutput))
/-- Actual empty target of a fixed restoring copy. -/
def copyTarget:Copy→Stack
  | .originalT=>oldAux .q | .levels=>product .multiplicand | .order=>oldAux .orderTodo
  | .height=>product .multiplier | .retained=>aux .retainedQ | .slopes|.array=>aux .reader
  | .count=>aux .remaining | .index=>aux .k | .readIndex=>aux .readTodo | .slope den=>reg .denBase den
  | .input _ right den=>rational (R.aux (if right then (if den then .rightDen else .rightSigned) else (if den then .leftDen else .leftSigned)))
  | .output site den=>reg (destination site) den
/-- Restoring-copy scratch is an actual empty Grid scratch word. -/
def copyStack (site:Copy) (k:Fin 3):Stack:=if k=0 then copySource site else if k=1 then copyTarget site else oldAux .copyScratch
/-- Forward/backward slope parser or zero-extended actual array-reader parser. -/
inductive Field where
  | slope (backward den:Bool) | coefficient (part:Part) (take den:Bool)
  deriving DecidableEq,Repr,Fintype
/-- Real parser input comes from the physically reached current tape. -/
def fieldInput:Field→Stack
  | .slope true _=>aux .reverseSlopes | .slope false _|.coefficient _ _ _=>aux .reader
/-- Real parser output is always an actual signed/magnitude cache word. -/
def fieldOutput:Field→Stack
  | .slope _ den=>reg .slope den | .coefficient _ _ den=>reg .numBase den
/-- All four parser operands are physical and distinct; validity is consumed by the caller. -/
def fieldStack (site:Field):F.Stack→Stack
  | .inl .input=>fieldInput site | .inl .scratch=>oldAux .frameScratch
  | .inl .output=>fieldOutput site | .inr ()=>oldAux .scan
/-- A slope row is prepended to the reversed catalogue; an output coefficient is prepended in descending i. -/
inductive Frame where | slope (den:Bool) | coefficient (den:Bool) deriving DecidableEq,Repr,Fintype
/-- Both actual frame sources retain their signed bytes and raw denominator padding. -/
def frameSource:Frame→Stack | .slope den=>reg .slope den | .coefficient den=>reg .denPower den
/-- The literal row-framing destination. -/
def frameTarget:Frame→Stack | .slope _=>aux .reverseSlopes | .coefficient _=>aux .nextArray
/-- Real Frame input/output/scratch map; tails are never recopied per row. -/
def frameStack (site:Frame) (k:Fin 3):Stack:=if k=0 then frameSource site else if k=1 then frameTarget site else oldAux .frameScratch
/-- Two physical reversals move a forward array without a free tail copy. -/
def reverseStack (second:Bool) (k:Fin 2):Stack:=
  if k=0 then (if second then oldAux .copyScratch else aux .nextArray)
  else if second then aux .array else oldAux .copyScratch
/-- Six actual old-word/factor/product fields are physically drained per inner pair. -/
def innerRole (i:Fin 6):Stack:=match i.val with
  | 0=>reg .numBase false | 1=>reg .numBase true | 2=>reg .denBase false
  | 3=>reg .denBase true | 4=>reg .numPower false | _=>reg .numPower true
/-- Literal physical zero seed is signFALSE, EMPTY numerator, denominatorONE. -/
def zeroSeed (den:Bool):Bool:=den
/-- The initial physical affine empty product is ALWAYS the singleton literal oneWord, including q0 and W0. -/
def oneArray:List Bool:=SemiprimeD1StackRecoveryGridView.slopeTape [SemiprimeJetBits.oneWord]
/-- All ten literal seed bytes are fixed before every input. -/
theorem oneArray_length:oneArray.length=10:=rfl
/-- Actual seed instruction order is the reverse of the fixed ten-byte output literal. -/
def seedByte (i:Fin 10):Bool:=oneArray.reverse[i.val]'(by rw [List.length_reverse,oneArray_length];exact i.isLt)
/-- Internal real operation phases; all four inputs are acquired before any aliased destination erase. -/
inductive OperationPhase where
  | copyInput (right den:Bool) | call | clearSigned | clearDen | save (den:Bool)
  | readSign | pushSign (negative:Bool) | clear (k:Fin 35) | done
  deriving DecidableEq,Repr,Fintype
/-- Entire literal finite source/geometry/counter/parser/convolution/cleanup control. -/
inductive Control where
  | start | ready | geometry | clearPoint | levels | order | subtractOrder | removeLevel | clearOrder | height | multiplyQ | clearLevels | retained | clearProduct | clearGeometry (i:Fin 10) | clearQ
  | copySlopes | seedReverse | reverseLoop | reverseEOF | field (site:Field) | valid (site:Field)
  | frame (site:Frame) | slopeTag | clearSlope (backward den:Bool)
  | seedArray (i:Fin 10) | slopeLoop | slopeEOF | seedNext | count | coefficientLoop | index
  | zeroDen | zeroSign | inner (part:Part) | readIndex (part:Part) | readCount (part:Part)
  | readTag (part:Part) (take:Bool) | clearReadWord (part:Part) (den:Bool) | clearReadTail (part:Part)
  | missingReader (part:Part) | missingTodo (part:Part) | missingDen (part:Part) | missingSign (part:Part)
  | factor (part:Part) | factorDen (part:Part) | factorMagnitude | factorSign
  | slopeFactor (den:Bool) | multiply (part:Part) | add (part:Part) | clearInner (part:Part) (i:Fin 6) | innerNext (part:Part)
  | coefficientTag | clearSum (den:Bool) | clearArray | move (second:Bool) | done | abort
  deriving DecidableEq,Repr,Fintype
/-- Every included real code and return label is fixed and finite before inputs. -/
inductive Label where
  | local (pc:Control) | grid (pc:Q.Label) | geometry (pc:G.Label) | product (pc:P.Label)
  | rational (pc:R.Label) | copy (site:Copy) (pc:Fin 9) | field (site:Field) (pc:F.Label)
  | frame (site:Frame) (pc:Fin 11) | reverse (second:Bool) (pc:Fin 4)
  | operation (site:Site) (pc:OperationPhase)
  deriving Fintype
local notation "ctl"=>Label.local
/-- Actual parser continuation after its TRUE-validity singleton is physically popped. -/
def afterField:Field→Label
  | .slope backward false=>ctl (.field (.slope backward true))
  | .slope false true=>ctl (.frame (.slope true))
  | .slope true true=>ctl .seedNext
  | .coefficient part take false=>ctl (.field (.coefficient part take true))
  | .coefficient part false true=>ctl (.clearReadWord part false)
  | .coefficient part true true=>ctl (.clearReadTail part)
/-- Exact physical frame order: denominator, signed numerator, then rowTRUE tag. -/
def afterFrame:Frame→Label
  | .slope true=>ctl (.frame (.slope false)) | .slope false=>ctl .slopeTag
  | .coefficient true=>ctl (.frame (.coefficient false)) | .coefficient false=>ctl .coefficientTag
/-- Actual normalized/twice-fitted scalar source, with both old destination fields and all35 private roles paid. -/
def operationProgram (site:Site):OperationPhase→C.Instruction Stack Label
  | .copyInput right den=>.call (.copy (.input site right den) 0)
      (.operation site (if den then (if right then .call else .copyInput true false) else .copyInput right true))
  | .call=>.call (.rational (SemiprimeD1StackRationalOperation.localLabel .start (operation site) false false)) (.operation site .clearSigned)
  | .clearSigned=>.base (.pop (reg (destination site) false) (.operation site .clearDen) (.operation site .clearSigned) (.operation site .clearSigned))
  | .clearDen=>.base (.pop (reg (destination site) true) (.operation site (.save false)) (.operation site .clearDen) (.operation site .clearDen))
  | .save den=>.call (.copy (.output site den) 0) (.operation site (if den then .readSign else .save true))
  | .readSign=>.base (.pop (rational R.signOutput) (ctl .abort) (.operation site (.pushSign false)) (.operation site (.pushSign true)))
  | .pushSign negative=>.base (.push (reg (destination site) false) negative (.operation site (.clear 0)))
  | .clear i=>.base (.pop (rational (Q.rationalRole i))
      (if h:i.val<34 then .operation site (.clear ⟨i.val+1,by omega⟩) else .operation site .done)
      (.operation site (.clear i)) (.operation site (.clear i)))
  | .done=>.ret
/-- ONE fixed whole source; no q, array coefficient, slope list, operation stream or native evaluator is supplied. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.grid (.local .start)) (ctl .ready)
  | .local .ready=>.call (.copy .originalT 0) (ctl .geometry)
  | .local .geometry=>.call (.geometry .start) (ctl .clearPoint)
  | .local .clearPoint=>.base (.pop (grid (SemiprimeD1StackRecoveryGrid.rippleStack .output)) (ctl .levels) (ctl .clearPoint) (ctl .clearPoint))
  | .local .levels=>.call (.copy .levels 0) (ctl .order)
  | .local .order=>.call (.copy .order 0) (ctl .subtractOrder)
  | .local .subtractOrder=>.base (.pop (oldAux .orderTodo) (ctl .height) (ctl .abort) (ctl .removeLevel))
  | .local .removeLevel=>.base (.pop (product .multiplicand) (ctl .clearOrder) (ctl .abort) (ctl .subtractOrder))
  | .local .clearOrder=>.base (.pop (oldAux .orderTodo) (ctl .height) (ctl .clearOrder) (ctl .clearOrder))
  | .local .height=>.call (.copy .height 0) (ctl .multiplyQ)
  | .local .multiplyQ=>.call (.product P.entry) (ctl .clearLevels)
  | .local .clearLevels=>.base (.pop (product .multiplicand) (ctl .retained) (ctl .clearLevels) (ctl .clearLevels))
  | .local .retained=>.call (.copy .retained 0) (ctl .clearProduct)
  | .local .clearProduct=>.base (.pop (product .product) (ctl (.clearGeometry 0)) (ctl .clearProduct) (ctl .clearProduct))
  | .local (.clearGeometry i)=>.base (.pop (grid (Q.geometryAux (Q.geometryRole i)))
      (if h:i.val<9 then ctl (.clearGeometry ⟨i.val+1,by omega⟩) else ctl .clearQ)
      (ctl (.clearGeometry i)) (ctl (.clearGeometry i)))
  | .local .clearQ=>.base (.pop (oldAux .q) (ctl .copySlopes) (ctl .clearQ) (ctl .clearQ))
  | .local .copySlopes=>.call (.copy .slopes 0) (ctl .seedReverse)
  | .local .seedReverse=>.base (.push (aux .reverseSlopes) false (ctl .reverseLoop))
  | .local .reverseLoop=>.base (.pop (aux .reader) (ctl .abort) (ctl .reverseEOF) (ctl (.field (.slope false false))))
  | .local .reverseEOF=>.base (.peek (aux .reader) (ctl (.seedArray 0)) (ctl .abort) (ctl .abort))
  | .local (.field site)=>.call (.field site (F.active .tagPop (none,false))) (ctl (.valid site))
  | .local (.valid site)=>.base (.pop (oldAux .scan) (ctl .abort) (ctl .abort) (afterField site))
  | .local (.frame site)=>.call (.frame site 0) (afterFrame site)
  | .local .slopeTag=>.base (.push (aux .reverseSlopes) true (ctl (.clearSlope false false)))
  | .local (.clearSlope backward den)=>.base (.pop (reg .slope den)
      (if den then (if backward then ctl .slopeLoop else ctl .reverseLoop) else ctl (.clearSlope backward true))
      (ctl (.clearSlope backward den)) (ctl (.clearSlope backward den)))
  | .local (.seedArray i)=>.base (.push (aux .array) (seedByte i)
      (if h:i.val<9 then ctl (.seedArray ⟨i.val+1,by omega⟩) else ctl .slopeLoop))
  | .local .slopeLoop=>.base (.pop (aux .reverseSlopes) (ctl .abort) (ctl .slopeEOF) (ctl (.field (.slope true false))))
  | .local .slopeEOF=>.base (.peek (aux .reverseSlopes) (ctl .done) (ctl .abort) (ctl .abort))
  | .local .seedNext=>.base (.push (aux .nextArray) false (ctl .count))
  | .local .count=>.call (.copy .count 0) (ctl .coefficientLoop)
  | .local .coefficientLoop=>.base (.pop (aux .remaining) (ctl .clearArray) (ctl .abort) (ctl .index))
  | .local .index=>.call (.copy .index 0) (ctl .zeroDen)
  | .local .zeroDen=>.base (.push (reg .denPower true) true (ctl .zeroSign))
  | .local .zeroSign=>.base (.push (reg .denPower false) false (ctl (.inner .unit)))
  | .local (.inner part)=>.call (.copy .array 0) (ctl (.readIndex part))
  | .local (.readIndex part)=>.call (.copy .readIndex 0) (ctl (.readCount part))
  | .local (.readCount part)=>.base (.pop (aux .readTodo) (ctl (.readTag part true)) (ctl .abort) (ctl (.readTag part false)))
  | .local (.readTag part take)=>.base (.pop (aux .reader) (ctl .abort) (ctl (.missingReader part)) (ctl (.field (.coefficient part take false))))
  | .local (.clearReadWord part den)=>.base (.pop (reg .numBase den)
      (if den then ctl (.readCount part) else ctl (.clearReadWord part true))
      (ctl (.clearReadWord part den)) (ctl (.clearReadWord part den)))
  | .local (.clearReadTail part)=>.base (.pop (aux .reader) (ctl (.factor part)) (ctl (.clearReadTail part)) (ctl (.clearReadTail part)))
  | .local (.missingReader part)=>.base (.pop (aux .reader) (ctl (.missingTodo part)) (ctl (.missingReader part)) (ctl (.missingReader part)))
  | .local (.missingTodo part)=>.base (.pop (aux .readTodo) (ctl (.missingDen part)) (ctl (.missingTodo part)) (ctl (.missingTodo part)))
  | .local (.missingDen part)=>.base (.push (reg .numBase true) true (ctl (.missingSign part)))
  | .local (.missingSign part)=>.base (.push (reg .numBase false) false (ctl (.factor part)))
  | .local (.factor .slope)=>.call (.copy (.slope false) 0) (ctl (.slopeFactor true))
  | .local (.factor part)=>.base (.push (reg .denBase true) true (ctl (.factorDen part)))
  | .local (.factorDen .unit)=>.base (.push (reg .denBase false) true (ctl .factorSign))
  | .local (.factorDen _)=>.base (.push (reg .denBase false) false (ctl (.multiply .zero)))
  | .local .factorMagnitude=>.base (.jump (ctl .factorSign))
  | .local .factorSign=>.base (.push (reg .denBase false) false (ctl (.multiply .unit)))
  | .local (.slopeFactor den)=>.call (.copy (.slope den) 0) (ctl (.multiply .slope))
  | .local (.multiply part)=>.call (.operation .product (.copyInput false false)) (ctl (.add part))
  | .local (.add part)=>.call (.operation .sum (.copyInput false false)) (ctl (.clearInner part 0))
  | .local (.clearInner part i)=>.base (.pop (innerRole i)
      (if h:i.val<5 then ctl (.clearInner part ⟨i.val+1,by omega⟩) else ctl (.innerNext part))
      (ctl (.clearInner part i)) (ctl (.clearInner part i)))
  | .local (.innerNext part)=>.base (.pop (aux .k) (ctl (.frame (.coefficient true))) (ctl .abort) (ctl (.inner (nextPart part))))
  | .local .coefficientTag=>.base (.push (aux .nextArray) true (ctl (.clearSum false)))
  | .local (.clearSum den)=>.base (.pop (reg .denPower den)
      (if den then ctl .coefficientLoop else ctl (.clearSum true)) (ctl (.clearSum den)) (ctl (.clearSum den)))
  | .local .clearArray=>.base (.pop (aux .array) (ctl (.move false)) (ctl .clearArray) (ctl .clearArray))
  | .local (.move second)=>.call (.reverse second 0) (if second then ctl (.clearSlope true false) else ctl (.move true))
  | .local .done|.local .abort=>.base .halt
  | .grid pc=>SemiprimeD1StackValidationLink.instruction grid Label.grid (Q.program pc)
  | .geometry pc=>SemiprimeD1StackValidationLink.instruction geometry Label.geometry (G.program pc)
  | .product pc=>SemiprimeD1StackMultiplierLink.instruction product Label.product (P.code pc)
  | .rational pc=>SemiprimeD1StackValidationLink.instruction rational Label.rational (R.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field site pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack site) (Label.field site) (F.code pc)
  | .frame site pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack site) (Label.frame site) (SemiprimeD1StackFrame.code pc)
  | .reverse second pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack second) (Label.reverse second) (SemiprimeD1StackReverseWord.code pc)
  | .operation site pc=>operationProgram site pc
/-- Honest whole source has exactly the original five acquired words; all new words are EMPTY. -/
def input (a M u t width:List Bool):Stack→List Bool:=Sum.elim (Q.input a M u t width) (fun _=>[])
/-- Whole source begins before actual Grid104, geometry, q, array or coefficient acquisition. -/
def initial (a M u t width:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input a M u t width,[]⟩
/-- ONE fixed genuine finite112-role source, independent of all original parameters and answers. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (oldAux .originalA) (aux .array) (ctl .start) program
/-- Every allocated source, cache, shadow, parser and coefficient role is counted. -/
theorem stack_card:Fintype.card Stack=112:=by simp only [Stack,Fintype.card_sum];decide
/-- All actual Boolean and saved-return alphabets are finite before the original inputs. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Finite control carries no index, coefficient, q, width, count, getter or evaluator. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryAffine
