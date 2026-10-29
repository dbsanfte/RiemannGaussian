/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetScalarMulExecution
import RiemannGaussian.SemiprimeD1StackJetScalarAddExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1RecoveryStripBits
/-! # Literal signed dyadic stripping and precision-round scalar recovery
The only physical inputs are sign::binary magnitude, a positive binary
 denominator and an actual unary precision cache. Lost low one bits trigger a
REAL raw increment for negative nonintegral floor division. A literal Newton
loop executes three real modular products and one real modular sum per actual
precision marker. Neither quotient, valuation, inverse nor answer enters control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinish
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace M
export SemiprimeD1StackJetScalarMul (Stack Label program store reduceStack)
end M
namespace A
export SemiprimeD1StackJetScalarAdd (Stack Label program store)
end A
namespace Raw
export SemiprimeD1StackAdder (Stack Label code)
end Raw
namespace R
export SemiprimeD1StackReduce (Label code)
end R
/-- Three original/saved-sign fields and fifteen actual work/cache words. -/
inductive Aux where
  | numerator | denominator | sign | numeratorWork | denominatorWork | content | lost | todo
  | inverseInput | negative | two | current | numeratorResidue | signedResidue | product | opposite | correction | copyScratch
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList
  [.numerator,.denominator,.sign,.numeratorWork,.denominatorWork,.content,.lost,.todo,.inverseInput,
    .negative,.two,.current,.numeratorResidue,.signedResidue,.product,.opposite,.correction,.copyScratch]
  (by intro k;cases k <;> simp)
/-- All35 allocated roles include the unused private scalar-add width shadow. -/
abbrev Stack:=M.Stack⊕(A.Stack⊕Aux)
/-- Literal whole11-role modular multiplier inclusion. -/
def main:M.Stack→Stack:=Sum.inl
/-- Literal allocated six-role modular-adder shadow bank. -/
def addWork (k:A.Stack):Stack:=.inr (.inl k)
/-- Actual original/cache/work address. -/
def aux (k:Aux):Stack:=.inr (.inr k)
/-- The actual unary WIDTH is shared by the real modular arithmetic operators. -/
def width:Stack:=main (.inr false)
/-- The actual final compact residue, kept in the real multiplier's output role. -/
def output:Stack:=main (M.reduceStack .output)
/-- Actual first multiplier input address. -/
def mulLeft:Stack:=main (.inl SemiprimeD1StackMultiplier.input)
/-- Actual second multiplier input address. -/
def mulRight:Stack:=main (.inl SemiprimeD1StackMultiplier.factor)
/-- Scalar-add WIDTH aliases actual multiplier WIDTH; its allocated shadow stays counted. -/
def addStack (k:A.Stack):Stack:=if k=.inr false then width else addWork k
/-- The existing multiplier's four reducer fields are reused before scalar multiplication begins. -/
def reduceStack (k:Raw.Stack):Stack:=main (M.reduceStack k)
/-- The existing scalar-adder's four binary fields perform the full floor-rounding increment. -/
def rawStack (k:Raw.Stack):Stack:=addStack (.inl k)
/-- Five fixed product call sites, independent of every operand and precision value. -/
inductive MulSite where | product | opposite | update | signed | final deriving DecidableEq,Repr
instance:Fintype MulSite:=Fintype.ofList [.product,.opposite,.update,.signed,.final] (by intro k;cases k <;> simp)
/-- Twelve actual consuming transfers; both raw and modular output words are physically drained. -/
inductive MoveSite where
  | plain | roundingInput | rounded | residue | inverseInput | two | one | product | opposite | update | signed | correction
  deriving DecidableEq,Repr
instance:Fintype MoveSite:=Fintype.ofList
  [.plain,.roundingInput,.rounded,.residue,.inverseInput,.two,.one,.product,.opposite,.update,.signed,.correction]
  (by intro k;cases k <;> simp)
/-- Fixed physical transfer source. -/
def moveSource:MoveSite→Stack
  | .plain|.roundingInput=>aux .numeratorWork
  | .rounded|.correction=>rawStack .output
  | _=>output
/-- Fixed physical transfer destination. -/
def moveTarget:MoveSite→Stack
  | .plain|.rounded=>reduceStack .left
  | .roundingInput=>rawStack .left
  | .residue=>aux .numeratorResidue
  | .inverseInput=>aux .inverseInput
  | .two=>aux .two
  | .one|.update=>aux .current
  | .product=>aux .product
  | .opposite=>aux .opposite
  | .signed=>aux .signedResidue
  | .correction=>aux .correction
/-- The actual cached left operand of each literal modular-product site. -/
def multiplyLeft:MulSite→Stack
  | .product=>aux .inverseInput
  | .opposite|.signed=>aux .negative
  | .update=>aux .current
  | .final=>aux .signedResidue
/-- The actual cached right operand of each literal modular-product site. -/
def multiplyRight:MulSite→Stack
  | .product|.final=>aux .current
  | .opposite=>aux .product
  | .update=>aux .correction
  | .signed=>aux .numeratorResidue
/-- Every nonfinal product replaces one physically cleared cache; the final result stays in multiplier output. -/
def multiplyTarget:MulSite→Stack
  | .product=>aux .product
  | .opposite=>aux .opposite
  | .update=>aux .current
  | .signed=>aux .signedResidue
  | .final=>output
/-- The fixed consuming move used after each nonfinal modular product. -/
def multiplyMove:MulSite→MoveSite
  | .product=>.product | .opposite=>.opposite | .update=>.update | .signed=>.signed | .final=>.signed
/-- All actual preserving-copy sites are fixed before the three input words. -/
inductive Copy where
  | numerator | denominator | width | negative | todo | odd | addLeft | addRight | positive
  | mulLeft (site:MulSite) | mulRight (site:MulSite) | move (site:MoveSite)
  deriving DecidableEq,Fintype
/-- Fixed physical source of each actual preserving copy. -/
def copySource:Copy→Stack
  | .numerator=>aux .numerator | .denominator=>aux .denominator
  | .width|.negative|.todo=>width | .odd=>aux .denominatorWork
  | .addLeft=>aux .two | .addRight=>aux .opposite | .positive=>aux .numeratorResidue
  | .mulLeft site=>multiplyLeft site | .mulRight site=>multiplyRight site | .move site=>moveSource site
/-- Fixed physical destination of each actual preserving copy. -/
def copyTarget:Copy→Stack
  | .numerator=>aux .numeratorWork | .denominator=>aux .denominatorWork
  | .width=>reduceStack .right | .negative=>aux .negative | .todo=>aux .todo | .odd=>reduceStack .left
  | .addLeft=>rawStack .left | .addRight=>rawStack .right | .positive=>aux .signedResidue
  | .mulLeft _=>mulLeft | .mulRight _=>mulRight | .move site=>moveTarget site
/-- Real three-role preserving-copy map. -/
def copyStack (site:Copy) (k:Fin 3):Stack:=
  if k=0 then copySource site else if k=1 then copyTarget site else aux .copyScratch
/-- Every one of the sixteen actual helper/cache words is drained at the end. -/
def cleanup:List Aux:=[.sign,.numeratorWork,.denominatorWork,.content,.lost,.todo,.inverseInput,
  .negative,.two,.current,.numeratorResidue,.signedResidue,.product,.opposite,.correction,.copyScratch]
/-- Fixed finite cleanup address; no input-derived index occurs in runtime control. -/
def cleanupRole (part:Fin 16):Stack:=aux (cleanup.get part)
/-- Literal finite recovery, low-bit/lost-bit, Newton and final cleanup control. -/
inductive Control where
  | start | sign | signFalse | signTrue | content | copyDen
  | strip (lost:Bool) | zero (lost:Bool) | shift (lost:Bool) | odd (lost:Bool) | saveLost (lost:Bool)
  | signFloor | negativeFloor | plain | increment | rawOne | rawAdd | rounded
  | qWidth | qReduce | saveQ | oddInput | aWidth | aReduce | saveA | negativeWord
  | twoHigh | twoLow | twoWidth | twoReduce | saveTwo | one | oneWidth | oneReduce | saveOne | copyTodo
  | loop | roundProduct | roundOpposite | addLeft | addRight | add | clearCorrection | saveCorrection | roundUpdate
  | signChoice | positive | signed | final | clear (part:Fin 16) | done | abort | returning
  deriving DecidableEq,Fintype
/-- Only fixed finite roles/sites and actual finite return symbols inhabit control. -/
inductive Label where
  | local (pc:Control) | multiply (pc:M.Label) | add (pc:A.Label) | rawAdd (pc:Raw.Label) | reduce (pc:R.Label)
  | copy (site:Copy) (pc:Fin 9) | move (site:MoveSite) (clear:Bool) | mul (site:MulSite) (part:Fin 6) | drain (role:Stack)
  deriving DecidableEq,Fintype
local notation "ctl"=>Label.local
/-- One literal finite source; numeric operands and loop counters remain on actual Boolean tapes. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.copy .numerator 0) (ctl .sign)
  | .local .sign=>.base (.pop (aux .numeratorWork) (ctl .abort) (ctl .signFalse) (ctl .signTrue))
  | .local .signFalse=>.base (.push (aux .sign) false (ctl .content))
  | .local .signTrue=>.base (.push (aux .sign) true (ctl .content))
  | .local .content=>.base (.push (aux .content) true (ctl .copyDen))
  | .local .copyDen=>.call (.copy .denominator 0) (ctl (.strip false))
  | .local (.strip lost)=>.base (.pop (aux .denominatorWork) (ctl .abort) (ctl (.zero lost)) (ctl (.odd lost)))
  | .local (.zero lost)=>.base (.push (aux .content) false (ctl (.shift lost)))
  | .local (.shift lost)=>.base (.pop (aux .numeratorWork) (ctl (.strip lost)) (ctl (.strip lost)) (ctl (.strip true)))
  | .local (.odd lost)=>.base (.push (aux .denominatorWork) true (ctl (.saveLost lost)))
  | .local (.saveLost lost)=>.base (.push (aux .lost) lost (ctl .signFloor))
  | .local .signFloor=>.base (.peek (aux .sign) (ctl .abort) (ctl .plain) (ctl .negativeFloor))
  | .local .negativeFloor=>.base (.peek (aux .lost) (ctl .abort) (ctl .plain) (ctl .increment))
  | .local .plain=>.call (.move .plain false) (ctl .qWidth)
  | .local .increment=>.call (.move .roundingInput false) (ctl .rawOne)
  | .local .rawOne=>.base (.push (rawStack .right) true (ctl .rawAdd))
  | .local .rawAdd=>.call (.rawAdd (.start false)) (ctl .rounded)
  | .local .rounded=>.call (.move .rounded false) (ctl .qWidth)
  | .local .qWidth=>.call (.copy .width 0) (ctl .qReduce)
  | .local .qReduce=>.call (.reduce .take) (ctl .saveQ)
  | .local .saveQ=>.call (.move .residue false) (ctl .oddInput)
  | .local .oddInput=>.call (.copy .odd 0) (ctl .aWidth)
  | .local .aWidth=>.call (.copy .width 0) (ctl .aReduce)
  | .local .aReduce=>.call (.reduce .take) (ctl .saveA)
  | .local .saveA=>.call (.move .inverseInput false) (ctl .negativeWord)
  | .local .negativeWord=>.call (.copy .negative 0) (ctl .twoHigh)
  | .local .twoHigh=>.base (.push (reduceStack .left) true (ctl .twoLow))
  | .local .twoLow=>.base (.push (reduceStack .left) false (ctl .twoWidth))
  | .local .twoWidth=>.call (.copy .width 0) (ctl .twoReduce)
  | .local .twoReduce=>.call (.reduce .take) (ctl .saveTwo)
  | .local .saveTwo=>.call (.move .two false) (ctl .one)
  | .local .one=>.base (.push (reduceStack .left) true (ctl .oneWidth))
  | .local .oneWidth=>.call (.copy .width 0) (ctl .oneReduce)
  | .local .oneReduce=>.call (.reduce .take) (ctl .saveOne)
  | .local .saveOne=>.call (.move .one false) (ctl .copyTodo)
  | .local .copyTodo=>.call (.copy .todo 0) (ctl .loop)
  | .local .loop=>.base (.pop (aux .todo) (ctl .signChoice) (ctl .abort) (ctl .roundProduct))
  | .local .roundProduct=>.call (.mul .product 0) (ctl .roundOpposite)
  | .local .roundOpposite=>.call (.mul .opposite 0) (ctl .addLeft)
  | .local .addLeft=>.call (.copy .addLeft 0) (ctl .addRight)
  | .local .addRight=>.call (.copy .addRight 0) (ctl .add)
  | .local .add=>.call (.add .start) (ctl .clearCorrection)
  | .local .clearCorrection=>.call (.drain (aux .correction)) (ctl .saveCorrection)
  | .local .saveCorrection=>.call (.move .correction false) (ctl .roundUpdate)
  | .local .roundUpdate=>.call (.mul .update 0) (ctl .loop)
  | .local .signChoice=>.base (.peek (aux .sign) (ctl .abort) (ctl .positive) (ctl .signed))
  | .local .positive=>.call (.copy .positive 0) (ctl .final)
  | .local .signed=>.call (.mul .signed 0) (ctl .final)
  | .local .final=>.call (.mul .final 0) (ctl (.clear 0))
  | .local (.clear part)=>.call (.drain (cleanupRole part))
      (if h:part.val<15 then ctl (.clear ⟨part.val+1,by omega⟩) else ctl .done)
  | .local .done|.local .abort=>.base .halt
  | .local .returning=>.ret
  | .move site false=>.call (.copy (.move site) 0) (.move site true)
  | .move site true=>.base (.pop (moveSource site) (ctl .returning) (.move site true) (.move site true))
  | .drain role=>.base (.pop role (ctl .returning) (.drain role) (.drain role))
  | .mul site part=>
    if part=0 then .call (.copy (.mulLeft site) 0) (.mul site 1)
    else if part=1 then .call (.copy (.mulRight site) 0) (.mul site 2)
    else if part=2 then .call (.multiply .start) (.mul site 3)
    else if part=3 then if site=.final then .ret else .call (.drain (multiplyTarget site)) (.mul site 4)
    else if part=4 then .call (.move (multiplyMove site) false) (.mul site 5)
    else .ret
  | .multiply pc=>SemiprimeD1StackValidationLink.instruction main Label.multiply (M.program pc)
  | .add pc=>SemiprimeD1StackValidationLink.instruction addStack Label.add (A.program pc)
  | .rawAdd pc=>SemiprimeD1StackMultiplierLink.instruction rawStack Label.rawAdd (Raw.code pc)
  | .reduce pc=>SemiprimeD1StackMultiplierLink.instruction reduceStack Label.reduce (R.code pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
/-- Exactly three actual input words; binary magnitudes and denominators are never expanded into unary. -/
def input (numerator denominator widthWord:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (fun _=>[]) (aux .numerator) numerator) (aux .denominator) denominator) width widthWord
/-- Actual three-word entry has every private/shadow/cache/result role empty. -/
def initial (numerator denominator widthWord:List Bool):C.State Stack Label:=
  ⟨some (ctl .start),none,none,input numerator denominator widthWord,[]⟩
/-- One fixed finite source, with honest prepared signed/binary/unary input configuration. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .numerator) output (ctl .start) program
/-- All35 actual roles include every alias shadow. -/
theorem stack_card:Fintype.card Stack=35:=by decide
/-- Real scalar-add mapping preserves every distinct underlying role. -/
theorem add_injective:Function.Injective addStack:=by decide
/-- Real raw increment uses four distinct scalar-add roles. -/
theorem raw_injective:Function.Injective rawStack:=by decide
/-- Real direct modular reductions use four distinct multiplier roles. -/
theorem reduce_injective:Function.Injective reduceStack:=by decide
/-- Every declared preserving-copy site has three distinct actual operands. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by
  cases site with
  | mulLeft site=>cases site <;> decide
  | mulRight site=>cases site <;> decide
  | move site=>cases site <;> decide
  | _=>decide
/-- Actual source control is fixed finite before every original integer or precision word. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every data and real-return alphabet is fixed finite before all operands. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRecoveryFinish
