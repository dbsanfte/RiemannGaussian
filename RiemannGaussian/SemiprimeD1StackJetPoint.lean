/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRoute
import RiemannGaussian.SemiprimeD1StackJetIndexEq
import RiemannGaussian.SemiprimeD1StackJetReadExecution
import RiemannGaussian.SemiprimeD1StackJetScalarMulExecution
import RiemannGaussian.SemiprimeD1StackJetScalarAddExecution

/-! # Fixed physical routed jet-coefficient controller
The two nested loops consume physical copies of the rank counter. Each candidate
pair calls the actual mixed-radix router, compares its acquired result with the
physical target index, and only then reads/multiplies/adds coefficient payloads.
No scalar/vector/routing result is an instruction argument. Context preparation
is a separate physical caller; correctness and time are separate obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackJetPoint
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace R
export SemiprimeD1StackJetRoute (Stack Label code control)
end R
namespace M
export SemiprimeD1StackJetScalarMul (Stack Label program reduceStack)
end M
namespace A
export SemiprimeD1StackJetScalarAdd (Stack Label program)
end A
namespace V
export SemiprimeD1StackJetRead (Stack Label program)
end V
namespace E
export SemiprimeD1StackJetIndexEq (Label code)
end E

/-- Constructive equality of literal finite statement locations. -/
def locationsDecidableEq {K L S : Type} (q : Turing.TM2.Stmt (fun _ : K => Bool) L S) :
    DecidableEq (SemiprimeD1StackFiniteControl.Locations q) :=
  match q with
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q =>
    letI := locationsDecidableEq q
    inferInstanceAs (DecidableEq (Unit ⊕ SemiprimeD1StackFiniteControl.Locations q))
  | .branch _ q r =>
    letI := locationsDecidableEq q
    letI := locationsDecidableEq r
    inferInstanceAs (DecidableEq (Unit ⊕ (SemiprimeD1StackFiniteControl.Locations q ⊕
      SemiprimeD1StackFiniteControl.Locations r)))
  | .goto _ | .halt => inferInstanceAs (DecidableEq Unit)

/-- Executable equality for compiled finite-control labels, without choice. -/
instance finiteControlLabelDecidableEq {K L S : Type} [DecidableEq L] [DecidableEq S]
    (p : L → Turing.TM2.Stmt (fun _ : K => Bool) L S) :
    DecidableEq (SemiprimeD1StackFiniteControl.Label p) := by
  letI : ∀l, DecidableEq (SemiprimeD1StackFiniteControl.Locations (p l)) :=
    fun l => locationsDecidableEq (p l)
  exact inferInstanceAs (DecidableEq ((l : L) × (S × SemiprimeD1StackFiniteControl.Locations (p l))))

/-- Persistent physical metadata/caches and literal reader/comparator workspace. -/
inductive Aux where
  | a | b | axes | rank | i | j | target | acc | reader | index | parser | skipped
  | valid | readCopy | eqRight | eqValid | eqScratch | addWork | copyWork
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList
  [.a,.b,.axes,.rank,.i,.j,.target,.acc,.reader,.index,.parser,.skipped,.valid,
   .readCopy,.eqRight,.eqValid,.eqScratch,.addWork,.copyWork]
  (by intro k; cases k <;> simp)

/-- Fixed finite data bank, every stack has Boolean alphabet. -/
abbrev Stack := R.Stack ⊕ (M.Stack ⊕ (SemiprimeD1StackAdder.Stack ⊕ Aux))
/-- Literal persistent/workspace address. -/
def aux (k : Aux) : Stack := .inr (.inr (.inr k))
/-- Literal multiplier-bank address. -/
def mulStack (k : M.Stack) : Stack := .inr (.inl k)
/-- Literal temporary addition-bank address. -/
def addBank (k : SemiprimeD1StackAdder.Stack) : Stack := .inr (.inr (.inl k))
/-- The actual linked multiplier's preserved precision cache. -/
def precision : Stack := mulStack (.inr false)
/-- Product output of the real modular scalar multiplier. -/
def product : Stack := mulStack (M.reduceStack .output)
/-- Newly acquired modular partial sum. -/
def newAcc : Stack := addBank .output

/-- Actual scalar-add aliases consume product and accumulator without a getter. -/
def addStack : A.Stack → Stack
  | .inl .left => product
  | .inl .right => aux .acc
  | .inl .scratch => addBank .scratch
  | .inl .output => newAcc
  | .inr false => precision
  | .inr true => aux .addWork

/-- Both actual readers share cleared workspace, preserving their own source cache. -/
def readStack (right : Bool) : V.Stack → Stack
  | .cache => aux (if right then .b else .a)
  | .reader => aux .reader
  | .index => aux .index
  | .parser => aux .parser
  | .skipped => aux .skipped
  | .output => mulStack (.inl (if right then SemiprimeD1StackMultiplier.factor else SemiprimeD1StackMultiplier.input))
  | .valid => aux .valid
  | .copy => aux .readCopy

/-- The comparator consumes the router's actual unary sum-index word. -/
def equalStack : SemiprimeD1StackAdder.Stack → Stack
  | .left => .inl .result
  | .right => aux .eqRight
  | .scratch => aux .eqScratch
  | .output => aux .eqValid

/-- Nine literal real-copy sites, all before the data-dependent run. -/
inductive Transfer where
  | rankI | rankJ | axes | routeI | routeJ | target | readI | readJ | accumulator
  deriving DecidableEq,Repr
instance : Fintype Transfer := Fintype.ofList
  [.rankI,.rankJ,.axes,.routeI,.routeJ,.target,.readI,.readJ,.accumulator]
  (by intro k; cases k <;> simp)
/-- Actual copy source. -/
def copySource : Transfer → Stack
  | .rankI | .rankJ => aux .rank
  | .axes => aux .axes
  | .routeI | .readI => aux .i
  | .routeJ | .readJ => aux .j
  | .target => aux .target
  | .accumulator => newAcc
/-- Actual copy destination. -/
def copyTarget : Transfer → Stack
  | .rankI => aux .i
  | .rankJ => aux .j
  | .axes => .inl .axes
  | .routeI => .inl .left
  | .routeJ => .inl .right
  | .target => aux .eqRight
  | .readI | .readJ => aux .index
  | .accumulator => aux .acc
/-- Actual copy inclusion, with a shared cleared scratch stack. -/
def copyStack (site : Transfer) (k : Fin 3) : Stack :=
  if k=0 then copySource site else if k=1 then copyTarget site else aux .copyWork

/-- Fixed finite nested-call program labels. -/
inductive Label where
  | start | outer | innerInit | inner | axesCopy | leftCopy | rightCopy | routeCall
  | routeDone | targetCopy | equalCall | equalDone | readLeftCopy | readLeftCall
  | readRightCopy | readRightCall | multiply | add | retain | clearNew | done
  | copy (site : Transfer) (pc : Fin 9)
  | route (pc : R.Label)
  | equal (pc : E.Label)
  | read (right : Bool) (pc : V.Label)
  | scalarMul (pc : M.Label)
  | scalarAdd (pc : A.Label)
  deriving DecidableEq,Fintype

/-- Actual fixed convolution-point machine, with physical nested loops and calls. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.copy .rankI 0) .outer
  | .outer => .base (.pop (aux .i) .done .innerInit .innerInit)
  | .innerInit => .call (.copy .rankJ 0) .inner
  | .inner => .base (.pop (aux .j) .outer .axesCopy .axesCopy)
  | .axesCopy => .call (.copy .axes 0) .leftCopy
  | .leftCopy => .call (.copy .routeI 0) .rightCopy
  | .rightCopy => .call (.copy .routeJ 0) .routeCall
  | .routeCall => .call (.route (R.control .copyLeft)) .routeDone
  | .routeDone => .base (.pop (.inl .valid) .inner .inner .targetCopy)
  | .targetCopy => .call (.copy .target 0) .equalCall
  | .equalCall => .call (.equal .loop) .equalDone
  | .equalDone => .base (.pop (aux .eqValid) .inner .inner .readLeftCopy)
  | .readLeftCopy => .call (.copy .readI 0) .readLeftCall
  | .readLeftCall => .call (.read false .start) .readRightCopy
  | .readRightCopy => .call (.copy .readJ 0) .readRightCall
  | .readRightCall => .call (.read true .start) .multiply
  | .multiply => .call (.scalarMul .start) .add
  | .add => .call (.scalarAdd .start) .retain
  | .retain => .call (.copy .accumulator 0) .clearNew
  | .clearNew => .base (.pop newAcc .inner .clearNew .clearNew)
  | .done => .base .halt
  | .copy site pc => SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site)
      (SemiprimeD1StackCopy.code pc)
  | .route pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.route (R.code pc)
  | .equal pc => SemiprimeD1StackMultiplierLink.instruction equalStack Label.equal (E.code pc)
  | .read right pc => SemiprimeD1StackValidationLink.instruction (readStack right) (Label.read right) (V.program pc)
  | .scalarMul pc => SemiprimeD1StackValidationLink.instruction mulStack Label.scalarMul (M.program pc)
  | .scalarAdd pc => SemiprimeD1StackValidationLink.instruction addStack Label.scalarAdd (A.program pc)

/-- Real compiled finite-stack target, with prepared physical caches and target index. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (aux .a) (aux .acc) Label.start program

/-- Prepared physical source data. Axes, rank, target and precision are words,
not native loop bounds; acquisition of the context is a separate caller. -/
def inputData (a b axes width rank target : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (fun _ => []) (aux .a) a) (aux .b) b)
      (aux .axes) axes) precision width) (aux .rank) rank) (aux .target) target

/-- Literal source entry, without a preloaded result, continuation or work value. -/
def initial (a b axes width rank target : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,inputData a b axes width rank target,[]⟩

/-- All component scalar-add registers remain physically distinct. -/
theorem addStack_injective : Function.Injective addStack := by decide
/-- Both literal vector-reader inclusions have distinct physical registers. -/
theorem readStack_injective (right : Bool) : Function.Injective (readStack right) := by cases right <;> decide
/-- The acquired-index comparator has distinct operand/work/result registers. -/
theorem equalStack_injective : Function.Injective equalStack := by decide
/-- Every literal copy site has distinct physical source, destination and scratch. -/
theorem copyStack_injective (site : Transfer) : Function.Injective (copyStack site) := by cases site <;> decide

end RiemannGaussian.SemiprimeD1StackJetPoint
