/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PortOwnerArithmeticSpec
import RiemannGaussian.SemiprimeD1StackPortOwnerMaddBounds
import RiemannGaussian.SemiprimeD1StackUnaryDivmodBytecode
import RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
import RiemannGaussian.SemiprimeD1StackFrame
/-! # Literal complete arithmetic endpoint recipe source
Only physically parsed unary edge/metadata words enter this procedure. Static
finite labels call real Copy, multiply-plus-offset, unary division, comparison
and framing code. No numeric recipe, endpoint, evaluator or key is an opcode.
Original-N parsing/caller composition remains a separate explicit obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipe
namespace C
export SemiprimeD1StackCalls (Instruction State run step execute)
end C
namespace M
export SemiprimeD1StackPortOwnerMadd (Stack Label program)
end M
namespace D
export SemiprimeD1StackUnaryDivmodBytecode (Label code entry)
export SemiprimeD1StackUnaryDivmod (Stack)
end D
namespace L
export SemiprimeD1StackUnarySumLessBytecode (Label code entry)
export SemiprimeD1StackUnarySumLess (Stack)
end L
/-- Nine acquired readonly unary words; original N itself is never unary here. -/
inductive Input where | r | t | digits | half | tag | a | b | c | d
  deriving DecidableEq
instance : Fintype Input := Fintype.ofList [.r,.t,.digits,.half,.tag,.a,.b,.c,.d]
  (by intro k;cases k <;> simp)
/-- All intermediate coordinate words, three actual comparison bits and literal tags. -/
inductive Register where
  | mode (j:Fin 10) | rt | width | qa | ma | qb | mb | tc | rc | pbc
  | aminus | bminus | dminus | bplus | slot10 | slot11 | slot12 | wd
  | slot13f | slot13t | slot14t | slot14f | wb | divInput | testLeft | testLimit
  | smallA | ltArt | ltNext | tagReader
  deriving DecidableEq,Fintype
/-- Every real primitive scratch stack and final compact-key output. -/
inductive Aux where
  | copyScratch | multiplier | productScratch | maddScratch | divCopy | divScratch | frameScratch | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.copyScratch,.multiplier,.productScratch,.maddScratch,.divCopy,.divScratch,.frameScratch,.output]
  (by intro k;cases k <;> simp)
/-- One fixed finite Boolean register bank, independent of every family dimension. -/
abbrev Stack := Input⊕(Register⊕Aux)
/-- Literal input role inclusion. -/
def arg (k:Input) : Stack := .inl k
/-- Literal intermediate role inclusion. -/
def reg (k:Register) : Stack := .inr (.inl k)
/-- Literal scratch/output inclusion. -/
def aux (k:Aux) : Stack := .inr (.inr k)
/-- Fixed source/destination copy tasks; mode tasks construct their own literal tags. -/
inductive Copy where
  | mode (j:Fin 9) | rtWidth | aDiv | bDiv | tTc | cTc | rRc | cRc
  | aMinus | bMinus | digitsMinus | bPlus | widthWd | dWd | widthWb | bWb
  | aTest | twoLimit | rtLimit | nextTest | digitsLimit | tag
  deriving DecidableEq,Fintype
/-- Every fixed multiply-plus-offset call has distinct physical operands. -/
inductive Madd where | rt | pbc | slot10 | slot11 | slot12 | slot13f | slot13t | slot14t | slot14f
  deriving DecidableEq
instance : Fintype Madd := Fintype.ofList [.rt,.pbc,.slot10,.slot11,.slot12,.slot13f,.slot13t,.slot14t,.slot14f]
  (by intro k;cases k <;> simp)
/-- Actual strict comparisons, all executed before finite recipe dispatch. -/
inductive Check where | smallA | art | next deriving DecidableEq
instance : Fintype Check := Fintype.ofList [.smallA,.art,.next]
  (by intro k;cases k <;> simp)
/-- The eight actual original signal constructors. -/
inductive Tag where | input | first | twiddle | second | product | carry | digit | orOut
  deriving DecidableEq
instance : Fintype Tag := Fintype.ofList [.input,.first,.twiddle,.second,.product,.carry,.digit,.orOut]
  (by intro k;cases k <;> simp)
/-- Twenty-two finite branch results; no coordinate value occurs in these labels. -/
inductive Recipe where
  | inputSource | inputFirst | firstFirst | firstScale | twiddleScale | twiddleSecond
  | secondSecond | secondProduct | secondCarry | productProduct | productFirst
  | carryInitial | carryOut | carryPrevious | carryTerminal
  | digitInput | digitCheck | digitOrFirst | digitOrNew | orSource | orNext | orCheck
  deriving DecidableEq
instance : Fintype Recipe := Fintype.ofList [.inputSource,.inputFirst,.firstFirst,.firstScale,.twiddleScale,.twiddleSecond,.secondSecond,.secondProduct,.secondCarry,.productProduct,.productFirst,.carryInitial,.carryOut,.carryPrevious,.carryTerminal,.digitInput,.digitCheck,.digitOrFirst,.digitOrNew,.orSource,.orNext,.orCheck]
  (by intro k;cases k <;> simp)
/-- Every preserving copy reads and writes these literal fixed roles. -/
def copyOperands : Copy→Stack×Stack
  | .mode j=>(reg (.mode ⟨j.val,by omega⟩),reg (.mode ⟨j.val+1,by omega⟩))
  | .rtWidth=>(reg .rt,reg .width)
  | .aDiv=>(arg .a,reg .divInput) | .bDiv=>(arg .b,reg .divInput)
  | .tTc=>(arg .t,reg .tc) | .cTc=>(arg .c,reg .tc)
  | .rRc=>(arg .r,reg .rc) | .cRc=>(arg .c,reg .rc)
  | .aMinus=>(arg .a,reg .aminus) | .bMinus=>(arg .b,reg .bminus)
  | .digitsMinus=>(arg .digits,reg .dminus) | .bPlus=>(arg .b,reg .bplus)
  | .widthWd=>(reg .width,reg .wd) | .dWd=>(arg .d,reg .wd)
  | .widthWb=>(reg .width,reg .wb) | .bWb=>(arg .b,reg .wb)
  | .aTest=>(arg .a,reg .testLeft) | .twoLimit=>(reg (.mode 2),reg .testLimit)
  | .rtLimit=>(reg .rt,reg .testLimit) | .nextTest=>(reg .bplus,reg .testLeft)
  | .digitsLimit=>(reg .dminus,reg .testLimit) | .tag=>(arg .tag,reg .tagReader)
/-- Copy's source, destination and real scratch inclusion. -/
def copyStack (task:Copy) (k:Fin 3) : Stack :=
  if k=0 then (copyOperands task).1 else if k=1 then (copyOperands task).2 else aux .copyScratch
/-- Static three acquired operands and destination of each real Madd call. -/
def maddOperands : Madd→Stack×Stack×Stack×Stack
  | .rt=>(arg .r,arg .t,reg (.mode 0),reg .rt)
  | .pbc=>(arg .t,arg .c,arg .b,reg .pbc)
  | .slot10=>(reg .qb,reg .width,arg .c,reg .slot10)
  | .slot11=>(reg .tc,reg .width,arg .d,reg .slot11)
  | .slot12=>(arg .b,reg .width,arg .d,reg .slot12)
  | .slot13f=>(reg .rc,reg .width,arg .d,reg .slot13f)
  | .slot13t=>(arg .a,reg .width,arg .d,reg .slot13t)
  | .slot14t=>(reg .qa,reg .width,arg .b,reg .slot14t)
  | .slot14f=>(reg (.mode 2),reg .width,arg .b,reg .slot14f)
/-- Exact real Madd scratch inclusion; readonly operands and destination never alias. -/
def maddStack (task:Madd) : M.Stack→Stack
  | .inl .a=>(maddOperands task).1
  | .inl .b=>(maddOperands task).2.1
  | .inl .c=>(maddOperands task).2.2.1
  | .inr .multiplier=>aux .multiplier
  | .inr .productScratch=>aux .productScratch
  | .inr .copyScratch=>aux .maddScratch
  | .inr .output=>(maddOperands task).2.2.2
/-- Both actual divisions consume a real copy of a or b and retain the acquired r word. -/
def divideStack (second:Bool) : D.Stack→Stack
  | .input=>reg .divInput | .divisor=>arg .r | .copied=>aux .divCopy | .scratch=>aux .divScratch
  | .quotient=>if second then reg .qb else reg .qa
  | .remainder=>if second then reg .mb else reg .ma
/-- The actual unary comparator consumes both copied operands and writes one real bit. -/
def lessStack (check:Check) : L.Stack→Stack
  | .left=>reg .testLeft | .right=>reg (.mode 0) | .limit=>reg .testLimit
  | .valid=>reg (match check with | .smallA=>.smallA | .art=>.ltArt | .next=>.ltNext)
/-- Literal physical scalar fields selected after actual finite branch tests. -/
def fields : Recipe→Fin 6→Stack
  | .inputSource=>![arg .c,reg (.mode 0),arg .a,arg .b,reg (.mode 0),reg (.mode 0)]
  | .inputFirst=>![reg .slot10,reg (.mode 1),arg .a,reg .mb,reg (.mode 0),reg (.mode 0)]
  | .firstFirst=>![reg .slot11,reg (.mode 1),arg .a,arg .b,reg (.mode 0),reg (.mode 0)]
  | .firstScale=>![arg .d,reg (.mode 2),arg .a,arg .b,arg .c,reg (.mode 0)]
  | .twiddleScale=>![reg .wd,reg (.mode 2),arg .a,arg .b,arg .c,reg (.mode 0)]
  | .twiddleSecond=>![reg .slot12,reg (.mode 3),arg .a,arg .c,reg (.mode 0),reg (.mode 0)]
  | .secondSecond=>![reg .slot13f,reg (.mode 3),arg .a,arg .b,reg (.mode 0),reg (.mode 0)]
  | .secondProduct=>![reg .slot13t,reg (.mode 4),reg .pbc,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .secondCarry=>![arg .d,reg (.mode 6),reg .pbc,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .productProduct=>![reg .slot14f,reg (.mode 4),arg .a,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .productFirst=>![reg .slot14t,reg (.mode 1),reg (.mode 2),reg .ma,reg (.mode 0),reg (.mode 0)]
  | .carryInitial=>![arg .b,reg (.mode 5),reg (.mode 0),reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .carryOut=>![reg .slot14f,reg (.mode 6),reg .aminus,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .carryPrevious=>![reg .wb,reg (.mode 6),arg .a,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .carryTerminal=>![arg .b,reg (.mode 7),reg (.mode 0),reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .digitInput=>![reg .width,reg (.mode 0),arg .a,arg .b,reg (.mode 0),reg (.mode 0)]
  | .digitCheck=>![reg (.mode 0),reg (.mode 9),arg .a,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .digitOrFirst=>![reg (.mode 0),reg (.mode 8),arg .a,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
  | .digitOrNew=>![reg (.mode 1),reg (.mode 8),arg .a,reg .bminus,reg (.mode 0),reg (.mode 0)]
  | .orSource=>![reg (.mode 2),reg (.mode 8),arg .a,arg .b,reg (.mode 0),reg (.mode 0)]
  | .orNext=>![reg (.mode 0),reg (.mode 8),arg .a,reg .bplus,reg (.mode 0),reg (.mode 0)]
  | .orCheck=>![reg (.mode 0),reg (.mode 9),arg .a,reg (.mode 0),reg (.mode 0),reg (.mode 0)]
/-- Framing runs from field five to zero, retaining the sentinel as a literal suffix. -/
def frameStack (recipe:Recipe) (part:Fin 6) (k:Fin 3) : Stack :=
  if k=0 then fields recipe ⟨5-part.val,by omega⟩ else if k=1 then aux .output else aux .frameScratch
/-- All local labels are finite static syntax locations and computed Boolean branches. -/
inductive Control where
  | start | modeCopy (j:Fin 9) | modePush (j:Fin 9) | prepare (pc:Fin 41)
  | classify (j:Fin 18) | half (tag:Tag) | choose (tag:Tag) (half:Bool)
  | secondLimit | carryZero | carryLimit | digitZero | digitSize | orLimit
  | begin (recipe:Recipe) | emit (recipe:Recipe) (part:Fin 6) | halt | abort
  deriving Fintype
/-- All callees are literal finite code, including real nested Madd calls/returns. -/
inductive Label where
  | local (pc:Control) | copy (task:Copy) (pc:Fin 9) | madd (task:Madd) (pc:M.Label)
  | divide (second:Bool) (pc:D.Label) | less (check:Check) (pc:L.Label)
  | frame (recipe:Recipe) (part:Fin 6) (pc:Fin 11)
  deriving Fintype
/-- Static next preparation location, then literal tag acquisition. -/
def nextPrepare (pc:Fin 41) : Label :=
  if h:pc.val<40 then .local (.prepare ⟨pc.val+1,by omega⟩) else .local (.classify 0)
/-- Static original signal tag dispatch, after the actual unary tag word was consumed. -/
def tagEnd (j:Fin 18) : Label :=
  if j=10 then .local (.half .input) else if j=11 then .local (.half .first)
  else if j=12 then .local (.half .twiddle) else if j=13 then .local (.half .second)
  else if j=14 then .local (.half .product) else if j=15 then .local (.half .carry)
  else if j=16 then .local (.half .digit) else if j=17 then .local (.half .orOut) else .local .abort
/-- Every arithmetic operation below is a real call over actual cached words. -/
def program : Label→C.Instruction Stack Label
  | .copy task pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack task) (Label.copy task) (SemiprimeD1StackCopy.code pc)
  | .madd task pc=>SemiprimeD1StackValidationLink.instruction (maddStack task) (Label.madd task) (M.program pc)
  | .divide second pc=>SemiprimeD1StackMultiplierLink.instruction (divideStack second) (Label.divide second) (D.code pc)
  | .less check pc=>SemiprimeD1StackMultiplierLink.instruction (lessStack check) (Label.less check) (L.code pc)
  | .frame recipe part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack recipe part) (Label.frame recipe part) (SemiprimeD1StackFrame.code pc)
  | .local .start=>.base (.jump (.local (.modeCopy 0)))
  | .local (.modeCopy j)=>.call (.copy (.mode j) 0) (.local (.modePush j))
  | .local (.modePush j)=>.base (.push (reg (.mode ⟨j.val+1,by omega⟩)) true
      (if h:j.val<8 then .local (.modeCopy ⟨j.val+1,by omega⟩) else .local (.prepare 0)))
  | .local (.prepare pc)=>
      match pc.val with
      | 0=>.call (.madd .rt (.inl .start)) (nextPrepare pc)
      | 1=>.call (.copy .rtWidth 0) (nextPrepare pc)
      | 2=>.base (.push (reg .width) true (nextPrepare pc))
      | 3=>.call (.copy .aDiv 0) (nextPrepare pc)
      | 4=>.call (.divide false D.entry) (nextPrepare pc)
      | 5=>.call (.copy .bDiv 0) (nextPrepare pc)
      | 6=>.call (.divide true D.entry) (nextPrepare pc)
      | 7=>.call (.copy .tTc 0) (nextPrepare pc)
      | 8=>.call (.copy .cTc 0) (nextPrepare pc)
      | 9=>.call (.copy .rRc 0) (nextPrepare pc)
      | 10=>.call (.copy .cRc 0) (nextPrepare pc)
      | 11=>.call (.madd .pbc (.inl .start)) (nextPrepare pc)
      | 12=>.call (.copy .aMinus 0) (nextPrepare pc)
      | 13=>.base (.pop (reg .aminus) (nextPrepare pc) (nextPrepare pc) (nextPrepare pc))
      | 14=>.call (.copy .bMinus 0) (nextPrepare pc)
      | 15=>.base (.pop (reg .bminus) (nextPrepare pc) (nextPrepare pc) (nextPrepare pc))
      | 16=>.call (.copy .digitsMinus 0) (nextPrepare pc)
      | 17=>.base (.pop (reg .dminus) (nextPrepare pc) (nextPrepare pc) (nextPrepare pc))
      | 18=>.call (.copy .bPlus 0) (nextPrepare pc)
      | 19=>.base (.push (reg .bplus) true (nextPrepare pc))
      | 20=>.call (.madd .slot10 (.inl .start)) (nextPrepare pc)
      | 21=>.call (.madd .slot11 (.inl .start)) (nextPrepare pc)
      | 22=>.call (.madd .slot12 (.inl .start)) (nextPrepare pc)
      | 23=>.call (.copy .widthWd 0) (nextPrepare pc)
      | 24=>.call (.copy .dWd 0) (nextPrepare pc)
      | 25=>.call (.madd .slot13f (.inl .start)) (nextPrepare pc)
      | 26=>.call (.madd .slot13t (.inl .start)) (nextPrepare pc)
      | 27=>.call (.madd .slot14t (.inl .start)) (nextPrepare pc)
      | 28=>.call (.madd .slot14f (.inl .start)) (nextPrepare pc)
      | 29=>.call (.copy .widthWb 0) (nextPrepare pc)
      | 30=>.call (.copy .bWb 0) (nextPrepare pc)
      | 31=>.call (.copy .aTest 0) (nextPrepare pc)
      | 32=>.call (.copy .twoLimit 0) (nextPrepare pc)
      | 33=>.call (.less .smallA L.entry) (nextPrepare pc)
      | 34=>.call (.copy .aTest 0) (nextPrepare pc)
      | 35=>.call (.copy .rtLimit 0) (nextPrepare pc)
      | 36=>.call (.less .art L.entry) (nextPrepare pc)
      | 37=>.call (.copy .nextTest 0) (nextPrepare pc)
      | 38=>.call (.copy .digitsLimit 0) (nextPrepare pc)
      | 39=>.call (.less .next L.entry) (nextPrepare pc)
      | 40=>.call (.copy .tag 0) (nextPrepare pc)
      | _=>.base .halt
  | .local (.classify j)=>.base (.pop (reg .tagReader) (tagEnd j)
      (if h:j.val<17 then .local (.classify ⟨j.val+1,by omega⟩) else .local .abort)
      (if h:j.val<17 then .local (.classify ⟨j.val+1,by omega⟩) else .local .abort))
  | .local (.half tag)=>.base (.peek (arg .half) (.local (.choose tag false))
      (.local (.choose tag true)) (.local (.choose tag true)))
  | .local (.choose tag half)=>
      match tag,half with
      | .input,false=>.base (.jump (.local (.begin .inputSource)))
      | .input,true=>.base (.jump (.local (.begin .inputFirst)))
      | .first,false=>.base (.jump (.local (.begin .firstFirst)))
      | .first,true=>.base (.jump (.local (.begin .firstScale)))
      | .twiddle,false=>.base (.jump (.local (.begin .twiddleScale)))
      | .twiddle,true=>.base (.jump (.local (.begin .twiddleSecond)))
      | .second,false=>.base (.jump (.local (.begin .secondSecond)))
      | .second,true=>.base (.jump (.local .secondLimit))
      | .product,false=>.base (.jump (.local (.begin .productProduct)))
      | .product,true=>.base (.jump (.local (.begin .productFirst)))
      | .carry,false=>.base (.jump (.local .carryZero))
      | .carry,true=>.base (.jump (.local .carryLimit))
      | .digit,false=>.base (.jump (.local (.begin .digitInput)))
      | .digit,true=>.base (.jump (.local .digitZero))
      | .orOut,false=>.base (.jump (.local (.begin .orSource)))
      | .orOut,true=>.base (.jump (.local .orLimit))
  | .local .secondLimit=>.base (.peek (reg .smallA) (.local .abort)
      (.local (.begin .secondCarry)) (.local (.begin .secondProduct)))
  | .local .carryZero=>.base (.peek (arg .a) (.local (.begin .carryInitial))
      (.local (.begin .carryOut)) (.local (.begin .carryOut)))
  | .local .carryLimit=>.base (.peek (reg .ltArt) (.local .abort)
      (.local (.begin .carryTerminal)) (.local (.begin .carryPrevious)))
  | .local .digitZero=>.base (.peek (arg .b) (.local .digitSize)
      (.local (.begin .digitOrNew)) (.local (.begin .digitOrNew)))
  | .local .digitSize=>.base (.peek (reg .dminus) (.local (.begin .digitCheck))
      (.local (.begin .digitOrFirst)) (.local (.begin .digitOrFirst)))
  | .local .orLimit=>.base (.peek (reg .ltNext) (.local .abort)
      (.local (.begin .orCheck)) (.local (.begin .orNext)))
  | .local (.begin recipe)=>.base (.push (aux .output) true (.local (.emit recipe 0)))
  | .local (.emit recipe part)=>.call (.frame recipe part 0)
      (if h:part.val<5 then .local (.emit recipe ⟨part.val+1,by omega⟩) else .local .halt)
  | .local .halt | .local .abort=>.base .halt
/-- Initial actual operands only; EVERY intermediate/tag/answer/output stack is empty. -/
def input (words:Input→List Bool) : Stack→List Bool := Sum.elim words (fun _=>[])
/-- Actual prepared parsed-record entry, with no key, coordinate answer or clock input. -/
def initial (words:Input→List Bool) : C.State Stack Label :=
  ⟨some (.local .start),none,none,input words,[]⟩
/-- One fixed finite internal machine, with literal Boolean alphabets on EVERY role. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (arg .r) (aux .output) (.local .start) program
/-- All physical alphabets, including every cache and return cell, are finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (arg .r) (aux .output) (.local .start) program
/-- No native Nat/list/expression/function/evaluator occurs in control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (arg .r) (aux .output) (.local .start) program
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipe
