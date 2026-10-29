/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScale
/-! # Literal public-scale copy and width-counted zero-padding traces
Every word in these theorems is the actual source stack content, never an
executing producer, expected result or clock operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScalePrimitives
open SemiprimeD1StackPublicScale SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact literal push on an actual stack. -/
theorem push (pc next : Label) (k : Stack) (b : Bool)
    (hc : program pc=.base (.push k b next)) (data : Stack→List Bool) :
    Runs program 1 pc data next (Function.update data k (b::data k)) := by
  apply one_base program pc next (.push k b next) _ _ hc <;> rfl
/-- Exact literal pop, selecting the actual EOF/Boolean branch. -/
theorem pop (pc empty low high : Label) (k : Stack)
    (hc : program pc=.base (.pop k empty low high)) (data : Stack→List Bool) :
    Runs program 1 pc data (SemiprimeD1StackBytecode.choose empty low high (data k).head?)
      (Function.update data k (data k).tail) := by
  apply one_base program pc _ (.pop k empty low high) _ _ hc <;> rfl
/-- Every preserving-copy call restores its actual source and pays all copied
bytes and restoration work. Destination/scratch freshness is a reached-state fact. -/
theorem copy_call (site : Fin 5) (pc next : Label) (hc : program pc=.call (.copy site 0) next)
    (data : Stack→List Bool) (hd : data (copyStack site 1)=[]) (hs : data (copyStack site 2)=[]) :
    Runs program (5*(data (copyStack site 0)).length+4) pc data next
      (Function.update data (copyStack site 1) (data (copyStack site 0))) := by
  let word:=data (copyStack site 0)
  have hin : Link.DataRel (copyStack site) data
      (SemiprimeD1StackCopy.state 0 none word [] []).store data := by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  have hout:=Link.data_update (copyStack site) (copy_injective site) _ _ _ hin (1:Fin 3) word
  have he : Function.update (SemiprimeD1StackCopy.state 0 none word [] []).store 1 word=
      (SemiprimeD1StackCopy.done word word).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply included_call program (copyStack site) (Label.copy site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none) hin hout
/-- Literal prepared padding state, only a proof view of the two physical stacks. -/
def padData (data : Stack→List Bool) (count word : List Bool) : Stack→List Bool :=
  Function.update (Function.update data (auxRole .padding) count) (dotStack I.rawRole) word
/-- Every original copied template cell is physically popped and creates one
false input cell. The numeric VALUE of the modulus is never traversed. -/
theorem zero_padding (data : Stack→List Bool) (count word : List Bool) :
    Runs program (2*count.length+1) .zeroPop (padData data count word) (.seed 0)
      (padData data [] (List.replicate count.length false++word)) := by
  induction count generalizing word with
  | nil=>
    have h:=pop .zeroPop (.seed 0) .zeroPush .zeroPush (auxRole .padding) rfl (padData data [] word)
    simpa [padData,auxRole,dotStack,I.rawRole,SemiprimeD1StackBytecode.choose,Function.update_comm] using h
  | cons b count ih=>
    have h0:=pop .zeroPop (.seed 0) .zeroPush .zeroPush (auxRole .padding) rfl (padData data (b::count) word)
    have h1:=push .zeroPush .zeroPop (dotStack I.rawRole) false rfl (padData data count word)
    have hc : Runs program 1 .zeroPop (padData data (b::count) word) .zeroPush (padData data count word) := by
      cases b <;> simpa [padData,auxRole,dotStack,I.rawRole,SemiprimeD1StackBytecode.choose,Function.update_comm] using h0
    have hp : Runs program 1 .zeroPush (padData data count word) .zeroPop (padData data count (false::word)) := by
      simpa [padData,auxRole,dotStack,I.rawRole,Function.update_comm] using h1
    have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ hc hp) (ih (false::word))
    have ht : 1+1+(2*count.length+1)=2*(b::count).length+1 := by simp only [List.length_cons];omega
    have hw : List.replicate count.length false++false::word=List.replicate (b::count).length false++word := by
      simp only [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append]
    simpa only [ht,hw] using h
/-- A whole output-word extraction on ACTUAL unread raw bytes and acquired width.
All fresh-work facts are reached physical-state equalities, not word answers. -/
theorem block_call (data : Stack→List Bool) (hc : data (blockStack 2)=[])
    (hs : data (blockStack 3)=[]) (ho : data (blockStack 4)=[]) :
    Runs program (SemiprimeD1StackWordBlockExecution.totalTime (data (blockStack 1))+1)
      .readOutput data .equal
      (Function.update (Function.update data (blockStack 0)
        ((data (blockStack 0)).drop (data (blockStack 1)).length)) (blockStack 4)
          (SemiprimeD1StackWordBlockExecution.result (data (blockStack 0)) (data (blockStack 1)))) := by
  let word:=data (blockStack 0)
  let cached:=data (blockStack 1)
  have hin : Link.DataRel blockStack data (W.initial word cached).data data := by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hc
      · exact hs
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update blockStack block_injective _ _ _ hin (0:Fin 5) (word.drop cached.length)
  have hout:=Link.data_update blockStack block_injective _ _ _ h0 (4:Fin 5) (SemiprimeD1StackWordBlockExecution.result word cached)
  have he : Function.update (Function.update (W.initial word cached).data 0 (word.drop cached.length)) 4
      (SemiprimeD1StackWordBlockExecution.result word cached)=(SemiprimeD1StackWordBlockExecution.done word cached).data := by
    funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply SemiprimeD1StackProcedureCallsTrace.included_call program blockStack Label.block block_injective
    W.program .start (fun _=>rfl) .readOutput .equal rfl (SemiprimeD1StackWordBlockExecution.totalTime cached)
    (W.initial word cached) (SemiprimeD1StackWordBlockExecution.done word cached)
    _ _ rfl rfl rfl rfl (SemiprimeD1StackWordBlockExecution.source_run word cached) hin hout
/-- Real numeric equality consumes both actual operands, leaves only its actual
singleton Boolean, and needs no canonicality or equality-result advice. -/
theorem equal_call (data : Stack→List Bool) (hs : data (equalStack .scratch)=[])
    (ho : data (equalStack .output)=[]) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime (data (equalStack .left)) (data (equalStack .right))+1)
      .equal data .done
      (Function.update (Function.update (Function.update data (equalStack .left) []) (equalStack .right) [])
        (equalStack .output) [decide (SemiprimeBitArithmetic.bitValue (data (equalStack .left))=
          SemiprimeBitArithmetic.bitValue (data (equalStack .right)))]) := by
  let left:=data (equalStack .left)
  let right:=data (equalStack .right)
  have hin : Link.DataRel equalStack data (SemiprimeD1StackWordEqual.state (some .loop) none left right []).store data := by
    constructor
    · intro k;cases k <;> first | rfl | exact hs | exact ho
    · intro k _;rfl
  have h0:=Link.data_update equalStack equal_injective _ _ _ hin SemiprimeD1StackAdder.Stack.left []
  have h1:=Link.data_update equalStack equal_injective _ _ _ h0 SemiprimeD1StackAdder.Stack.right []
  have hout:=Link.data_update equalStack equal_injective _ _ _ h1 SemiprimeD1StackAdder.Stack.output
    [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]
  have he : Function.update (Function.update (Function.update
      (SemiprimeD1StackWordEqual.state (some .loop) none left right []).store .left []) .right []) .output
        [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]=
      (SemiprimeD1StackWordEqual.state none none [] []
        [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]).store := by
    funext k;cases k <;> rfl
  rw [he] at hout
  apply included_call program equalStack Label.compare equal_injective E.code .loop (fun _=>rfl)
    .equal .done rfl (SemiprimeD1StackWordEqualExecution.executionTime left right)
    (SemiprimeD1StackWordEqual.state (some .loop) none left right [])
    (SemiprimeD1StackWordEqual.state none none [] []
      [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)])
    _ _ rfl rfl (SemiprimeD1StackWordEqualExecution.source_run left right none) hin hout
end RiemannGaussian.SemiprimeD1StackPublicScalePrimitives
