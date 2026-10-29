/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidence
/-! # Real preserving copy and literal incidence-query operations -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidencePrimitives
open SemiprimeD1StackSourceIncidence
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Same literal program trace fragments compose with arbitrary actual caller return cells. -/
theorem join {m n:Nat} {pc mid finish:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between finish after) :
    Runs program (m+n) pc before finish after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- Every paid preserving-copy call changes only its actual destination. -/
theorem copy_call (part:Copy) (pc next:Label) (hc:program pc=.call (.copier part 0) next)
    (bank:Stack→List Bool) (hd:bank (copyStack part 1)=[]) (hs:bank (copyStack part 2)=[]) :
    Runs program (5*(bank (copyStack part 0)).length+4) pc bank next
      (Function.update bank (copyStack part 1) (bank (copyStack part 0))) :=by
  let before:=SemiprimeD1StackCopy.state 0 none (bank (copyStack part 0)) [] []
  let after:=SemiprimeD1StackCopy.done (bank (copyStack part 0)) (bank (copyStack part 0)++[])
  have hin:Link.DataRel (copyStack part) bank before.store bank:=by
    constructor
    · intro i;fin_cases i
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  apply included_call program (copyStack part) (Label.copier part) (copy_injective part)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*(bank (copyStack part 0)).length+3)
    before after _ _ rfl rfl (SemiprimeD1StackCopy.copy_words _ [] none) hin
  have h:=Link.data_update (copyStack part) (copy_injective part) bank before.store bank hin 1 (bank (copyStack part 0))
  have he:Function.update before.store 1 (bank (copyStack part 0))=after.store:=by
    dsimp only [after]
    rw [List.append_nil]
    funext i;fin_cases i <;> rfl
  simpa only [he] using h
/-- One literal local push preserves the entire other physical bank and all real outer returns. -/
theorem push_run (pc:Label) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program pc=.base (.push k b next)) :
    Runs program 1 pc before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One literal local pop consumes ONLYthe actual physical Boolean head. -/
theorem pop_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail) :=by
  apply one_base program pc _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Real EOF peek does not silently discard any remaining singleton-result bytes. -/
theorem peek_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.peek k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before :=by
  apply one_base program pc _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Every table/key/owner/row cleanup actually visits every byte and its final empty branch. -/
theorem drain_loop (pc:Label) (next:Label) (k:Stack)
    (hc:program pc=.base (.pop k next pc pc)) (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs) :
    Runs program (xs.length+1) pc before next (Function.update before k []) :=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next pc pc k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next pc pc k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- Actual four-role numeric equality consumes both copied operands and physically writes its comparison bit. -/
theorem equal_call (pc next:Label) (hc:program pc=.call (.equality .loop) next)
    (bank:Stack→List Bool) (hs:bank (aux .eqScratch)=[]) (ho:bank (aux .eqOutput)=[]) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime (bank (aux .eqLeft)) (bank (aux .eqRight))+1)
      pc bank next (Function.update (Function.update (Function.update bank (aux .eqLeft) []) (aux .eqRight) [])
        (aux .eqOutput) [decide (SemiprimeBitArithmetic.bitValue (bank (aux .eqLeft))=
          SemiprimeBitArithmetic.bitValue (bank (aux .eqRight)))]) :=by
  let left:=bank (aux .eqLeft)
  let right:=bank (aux .eqRight)
  let before:=SemiprimeD1StackWordEqual.state (some .loop) none left right []
  let after:=SemiprimeD1StackWordEqual.state none none [] []
    [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]
  have hin:Link.DataRel equalStack bank before.store bank:=by
    constructor
    · intro k;cases k
      · rfl
      · rfl
      · exact hs
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update equalStack equal_injective bank before.store bank hin (.left:A.Stack) []
  have h1:=Link.data_update equalStack equal_injective bank _ _ h0 (.right:A.Stack) []
  have h2:=Link.data_update equalStack equal_injective bank _ _ h1 (.output:A.Stack)
    [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]
  have he:Function.update (Function.update (Function.update before.store (.left:A.Stack) []) (.right:A.Stack) [])
      (.output:A.Stack) [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]=after.store:=by
    funext k;cases k <;> rfl
  rw [he] at h2
  exact included_call program equalStack Label.equality equal_injective Q.code .loop (fun _=>rfl) pc next hc
    (SemiprimeD1StackWordEqualExecution.executionTime left right) before after bank _ rfl rfl
    (SemiprimeD1StackWordEqualExecution.source_run left right none) hin h2
/-- Actual ripple addition consumes its copied total and actual selected term, with no supplied result. -/
theorem add_call (bank:Stack→List Bool) (hs:bank (aux .sumScratch)=[]) (ho:bank (aux .total)=[]) :
    Runs program (3*(max (bank (aux .sumLeft)).length (bank (aux .term)).length+1)+
      2*(SemiprimeBitArithmetic.addBits (bank (aux .sumLeft)) (bank (aux .term)) false).bits.length+3)
      .add bank (.clearKey true .owner)
      (Function.update (Function.update (Function.update bank (aux .sumLeft) []) (aux .term) [])
        (aux .total) (SemiprimeBitArithmetic.addBits (bank (aux .sumLeft)) (bank (aux .term)) false).bits) :=by
  let left:=bank (aux .sumLeft)
  let right:=bank (aux .term)
  let before:=SemiprimeD1StackAdder.state (some (.start false)) none left right [] []
  let after:=SemiprimeD1StackAdder.state none none [] [] [] (SemiprimeBitArithmetic.addBits left right false).bits
  have hin:Link.DataRel addStack bank before.store bank:=by
    constructor
    · intro k;cases k
      · rfl
      · rfl
      · exact hs
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update addStack add_injective bank before.store bank hin (.left:A.Stack) []
  have h1:=Link.data_update addStack add_injective bank _ _ h0 (.right:A.Stack) []
  have h2:=Link.data_update addStack add_injective bank _ _ h1 (.output:A.Stack) (SemiprimeBitArithmetic.addBits left right false).bits
  have he:Function.update (Function.update (Function.update before.store (.left:A.Stack) []) (.right:A.Stack) [])
      (.output:A.Stack) (SemiprimeBitArithmetic.addBits left right false).bits=after.store:=by
    funext k;cases k <;> rfl
  rw [he] at h2
  exact included_call program addStack Label.adder add_injective A.code (.start false) (fun _=>rfl)
    .add (.clearKey true .owner) rfl
    (3*(max left.length right.length+1)+2*(SemiprimeBitArithmetic.addBits left right false).bits.length+2)
    before after bank _ rfl rfl (SemiprimeD1StackAdderExecution.source_run left right false) hin h2
/-- Physical field parsing consumes each endpoint frame and produces a real validity singleton. -/
theorem parse_call (inner:Bool) (kind:Edge) (bank:Stack→List Bool) (word tail:List Bool)
    (hi:bank (fieldStack inner kind (.inl .input))=SemiprimeSourceHistogramKeyBits.frame word tail)
    (ho:bank (key inner kind)=[]) (hs:bank (aux .fieldScratch)=[]) (hv:bank (aux .valid)=[]) :
    Runs program (8*word.length+7) (.parse inner kind) bank (.valid inner kind)
      (Function.update (Function.update (Function.update bank (fieldStack inner kind (.inl .input)) tail)
        (key inner kind) word) (aux .valid) [true]) :=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (SemiprimeSourceHistogramKeyBits.frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack inner kind) bank before.store bank:=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hi
        · exact hs
        · exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update (fieldStack inner kind) (field_injective inner kind) bank before.store bank hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack inner kind) (field_injective inner kind) bank _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack inner kind) (field_injective inner kind) bank _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail) (.inl .output) word)
      (.inr ()) [true]=after.store:=by funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact included_call program (fieldStack inner kind) (Label.parser inner kind) (field_injective inner kind)
    Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) (.parse inner kind) (.valid inner kind) rfl
    (8*word.length+6) before after bank _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Complete real preserving environment lookup, including its own nested calls and actual return. -/
theorem lookup_call (kind:Edge) (side:Bool) (bank:Stack→List Bool)
    (ids:List (List Bool)) (chosen q pfx:List Bool)
    (hi:∀k,bank (environmentStack k)=(SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids chosen q pfx).data k) :
    ∃t≤201*(q.length+1)*((SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids).length+1)+1,
      Runs program t (.lookup kind side) bank (.readFound kind side)
        (Sum.elim (SemiprimeD1StackSourceEnvironmentExecution.lookupDone ids chosen q pfx).data (fun k=>bank (aux k))) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceEnvironmentExecution.lookup_run ids chosen q pfx
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program environmentStack Label.environment environment_injective
    E.program (.local .lookup) (fun _=>rfl) (.lookup kind side) (.readFound kind side) rfl t
    (SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids chosen q pfx)
    (SemiprimeD1StackSourceEnvironmentExecution.lookupDone ids chosen q pfx) bank _ rfl rfl rfl rfl hr
  · constructor
    · exact hi
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidencePrimitives
