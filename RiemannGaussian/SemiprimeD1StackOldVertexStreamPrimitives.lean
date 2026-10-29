/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStream
/-! # Exact physical stream reads, copies, whole vertex calls and row splices -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamPrimitives
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
open SemiprimeD1StackProcedureTrace
namespace M
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end M
/-- Exact trace composition keeps arbitrary actual outer returns. -/
theorem join {m n : ℕ} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Literal pushes change exactly one physical word. -/
theorem push_run (pc next : Label) (k : Stack) (b : Bool) (before : Stack→List Bool)
    (hc : program pc=.base (.push k b next)) :
    Runs program 1 pc before next (Function.update before k (b::before k)):=
  one_base program _ _ _ _ _ hc rfl rfl
/-- Every dispatch reads and consumes the actual top bit. -/
theorem pop_run (pc empty low high : Label) (k : Stack) (before : Stack→List Bool) (xs : List Bool)
    (hc : program pc=.base (.pop k empty low high)) (hx : before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail):=by
  apply one_base program pc _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Real cleanup pays every byte and its final empty branch. -/
theorem drain_loop (pc next : Label) (k : Stack) (before : Stack→List Bool) (xs : List Bool)
    (hc : program pc=.base (.pop k next pc pc)) (hx : before k=xs) :
    Runs program (xs.length+1) pc before next (Function.update before k []):=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next pc pc k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next pc pc k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- Physical copy preserves its input and performs both restoration loops. -/
theorem copy_call (site : Copy) (pc next : Label)
    (hc : program pc=.call (.copy site 0) next) (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before (copyStack site 0)=xs) (hy : before (copyStack site 1)=ys) (hs : before (copyStack site 2)=[]) :
    Runs program (5*xs.length+4) pc before next (Function.update before (copyStack site 1) (xs++ys)):=by
  let source:=SemiprimeD1StackCopy.state 0 none xs ys []
  let out:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi : M.DataRel (copyStack site) before source.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=M.data_update (copyStack site) (copy_injective site) before source.store before hi (1 : Fin 3) (xs++ys)
  have he : Function.update source.store 1 (xs++ys)=out.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (Label.copy site) (copy_injective site) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hc (5*xs.length+3) source out before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Exact field read consumes its physical framing and writes a physical validity bit. -/
theorem field_call (site : Field) (pc next : Label)
    (hc : program pc=.call (.field site (P.active .tagPop (none,false))) next)
    (before : Stack→List Bool) (word tail : List Bool)
    (hi : before (fieldInput site)=SemiprimeSourceHistogramKeyBits.frame word tail)
    (ho : before (fieldOutput site)=[]) (hs : before (fieldWork (.inl .scratch))=[])
    (hv : before (fieldWork (.inr ()))=[]) :
    Runs program (8*word.length+7) pc before next
      (Function.update (Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word)
        (fieldWork (.inr ())) [true]):=by
  let source:=SemiprimeD1TensorTapeFieldBytecode.initial (SemiprimeSourceHistogramKeyBits.frame word tail) []
  let out : SemiprimeD1StackBytecode.State F.Stack P.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin : M.DataRel (fieldStack site) before source.store before:=by
    constructor
    · intro k
      rcases k with k|k
      · cases k
        · exact hi
        · exact hs
        · exact ho
      · exact hv
    · intro k _;rfl
  have h0:=M.data_update (fieldStack site) (field_injective site) before source.store before hin (.inl .input) tail
  have h1:=M.data_update (fieldStack site) (field_injective site) before _ _ h0 (.inl .output) word
  have h2:=M.data_update (fieldStack site) (field_injective site) before _ _ h1 (.inr ()) [true]
  have he : Function.update (Function.update (Function.update source.store (.inl .input) tail) (.inl .output) word)
      (.inr ()) [true]=out.store:=by
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · cases k;rfl
  rw [he] at h2
  exact included_call program (fieldStack site) (Label.field site) (field_injective site)
    P.code (P.active .tagPop (none,false)) (fun _=>rfl) pc next hc (8*word.length+6)
    source out before _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Real whole169 execution retains every foreign physical word and all actual return frames. -/
theorem vertex_call (time : ℕ) (source out : C.State ChoiceStack X.Label) (before after : Stack→List Bool)
    (he : source.pc=some (.local .start)) (hf : source.frames=[]) (hs : out.pc=none) (hrf : out.frames=[])
    (hr : SemiprimeD1StackCalls.run X.program time source=some out)
    (hin : M.DataRel choice before source.data before) (hout : M.DataRel choice before out.data after) :
    Runs program (time+1) (.local .vertex) before (.local .splice) after:=by
  exact SemiprimeD1StackProcedureCallsTrace.included_call program choice Label.vertex choice_injective
    X.program (.local .start) (fun _=>rfl) (.local .vertex) (.local .splice) rfl time source out before after
    he hf hs hrf hr hin hout
/-- Each new singleton is consumed without traversing the existing history tail. -/
theorem splice_call (before : Stack→List Bool) (row history : List Bool)
    (hr : before (choice X.output)=row++[false]) (hh : before (aux .history)=history) :
    Runs program (2*row.length+8) (.local .splice) before (.local .clearPorts)
      (Function.update (Function.update before (choice X.output) []) (aux .history) (row.reverse++history)):=by
  let source:=SemiprimeD1StackVertexRecordSplice.initial (row++[false]) history
  let out:=SemiprimeD1StackVertexRecordSplice.done (row.reverse++history)
  have hin : M.DataRel spliceStack before source.data before:=by
    constructor
    · intro k;fin_cases k
      · exact hr
      · exact hh
    · intro k _;rfl
  have h0:=M.data_update spliceStack splice_injective before source.data before hin (0 : Fin 2) []
  have h1:=M.data_update spliceStack splice_injective before _ _ h0 (1 : Fin 2) (row.reverse++history)
  have he : Function.update (Function.update source.data 0 []) 1 (row.reverse++history)=out.data:=by
    funext k;fin_cases k <;> rfl
  rw [he] at h1
  have h:=SemiprimeD1StackProcedureCallsTrace.included_call program spliceStack Label.splice splice_injective
    S.program (.local .start) (fun _=>rfl) (.local .splice) (.local .clearPorts) rfl
    (SemiprimeD1StackVertexRecordSplice.timeBound row) source out before _ rfl rfl rfl rfl
    (SemiprimeD1StackVertexRecordSpliceExecution.source_run row history) hin h1
  exact h
/-- Only the final reversal visits the complete accumulated history. -/
theorem reverse_call (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before (aux .history)=xs) (hy : before (aux .output)=ys) :
    Runs program (2*xs.length+3) (.local .reverse) before (.local .success)
      (Function.update (Function.update before (aux .history) []) (aux .output) (xs.reverse++ys)):=by
  let source:=SemiprimeD1StackReverseWord.state none xs ys
  let out:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hin : M.DataRel reverseStack before source.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=M.data_update reverseStack reverse_injective before source.store before hin (0 : Fin 2) []
  have h1:=M.data_update reverseStack reverse_injective before _ _ h0 (1 : Fin 2) (xs.reverse++ys)
  have he : Function.update (Function.update source.store 0 []) 1 (xs.reverse++ys)=out.store:=by
    funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program reverseStack Label.reverse reverse_injective SemiprimeD1StackReverseWord.code 0
    (fun _=>rfl) (.local .reverse) (.local .success) rfl (2*xs.length+2) source out before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hin h1
end RiemannGaussian.SemiprimeD1StackOldVertexStreamPrimitives
