/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordPrimitives
/-! # Complete actual descriptor parsing, dispatch and Boolean-row acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordExecution
open SemiprimeD1StackBooleanDescriptorRecord SemiprimeD1StackBooleanDescriptorRecordEncoding
open SemiprimeD1StackBooleanDescriptorRecordView SemiprimeD1StackBooleanDescriptorRecordPrimitives
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- One actual field read plus its actual successful-validity pop. -/
theorem field_run (part : Fin 5) (base : R.Stack→List Bool) (w : Record) (tail : List Bool) :
    Runs program (8*(w part).length+8) (.local (.field part))
      (clean base (parsed part.val w) (suffix w part.val tail)) (nextField part)
      (clean base (parsed (part.val+1) w) (suffix w (part.val+1) tail)) := by
  have h0:=field_call part (clean base (parsed part.val w) (suffix w part.val tail))
    (w part) (suffix w (part.val+1) tail) (suffix_step w part tail)
    (by change (if part.val<part.val then w part else [])=[];simp) rfl rfl
  unfold clean at h0
  rw [update_reader,update_cache,parsed_step,update_valid] at h0
  have h1 : Runs program 1 (.local (.valid part))
      (data base (parsed (part.val+1) w) (suffix w (part.val+1) tail) [true] []) (nextField part)
      (clean base (parsed (part.val+1) w) (suffix w (part.val+1) tail)) := by
    apply one_base program (.local (.valid part)) (nextField part)
      (.pop (aux .valid) (.local .abort) (.local .abort) (nextField part)) _ _ rfl
    · rfl
    · exact update_valid _ _ _ _ _ _
  have h:=h0.trans h1
  simpa only [clean,Nat.add_assoc,show 7+1=8 from rfl] using h
/-- All five actual descriptor fields are acquired, including arbitrary caller suffixes. -/
theorem all_fields (base : R.Stack→List Bool) (w : Record) (tail : List Bool) :
    Runs program (8*mass w+40) (.local (.field 0))
      (clean base (fun _=>[]) (record w tail)) (.local .copyTag) (clean base w tail) := by
  have h0:=field_run 0 base w tail
  have h1:=field_run 1 base w tail
  have h2:=field_run 2 base w tail
  have h3:=field_run 3 base w tail
  have h4:=field_run 4 base w tail
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have hm:mass w=(w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+0)))):=rfl
  have ht:(8*(w 0).length+8)+((8*(w 1).length+8)+((8*(w 2).length+8)+
      ((8*(w 3).length+8)+(8*(w 4).length+8))))=8*mass w+40 := by omega
  rw [ht] at h
  change Runs program (8*mass w+40) (.local (.field 0))
    (clean base (parsed 0 w) (record w tail)) (.local .copyTag) (clean base (parsed 5 w) tail) at h
  have hz:parsed 0 w=fun _=>[]:=by funext k;simp [parsed]
  rw [parsed_end,hz] at h
  exact h
/-- Every unary constructor marker executes one real pop; EOF selects a literal finite branch. -/
theorem decode_run (n i : Nat) (hi:i+n<18) (base : R.Stack→List Bool) (w : Record) (tail : List Bool) :
    Runs program (n+1) (.local (.decode ⟨i,by omega⟩))
      (data base w tail [] (List.replicate n true)) (dispatch ⟨i+n,hi⟩) (clean base w tail) := by
  induction n generalizing i with
  | zero=>
    apply one_base program _ _ (.pop (aux .tagReader) (dispatch ⟨i,by omega⟩)
      (nextDecode ⟨i,by omega⟩) (nextDecode ⟨i,by omega⟩)) _ _ rfl
    · rfl
    · exact update_tagReader _ _ _ _ _ _
  | succ n ih=>
    have hit:i<17:=by omega
    have hc:program (.local (.decode ⟨i,by omega⟩))=.base (.pop (aux .tagReader) (dispatch ⟨i,by omega⟩)
      (.local (.decode ⟨i+1,by omega⟩)) (.local (.decode ⟨i+1,by omega⟩))):=by
        simp [program,nextDecode,hit]
    have h0:Runs program 1 (.local (.decode ⟨i,by omega⟩))
        (data base w tail [] (List.replicate (n+1) true)) (.local (.decode ⟨i+1,by omega⟩))
        (data base w tail [] (List.replicate n true)) := by
      apply one_base program _ _ (.pop (aux .tagReader) (dispatch ⟨i,by omega⟩)
        (.local (.decode ⟨i+1,by omega⟩)) (.local (.decode ⟨i+1,by omega⟩))) _ _ hc
      · rfl
      · change Function.update (data base w tail [] (List.replicate (n+1) true))
          (aux .tagReader) (List.replicate (n+1) true).tail=_
        simp only [List.replicate_succ,List.tail_cons]
        exact update_tagReader _ _ _ _ _ _
    have h1:=ih (i+1) (by omega)
    have he:(⟨i+1+n,by omega⟩:Fin 18)=⟨i+(n+1),hi⟩:=by
      apply Fin.ext
      change i+1+n=i+(n+1)
      omega
    rw [he] at h1
    simpa only [show 1+(n+1)=n+1+1 by omega] using h0.trans h1
/-- Exact clean halt, retaining all parsed fields, the unread descriptor suffix and scope bank. -/
def done (mode : SemiprimeD1StackBooleanEntry.Mode) (w : Record) (tail : List Bool)
    (scope : List (List Bool)) (hist out : List Bool) : C.State Stack Label :=
  ⟨none,none,none,clean (R.done mode scope hist out).data w tail,[]⟩
/-- Complete own source allowance: every parse, tag-copy/pop, nested row call and halt. -/
def timeBound (code : Fin 18) (w : Record) (mode : SemiprimeD1StackBooleanEntry.Mode)
    (scope : List (List Bool)) : Nat :=
  SemiprimeD1StackBooleanRecordExecution.timeBound mode scope+8*mass w+6*code.val+47
/-- The same fixed program physically reads the actual descriptor before selecting
the Boolean row. The hypotheses describe source bytes; no mode is passed to control. -/
theorem source_run (code : Fin 18) (w : Record) (tail : List Bool)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (htag:w 0=List.replicate code.val true)
    (hm:dispatch code=.local (.record mode)) (scope : List (List Bool)) (hist out : List Bool) :
    ∃t ≤ timeBound code w mode scope,
      C.run program t (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)=
        some (done mode w tail scope hist out) := by
  let base:=recordInput (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out
  have h0:=all_fields base w tail
  have h1:=copy_tag base w tail
  rw [htag,List.length_replicate] at h1
  have h2:=decode_run code.val 0 (by omega) base w tail
  have he:(⟨0+code.val,by omega⟩:Fin 18)=code:=by
    apply Fin.ext
    change 0+code.val=code.val
    omega
  rw [he,hm] at h2
  obtain ⟨t,ht,h3⟩:=record_call mode scope hist out tail w
  have h:=h0.trans (h1.trans (h2.trans h3))
  obtain ⟨finish,hr,ho⟩:=h []
    (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨(8*mass w+40)+((5*code.val+4)+((code.val+1)+(t+1)))+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases ho with ⟨hp,hd,hf⟩
    change C.step program finish=some (done mode w tail scope hist out)
    simp only [C.step,SemiprimeD1StackCalls.step,hp,Option.map_some,program,C.execute,hd,hf,done]
/-- Genuine finite-machine execution, with the actual descriptor as its source
and the acquired binary scope supplied by the explicit caller. -/
noncomputable def descriptorRecordInTime (code : Fin 18) (w : Record) (tail : List Bool)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (htag:w 0=List.replicate code.val true)
    (hm:dispatch code=.local (.record mode)) (scope : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out))
      (some (SemiprimeD1StackCalls.configuration (done mode w tail scope hist out))) (timeBound code w mode scope) := by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .reader) (.inl R.history) (.local (.field 0)) program
  have h:=source_run code w tail mode htag hm scope hist out
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordExecution
