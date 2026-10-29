/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCountFields
/-! # Actual complete six-field scan acquires M=2E and the retained E tally -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackEdgeCountLoop
open SemiprimeD1StackEdgeCount SemiprimeD1StackEdgeCountFields
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Nonempty records are detected by peek only; a false empty-side marker is
preserved for the actual first Field call instead of being treated as EOF. -/
theorem peek_record (words : Record) (bank tail count wire : List Bool) :
    Runs program 1 (.inl .peekRecord) (data bank (record words tail) count [] [] [] wire)
      (.inl (.read 0)) (data bank (record words tail) count [] [] [] wire) := by
  apply one_base program _ _ (.peek .reader (.inl .done) (.inl (.read 0)) (.inl (.read 0))) _ _ rfl
  · cases hw : words 0 with
    | nil => simp [B.execute,SemiprimeD1StackDigitCount.data,record,frame,hw,SemiprimeD1StackBytecode.choose]
    | cons b bs => simp [B.execute,SemiprimeD1StackDigitCount.data,record,frame,hw,SemiprimeD1StackBytecode.choose]
  · rfl

/-- All three markers are physically pushed: TWO canonical occurrence markers
and ONE retained original-wire marker, only after six successful field rounds. -/
theorem push_markers (bank reader count wire : List Bool) :
    Runs program 3 (.inl .pushCount) (data bank reader count [] [] [] wire)
      (.inl .peekRecord) (data bank reader (true::true::count) [] [] [] (true::wire)) := by
  have h0 : Runs program 1 (.inl .pushCount) (data bank reader count [] [] [] wire)
      (.inl .pushSecond) (data bank reader (true::count) [] [] [] wire) := by
    apply one_base program _ _ (.push .count true (.inl .pushSecond)) _ _ rfl
    · rfl
    · funext k; cases k <;> simp [B.execute,SemiprimeD1StackDigitCount.data,Function.update]
  have h1 : Runs program 1 (.inl .pushSecond) (data bank reader (true::count) [] [] [] wire)
      (.inl .pushWire) (data bank reader (true::true::count) [] [] [] wire) := by
    apply one_base program _ _ (.push .count true (.inl .pushWire)) _ _ rfl
    · rfl
    · funext k; cases k <;> simp [B.execute,SemiprimeD1StackDigitCount.data,Function.update]
  have h2 : Runs program 1 (.inl .pushWire) (data bank reader (true::true::count) [] [] [] wire)
      (.inl .peekRecord) (data bank reader (true::true::count) [] [] [] (true::wire)) := by
    apply one_base program _ _ (.push .copyScratch true (.inl .peekRecord)) _ _ rfl
    · rfl
    · funext k; cases k <;> simp [B.execute,SemiprimeD1StackDigitCount.data,Function.update]
  exact (h0.trans h1).trans h2

/-- Actual executed transition sum for all complete records. -/
def loopTime : List Record→ℕ
  | [] => 1
  | word::words => 1+fieldsTime word+3+loopTime words

/-- All complete records are physically scanned, giving M=2E occurrence
markers and E wire markers. Neither payload maxima nor encoded values matter. -/
theorem loop_run (words : List Record) (bank count wire : List Bool) :
    Runs program (loopTime words) (.inl .peekRecord) (data bank (tape words []) count [] [] [] wire)
      (.inl .done) (data bank [] (List.replicate (2*words.length) true++count) [] [] []
        (List.replicate words.length true++wire)) := by
  induction words generalizing count wire with
  | nil =>
    change Runs program 1 (.inl .peekRecord) (data bank [] count [] [] [] wire)
      (.inl .done) (data bank [] count [] [] [] wire)
    apply one_base program _ _ (.peek .reader (.inl .done) (.inl (.read 0)) (.inl (.read 0))) _ _ rfl
    · rfl
    · rfl
  | cons word words ih =>
    have h0:=peek_record word bank (tape words []) count wire
    have h1:=fields_run word bank (tape words []) count wire
    have h2:=push_markers bank (tape words []) count wire
    have h3:=ih (true::true::count) (true::wire)
    have hh:=((h0.trans h1).trans h2).trans h3
    have hc : List.replicate (2*words.length) true++true::true::count=
        List.replicate (2*(word::words).length) true++count := by
      rw [List.length_cons,show 2*(words.length+1)=2*words.length+2 by omega,List.replicate_add,List.append_assoc]
      rfl
    have hw : List.replicate words.length true++true::wire=
        List.replicate (word::words).length true++wire := by
      rw [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [hc,hw] at hh
    exact hh

/-- Literal bytes pay all six field parses, payload drains, validity pops and
both occurrence pushes plus wire push; empty fields have actual header bytes. -/
theorem loopTime_le (words : List Record) : loopTime words≤10*(tape words []).length+1 := by
  induction words with
  | nil => simp [loopTime,tape]
  | cons word words ih =>
    simp only [loopTime,tape,List.foldr_cons,record_length] at ih ⊢
    unfold fieldsTime
    have hsum : ((List.finRange 6).map (fun i=>(word i).length)).sum=
      (word 0).length+(word 1).length+(word 2).length+(word 3).length+(word 4).length+(word 5).length := by
      simp [List.finRange_succ]
      omega
    rw [hsum]
    omega

/-- Whole count stage starts with the actual bank ONLY. -/
def totalTime (words : List Record) : ℕ := 5*(tape words []).length+4+loopTime words+1
/-- Actual full count-stage entry, retaining the source tape and both tallies. -/
theorem source_run (words : List Record) :
    C.run program (totalTime words) (initial (tape words []))=some (done (tape words []) words.length) := by
  have hh:=(copy_call (tape words [])).trans (loop_run words (tape words []) [] [])
  obtain ⟨finish,hfinish,hAt⟩:=hh [] (initial (tape words [])) ⟨rfl,rfl,rfl⟩
  unfold totalTime
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
  rcases hAt with ⟨hpc,hd,hframes⟩
  change C.step program finish=some _
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hd,hframes,done]
/-- Closed linear whole-tape count time, no supplied E/M/cardinality/width. -/
theorem totalTime_le (words : List Record) : totalTime words≤15*(tape words []).length+6 := by
  have h:=loopTime_le words
  unfold totalTime
  omega

end RiemannGaussian.SemiprimeD1StackEdgeCountLoop
