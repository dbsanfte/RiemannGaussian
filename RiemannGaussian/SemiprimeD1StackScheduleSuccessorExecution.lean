/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleSuccessor

/-! # Exact six-stack schedule execution with real calls and returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1StackScheduleSuccessorExecution
open SemiprimeD1StackScheduleSuccessor SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
local notation "cpy" => (fun kind pc=>Sum.inr (kind,pc):CopyKind→Fin 9→Label)
/-- Concatenate actual traces of this one fixed schedule program. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=
  runs_trans program m n pc mid next before between after h g
/-- Actual number of pairwise scan instructions, including the final empty pop. -/
def halfTime : List Bool→Nat
  | [] => 1 | [_] => 2 | _::_::rest => 3+halfTime rest
/-- Complete clock of the actual program, including all four calls and halt. -/
def runTime (a u:List Bool) : Nat :=
  5*u.length+5*a.length+10*(u.length/2)+halfTime u+17
/-- Actual halt retains both parent words and both acquired child words. -/
def done (a u:List Bool) : C.State Stack Label :=
  ⟨none,none,none,result a u,[]⟩
/-- A real preserving-copy call, with every other stack retained literally. -/
theorem copy_call (kind:CopyKind) (pc next:Control)
    (hc:program (ctl pc)=.call (cpy kind 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copySource kind)=xs) (hy:before (copyTarget kind)=ys)
    (hz:before .scratch=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl next)
      (Function.update before (copyTarget kind) (xs++ys)) := by
  apply included_call program (copyStack kind) (cpy kind) (copyStack_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc
    (5*xs.length+3) (SemiprimeD1StackCopy.state 0 none xs ys [])
    (SemiprimeD1StackCopy.done xs (xs++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update before (copyTarget kind) (xs++ys) (copySource kind)=xs
        rw [Function.update_of_ne (by cases kind <;> decide),hx]
      · exact Function.update_self _ _ _
      · change Function.update before (copyTarget kind) (xs++ys) .scratch=[]
        rw [Function.update_of_ne (by cases kind <;> decide),hz]
    · intro k hk
      exact Function.update_of_ne (fun h=>hk 1 h.symm) _ _
/-- Identical emitted markers commute past an already accumulated unary block. -/
theorem marker_bump (n:Nat) (tail:List Bool) :
    List.replicate n true++true::tail=true::(List.replicate n true++tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,ih]
/-- The literal scan consumes two physical cells for every child marker.
The input marker bits may be arbitrary; no decoded length is consulted. -/
theorem half_run (reader a u q out:List Bool) :
    Runs program (halfTime reader) (ctl .half) (data a u reader [] q out)
      (ctl .exponent) (data a u [] [] (halfWord reader++q) out) := by
  induction reader using List.twoStepInduction generalizing q with
  | nil =>
    apply one_base program (ctl .half) (ctl .exponent)
      (.pop .reader (ctl .exponent) (ctl .second) (ctl .second)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | singleton b =>
    have h0 : Runs program 1 (ctl .half) (data a u [b] [] q out)
        (ctl .second) (data a u [] [] q out) := by
      apply one_base program (ctl .half) (ctl .second)
        (.pop .reader (ctl .exponent) (ctl .second) (ctl .second)) _ _ rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 (ctl .second) (data a u [] [] q out)
        (ctl .exponent) (data a u [] [] q out) := by
      apply one_base program (ctl .second) (ctl .exponent)
        (.pop .reader (ctl .exponent) (ctl .emit) (ctl .emit)) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    simpa [halfTime,halfWord] using join h0 h1
  | cons_cons b c reader ih _ =>
    have h0 : Runs program 1 (ctl .half) (data a u (b::c::reader) [] q out)
        (ctl .second) (data a u (c::reader) [] q out) := by
      apply one_base program (ctl .half) (ctl .second)
        (.pop .reader (ctl .exponent) (ctl .second) (ctl .second)) _ _ rfl
      · cases b <;> rfl
      · funext k;cases k <;> rfl
    have h1 : Runs program 1 (ctl .second) (data a u (c::reader) [] q out)
        (ctl .emit) (data a u reader [] q out) := by
      apply one_base program (ctl .second) (ctl .emit)
        (.pop .reader (ctl .exponent) (ctl .emit) (ctl .emit)) _ _ rfl
      · cases c <;> rfl
      · funext k;cases k <;> rfl
    have h2 : Runs program 1 (ctl .emit) (data a u reader [] q out)
        (ctl .half) (data a u reader [] (true::q) out) := by
      apply one_base program (ctl .emit) (ctl .half)
        (.push .nextLevels true (ctl .half)) _ _ rfl
      · rfl
      · funext k;cases k <;> rfl
    have h:=join (join (join h0 h1) h2) (ih (true::q))
    have hn:(b::c::reader).length/2=reader.length/2+1 := by
      simp only [List.length_cons];omega
    simpa only [halfTime,halfWord,hn,List.replicate_succ,List.cons_append,
      marker_bump] using h
/-- All four real copy invocations and the scan reach the literal final halt. -/
theorem source_trace (a u:List Bool) :
    Runs program (runTime a u-1) (ctl .start) (data a u [] [] [] [])
      (ctl .done) (result a u) := by
  have h0:=copy_call .levels .start .half rfl (data a u [] [] [] []) u [] rfl rfl rfl
  have he0:Function.update (data a u [] [] [] []) Stack.reader (u++[])=
      data a u u [] [] [] := by funext k;cases k <;> simp [data,Function.update]
  simp only [copyTarget] at h0
  rw [he0] at h0
  have h1:=half_run u a u [] []
  simp only [List.append_nil] at h1
  have h2:=copy_call .exponent .exponent .first rfl
    (data a u [] [] (halfWord u) []) a [] rfl rfl rfl
  have he2:Function.update (data a u [] [] (halfWord u) []) Stack.nextExponent (a++[])=
      data a u [] [] (halfWord u) a := by funext k;cases k <;> simp [data,Function.update]
  simp only [copyTarget] at h2
  rw [he2] at h2
  have h3:=copy_call .nextLevels .first .last rfl
    (data a u [] [] (halfWord u) a) (halfWord u) a rfl rfl rfl
  have he3:Function.update (data a u [] [] (halfWord u) a) Stack.nextExponent (halfWord u++a)=
      data a u [] [] (halfWord u) (halfWord u++a) := by funext k;cases k <;> rfl
  simp only [copyTarget] at h3
  rw [he3] at h3
  have h4:=copy_call .nextLevels .last .done rfl
    (data a u [] [] (halfWord u) (halfWord u++a)) (halfWord u) (halfWord u++a) rfl rfl rfl
  have he4:Function.update (data a u [] [] (halfWord u) (halfWord u++a)) Stack.nextExponent
      (halfWord u++(halfWord u++a))=result a u := by
    funext k;cases k <;> simp [Function.update,data,result,List.append_assoc]
  simp only [copyTarget] at h4
  rw [he4] at h4
  have ht:=join (join (join (join h0 h1) h2) h3) h4
  have hc:(((5*u.length+4+halfTime u)+(5*a.length+4))+
      (5*(halfWord u).length+4))+(5*(halfWord u).length+4)=runTime a u-1 := by
    simp only [halfWord,List.length_replicate,runTime];omega
  rw [hc] at ht
  exact ht
/-- The same fixed program halts after its own exact acquired-input clock. -/
theorem source_run (a u:List Bool) :
    SemiprimeD1StackCalls.run program (runTime a u) (initial a u)=some (done a u) := by
  obtain ⟨finish,hf,hs⟩:=source_trace a u [] (initial a u) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result a u) [] finish hs
  have ht:runTime a u=(runTime a u-1)+1 := by unfold runTime;omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackScheduleSuccessorExecution
