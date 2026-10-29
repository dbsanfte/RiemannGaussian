/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleActive

/-! # Exact physical active-guard execution and acquisition of its verdict -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1StackScheduleActiveExecution
open SemiprimeD1StackScheduleActive SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Literal input encoding of the four bounded metadata counters. -/
def unaryWords (values:Param→Nat) : Param→List Bool := fun k=>List.replicate (values k) true
/-- Actual total retained operand bytes, not a caller-provided clock. -/
def volume (values:Param→Nat) : Nat := values .leaf+values .minimum+values .levels+values .edges
/-- Mathematical intended conjunction; this function is never an instruction operand. -/
def answer (values:Param→Nat) : Bool :=
  decide (values .leaf<values .edges ∧ values .minimum≤values .levels ∧ values .levels≤values .edges)
/-- Prepared physical input, containing no advised branch. -/
def start (values:Param→Nat) : C.State Stack Label :=
  ⟨some (ctl (.left .leaf)),none,none,data (unaryWords values) [] [] [] [],[]⟩
/-- All retained metadata and the acquired sole verdict at the actual halt. -/
def done (values:Param→Nat) : C.State Stack Label :=
  ⟨none,none,none,data (unaryWords values) [] [] [] [answer values],[]⟩
/-- Exact actual trace concatenation for this one literal program. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=
  runs_trans program m n pc mid next before between after h g
/-- A real preserving-copy call retains all other physical roles. -/
theorem copy_call (test:Test) (right:Bool) (pc next:Control)
    (hc:program (ctl pc)=.call (copyLabel test right 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (paramStack (operand test right))=xs)
    (hy:before (if right then Stack.limit else Stack.left)=ys) (hz:before .scratch=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl next)
      (Function.update before (if right then Stack.limit else Stack.left) (xs++ys)) := by
  apply included_call program (copyStack test right) (copyLabel test right)
    (copyStack_injective test right) SemiprimeD1StackCopy.code 0 (fun _=>rfl)
    (ctl pc) (ctl next) hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys)) before _
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
      · change Function.update before (if right then Stack.limit else Stack.left) (xs++ys)
          (paramStack (operand test right))=xs
        rw [Function.update_of_ne (by cases test <;> cases right <;> decide),hx]
      · exact Function.update_self _ _ _
      · change Function.update before (if right then Stack.limit else Stack.left) (xs++ys) .scratch=[]
        rw [Function.update_of_ne (by cases right <;> decide),hz]
    · intro k hk
      exact Function.update_of_ne (fun h=>hk 1 h.symm) _ _
/-- Actual left-operand acquisition from the retained metadata field. -/
theorem left_call (test:Test) (w:Param→List Bool) :
    Runs program (5*(w (operand test false)).length+4) (ctl (.left test)) (data w [] [] [] [])
      (ctl (.right test)) (data w (w (operand test false)) [] [] []) := by
  have hx:data w [] [] [] [] (paramStack (operand test false))=w (operand test false) := by
    cases operand test false <;> rfl
  have h:=copy_call test false (.left test) (.right test) rfl (data w [] [] [] [])
    (w (operand test false)) [] hx rfl rfl
  have he:Function.update (data w [] [] [] []) Stack.left (w (operand test false)++[])=
      data w (w (operand test false)) [] [] [] := by
    funext k;cases k <;> simp [data,Function.update]
  simpa only [Bool.false_eq_true,ite_false,he] using h
/-- Actual threshold acquisition into the consuming comparator. -/
theorem right_call (test:Test) (w:Param→List Bool) :
    Runs program (5*(w (operand test true)).length+4) (ctl (.right test))
      (data w (w (operand test false)) [] [] []) (ctl (.compare test))
      (data w (w (operand test false)) (w (operand test true)) [] []) := by
  have hx:data w (w (operand test false)) [] [] [] (paramStack (operand test true))=
      w (operand test true) := by cases operand test true <;> rfl
  have h:=copy_call test true (.right test) (.compare test) rfl
    (data w (w (operand test false)) [] [] []) (w (operand test true)) [] hx rfl rfl
  have he:Function.update (data w (w (operand test false)) [] [] []) Stack.limit
      (w (operand test true)++[])=data w (w (operand test false)) (w (operand test true)) [] [] := by
    funext k;cases k <;> simp [data,Function.update]
  simpa only [ite_true,he] using h
/-- The literal comparator source is concretely discharged; no verdict/time supplier. -/
theorem less_call (test:Test) (w:Param→List Bool) (m d:Nat) :
    ∃t≤30*(m+d+1)+11,Runs program t (ctl (.compare test))
      (data w (List.replicate m true) (List.replicate d true) [] [])
      (ctl (.branch test)) (data w [] [] [decide (m<d)] []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackUnarySumLessBytecode.compare_run m 0 d
  refine ⟨t+1,by omega,?_⟩
  apply included_call program lessStack (lessLabel test) lessStack_injective Less.code Less.entry
    (fun _=>rfl) (ctl (.compare test)) (ctl (.branch test)) rfl t
    (⟨some Less.entry,none,Less.contents (List.replicate m true) [] (List.replicate d true) []⟩:
      SemiprimeD1StackBytecode.State Less.Stack Less.Label)
    (⟨none,none,Less.contents [] [] [] [decide (m<d)]⟩:
      SemiprimeD1StackBytecode.State Less.Stack Less.Label) _ _
  · rfl
  · rfl
  · simpa only [Nat.add_zero,SemiprimeD1StackUnaryDivmod.unary,List.replicate_zero] using hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;cases k <;> first
        | rfl
        | exact False.elim (hk .left rfl)
        | exact False.elim (hk .limit rfl)
        | exact False.elim (hk .valid rfl)
/-- Read and erase the physically computed Boolean before the next stage. -/
theorem branch_run (test:Test) (w:Param→List Bool) (bit:Bool) :
    Runs program 1 (ctl (.branch test)) (data w [] [] [bit] [])
      (ctl (afterCheck test bit)) (data w [] [] [] []) := by
  apply one_base program (ctl (.branch test)) (ctl (afterCheck test bit))
    (.pop .valid (ctl (.emit false)) (ctl (afterCheck test false)) (ctl (afterCheck test true))) _ _ rfl
  · cases bit <;> rfl
  · funext k;cases k <;> rfl
/-- Every actual comparison uses two distinct retained fields. -/
theorem operands_le (test:Test) (values:Param→Nat) :
    values (operand test false)+values (operand test true) ≤ volume values := by
  cases test <;> simp only [operand,volume] <;> omega
/-- Complete physical operand copies/comparison/verdict read under a linear own clock. -/
theorem check_run (test:Test) (values:Param→Nat) :
    ∃t≤50*(volume values+1),Runs program t (ctl (.left test)) (data (unaryWords values) [] [] [] [])
      (ctl (afterCheck test (decide (values (operand test false)<values (operand test true)))))
      (data (unaryWords values) [] [] [] []) := by
  have h0:=left_call test (unaryWords values)
  have h1:=right_call test (unaryWords values)
  obtain ⟨t,ht,h2⟩:=less_call test (unaryWords values)
    (values (operand test false)) (values (operand test true))
  have h3:=branch_run test (unaryWords values)
    (decide (values (operand test false)<values (operand test true)))
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,h⟩
  have hv:=operands_le test values
  simp only [unaryWords,List.length_replicate]
  omega
/-- Acquiring the final Boolean is one literal push, after all private work is empty. -/
theorem emit_run (w:Param→List Bool) (bit:Bool) :
    Runs program 1 (ctl (.emit bit)) (data w [] [] [] [])
      (ctl .done) (data w [] [] [] [bit]) := by
  apply one_base program (ctl (.emit bit)) (ctl .done) (.push .output bit (ctl .done)) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl
/-- The complete three-stage guard acquires the original conjunction for all counters. -/
theorem source_trace (v:Param→Nat) :
    ∃t≤150*(volume v+1)+1,Runs program t (ctl (.left .leaf))
      (data (unaryWords v) [] [] [] []) (ctl .done) (data (unaryWords v) [] [] [] [answer v]) := by
  obtain ⟨t0,ht0,h0⟩:=check_run .leaf v
  simp only [operand] at h0
  by_cases hl:v .leaf<v .edges
  · simp only [hl,decide_true,afterCheck] at h0
    obtain ⟨t1,ht1,h1⟩:=check_run .minimum v
    simp only [operand] at h1
    by_cases hm:v .levels<v .minimum
    · simp only [hm,decide_true,afterCheck] at h1
      have ha:answer v=false := by simp [answer,show ¬v .minimum≤v .levels by omega]
      rw [ha]
      exact ⟨t0+t1+1,by omega,join (join h0 h1) (emit_run _ false)⟩
    · simp only [hm,decide_false,afterCheck] at h1
      obtain ⟨t2,ht2,h2⟩:=check_run .maximum v
      simp only [operand] at h2
      by_cases he:v .edges<v .levels
      · simp only [he,decide_true,afterCheck] at h2
        have ha:answer v=false := by simp [answer,show ¬v .levels≤v .edges by omega]
        rw [ha]
        exact ⟨t0+t1+t2+1,by omega,join (join (join h0 h1) h2) (emit_run _ false)⟩
      · simp only [he,decide_false,afterCheck] at h2
        have ha:answer v=true := by
          simp [answer,hl,show v .minimum≤v .levels by omega,show v .levels≤v .edges by omega]
        rw [ha]
        exact ⟨t0+t1+t2+1,by omega,join (join (join h0 h1) h2) (emit_run _ true)⟩
  · simp only [hl,decide_false,afterCheck] at h0
    have ha:answer v=false := by simp [answer,hl]
    rw [ha]
    exact ⟨t0+1,by omega,join h0 (emit_run _ false)⟩
/-- Same actual complete source execution, including its physical final halt. -/
theorem source_run (v:Param→Nat) :
    ∃t≤200*(volume v+1),SemiprimeD1StackCalls.run program t (start v)=some (done v) := by
  obtain ⟨t,ht,h⟩:=source_trace v
  obtain ⟨finish,hf,hs⟩:=h [] (start v) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (data (unaryWords v) [] [] [] [answer v]) [] finish hs
  refine ⟨t+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackScheduleActiveExecution
