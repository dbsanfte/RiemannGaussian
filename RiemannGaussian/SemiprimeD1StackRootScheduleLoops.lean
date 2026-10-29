/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSchedulePrimitives
import RiemannGaussian.SemiprimeD1StackRootScheduleArithmetic
/-! # Paid actual quotient cleanup and logarithmic metadata loops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleLoops
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootSchedulePrimitives
open SemiprimeD1StackProcedureTrace
/-- Actual post-divider physical quotient/remainder, with every other field retained. -/
def divided (base : Stack→List Bool) (q r : Nat) : Stack→List Bool :=
  withDiv base (D.contents [] (D.unary 2) [] [] (D.unary q) (D.unary r))
/-- Every remainder cell is physically erased and every quotient cell physically
moved into the next actual divider input. -/
theorem cleanup_move (job : Job) (base : Stack→List Bool) (q r : Nat) :
    Runs program ((r+1)+(2*q+1)) (.clearRemainder job) (divided base q r)
      (afterMove job) (clean base q) := by
  have hd:=SemiprimeD1StackPhysicalLoops.drain program (.clearRemainder job) (.move job)
    (divStack .remainder) rfl (divided base q r) (D.unary r)
  have he0:Function.update (divided base q r) (divStack .remainder) (D.unary r)=divided base q r:=by
    exact Function.update_eq_self _ _
  have he1:Function.update (divided base q r) (divStack .remainder) []=divided base q 0:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> simp [divided,withDiv,D.contents,divStack,Function.update,D.unary]
      · rfl
  rw [he0,he1] at hd
  have hm:=SemiprimeD1StackPhysicalLoops.move_unary program (.move job) (.movePush job) (afterMove job)
    (divStack .quotient) (divStack .input) (by decide) rfl rfl (clean base 0) q []
  have he2:Function.update (Function.update (clean base 0) (divStack .input) [])
      (divStack .quotient) (D.unary q)=divided base q 0:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> simp [divided,clean,withDiv,D.contents,divStack,Function.update,D.unary]
      · rfl
  have he3:Function.update (Function.update (clean base 0) (divStack .input) (D.unary q++[]))
      (divStack .quotient) []=clean base q:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> simp [clean,withDiv,D.contents,divStack,Function.update,D.unary]
      · rfl
  dsimp only [D.unary] at he2 he3
  rw [he2,he3] at hm
  simpa only [D.unary,List.length_replicate] using join hd hm
/-- One or four actual writes per completed physical size iteration. -/
def factor (minimum : Bool) : Nat :=if minimum then 4 else 1
/-- Four literal minimum-level markers end at the real next loop probe. -/
def emitPhase (i : Nat) : Label :=if h:i<4 then .emitSize true ⟨i,h⟩ else .probe true
/-- Fixed finite physical emit instructions, before all N. -/
theorem emit_code (i : Nat) (hi : i<4) :
    program (emitPhase i)=.base (.push (sizeOutput true) true (emitPhase (i+1))) := by
  interval_cases i <;> rfl
/-- Full marker effect of each actual size iteration, with no native increment opcode. -/
theorem emit_run (minimum : Bool) (base : Stack→List Bool) (n : Nat) (tail : List Bool) :
    Runs program (factor minimum) (.emitSize minimum 0) (ready base minimum n tail)
      (.probe minimum) (ready base minimum n (D.unary (factor minimum)++tail)) := by
  have he (f : Nat):Function.update (ready base minimum n tail) (sizeOutput minimum)
      (D.unary f++(ready base minimum n tail) (sizeOutput minimum))=
      ready base minimum n (D.unary f++tail):=by
    funext k
    cases minimum <;> rcases k with k|k
    all_goals first
    | rfl
    | (rcases k with k|k
       · rfl
       · cases k <;> simp [ready,clean,withDiv,sizeOutput,aux,Function.update])
  cases minimum with
  | false=>
    have h:=push (.emitSize false 0) (.probe false) (sizeOutput false) (ready base false n tail) rfl
    change Runs program 1 _ _ _ _
    have hx:Function.update (ready base false n tail) (sizeOutput false)
        (true::(ready base false n tail) (sizeOutput false))=ready base false n (D.unary 1++tail):=by
      simpa only [D.unary,List.replicate_one,List.singleton_append] using he 1
    rw [hx] at h
    exact h
  | true=>
    have h:=push_chain emitPhase 4 (sizeOutput true) emit_code 4 0 (by omega) (ready base true n tail)
    rw [he 4] at h
    exact h
/-- Exact cumulative size-loop metadata comes from repeated ACTUAL divider calls. -/
theorem size_loop (minimum : Bool) (base : Stack→List Bool) (n : Nat) (tail : List Bool) :
    ∃t≤1000*(n+1)^2,Runs program t (.probe minimum) (ready base minimum n tail)
      (if minimum then .copyLevels else .seedMinimum 0)
      (ready base minimum 0 (D.unary (factor minimum*n.size)++tail)) := by
  induction n using Nat.strong_induction_on generalizing tail with
  | h n ih=>
    by_cases hz:n=0
    · subst n
      refine ⟨1,by norm_num,?_⟩
      simpa only [Nat.size_zero,Nat.mul_zero,D.unary,List.replicate_zero,List.nil_append] using
        SemiprimeD1StackPhysicalLoops.peek_empty program (.probe minimum)
          (if minimum then .copyLevels else .seedMinimum 0) (.divide minimum) (.divide minimum)
          (divStack .input) rfl (ready base minimum 0 tail) rfl
    · have hn:0<n:=by omega
      have hq:n/2<n:=Nat.div_lt_self hn (by decide)
      have h0:Runs program 1 (.probe minimum) (ready base minimum n tail)
          (.divide minimum) (ready base minimum n tail):=by
        obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hz
        subst n
        exact SemiprimeD1StackPhysicalLoops.peek_nonempty program (.probe minimum)
          (if minimum then .copyLevels else .seedMinimum 0) (.divide minimum) (divStack .input)
          rfl (ready base minimum (k+1) tail) true (D.unary k) rfl
      obtain ⟨td,hd,hdiv⟩:=division_call (.divide minimum) (.clearRemainder (.size minimum)) rfl
        (Function.update base (sizeOutput minimum) tail) n
      have hm:=cleanup_move (.size minimum) (Function.update base (sizeOutput minimum) tail) (n/2) (n%2)
      have he:=emit_run minimum base (n/2) tail
      obtain ⟨tr,hr,hrec⟩:=ih (n/2) hq (D.unary (factor minimum)++tail)
      have h:=join (join (join (join h0 hdiv) hm) he) hrec
      have hs:n.size=(n/2).size+1:=SemiprimeD1StackRootScheduleArithmetic.size_step n hn
      have hout:D.unary (factor minimum*(n/2).size)++(D.unary (factor minimum)++tail)=
          D.unary (factor minimum*n.size)++tail:=by
        rw [←List.append_assoc,←SemiprimeD1StackUnaryDivmod.unary_add,hs,Nat.mul_add,Nat.mul_one]
      rw [hout] at h
      refine ⟨(((1+td)+((n%2+1)+(2*(n/2)+1)))+factor minimum)+tr,?_,h⟩
      have hm2:n%2<2:=Nat.mod_lt n (by decide)
      have hf:factor minimum≤4:=by cases minimum <;> decide
      have hp:(n/2+1)^2≤n^2:=Nat.pow_le_pow_left (by omega) 2
      nlinarith
end RiemannGaussian.SemiprimeD1StackRootScheduleLoops
