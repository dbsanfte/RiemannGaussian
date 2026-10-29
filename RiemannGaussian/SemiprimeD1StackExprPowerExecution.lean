/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprPowerSpec

/-! # Counted literal power-syntax construction trace
Every base occurrence is physically copied. Both exponent passes consume their
own real acquired counter copies; no result syntax or stop count is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprPowerExecution
open SemiprimeD1StackExprPower SemiprimeD1StackExprPowerSpec SemiprimeD1StackProcedureTrace

/-- Exact reached payload after one real count/base copy. -/
def copied (isBase : Bool) (baseCode cached count out : List Bool) : Stack→List Bool :=
  store baseCode cached (if isBase then count else cached++count) [] (if isBase then baseCode++out else out)

/-- Real included Copy, preserving its actual cached source and all other cells. -/
theorem copy_call (isBase : Bool) (baseCode cached count out : List Bool) (pc next : Label)
    (hcall : program pc=.call (.copy isBase 0) next) :
    Runs program (5*(if isBase then baseCode else cached).length+4) pc
      (store baseCode cached count [] out) next (copied isBase baseCode cached count out) := by
  apply included_call program (copyStack isBase) (Label.copy isBase) (copyStack_injective isBase)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hcall
    (5*(if isBase then baseCode else cached).length+3)
    (SemiprimeD1StackCopy.state 0 none (if isBase then baseCode else cached) (if isBase then out else count) [])
    (SemiprimeD1StackCopy.done (if isBase then baseCode else cached)
      ((if isBase then baseCode else cached)++(if isBase then out else count)))
    (store baseCode cached count [] out) (copied isBase baseCode cached count out)
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;cases isBase <;> fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases isBase <;> fin_cases k <;> rfl
    · intro k hk
      cases isBase <;> fin_cases k <;> first | rfl | exact False.elim (hk 1 rfl)

/-- Empty disposable count is populated by an actual preserving cache Copy. -/
theorem count_copy (baseCode cached out : List Bool) (pc next : Label)
    (hcall : program pc=.call (.copy false 0) next) :
    Runs program (5*cached.length+4) pc (store baseCode cached [] [] out)
      next (store baseCode cached cached [] out) := by
  simpa only [copied,Bool.false_eq_true,ite_false,List.append_nil] using
    copy_call false baseCode cached [] out pc next hcall

/-- One actual base Copy prepends the WHOLE acquired base byte stream. -/
theorem base_copy (baseCode cached count out : List Bool) :
    Runs program (5*baseCode.length+4) .baseCopy (store baseCode cached count [] out)
      .baseLoop (store baseCode cached count [] (baseCode++out)) := by
  exact copy_call true baseCode cached count out .baseCopy .baseLoop rfl

/-- Actual fixed push helper, used only with declared literal program instructions. -/
theorem push_run (pc next : Label) (b : Bool) (baseCode cached count out : List Bool)
    (hcode : program pc=.base (.push output b next)) :
    Runs program 1 pc (store baseCode cached count [] out)
      next (store baseCode cached count [] (b::out)) := by
  apply one_base program pc next (.push output b next) _ _ hcode
  · rfl
  · funext k;fin_cases k <;> rfl

/-- Every actual exponent marker triggers one complete base-code Copy. -/
theorem base_loop (count baseCode cached out : List Bool) :
    Runs program ((5*baseCode.length+5)*count.length+1) .baseLoop (store baseCode cached count [] out)
      .one0 (store baseCode cached [] [] (repeated count.length baseCode out)) := by
  induction count generalizing out with
  | nil =>
    apply one_base program .baseLoop .one0 (.pop counter .one0 .baseCopy .baseCopy) _ _ rfl
    · rfl
    · funext k;fin_cases k <;> rfl
  | cons bit count ih =>
    have h0 : Runs program 1 .baseLoop (store baseCode cached (bit::count) [] out)
        .baseCopy (store baseCode cached count [] out) := by
      apply one_base program .baseLoop .baseCopy (.pop counter .one0 .baseCopy .baseCopy) _ _ rfl
      · cases bit <;> rfl
      · funext k;fin_cases k <;> rfl
    have h1:=base_copy baseCode cached count out
    have h2:=ih (baseCode++out)
    rw [repeated_push] at h2
    have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    convert hh using 1
    · simp only [List.length_cons,Nat.mul_succ]
      omega
    · simp only [List.length_cons,repeated]

/-- The five fixed pushes produce exactly the original literal-one code prefix. -/
theorem one_run (baseCode cached out : List Bool) :
    Runs program 5 .one0 (store baseCode cached [] [] out)
      .copyAgain (store baseCode cached [] [] (oneCode++out)) := by
  have h0:=push_run .one0 .one1 false baseCode cached [] out rfl
  have h1:=push_run .one1 .one2 true baseCode cached [] (false::out) rfl
  have h2:=push_run .one2 .one3 true baseCode cached [] (true::false::out) rfl
  have h3:=push_run .one3 .one4 false baseCode cached [] (true::true::false::out) rfl
  have h4:=push_run .one4 .copyAgain false baseCode cached [] (false::true::true::false::out) rfl
  exact runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4

/-- All exponent markers are consumed by actual tag-constructor pushes. -/
theorem tags_loop (count baseCode cached out : List Bool) :
    Runs program (3*count.length+1) .mulLoop (store baseCode cached count [] out)
      .done (store baseCode cached [] [] (tags count.length out)) := by
  induction count generalizing out with
  | nil =>
    apply one_base program .mulLoop .done (.pop counter .done .mul0 .mul0) _ _ rfl
    · rfl
    · funext k;fin_cases k <;> rfl
  | cons bit count ih =>
    have h0 : Runs program 1 .mulLoop (store baseCode cached (bit::count) [] out)
        .mul0 (store baseCode cached count [] out) := by
      apply one_base program .mulLoop .mul0 (.pop counter .done .mul0 .mul0) _ _ rfl
      · cases bit <;> rfl
      · funext k;fin_cases k <;> rfl
    have h1:=push_run .mul0 .mul1 true baseCode cached count out rfl
    have h2:=push_run .mul1 .mulLoop true baseCode cached count (true::out) rfl
    have h3:=ih (true::true::out)
    rw [prefix_push] at h3
    have hh:=runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
    simpa only [List.length_cons,tags,
      show (1+1)+1+(3*count.length+1)=3*(count.length+1)+1 by omega] using hh

/-- Whole actual elapsed count, including all copied base bytes and the real halt. -/
def totalTime (baseCode cached : List Bool) : ℕ :=
  (5*cached.length+4)+((5*baseCode.length+5)*cached.length+1)+5+
    (5*cached.length+4)+(3*cached.length+1)+1
/-- Exact actual final cells; both caches retained, all work and return cells empty. -/
def done (baseCode cached tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store baseCode cached [] [] (result cached.length baseCode tail),[]⟩

/-- Complete physical power-expression acquisition from the acquired base and
actual exponent tape; no Expr tree, output code or desired numerical power input. -/
theorem source_run (baseCode cached tail : List Bool) :
    C.run program (totalTime baseCode cached) (initial baseCode cached tail)=some (done baseCode cached tail) := by
  have h0:=count_copy baseCode cached tail .start .baseLoop rfl
  have h1:=base_loop cached baseCode cached tail
  have h2:=one_run baseCode cached (repeated cached.length baseCode tail)
  have h3:=count_copy baseCode cached (oneCode++repeated cached.length baseCode tail) .copyAgain .mulLoop rfl
  have h4:=tags_loop cached baseCode cached (oneCode++repeated cached.length baseCode tail)
  have hh:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4
  obtain ⟨finish,hf,ho⟩:=hh [] (initial baseCode cached tail) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (store baseCode cached [] [] (result cached.length baseCode tail)) [] finish ho
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some,he]
  rfl

end RiemannGaussian.SemiprimeD1StackExprPowerExecution
