/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTableLoad
import RiemannGaussian.SemiprimeD1StackStaticTableEmit
/-! # Every actual static checker leaf copy, reversal and real call -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticTableLeafCalls
open SemiprimeD1StackStaticTable SemiprimeD1StackStaticTableSpec
open SemiprimeD1StackStaticTablePrimitives SemiprimeD1StackStaticTableCleanup
open SemiprimeD1StackStaticTableLoad SemiprimeD1StackStaticTableEmit
open SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Updating one real checker role commutes with the complete caller-bank view. -/
theorem withChecker_update (base : Stack K→List Bool) (live : K→List Bool) (key : K) (word : List Bool) :
    Function.update (withChecker base live) (checker key) word=
      withChecker base (Function.update live key word) := by
  funext k
  cases k with
  | inl k=>
    by_cases h:k=key
    · subst k
      change Function.update (withChecker base live) (Sum.inl key) word (Sum.inl key)=
        Function.update live key word key
      rw [Function.update_self,Function.update_self]
    · have hn:(Sum.inl k : Stack K)≠checker key:=by intro he;exact h (Sum.inl.inj he)
      rw [Function.update_of_ne hn]
      change live k=Function.update live key word k
      rw [Function.update_of_ne h]
  | inr k=>rw [Function.update_of_ne (by intro h;cases h)];rfl
/-- A literal full-bank load enters every physical original input field. -/
theorem load_call [Fintype K] (original : K→List Bool) (bank front hist : List Bool) :
    ∃t≤ s.roles.length*(6*inputBytes original+5)+2,Runs (program s) t .leaf
      (data original bank 0 front hist) .prefixCopy (loadedData original bank front hist) := by
  obtain ⟨t,ht,hr⟩:=load_returns s (data original bank 0 front hist) rfl
  have h:=SemiprimeD1StackProcedureReturns.call (program s) t .leaf (.load 0) .prefixCopy _ _ rfl hr
  have he:loaded (data original bank 0 front hist)=loadedData original bank front hist:=by
    funext k;cases k <;> rfl
  rw [he] at h
  refine ⟨1+t,?_,h⟩
  have hi:inventory (data original bank 0 front hist)=0 := by simp [inventory,data,store,checker]
  have hT:templateInventory (data original bank 0 front hist)=inputBytes original := rfl
  unfold loadUnit at ht
  rw [hi,hT] at ht
  simp only [Nat.zero_add] at ht
  omega
/-- Current reverse-prefix copying retains the actual prefix and original template. -/
theorem copy_prefix (original : K→List Bool) (bank front hist : List Bool) :
    Runs (program s) (5*front.length+4) .prefixCopy (loadedData original bank front hist) .reversePrefix
      (Function.update (loadedData original bank front hist) (aux .work) front) :=
  copy_call s none .prefixCopy .reversePrefix rfl (loadedData original bank front hist) rfl rfl
/-- The real consuming reversal supplies the raw operand directly; the template
raw field is empty, as proved by each concrete original-input client. -/
theorem reverse_prefix (original : K→List Bool) (hraw : original s.raw=[])
    (bank front hist : List Bool) :
    Runs (program s) (2*front.length+3) .reversePrefix
      (Function.update (loadedData original bank front hist) (aux .work) front) .check
      (withChecker (data original bank 0 front hist) (Function.update original s.raw front.reverse)) := by
  let d:=loadedData original bank front hist
  have hr:=reverse_call s false .reversePrefix .check rfl (Function.update d (aux .work) front)
  have h0:(Function.update d (aux .work) front) (reverseStack s false 0)=front :=
    Function.update_self _ _ _
  have h1:(Function.update d (aux .work) front) (reverseStack s false 1)=[] := by
    change Function.update d (aux .work) front (checker s.raw)=[]
    rw [Function.update_of_ne (by intro h;cases h)]
    exact hraw
  rw [h0,h1,List.append_nil] at hr
  have he:Function.update (Function.update (Function.update d (aux .work) front) (aux .work) [])
      (checker s.raw) front.reverse=Function.update d (checker s.raw) front.reverse := by
    funext k
    by_cases hc:k=checker s.raw
    · subst k;rw [Function.update_self,Function.update_self]
    · rw [Function.update_of_ne hc,Function.update_of_ne hc]
      by_cases hw:k=aux .work
      · subst k;rw [Function.update_self];rfl
      · rw [Function.update_of_ne hw,Function.update_of_ne hw]
  change Runs (program s) (2*front.length+3) .reversePrefix (Function.update d (aux .work) front) .check
    (Function.update (Function.update (Function.update d (aux .work) front) (aux .work) [])
      (checker s.raw) front.reverse) at hr
  have hd:Function.update d (checker s.raw) front.reverse=
      withChecker (data original bank 0 front hist) (Function.update original s.raw front.reverse):=
    withChecker_update (data original bank 0 front hist) original s.raw front.reverse
  rw [he,hd] at hr
  exact hr
/-- A concrete proved checker trace is included as a REAL call; its original
program executes, rather than a predicate/callback/evaluator opcode. -/
theorem checker_call (original : K→List Bool) (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s original answer budget) (bank front hist : List Bool) :
    ∃t≤ budget front.length,∃finish:C.State K L,
      C.run s.code t (checkerInitial s original front.reverse)=some finish ∧
      finish.data s.output=[answer front.reverse] ∧
      Runs (program s) (t+1) .check
        (withChecker (data original bank 0 front hist) (Function.update original s.raw front.reverse)) .verdict
        (withChecker (data original bank 0 front hist) finish.data) := by
  obtain ⟨t,ht,finish,hpc,hframes,hr,hvalue⟩:=hc front.reverse
  refine ⟨t,by simpa only [List.length_reverse] using ht,finish,hr,hvalue,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s) checker Label.checker
    Sum.inl_injective s.code s.entry (fun _=>rfl) .check .verdict rfl t
    (checkerInitial s original front.reverse) finish
  · rfl
  · rfl
  · exact hpc
  · exact hframes
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- The Boolean branch consumes the ACTUAL singleton output and changes no
other physical checker field or caller/cache/template role. -/
theorem verdict_pop (original : K→List Bool) (bank front hist : List Bool)
    (live : K→List Bool) (b : Bool) (hv : live s.output=[b]) :
    Runs (program s) 1 .verdict (withChecker (data original bank 0 front hist) live) (emitStart s b)
      (withChecker (data original bank 0 front hist) (Function.update live s.output [])) := by
  apply SemiprimeD1StackProcedureFragments.one_base (program s) .verdict (emitStart s b)
    (.pop (checker s.output) .bad (.zero 0) (.one 0)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose .bad (.zero 0) (.one 0) (live s.output).head?)=some (emitStart s b)
    rw [hv]
    cases b <;> rfl
  · change Function.update (withChecker (data original bank 0 front hist) live)
      (checker s.output) (live s.output).tail=_
    rw [hv,List.tail_cons,withChecker_update]
end RiemannGaussian.SemiprimeD1StackStaticTableLeafCalls
