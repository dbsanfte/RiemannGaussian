/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSchedule
/-! # Literal root-schedule copies, writes and actual divider calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootSchedulePrimitives
open SemiprimeD1StackRootSchedule SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Replace only the actual six physical divider fields. -/
def withDiv (base : Stack→List Bool) (componentData : D.Stack→List Bool) : Stack→List Bool
  | .inr (.inl k)=>componentData k | k=>base k
/-- Clean actual division input; the two-marker divisor was physically seeded. -/
def clean (base : Stack→List Bool) (n : Nat) : Stack→List Bool :=
  withDiv base (D.contents (D.unary n) (D.unary 2) [] [] [] [])
/-- Size-loop input with one actual accumulated metadata destination. -/
def ready (base : Stack→List Bool) (minimum : Bool) (n : Nat) (tail : List Bool) : Stack→List Bool :=
  clean (Function.update base (sizeOutput minimum) tail) n
/-- Concatenate two actual fragments, retaining every real outer frame. -/
theorem join {m n : Nat} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- One physically executed literal write. -/
theorem push (pc next : Label) (key : Stack) (d : Stack→List Bool)
    (hc : program pc=.base (.push key true next)) :
    Runs program 1 pc d next (Function.update d key (true::d key)) := by
  apply one_base program pc next (.push key true next) _ _ hc <;> rfl
/-- A bounded static chain accounts for EVERY actual marker push. All concrete
uses have fixed lengths20,8,4,2 before N; the machine never receives this chain. -/
theorem push_chain (phase : Nat→Label) (limit : Nat) (key : Stack)
    (hc : ∀i<limit,program (phase i)=.base (.push key true (phase (i+1))))
    (n start : Nat) (hbound : start+n≤limit) (d : Stack→List Bool) :
    Runs program n (phase start) d (phase (start+n))
      (Function.update d key (D.unary n++d key)) := by
  induction n generalizing start d with
  | zero=>simpa only [Nat.add_zero,D.unary,List.replicate_zero,List.nil_append,Function.update_eq_self] using runs_refl program (phase start) d
  | succ n ih=>
    have h0:=push (phase start) (phase (start+1)) key d (hc start (by omega))
    have h1:=ih (start+1) (by omega) (Function.update d key (true::d key))
    have h:=join h0 h1
    have he:Function.update (Function.update d key (true::d key)) key
        (D.unary n++(Function.update d key (true::d key)) key)=
      Function.update d key (D.unary (n+1)++d key) := by
      funext k
      by_cases hk:k=key
      · subst k
        simp only [Function.update_self]
        exact SemiprimeD1StackUnaryDivmod.unary_bump n (d key)
      · simp only [Function.update_of_ne hk]
    rw [he] at h
    have ht:1+n=n+1:=by omega
    have hp:start+1+n=start+(n+1):=by omega
    rw [ht,hp] at h
    exact h
/-- One actual preserving copy, allowing the second level block to append to
an existing exponent. No old bank is synthesized or silently reset. -/
theorem copy_call (kind : Fin 3) (pc next : Label)
    (hc : program pc=.call (.copy kind 0) next) (d : Stack→List Bool)
    (hz : d (aux .scratch)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind)++d (copyTarget kind))) := by
  let xs:=d (copySource kind)
  let ys:=d (copyTarget kind)
  have hin:Link.DataRel (copyStack kind) d (SemiprimeD1StackCopy.state 0 none xs ys []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hz
    · intro k _;rfl
  have hout:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hin (1:Fin 3) (xs++ys)
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs ys []).store 1 (xs++ys)=
      (SemiprimeD1StackCopy.done xs (xs++ys)).store:=by funext k;fin_cases k <;> rfl
  rw [he] at hout
  exact included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys))
    d _ rfl rfl (SemiprimeD1StackCopy.copy_words xs ys none) hin hout
/-- The literal full unary divider is executed on the actual input and two
physical divisor markers. Its quotient/remainder are never initialized as advice. -/
theorem division_call (pc next : Label) (hc : program pc=.call (.division Div.entry) next)
    (base : Stack→List Bool) (n : Nat) :
    ∃t≤100*(n+3)+1,Runs program t pc (clean base n) next
      (withDiv base (D.contents [] (D.unary 2) [] [] (D.unary (n/2)) (D.unary (n%2)))) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackUnaryDivmodBytecode.divide_run n 2
  refine ⟨t+1,by omega,?_⟩
  apply included_call program divStack Label.division div_injective Div.code Div.entry (fun _=>rfl)
    pc next hc t ⟨some Div.entry,none,D.contents (D.unary n) (D.unary 2) [] [] [] []⟩
    ⟨none,none,D.contents [] (D.unary 2) [] [] (D.unary (n/2)) (D.unary (n%2))⟩ _ _ rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
end RiemannGaussian.SemiprimeD1StackRootSchedulePrimitives
