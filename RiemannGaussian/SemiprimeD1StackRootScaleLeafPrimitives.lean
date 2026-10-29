/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeaf
/-! # Literal root-schedule copies, writes and actual divider calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Replace only the actual six physical divider fields. -/
def withDiv (base : Stack→List Bool) (componentData : D.Stack→List Bool) : Stack→List Bool
  | .inr (.inl k)=>componentData k | k=>base k
/-- Clean actual division input; the divisor was physically acquired. -/
def clean (base : Stack→List Bool) (n d : Nat) : Stack→List Bool :=
  withDiv base (D.contents (D.unary n) (D.unary d) [] [] [] [])
/-- Concatenate two actual fragments, retaining every real outer frame. -/
theorem join {m n : Nat} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- One physically executed literal write. -/
theorem push (pc next : Label) (key : Stack) (d : Stack→List Bool)
    (hc : program pc=.base (.push key true next)) :
    Runs program 1 pc d next (Function.update d key (true::d key)) := by
  apply one_base program pc next (.push key true next) _ _ hc <;> rfl
/-- One actual preserving copy with its real restoration and return.
No old cache is synthesized or silently reset. -/
theorem copy_call (kind : Fin 5) (pc next : Label)
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
/-- The literal full unary divider executes on actual physically acquired
operands. Its quotient/remainder are never initialized as advice. -/
theorem division_call (pc next : Label) (hc : program pc=.call (.division Div.entry) next)
    (base : Stack→List Bool) (n d : Nat) :
    ∃t≤100*(n+d+1)+1,Runs program t pc (clean base n d) next
      (withDiv base (D.contents [] (D.unary d) [] [] (D.unary (n/d)) (D.unary (n%d)))) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackUnaryDivmodBytecode.divide_run n d
  refine ⟨t+1,by omega,?_⟩
  apply included_call program divStack Label.division div_injective Div.code Div.entry (fun _=>rfl)
    pc next hc t ⟨some Div.entry,none,D.contents (D.unary n) (D.unary d) [] [] [] []⟩
    ⟨none,none,D.contents [] (D.unary d) [] [] (D.unary (n/d)) (D.unary (n%d))⟩ _ _ rfl rfl hr
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
end RiemannGaussian.SemiprimeD1StackRootScaleLeafPrimitives
