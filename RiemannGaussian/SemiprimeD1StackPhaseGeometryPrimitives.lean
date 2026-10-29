/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryArithmetic
/-! # Included real-copy/subtractor calls and explicit physical phase stores -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryPrimitives
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryArithmetic SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact physical state view; both real scratch banks are empty at stage boundaries. -/
def data (a t counter center alpha sign zero order scan left right output : List Bool) : Stack→List Bool :=
  store (S.store left right [] output) (words a t counter center alpha sign zero order scan [])
/-- Chronological source composition retains arbitrary real caller frames. -/
theorem join {m n : Nat} {pc mid next : Label} {d e f : Stack→List Bool}
    (h : Runs program m pc d mid e) (g : Runs program n mid e next f) :
    Runs program (m+n) pc d next f :=runs_trans program m n pc mid next d e f h g
/-- One actual binary-bit write, without a native arithmetic opcode. -/
theorem push (pc next : Label) (key : Stack) (bit : Bool) (d : Stack→List Bool)
    (hc : program pc=.base (.push key bit next)) :
    Runs program 1 pc d next (Function.update d key (bit::d key)) :=by
  apply one_base program pc next (.push key bit next) _ _ hc <;> rfl
/-- Every preserving copy pays both loops, restoration and real call/return. -/
theorem copy_call (kind : Fin 7) (pc next : Label)
    (hc : program pc=.call (.copy kind 0) next) (d : Stack→List Bool)
    (hz : d (aux .scratch)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind)++d (copyTarget kind))) :=by
  let xs:=d (copySource kind)
  let ys:=d (copyTarget kind)
  have hi:Link.DataRel (copyStack kind) d (SemiprimeD1StackCopy.state 0 none xs ys []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hz
    · intro k _;rfl
  have ho:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hi (1:Fin 3) (xs++ys)
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs ys []).store 1 (xs++ys)=
      (SemiprimeD1StackCopy.done xs (xs++ys)).store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys))
    d _ rfl rfl (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- A clear destination receives the literal source word, with source restored. -/
theorem copy_empty (kind : Fin 7) (pc next : Label)
    (hc : program pc=.call (.copy kind 0) next) (d : Stack→List Bool)
    (hz : d (aux .scratch)=[]) (ht : d (copyTarget kind)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind))) :=by
  simpa only [ht,List.append_nil] using copy_call kind pc next hc d hz
/-- Only the actual four ripple fields are replaced by this view. -/
def withSub (base : Stack→List Bool) (sub : S.Stack→List Bool) : Stack→List Bool
  | .inl k=>sub k | .inr k=>base (.inr k)
/-- Full literal ripple subtraction returns its ACTUAL borrow-prefix and padded bits. -/
theorem subtract_call (negative : Bool) (d : Stack→List Bool) (xs ys : List Bool)
    (hi : ∀k,d (subStack k)=S.store xs ys [] [] k) :
    Runs program (3*(max xs.length ys.length+1)+2*(difference xs ys).length+4)
      (.subtract negative) d (if negative then .readSecond else .readFirst)
      (withSub d (S.store [] [] [] ((SemiprimeBitDivision.subBits xs ys false).borrow::difference xs ys))) :=by
  apply included_call program subStack Label.ripple sub_injective S.code (.start false) (fun _=>rfl)
    (.subtract negative) (if negative then .readSecond else .readFirst) rfl
    (3*(max xs.length ys.length+1)+2*(difference xs ys).length+3)
    (S.state (some (.start false)) none xs ys [] [])
    (S.state none none [] [] [] ((SemiprimeBitDivision.subBits xs ys false).borrow::difference xs ys))
    d _ rfl rfl (SemiprimeD1StackSubtractorExecution.source_run xs ys false)
  · constructor
    · exact hi
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Every actual difference field has exactly the longer physical operand width. -/
theorem difference_length (xs ys : List Bool) : (difference xs ys).length=max xs.length ys.length :=
  (SemiprimeBitDivision.subBits_counts xs ys false).2.2.2.2
end RiemannGaussian.SemiprimeD1StackPhaseGeometryPrimitives
