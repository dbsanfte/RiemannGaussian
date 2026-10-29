/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryPower
/-! # Actual borrow dispatch and exact absolute-value subtraction -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometrySubtract
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryArithmetic
open SemiprimeD1StackPhaseGeometryPrimitives SemiprimeD1StackProcedureTrace
/-- Full physical phase state retaining original operands and acquired binary powers. -/
def phase (a t left right output sign : List Bool) : Stack→List Bool :=
  data a t [] (powerWord a.length) (powerWord (a.length+1)) sign [] [] [] left right output
/-- One real copy of EACH original operand precedes every actual ripple call. -/
theorem operands (negative : Bool) (a t sign : List Bool) :
    Runs program (5*t.length+5*(powerWord a.length).length+8) (.left negative)
      (phase a t [] [] [] sign) (.subtract negative)
      (phase a t (if negative then powerWord a.length else t)
        (if negative then t else powerWord a.length) [] sign) :=by
  have h0:=copy_empty (if negative then 4 else 2) (.left negative) (.right negative) rfl
    (phase a t [] [] [] sign) rfl (by cases negative <;> rfl)
  have he0:Function.update (phase a t [] [] [] sign) (copyTarget (if negative then 4 else 2))
      (phase a t [] [] [] sign (copySource (if negative then 4 else 2)))=
      phase a t (if negative then powerWord a.length else t) [] [] sign:=by
    funext k;cases negative <;> rcases k with k|k <;> cases k <;> rfl
  rw [he0] at h0
  have h1:=copy_empty (if negative then 5 else 3) (.right negative) (.subtract negative) rfl
    (phase a t (if negative then powerWord a.length else t) [] [] sign) rfl (by cases negative <;> rfl)
  have he1:Function.update (phase a t (if negative then powerWord a.length else t) [] [] sign)
      (copyTarget (if negative then 5 else 3))
      (phase a t (if negative then powerWord a.length else t) [] [] sign (copySource (if negative then 5 else 3)))=
      phase a t (if negative then powerWord a.length else t) (if negative then t else powerWord a.length) [] sign:=by
    funext k;cases negative <;> rcases k with k|k <;> cases k <;> rfl
  rw [he1] at h1
  have hh:=join h0 h1
  cases negative
  · change Runs program ((5*t.length+4)+(5*(powerWord a.length).length+4)) _ _ _ _ at hh
    convert hh using 1
    omega
  · change Runs program ((5*(powerWord a.length).length+4)+(5*t.length+4)) _ _ _ _ at hh
    convert hh using 1
    omega
/-- Included subtraction has exact physical store and actual final borrow prefix. -/
theorem ripple (negative : Bool) (a t xs ys sign : List Bool) :
    Runs program (3*(max xs.length ys.length+1)+2*(difference xs ys).length+4)
      (.subtract negative) (phase a t xs ys [] sign)
      (if negative then .readSecond else .readFirst)
      (phase a t [] [] ((SemiprimeBitDivision.subBits xs ys false).borrow::difference xs ys) sign) :=by
  have h:=subtract_call negative (phase a t xs ys [] sign) xs ys (fun _=>rfl)
  have he:withSub (phase a t xs ys [] sign)
      (S.store [] [] [] ((SemiprimeBitDivision.subBits xs ys false).borrow::difference xs ys))=
      phase a t [] [] ((SemiprimeBitDivision.subBits xs ys false).borrow::difference xs ys) sign:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h
  exact h
/-- The actual first borrow is popped and saved as one physical singleton sign. -/
theorem read_first (a t diff : List Bool) (b : Bool) :
    Runs program 2 .readFirst (phase a t [] [] (b::diff) [])
      (if b then .clearWrapped else .scanCopy) (phase a t [] [] diff [b]) :=by
  have h0:Runs program 1 .readFirst (phase a t [] [] (b::diff) [])
      (.saveSign b) (phase a t [] [] diff []):=by
    apply one_base program .readFirst (.saveSign b)
      (.pop (subStack .output) (.saveSign false) (.saveSign false) (.saveSign true)) _ _ rfl
    · cases b <;> rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h1:=push (.saveSign b) (if b then .clearWrapped else .scanCopy) (aux .sign) b
    (phase a t [] [] diff []) rfl
  have he:Function.update (phase a t [] [] diff []) (aux .sign)
      (b::phase a t [] [] diff [] (aux .sign))=phase a t [] [] diff [b]:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h1
  exact join h0 h1
/-- Underflow's wrapped low word is physically erased before the second subtraction. -/
theorem clear_wrapped (a t diff : List Bool) :
    Runs program (diff.length+1) .clearWrapped (phase a t [] [] diff [true])
      (.left true) (phase a t [] [] [] [true]) :=by
  have h:=SemiprimeD1StackPhysicalLoops.drain program .clearWrapped (.left true) (subStack .output)
    rfl (phase a t [] [] diff [true]) diff
  have hi:Function.update (phase a t [] [] diff [true]) (subStack .output) diff=
      phase a t [] [] diff [true]:=Function.update_eq_self _ _
  have ho:Function.update (phase a t [] [] diff [true]) (subStack .output) []=
      phase a t [] [] [] [true]:=by funext k;rcases k with k|k <;> cases k <;> rfl
  rw [hi,ho] at h
  exact h
/-- The second actual borrow is consumed; only its actual absolute low word remains. -/
theorem read_second (a t diff : List Bool) (b : Bool) :
    Runs program 1 .readSecond (phase a t [] [] (b::diff) [true])
      .scanCopy (phase a t [] [] diff [true]) :=by
  apply one_base program .readSecond .scanCopy (.pop (subStack .output) .scanCopy .scanCopy .scanCopy) _ _ rfl
  · cases b <;> rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Actual physical absolute subtraction, with paid underflow cleanup and all copies. -/
theorem source_run (a t : List Bool) :
    ∃q≤200*(a.length+t.length+1),Runs program q (.left false)
      (SemiprimeD1StackPhaseGeometryPower.prepared a t) .scanCopy
      (phase a t [] [] (magnitude a.length t) [negative a.length t]) :=by
  have h0:=operands false a t []
  have h1:=ripple false a t t (powerWord a.length) []
  have h2:=read_first a t (difference t (powerWord a.length)) (negative a.length t)
  have hfirst:=join (join h0 h1) h2
  have hlen:=difference_length t (powerWord a.length)
  have hpow:=powerWord_length a.length
  have hm:max t.length (powerWord a.length).length≤ t.length+a.length+1:=max_le (by omega) (by omega)
  cases hn:negative a.length t with
  | false=>
    rw [hn] at hfirst
    refine ⟨_,?_,by simpa only [magnitude,hn,Bool.false_eq_true,ite_false,phase,SemiprimeD1StackPhaseGeometryPower.prepared] using hfirst⟩
    omega
  | true=>
    rw [hn] at hfirst
    have h3:=clear_wrapped a t (difference t (powerWord a.length))
    have h4:=operands true a t [true]
    have h5:=ripple true a t (powerWord a.length) t [true]
    have h6:=read_second a t (difference (powerWord a.length) t)
      (SemiprimeBitDivision.subBits (powerWord a.length) t false).borrow
    have hh:=join (join (join (join hfirst h3) h4) h5) h6
    have hlen2:=difference_length (powerWord a.length) t
    have hm2:max (powerWord a.length).length t.length≤ t.length+a.length+1:=max_le (by omega) (by omega)
    refine ⟨_,?_,by simpa only [magnitude,hn,ite_true,phase,SemiprimeD1StackPhaseGeometryPower.prepared] using hh⟩
    omega
end RiemannGaussian.SemiprimeD1StackPhaseGeometrySubtract
