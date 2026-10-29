/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardPrimitives
/-! # Whole physical original-phase conjunction and complete cache retention -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardComponents
open SemiprimeD1StackPhaseGeometryGuard SemiprimeD1StackPhaseGeometryGuardPrimitives
open SemiprimeD1StackProcedureTrace
/-- The actual selected comparison bound, described only for its trace proof. -/
def limit (second : Bool) (a u : Nat) : Nat :=if second then u else a
/-- Proof-side verdict describes the actual zero peek and both strict comparisons. -/
def accepted (a u : Nat) (t : List Bool) : Bool :=
  if zero a t then false else if order a t<a then decide (order a t<u) else false
/-- Exact acquired cache/u and one actually emitted verdict; every guard work role empty. -/
def result (a u : Nat) (t : List Bool) : Stack→List Bool :=context a u t [] [] [] [accepted a u t]
/-- Physically copied acquired order and actual a/u operand feed the consuming checker. -/
theorem operands (second : Bool) (a u : Nat) (t : List Bool) :
    Runs program ((5*order a t+4)+(5*limit second a u+4)) (.left second)
      (context a u t [] [] [] []) (.compare second)
      (context a u t (List.replicate (order a t) true) (List.replicate (limit second a u) true) [] []) :=by
  have h0:=copy_call 0 (.left second) (.limit second) rfl (context a u t [] [] [] []) rfl rfl
  have hsource:context a u t [] [] [] [] (copySource 0)=List.replicate (order a t) true:=cache_order a t
  rw [hsource,List.length_replicate] at h0
  have he0:Function.update (context a u t [] [] [] []) (copyTarget 0) (List.replicate (order a t) true)=
      context a u t (List.replicate (order a t) true) [] [] []:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he0] at h0
  have h1:=copy_call (if second then 2 else 1) (.limit second) (.compare second) rfl
    (context a u t (List.replicate (order a t) true) [] [] []) rfl (by cases second <;> rfl)
  have hsource1:context a u t (List.replicate (order a t) true) [] [] [] (copySource (if second then 2 else 1))=
      List.replicate (limit second a u) true:=by cases second <;> rfl
  rw [hsource1,List.length_replicate] at h1
  have he1:Function.update (context a u t (List.replicate (order a t) true) [] [] [])
      (copyTarget (if second then 2 else 1)) (List.replicate (limit second a u) true)=
      context a u t (List.replicate (order a t) true) (List.replicate (limit second a u) true) [] []:=by
    funext k;cases second <;> rcases k with k|k
    · rfl
    · cases k <;> rfl
    · rfl
    · cases k <;> rfl
  rw [he1] at h1
  exact join h0 h1
/-- Each real comparison pays both physical copies and actual finite comparator instructions. -/
theorem comparison (second : Bool) (a u : Nat) (t : List Bool) :
    ∃q≤60*(order a t+a+u+1),Runs program q (.left second) (context a u t [] [] [] [])
      (.branch second) (context a u t [] [] [decide (order a t<limit second a u)] []) :=by
  obtain ⟨q,hq,h1⟩:=less_call second a u (order a t) (limit second a u) t
  have hh:=join (operands second a u t) h1
  refine ⟨_,?_,hh⟩
  have hl:limit second a u≤ a+u:=by cases second <;> simp only [limit,ite_true,Bool.false_eq_true,ite_false] <;> omega
  omega
/-- One literal pop consumes the actual finite comparator result, with real branch routing. -/
theorem branch (second bit : Bool) (a u : Nat) (t : List Bool) :
    Runs program 1 (.branch second) (context a u t [] [] [bit] [])
      (if bit then (if second then .emit true else .left true) else .emit false)
      (context a u t [] [] [] []) :=by
  apply one_base program (.branch second) _
    (.pop (aux .valid) (.emit false) (.emit false) (if second then .emit true else .left true)) _ _ rfl
  · cases bit <;> rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- The acquired zero flag is peeked physically and retained; zero never reaches comparison. -/
theorem zero_peek (a u : Nat) (t : List Bool) :
    Runs program 1 .zero (context a u t [] [] [] [])
      (if zero a t then .emit false else .left false) (context a u t [] [] [] []) :=by
  apply one_base program .zero _ (.peek (geometryStack (G.aux .zero)) (.emit false) (.left false) (.emit false)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (Label.emit false) (Label.left false) (Label.emit false)
      ((cache a t (G.aux .zero)).head?))=some _
    rw [cache_zero]
    cases zero a t <;> rfl
  · rfl
/-- The sole verdict bit is physically written after actual guard control. -/
theorem emit (bit : Bool) (a u : Nat) (t : List Bool) :
    Runs program 1 (.emit bit) (context a u t [] [] [] []) .done (context a u t [] [] [] [bit]) :=by
  apply one_base program (.emit bit) .done (.push (aux .output) bit .done) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Entire guard from the ACTUALLY acquired geometry cache; no order/advised branch input. -/
theorem guard_run (a u : Nat) (t : List Bool) :
    ∃q≤400*(a+u+t.length+1),Runs program q .zero (context a u t [] [] [] []) .done (result a u t) :=by
  have hi:order a t≤ a+t.length+1:=(order_le a t).trans (max_le (by omega) (by omega))
  have h0:=zero_peek a u t
  cases hz:zero a t with
  | true=>
    rw [hz] at h0
    have hh:=join h0 (emit false a u t)
    refine ⟨2,by omega,?_⟩
    simpa only [result,accepted,hz,ite_true] using hh
  | false=>
    rw [hz] at h0
    obtain ⟨b,hb,h1⟩:=comparison false a u t
    have h2:=branch false (decide (order a t<a)) a u t
    have hh:=join (join h0 h1) h2
    by_cases ha:order a t<a
    · simp only [ha,decide_true,ite_true] at hh
      obtain ⟨c,hc,h3⟩:=comparison true a u t
      have h4:=branch true (decide (order a t<u)) a u t
      have hmore:=join (join hh h3) h4
      by_cases hu:order a t<u
      · simp only [hu,decide_true,ite_true] at hmore
        have hall:=join hmore (emit true a u t)
        refine ⟨_,?_,by simpa only [result,accepted,hz,Bool.false_eq_true,ite_false,ha,ite_true,hu,decide_true] using hall⟩
        omega
      · simp only [hu,decide_false,Bool.false_eq_true,ite_false] at hmore
        have hall:=join hmore (emit false a u t)
        refine ⟨_,?_,by simpa only [result,accepted,hz,Bool.false_eq_true,ite_false,ha,ite_true,hu,decide_false] using hall⟩
        omega
    · simp only [ha,decide_false,Bool.false_eq_true,ite_false] at hh
      have hall:=join hh (emit false a u t)
      refine ⟨_,?_,by simpa only [result,accepted,hz,Bool.false_eq_true,ite_false,ha] using hall⟩
      omega
/-- Own complete linear clock in the ACTUAL original metadata/index input bytes. -/
def runBound (a u : Nat) (t : List Bool) : Nat :=10000*(a+u+t.length+1)
/-- Complete whole source pays the actual geometry call before every guard operation. -/
theorem source_trace (a u : Nat) (t : List Bool) :
    ∃q,q+1≤ runBound a u t ∧ Runs program q .start (input a u t) .done (result a u t) :=by
  obtain ⟨b,hb,h0⟩:=geometry_call a u t
  obtain ⟨c,hc,h1⟩:=guard_run a u t
  refine ⟨b+c,?_,join h0 h1⟩
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardComponents
