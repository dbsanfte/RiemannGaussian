/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryPrimitives
/-! # Paid unary-exponent scan constructing binary center and alpha words -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryPower
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryArithmetic
open SemiprimeD1StackPhaseGeometryPrimitives SemiprimeD1StackProcedureTrace
/-- Actual center-building state; only the unprocessed exponent copy is consumed. -/
def stateData (a t remaining center : List Bool) : Stack→List Bool :=data a t remaining center [] [] [] [] [] [] [] []
/-- One metadata cell physically adds one low zero to the binary power. -/
theorem power_step (a t : List Bool) (b : Bool) (remaining center : List Bool) :
    Runs program 2 .power (stateData a t (b::remaining) center)
      .power (stateData a t remaining (false::center)) :=by
  have h0:Runs program 1 .power (stateData a t (b::remaining) center)
      .shift (stateData a t remaining center):=by
    apply one_base program .power .shift (.pop (aux .counter) .alphaCopy .shift .shift) _ _ rfl
    · cases b <;> rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h1:=push .shift .power (aux .center) false (stateData a t remaining center) rfl
  have he:Function.update (stateData a t remaining center) (aux .center)
      (false::stateData a t remaining center (aux .center))=stateData a t remaining (false::center):=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h1
  exact join h0 h1
/-- Complete physical metadata scan costs exactly two instructions per cell plus EOF. -/
theorem power_run (a t remaining center : List Bool) :
    Runs program (2*remaining.length+1) .power (stateData a t remaining center)
      .alphaCopy (stateData a t [] (List.replicate remaining.length false++center)) :=by
  induction remaining generalizing center with
  | nil=>
    apply one_base program .power .alphaCopy (.pop (aux .counter) .alphaCopy .shift .shift) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  | cons b remaining ih=>
    have hh:=join (power_step a t b remaining center) (ih (false::center))
    have hv:List.replicate remaining.length false++(false::center)=List.replicate (b::remaining).length false++center:=by
      rw [List.length_cons,List.replicate_succ']
      simp only [List.append_assoc,List.singleton_append]
    rw [hv] at hh
    convert hh using 1
    simp only [List.length_cons]
    omega
/-- All actual outputs after center and alpha acquisition, before any subtraction. -/
def prepared (a t : List Bool) : Stack→List Bool :=
  data a t [] (powerWord a.length) (powerWord (a.length+1)) [] [] [] [] [] [] []
/-- Original a and t are preserved through the actual copy/shift program. -/
theorem source_run (a t : List Bool) :
    Runs program (12*a.length+16) .start (input a t) (.left false) (prepared a t) :=by
  have h0:=copy_empty 0 .start .seed rfl (input a t) rfl rfl
  have h0e:Function.update (input a t) (copyTarget 0) (input a t (copySource 0))=stateData a t a []:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [h0e] at h0
  have h1:=push .seed .power (aux .center) true (stateData a t a []) rfl
  have h1e:Function.update (stateData a t a []) (aux .center)
      (true::stateData a t a [] (aux .center))=stateData a t a [true]:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [h1e] at h1
  have h2:=power_run a t a [true]
  have h3:=copy_empty 1 .alphaCopy .alphaShift rfl (stateData a t [] (powerWord a.length)) rfl rfl
  have h3e:Function.update (stateData a t [] (powerWord a.length)) (copyTarget 1)
      (stateData a t [] (powerWord a.length) (copySource 1))=
      data a t [] (powerWord a.length) (powerWord a.length) [] [] [] [] [] [] []:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [h3e] at h3
  have h4:=push .alphaShift (.left false) (aux .alpha) false
    (data a t [] (powerWord a.length) (powerWord a.length) [] [] [] [] [] [] []) rfl
  have h4e:Function.update (data a t [] (powerWord a.length) (powerWord a.length) [] [] [] [] [] [] []) (aux .alpha)
      (false::powerWord a.length)=prepared a t:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  change Runs program 1 .alphaShift _ (.left false)
    (Function.update _ (aux .alpha) (false::powerWord a.length)) at h4
  rw [h4e] at h4
  have hh:=join (join (join (join h0 h1) h2) h3) h4
  change Runs program (((((5*a.length+4)+1)+(2*a.length+1))+(5*(powerWord a.length).length+4))+1) .start _ (.left false) _ at hh
  rw [powerWord_length] at hh
  convert hh using 1
  omega
end RiemannGaussian.SemiprimeD1StackPhaseGeometryPower
