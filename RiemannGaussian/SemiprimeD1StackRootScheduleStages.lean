/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleHalves
import RiemannGaussian.SemiprimeD1StackRootScheduleSeeds
/-! # Actual original-N root metadata stages with no prepared counters -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleStages
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootSchedulePrimitives
open SemiprimeD1StackRootScheduleLoops SemiprimeD1StackRootScheduleSeeds
open SemiprimeD1StackRootScheduleArithmetic SemiprimeD1StackProcedureTrace
/-- Reached clean physical store, retaining original binary N and acquired width. -/
def context (bits lam levels exponent minimum : List Bool) : Stack→List Bool :=
  store (Boot.done bits).store (D.contents [] (D.unary 2) [] [] [] [])
    (metadata lam levels exponent minimum [])
/-- Exact acquired guard after the real second logarithmic loop. -/
def minimum (n : Nat) : Nat :=4*(lambda n).size+8
/-- Exact acquired original root level count. -/
def levels (n : Nat) : Nat :=lambda n/2^17
/-- Root exponent is formed by two real level-word copies. -/
def exponent (n : Nat) : Nat :=2*levels n
/-- The actual bootstrap, width branch, offset writes and two divisor writes. -/
theorem setup (bits : List Bool) :
    ∃t≤5*bits.length+28,Runs program t .start (input bits) .copyWidth
      (context bits (D.unary (seed bits.length)) [] [] []) := by
  have h0:=bootstrap_call bits
  have h1:=choose_seed bits
  have h2:=two_seed (Function.update (afterBootstrap bits) (aux .lambda) (D.unary (seed bits.length)))
  have he:Function.update (Function.update (afterBootstrap bits) (aux .lambda) (D.unary (seed bits.length)))
      (divStack .divisor)
      (D.unary 2++(Function.update (afterBootstrap bits) (aux .lambda) (D.unary (seed bits.length))) (divStack .divisor))=
      context bits (D.unary (seed bits.length)) [] [] []:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
  rw [he] at h2
  refine ⟨(5*bits.length+5)+(1+seed bits.length)+2,?_,join (join h0 h1) h2⟩
  have hs:seed bits.length≤20:=by unfold seed;split <;> omega
  omega
/-- Actual source lambda acquisition from the real copied bit-width word. -/
theorem acquire_lambda (bits : List Bool) :
    ∃t≤5*bits.length+4+1000*(bits.length+1)^2,
      Runs program t .copyWidth (context bits (D.unary (seed bits.length)) [] [] [])
        (.seedMinimum 0) (context bits (D.unary (lambda bits.length)) [] [] []) := by
  let base:=context bits [] [] [] []
  let before:=context bits (D.unary (seed bits.length)) [] [] []
  have h0:=copy_call 0 .copyWidth (.probe false) rfl before rfl
  have hlen:(before (copySource 0)).length=bits.length:=by
    change (List.replicate bits.length true).length=bits.length
    simp only [List.length_replicate]
  rw [hlen] at h0
  have he0:Function.update before (copyTarget 0) (before (copySource 0)++before (copyTarget 0))=
      ready base false bits.length (D.unary (seed bits.length)):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> first | rfl | (change D.unary bits.length++[]=D.unary bits.length;exact List.append_nil _)
      · cases k <;> rfl
  rw [he0] at h0
  obtain ⟨ts,ht,hs⟩:=size_loop false base bits.length (D.unary (seed bits.length))
  have hw:D.unary (factor false*bits.length.size)++D.unary (seed bits.length)=D.unary (lambda bits.length):=by
    rw [←SemiprimeD1StackUnaryDivmod.unary_add]
    congr 1
    simp only [factor,Bool.false_eq_true,ite_false,Nat.one_mul]
    unfold lambda seed
    split <;> simp_all [Nat.add_comm]
  have he1:ready base false 0 (D.unary (factor false*bits.length.size)++D.unary (seed bits.length))=
      context bits (D.unary (lambda bits.length)) [] [] []:=by
    rw [hw]
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
  rw [he1] at hs
  refine ⟨(5*bits.length+4)+ts,by omega,?_⟩
  exact join h0 hs
/-- Eight guard offset writes, the real lambda copy and complete second size loop. -/
theorem acquire_minimum (bits : List Bool) :
    ∃t≤5*lambda bits.length+12+1000*(lambda bits.length+1)^2,
      Runs program t (.seedMinimum 0) (context bits (D.unary (lambda bits.length)) [] [] [])
        .copyLevels (context bits (D.unary (lambda bits.length)) [] [] (D.unary (minimum bits.length))) := by
  let base:=context bits (D.unary (lambda bits.length)) [] [] []
  let seeded:=context bits (D.unary (lambda bits.length)) [] [] (D.unary 8)
  have h0:=minimum_seed base
  have he0:Function.update base (aux .minimum) (D.unary 8++base (aux .minimum))=seeded:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  rw [he0] at h0
  have h1:=copy_call 1 .copyMinimum (.probe true) rfl seeded rfl
  have hlen:(seeded (copySource 1)).length=lambda bits.length:=by
    change (List.replicate (lambda bits.length) true).length=lambda bits.length
    simp only [List.length_replicate]
  rw [hlen] at h1
  have he1:Function.update seeded (copyTarget 1) (seeded (copySource 1)++seeded (copyTarget 1))=
      ready base true (lambda bits.length) (D.unary 8):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> first | rfl | (change D.unary (lambda bits.length)++[]=D.unary (lambda bits.length);exact List.append_nil _)
      · cases k <;> rfl
  rw [he1] at h1
  obtain ⟨ts,ht,hs⟩:=size_loop true base (lambda bits.length) (D.unary 8)
  have he2:ready base true 0 (D.unary (factor true*(lambda bits.length).size)++D.unary 8)=
      context bits (D.unary (lambda bits.length)) [] [] (D.unary (minimum bits.length)):=by
    have hw:D.unary (factor true*(lambda bits.length).size)++D.unary 8=D.unary (minimum bits.length):=by
      rw [←SemiprimeD1StackUnaryDivmod.unary_add]
      rfl
    rw [hw]
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
  rw [he2] at hs
  refine ⟨8+(5*lambda bits.length+4)+ts,by omega,?_⟩
  exact join (join h0 h1) hs
/-- The original root block and exponent execute seventeen full real divisions,
physical quotient delivery and BOTH actual exponent copies. -/
theorem acquire_levels (bits : List Bool) :
    ∃t≤5*lambda bits.length+12+180000*(lambda bits.length+1)+10*levels bits.length,
      Runs program t .copyLevels
        (context bits (D.unary (lambda bits.length)) [] [] (D.unary (minimum bits.length)))
        .done (context bits (D.unary (lambda bits.length)) (D.unary (levels bits.length))
          (D.unary (exponent bits.length)) (D.unary (minimum bits.length))) := by
  let base:=context bits (D.unary (lambda bits.length)) [] [] (D.unary (minimum bits.length))
  let first:=context bits (D.unary (lambda bits.length)) (D.unary (levels bits.length)) [] (D.unary (minimum bits.length))
  let second:=context bits (D.unary (lambda bits.length)) (D.unary (levels bits.length))
    (D.unary (levels bits.length)) (D.unary (minimum bits.length))
  have h0:=copy_call 1 .copyLevels (.halve 0) rfl base rfl
  have hl0:(base (copySource 1)).length=lambda bits.length:=by
    change (List.replicate (lambda bits.length) true).length=lambda bits.length
    simp only [List.length_replicate]
  rw [hl0] at h0
  have he0:Function.update base (copyTarget 1) (base (copySource 1)++base (copyTarget 1))=
      clean base (lambda bits.length):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> first | rfl | (change D.unary (lambda bits.length)++[]=D.unary (lambda bits.length);exact List.append_nil _)
      · cases k <;> rfl
  rw [he0] at h0
  obtain ⟨th,ht,hh⟩:=SemiprimeD1StackRootScheduleHalves.halves base 17 (by omega) (lambda bits.length)
  have hi:SemiprimeD1StackRootScheduleHalves.index 17 (by omega)=(0:Fin 18):=by apply Fin.ext;rfl
  rw [hi] at hh
  have he1:Function.update (clean base 0) (aux .levels)
      (D.unary (lambda bits.length/2^17)++base (aux .levels))=first:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | (change D.unary (levels bits.length)++[]=D.unary (levels bits.length);exact List.append_nil _)
  rw [he1] at hh
  have h1:=copy_call 2 .copyFirst .copySecond rfl first rfl
  have hl1:(first (copySource 2)).length=levels bits.length:=by
    change (List.replicate (levels bits.length) true).length=levels bits.length
    simp only [List.length_replicate]
  rw [hl1] at h1
  have he2:Function.update first (copyTarget 2) (first (copySource 2)++first (copyTarget 2))=second:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | (change D.unary (levels bits.length)++[]=D.unary (levels bits.length);exact List.append_nil _)
  rw [he2] at h1
  have h2:=copy_call 2 .copySecond .done rfl second rfl
  have hl2:(second (copySource 2)).length=levels bits.length:=hl1
  rw [hl2] at h2
  have hw:D.unary (levels bits.length)++D.unary (levels bits.length)=D.unary (exponent bits.length):=by
    rw [←SemiprimeD1StackUnaryDivmod.unary_add]
    congr 1
    unfold exponent
    omega
  have he3:Function.update second (copyTarget 2) (second (copySource 2)++second (copyTarget 2))=
      context bits (D.unary (lambda bits.length)) (D.unary (levels bits.length))
        (D.unary (exponent bits.length)) (D.unary (minimum bits.length)):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact hw
  rw [he3] at h2
  refine ⟨((5*lambda bits.length+4)+th)+(5*levels bits.length+4)+(5*levels bits.length+4),?_,join (join (join h0 hh) h1) h2⟩
  nlinarith
end RiemannGaussian.SemiprimeD1StackRootScheduleStages
