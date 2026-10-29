/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputWidthLoops

/-! # Whole actual physical active-digit bound source
Every copy, offset-product cell, paired subtraction/minimum read, excess drain,
bound bit, call/return and enclosing halt is paid on this literal program.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackInputWidthExecution
open SemiprimeD1StackInputWidth SemiprimeD1StackInputWidthComponents
open SemiprimeD1StackInputWidthLoops SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)

/-- Actual original-width suffix after consuming physically acquired offsets. -/
def remaining (c : Cache) : List Bool := c.width.drop (c.index.length*c.radix.length)
/-- Width specified by the actual saturating-subtraction/minimum trace. -/
def width (c : Cache) : ℕ := min c.radix.length (c.width.length-c.index.length*c.radix.length)
/-- Exact physically constructed binary power-of-two bound. -/
def bound (c : Cache) : List Bool := List.replicate (width c) false++[true]
/-- Exact clean halt: every actual input cache is retained, all work is empty. -/
def done (c : Cache) : C.State Stack Label := ⟨none,none,none,store c [] [] [] [] (bound c),[]⟩
/-- Output-sensitive bound in original physical cache/offset cells. Numerical
bound VALUE never enters this allowance or the executing control. -/
def timeBound (c : Cache) : ℕ :=
  100*(c.width.length+c.radix.length+c.index.length+c.index.length*c.radix.length+1)

/-- The literal high one is actually pushed before minimum-loop zero pushes. -/
theorem init_bound (c : Cache) (word : List Bool) :
    Runs program 1 .initBound (store c word [] [] c.radix []) .minLoop (store c word [] [] c.radix [true]) := by
  apply one_base program .initBound .minLoop (.push .output true .minLoop) _ _ rfl
  · rfl
  · funext k;cases k <;> rfl

/-- Complete SAME actual source, on arbitrary physical marker bytes and every
cache length, including zero radix/width and arbitrarily large indices. -/
theorem source_run (c : Cache) :
    ∃t≤timeBound c,C.run program t (initial c)=some (done c) := by
  have h0:=copy_width c
  have h1:=copy_index c
  obtain ⟨a,ha,h2⟩:=product_call c
  obtain ⟨b,hb,h3⟩:=skip_loop c c.width (unary (c.index.length*c.radix.length))
  simp only [unary,List.length_replicate] at hb h3
  change Runs program b .skipLoop (store c c.width [] (unary (c.index.length*c.radix.length)) [] [])
    .copyLimit (store c (remaining c) [] [] [] []) at h3
  have h4:=copy_limit c (remaining c)
  have h5:=init_bound c (remaining c)
  obtain ⟨d,hd,h6⟩:=min_loop c (remaining c) c.radix [true]
  have hw : min (remaining c).length c.radix.length=width c := by
    simp only [remaining,width,List.length_drop,Nat.min_comm]
  rw [hw] at h6
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6
  obtain ⟨finish,hr,ho⟩:=h [] (initial c) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (store c [] [] [] [] (bound c)) [] finish ho
  refine ⟨((((((5*c.width.length+4)+(5*c.index.length+4))+(a+1))+b)+(5*c.radix.length+4))+1)+d+1,?_,?_⟩
  · have hrem : (remaining c).length≤c.width.length := by simp only [remaining,List.length_drop];omega
    have hp : 5*(c.index.length*(2*c.radix.length+3)+1)=
        10*(c.index.length*c.radix.length)+15*c.index.length+5 := by ring
    rw [hp] at ha
    unfold timeBound
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl
/-- Exact completed output, with no supplied width/bound/verdict answer. -/
theorem output_bound (c : Cache) : (done c).data .output=bound c := rfl
/-- All actual original cache bytes, including arbitrary marker bits, survive. -/
theorem retained_caches (c : Cache) :
    (done c).data .widthCache=c.width ∧ (done c).data .radixCache=c.radix ∧ (done c).data .indexCache=c.index :=
  ⟨rfl,rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackInputWidthExecution
