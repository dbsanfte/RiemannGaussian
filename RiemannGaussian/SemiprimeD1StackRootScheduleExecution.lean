/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleStages
/-! # Complete original-binary root schedule execution and its own clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleExecution
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootScheduleStages
open SemiprimeD1StackRootScheduleArithmetic SemiprimeD1StackRootSchedulePrimitives
open SemiprimeD1StackProcedureTrace
/-- Exact final actual15-role bank: N stays binary, width/metadata are paid markers,
all copying/divider work is empty, and the constant divisor stays retained. -/
def result (bits : List Bool) : Stack→List Bool :=
  context bits (D.unary (lambda bits.length)) (D.unary (levels bits.length))
    (D.unary (exponent bits.length)) (D.unary (minimum bits.length))
/-- Actual clean halt, with no silently erased physical work or real return cells. -/
def done (bits : List Bool) : C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- One fixed polynomial in original INPUT BYTES, never supplied to the machine. -/
def runBound (bits : List Bool) : Nat :=100000000*(bits.length+1)^3
/-- Pure numeric substitution for the actual four source stages and final halt. -/
theorem arithmetic_bound (n lam u a b c d : Nat) (hl : lam≤n+20) (hu : u≤lam)
    (ha : a≤5*n+28) (hb : b≤5*n+4+1000*(n+1)^2)
    (hc : c≤5*lam+12+1000*(lam+1)^2)
    (hd : d≤5*lam+12+180000*(lam+1)+10*u) :
    a+b+c+d+1≤100000000*(n+1)^3 := by
  have hl':lam+1≤21*(n+1):=by omega
  have hp: (lam+1)^2≤441*(n+1)^2:=by
    have h:=Nat.pow_le_pow_left hl' 2
    simpa only [mul_pow,show (21:Nat)^2=441 by decide] using h
  have hs:a+b+c+d+1≤10000000*(n+1)^2:=by nlinarith
  have hpow:(n+1)^2≤(n+1)^3:=Nat.pow_le_pow_right (by omega) (by decide)
  exact hs.trans ((Nat.mul_le_mul_left _ hpow).trans (Nat.mul_le_mul_right _ (by decide)))
/-- ENTIRE paid root acquisition starts with only the original binary word.
All source traces below are concrete frozen/bootstrap/divider instructions. -/
theorem source_trace (bits : List Bool) :
    ∃t,t+1≤runBound bits ∧ Runs program t .start (input bits) .done (result bits) := by
  obtain ⟨a,ha,h0⟩:=setup bits
  obtain ⟨b,hb,h1⟩:=acquire_lambda bits
  obtain ⟨c,hc,h2⟩:=acquire_minimum bits
  obtain ⟨d,hd,h3⟩:=acquire_levels bits
  refine ⟨((a+b)+c)+d,?_,join (join (join h0 h1) h2) h3⟩
  exact arithmetic_bound bits.length (lambda bits.length) (levels bits.length) a b c d
    (lambda_le bits.length) (Nat.div_le_self _ _) ha hb hc hd
/-- Real original-input source halt with the same own fixed polynomial clock. -/
theorem source_run (bits : List Bool) :
    ∃t≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,hr⟩:=source_trace bits
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result bits) [] finish hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- The same program has a genuine one-input initialization, with no hidden
width, scale, lambda, divisor, root levels, exponent or minimum guard input. -/
theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:SemiprimeD1StackCalls.initial (boot .input) Label.start bits=initial bits:=by
    apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:C.State Stack Label))
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k <;> rfl
  exact (SemiprimeD1StackCalls.initial_correct (boot .input) (aux .exponent) Label.start program bits).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Complete original-N acquisition on ONE fixed genuine finite-control machine. -/
noncomputable def acquireInTime (bits : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (boot .input) (aux .exponent) .start program
  let h:=source_run bits
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackRootScheduleExecution
