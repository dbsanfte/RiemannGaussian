/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSchedulePrimitives
/-! # Paid fixed literal root-schedule constants and original-input bootstrap -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleSeeds
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootSchedulePrimitives
open SemiprimeD1StackProcedureTrace
/-- Actual fixed twenty-marker instruction chain. -/
def lambdaPhase (i : Nat) : Label :=if h:i<20 then .seedLambda ⟨i,h⟩ else .seedTwo 0
/-- Actual fixed two-marker divisor instruction chain. -/
def twoPhase (i : Nat) : Label :=if h:i<2 then .seedTwo ⟨i,h⟩ else .copyWidth
/-- Actual fixed eight-marker guard instruction chain. -/
def minimumPhase (i : Nat) : Label :=if h:i<8 then .seedMinimum ⟨i,h⟩ else .copyMinimum
/-- All twenty original-scale offset markers execute literal pushes. -/
theorem lambda_seed (d : Stack→List Bool) :
    Runs program 20 (.seedLambda 0) d (.seedTwo 0)
      (Function.update d (aux .lambda) (D.unary 20++d (aux .lambda))) := by
  exact push_chain lambdaPhase 20 (aux .lambda)
    (by intro i hi;interval_cases i <;> rfl) 20 0 (by omega) d
/-- Both divisor markers are physically written, never supplied in initial data. -/
theorem two_seed (d : Stack→List Bool) :
    Runs program 2 (.seedTwo 0) d .copyWidth
      (Function.update d (divStack .divisor) (D.unary 2++d (divStack .divisor))) := by
  exact push_chain twoPhase 2 (divStack .divisor)
    (by intro i hi;interval_cases i <;> rfl) 2 0 (by omega) d
/-- All eight minimum-level offset cells execute actual writes. -/
theorem minimum_seed (d : Stack→List Bool) :
    Runs program 8 (.seedMinimum 0) d .copyMinimum
      (Function.update d (aux .minimum) (D.unary 8++d (aux .minimum))) := by
  exact push_chain minimumPhase 8 (aux .minimum)
    (by intro i hi;interval_cases i <;> rfl) 8 0 (by omega) d
/-- Exactly the real returned bootstrap payload; every new metadata/work field empty. -/
def afterBootstrap (bits : List Bool) : Stack→List Bool :=
  store (Boot.done bits).store (fun _=>[]) (fun _=>[])
/-- Fixed bootstrap call retains original binary N and physically acquires width. -/
theorem bootstrap_call (bits : List Bool) :
    Runs program (5*bits.length+5) .start (input bits) .choose (afterBootstrap bits) := by
  apply included_call program boot Label.bootstrap boot_injective Boot.code (.scan,false)
    (fun _=>rfl) .start .choose rfl (5*bits.length+4)
    (SemiprimeD1BinaryBootstrap.state .scan false none bits [] [] []) (Boot.done bits)
    _ _ rfl rfl (SemiprimeD1BinaryBootstrap.bootstrap_run bits)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The exact fixed offset chosen by a real EMPTY-width test. -/
def seed (n : Nat) : Nat :=if n=0 then 1 else 20
/-- The width-zero and positive-width branches are both fully paid actual code. -/
theorem choose_seed (bits : List Bool) :
    Runs program (1+seed bits.length) .choose (afterBootstrap bits) (.seedTwo 0)
      (Function.update (afterBootstrap bits) (aux .lambda) (D.unary (seed bits.length))) := by
  cases bits with
  | nil=>
    have h0:=SemiprimeD1StackPhysicalLoops.peek_empty program .choose .zeroLambda (.seedLambda 0) (.seedLambda 0)
      (boot .width) rfl (afterBootstrap []) rfl
    have h1:=push .zeroLambda (.seedTwo 0) (aux .lambda) (afterBootstrap []) rfl
    exact join h0 h1
  | cons bit bits=>
    have h0:=SemiprimeD1StackPhysicalLoops.peek_nonempty program .choose .zeroLambda (.seedLambda 0) (boot .width)
      rfl (afterBootstrap (bit::bits)) true (D.unary bits.length) rfl
    have h1:=lambda_seed (afterBootstrap (bit::bits))
    simpa only [seed,List.length_cons,Nat.succ_ne_zero,ite_false,show afterBootstrap (bit::bits) (aux .lambda)=[] from rfl,List.append_nil] using join h0 h1
end RiemannGaussian.SemiprimeD1StackRootScheduleSeeds
