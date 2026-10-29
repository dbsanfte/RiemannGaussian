/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryWidthPrimitives
/-! # Actual a-driven unary doubling creates and pays N=2^(a+1) -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthSetup
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary unary_add)
/-- Each actual copied grid marker is popped and replaced by one real true push on the retained grid stack. -/
theorem double_move (w:Words) (xs:List Bool) :
    Runs program (2*xs.length+1) .doubleMove (bank {w with multiplier:=xs}) .power
      (bank {w with multiplier:=[],grid:=unary xs.length++w.grid}) :=by
  induction xs generalizing w with
  | nil=>
    have h:=pop_run .doubleMove .power .doublePush .doublePush (aux .multiplier)
      (bank {w with multiplier:=[]}) [] rfl rfl
    rw [update_multiplier] at h
    exact h
  | cons b xs ih=>
    have h0:=pop_run .doubleMove .power .doublePush .doublePush (aux .multiplier)
      (bank {w with multiplier:=b::xs}) (b::xs) rfl rfl
    rw [update_multiplier] at h0
    have he:SemiprimeD1StackBytecode.choose Label.power .doublePush .doublePush (b::xs).head?=.doublePush:=by cases b <;> rfl
    rw [he] at h0
    have h1:=push_run .doublePush .doubleMove (aux .grid) true (bank {w with multiplier:=xs}) rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (aux .grid) (true::w.grid)) at h1
    rw [update_grid] at h1
    have h2:=ih {w with grid:=true::w.grid}
    have h:=join (join h0 h1) h2
    have heq:unary xs.length++true::w.grid=unary (b::xs).length++w.grid:=by
      simp only [List.length_cons,SemiprimeD1StackUnaryDivmod.unary_succ,SemiprimeD1StackUnaryDivmod.unary_bump,List.cons_append]
    change Runs _ _ _ _ _ (bank {w with multiplier:=[],grid:=unary xs.length++true::w.grid}) at h
    rw [heq] at h
    convert h using 1
    simp only [List.length_cons]
    omega
/-- Exact real scan/copy/doubling clock, before any arithmetic gate or template is supplied. -/
def powerTime :Nat→Nat→Nat
  | 0,_=>1
  | n+1,current=>1+(5*current+4)+(2*current+1)+powerTime n (2*current)
/-- Actual copied a markers drive all doublings; all existing grid markers are physically copied and moved each time. -/
theorem power_run (a M remaining current:Nat) :
    Runs program (powerTime remaining current) .power
      (bank {a:=unary a,m:=unary M,todo:=unary remaining,grid:=unary current}) (.gate 0)
      (bank {a:=unary a,m:=unary M,grid:=unary (2^remaining*current)}) :=by
  induction remaining generalizing current with
  | zero=>
    have h:=pop_run .power (.gate 0) .doubleCopy .doubleCopy (aux .todo)
      (bank {a:=unary a,m:=unary M,todo:=[],grid:=unary current}) [] rfl rfl
    rw [update_todo] at h
    change Runs program 1 .power (bank {a:=unary a,m:=unary M,grid:=unary current}) (.gate 0)
      (bank {a:=unary a,m:=unary M,grid:=unary current}) at h
    simpa only [powerTime,pow_zero,Nat.one_mul,unary,List.replicate_zero] using h
  | succ remaining ih=>
    have h0:=pop_run .power (.gate 0) .doubleCopy .doubleCopy (aux .todo)
      (bank {a:=unary a,m:=unary M,todo:=unary (remaining+1),grid:=unary current})
      (true::unary remaining) rfl rfl
    rw [update_todo] at h0
    have h1:=copy_call .double .doubleCopy .doubleMove rfl
      (bank {a:=unary a,m:=unary M,todo:=unary remaining,grid:=unary current}) (unary current) [] rfl rfl rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (aux .multiplier) (unary current++[])) at h1
    rw [List.append_nil,update_multiplier] at h1
    have h2:=double_move {a:=unary a,m:=unary M,todo:=unary remaining,grid:=unary current} (unary current)
    simp only [unary,List.length_replicate] at h1 h2
    have h3:=ih (2*current)
    have hgrid:List.replicate current true++List.replicate current true=unary (2*current):=by
      rw [←List.replicate_add]
      congr 1
      omega
    rw [hgrid] at h2
    have h:=join (join (join h0 h1) h2) h3
    have hp:2^remaining*(2*current)=2^(remaining+1)*current:=by rw [pow_succ];ring
    rw [hp] at h
    exact h
/-- Paid preserving a-copy, two literal seed markers and all actual grid-doubling transitions. -/
def setupTime (a:Nat) :Nat:=(5*a+4)+1+1+powerTime a 2
/-- The actual source front door acquires its own N by VALUE and arrives at the empty first gate bank. -/
theorem setup_run (a M:Nat) :
    Runs program (setupTime a) .start (input (unary a) (unary M)) (.gate 0)
      (bank (atGate 0 a M (gridSize a))) :=by
  rw [initial_bank]
  have h0:=copy_call .acquireA .start .seedOne rfl (bank {a:=unary a,m:=unary M}) (unary a) [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .todo) (unary a++[])) at h0
  rw [List.append_nil,update_todo] at h0
  have h1:=push_run .seedOne .seedTwo (aux .grid) true (bank {a:=unary a,m:=unary M,todo:=unary a}) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .grid) [true]) at h1
  rw [update_grid] at h1
  have h2:=push_run .seedTwo .power (aux .grid) true (bank {a:=unary a,m:=unary M,todo:=unary a,grid:=[true]}) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .grid) [true,true]) at h2
  rw [update_grid] at h2
  have h3:=power_run a M a 2
  have he:2^a*2=gridSize a:=by rw [gridSize,pow_succ]
  rw [he] at h3
  have h:=join (join (join h0 h1) h2) h3
  simp only [unary,List.length_replicate] at h
  change Runs _ _ _ _ _ (bank {a:=unary a,m:=unary M,grid:=unary (gridSize a)}) at h
  unfold atGate
  rw [zero_registers]
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryWidthSetup
