/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeActivation
/-! # Literal feasible-branch subtraction and the sole failed end test
Only actual unary marker pops decide whether another child is visited. The
source has neither a natural division instruction nor an exponent catalogue.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeSubtract
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeActivation (join)
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Splitting unary metadata means splitting actual marker cells, not an instruction. -/
theorem unary_add (a b:Nat) :unary (a+b)=unary a++unary b:=List.replicate_add a b true
/-- One successful subtraction pair pops one actual todo and one actual budget marker. -/
theorem pair (v:Words) (todo budget:List Bool) (ht:v.subTodo=true::todo) (hb:v.budget=true::budget) :
    Runs program 2 (ctl .subtract) (store v) (ctl .subtract)
      (store {v with subTodo:=todo,budget:=budget}):=by
  let v1:Words:={v with subTodo:=todo}
  have h0:=pop_run .subtract (ctl .increment) (ctl .budgetPop) (ctl .budgetPop) .subTodo (store v)
    (true::todo) rfl ht
  rw [store_write] at h0
  change Runs program 1 _ _ (ctl .budgetPop) (store v1) at h0
  have h1:=pop_run .budgetPop (ctl .failure) (ctl .subtract) (ctl .subtract) .budget (store v1)
    (true::budget) rfl hb
  rw [store_write] at h1
  change Runs program 1 _ _ (ctl .subtract) (store {v with subTodo:=todo,budget:=budget}) at h1
  exact join h0 h1
/-- Every matched prefix is consumed by exactly two physical pops per marker. -/
theorem pairs (n:Nat) (v:Words) (todo budget:List Bool)
    (ht:v.subTodo=unary n++todo) (hb:v.budget=unary n++budget) :
    Runs program (2*n) (ctl .subtract) (store v) (ctl .subtract)
      (store {v with subTodo:=todo,budget:=budget}):=by
  induction n generalizing v with
  | zero=>
    simp only [unary,List.replicate_zero,List.nil_append] at ht hb
    have he:store {v with subTodo:=todo,budget:=budget}=store v:=by
      rw [←ht,←hb]
    rw [he]
    exact runs_refl program _ _
  | succ n ih=>
    rw [unary_succ,List.cons_append] at ht hb
    let v1:Words:={v with subTodo:=unary n++todo,budget:=unary n++budget}
    have h0:=pair v (unary n++todo) (unary n++budget) ht hb
    have h1:=ih v1 rfl rfl
    have hh:=join h0 h1
    change Runs program (2+2*n) _ _ _ (store {v with subTodo:=todo,budget:=budget}) at hh
    convert hh using 1;omega
/-- A complete feasible subtraction pays its final todo EOF and exponent-marker push. -/
theorem success (v:Words) (w R e:Nat) (ht:v.subTodo=unary w) (hb:v.budget=unary (w+R))
    (he:v.exponent=unary e) :
    Runs program (2*w+2) (ctl .subtract) (store v) (ctl (.save 4))
      (store {v with subTodo:=[],budget:=unary R,exponent:=unary (e+1)}):=by
  let v1:Words:={v with subTodo:=[],budget:=unary R}
  have h0:=pairs w v [] (unary R) (by simpa only [List.append_nil] using ht) (by rw [←unary_add];exact hb)
  change Runs program (2*w) _ _ _ (store v1) at h0
  have h1:=pop_run .subtract (ctl .increment) (ctl .budgetPop) (ctl .budgetPop) .subTodo (store v1) [] rfl rfl
  rw [store_write] at h1
  change Runs program 1 _ _ (ctl .increment) (store v1) at h1
  have h2:=push_run .increment (ctl (.save 4)) .exponent true (store v1) rfl
  rw [store_write] at h2
  change Runs program 1 _ _ _ (store {v with subTodo:=[],budget:=unary R,exponent:=true::v.exponent}) at h2
  rw [he,←unary_succ] at h2
  have hh:=join h0 (join h1 h2)
  simpa only [Nat.add_assoc] using hh
/-- The first failed subtraction reaches cleanup and never calls a spurious child. -/
theorem failure (v:Words) (R d:Nat) (ht:v.subTodo=unary (R+d+1)) (hb:v.budget=unary R) :
    Runs program (2*R+d+3) (ctl .subtract) (store v) (ctl (.cleanup 0))
      (store {v with subTodo:=[],budget:=[]}):=by
  let v1:Words:={v with subTodo:=unary (d+1),budget:=[]}
  let v2:Words:={v1 with subTodo:=unary d}
  have h0:=pairs R v (unary (d+1)) [] (by
    rw [←unary_add]
    simpa only [Nat.add_assoc] using ht) (by simpa only [List.append_nil] using hb)
  change Runs program (2*R) _ _ _ (store v1) at h0
  have h1:=pop_run .subtract (ctl .increment) (ctl .budgetPop) (ctl .budgetPop) .subTodo (store v1)
    (true::unary d) rfl (unary_succ d)
  rw [store_write] at h1
  change Runs program 1 _ _ (ctl .budgetPop) (store v2) at h1
  have h2:=pop_run .budgetPop (ctl .failure) (ctl .subtract) (ctl .subtract) .budget (store v2) [] rfl rfl
  rw [store_write] at h2
  change Runs program 1 _ _ (ctl .failure) (store v2) at h2
  have h3:=drain_loop .failure (ctl (.cleanup 0)) .subTodo rfl (store v2) (unary d) rfl
  rw [store_write] at h3
  change Runs program ((unary d).length+1) _ _ _ (store {v with subTodo:=[],budget:=[]}) at h3
  rw [unary_length] at h3
  have hh:=join h0 (join h1 (join h2 h3))
  convert hh using 1;omega
end RiemannGaussian.SemiprimeD1StackWeightedModeSubtract
