/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTableBounds
/-! # ALL134 whole child-table roles and genuine DFS return cells at every prefix
The original table/header/order template and actual scope are acquired caller
operands. This is a prepared machine configuration, not an N-only initList.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTableStorage
open SemiprimeD1StackChildLiftTable
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace R
export SemiprimeD1StackChildLiftTableResources (resource resource_pos template_bytes)
end R
namespace O
export SemiprimeD1StackChildLiftTableOriginal (original answer done timeBound)
end O
/-- One fixed whole physical-space bound precedes the entire table/context/scope family. -/
def spacePolynomial {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) : ℕ :=
  10^24*(R.resource old extra oldp newp parent order scope)^2*2^scope.length
/-- Whole source/runtime and actually initialized bytes jointly pay ALL134 data words and real returns. -/
theorem cells_le {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    135*(SemiprimeD1StackVectorTableSpec.inputBytes (O.original old extra oldp newp parent order)+
      (vectorBits scope).length+O.timeBound old extra oldp newp parent order scope+1)≤
      spacePolynomial old extra oldp newp parent order scope := by
  let r := R.resource old extra oldp newp parent order scope
  let e := 2^scope.length
  have hr : 1≤r := R.resource_pos old extra oldp newp parent order scope
  have he : 1≤e := Nat.one_le_pow _ _ (by decide : 1≤(2 : ℕ))
  have hp : r≤r^2 := Nat.le_pow (by decide : 0<2)
  have hpay : r^2≤r^2*e := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r^2) he
  have hi := R.template_bytes old extra oldp newp parent order scope
  change SemiprimeD1StackVectorTableSpec.inputBytes (O.original old extra oldp newp parent order)≤61*r at hi
  have hi' := hi.trans (Nat.mul_le_mul_left 61 (hp.trans hpay))
  have hs : (vectorBits scope).length≤r := Nat.le_add_left _ _
  have hs' := hs.trans (hp.trans hpay)
  have h1 := hr.trans (hp.trans hpay)
  have ht := SemiprimeD1StackChildLiftTableBounds.timeBound_le old extra oldp newp parent order scope
  have ht' : O.timeBound old extra oldp newp parent order scope≤10^20*(r^2*e) := by
    simpa only [SemiprimeD1StackChildLiftTableBounds.polynomial,Nat.mul_assoc] using ht
  unfold spacePolynomial
  rw [Nat.mul_assoc]
  change _≤10^24*(r^2*e)
  omega
/-- EVERY genuine same-source primitive prefix counts both full61-role banks and all real recursive returns. -/
theorem prefix_cells {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order : List ℕ) (scope : List (List Bool)) (fuel : ℕ)
    (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope))=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤ spacePolynomial old extra oldp newp parent order scope := by
  have h := SemiprimeD1StackVectorTableBounds.prefix_cells source
    (O.original old extra oldp newp parent order) (SemiprimeD1StackChildLiftTableInput.raw_empty _ _ _ _ _ _)
    (O.answer old extra newp parent order) (SemiprimeD1StackChildLiftTableInput.budget old extra oldp newp parent order)
    (SemiprimeD1StackChildLiftTableInput.source_trace old ho extra he oldp newp hp parent hg order) scope fuel out hr
  rw [E.stack_card] at h
  exact h.trans (cells_le old extra oldp newp parent order scope)
/-- All actual compiled prefix stacks include every source/template/shadow/counter/tree word and actual return cell. -/
theorem machine_prefix_cells {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order : List ℕ) (scope : List (List Bool)) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c => c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
          (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope))))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ spacePolynomial old extra oldp newp parent order scope := by
  have heq := SemiprimeD1StackCalls.run_correct (SemiprimeD1StackVectorTable.counter .bank)
    (SemiprimeD1StackVectorTable.aux .output) .start program fuel
    (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
      (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope))
  have hh := heq.trans hr
  cases hout : SemiprimeD1StackCalls.run program fuel
      (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope)) with
  | none => rw [hout] at hh;cases hh
  | some out =>
    rw [hout] at hh
    have hcfg : cfg=SemiprimeD1StackCalls.configuration out := (Option.some.inj hh).symm
    subst cfg
    exact prefix_cells old ho extra he oldp newp hp parent hg order scope fuel out hout
end RiemannGaussian.SemiprimeD1StackChildLiftTableStorage
