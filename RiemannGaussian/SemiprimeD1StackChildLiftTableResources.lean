/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTableInput
/-! # Actual source-byte, acquired-rank and precision-VALUE caps for whole child tables
The resource includes the original table/order/header bytes, physically paid
rank and precision VALUES and actual scope bytes. No child answer, native
runtime or recursively enlarged elapsed-clock width supplies a resource.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTableResources
open SemiprimeD1StackChildLiftTable
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Input
export SemiprimeD1StackChildLiftTableInput (original budget)
end Input
/-- Fixed physical resource: source bytes and actual acquired dimension VALUES plus scope tape bytes. -/
def resource {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) : ℕ :=
  SemiprimeD1StackChildTableEntryBounds.resource old.axes (extra++old.axes) oldp newp parent order []+
    (vectorBits scope).length
/-- Every actual source resource includes its own positive constant overhead. -/
theorem resource_pos {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    1≤resource old extra oldp newp parent order scope := by
  unfold resource SemiprimeD1StackChildTableEntryBounds.resource
  omega
/-- Physically counting scope records pays arity by actual tape bytes, including empty zero-ID fields. -/
theorem scope_le {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    scope.length≤resource old extra oldp newp parent order scope :=
  (SemiprimeD1StackVectorTableBounds.scope_count_le scope).trans (Nat.le_add_left _ _)
/-- All61 original-template roles are physically counted, including all empty private shadows. -/
theorem template_bytes {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    SemiprimeD1StackVectorTableSpec.inputBytes
      (Input.original (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp)≤
      61*resource old extra oldp newp parent order scope := by
  have h (k : E.Stack) := SemiprimeD1StackChildTableEntryStorage.initial_length old.axes (extra++old.axes)
    oldp newp parent order [] k
  have hb (k : E.Stack) :
      (Input.original (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp k).length≤
      resource old extra oldp newp parent order scope := (h k).trans (Nat.le_add_right _ _)
  unfold SemiprimeD1StackVectorTableSpec.inputBytes
  calc
    _≤∑_k : E.Stack,resource old extra oldp newp parent order scope := Finset.sum_le_sum (fun k _ => hb k)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,E.stack_card,smul_eq_mul]
/-- EVERY actual assignment has one fixed quadratic Entry61 budget in the same physically paid resource. -/
theorem entry_budget {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    Input.budget old extra oldp newp parent order scope.length≤10^8*(resource old extra oldp newp parent order scope)^2 := by
  have hn := SemiprimeD1StackVectorTableBounds.scope_count_le scope
  have hres : SemiprimeD1StackChildTableEntryBounds.resource old.axes (extra++old.axes) oldp newp parent order
      (List.replicate scope.length false)≤resource old extra oldp newp parent order scope := by
    unfold resource SemiprimeD1StackChildTableEntryBounds.resource
    simp only [List.length_replicate,List.length_nil]
    omega
  exact Nat.mul_le_mul_left (10^8) (Nat.pow_le_pow_left hres 2)
end RiemannGaussian.SemiprimeD1StackChildLiftTableResources
