/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableState
/-! # Literal product-table DFS transitions preserving exact local-port order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableDFSParts
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState SemiprimeD1StackProcedureTrace
/-- Actual depth EOF enters the real leaf checker procedure. -/
theorem visit_zero (bits front hist : List Bool) :
    Runs program 1 .visit (data bits 0 front hist) .leaf (data bits 0 front hist) := by
  apply one_base program .visit .leaf (.pop (.inr .depth) .leaf .fork .fork) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- One actual acquired depth marker is popped at an internal node. -/
theorem visit_succ (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .visit (data bits (n+1) front hist) .fork (data bits n front hist) := by
  apply one_base program .visit .fork (.pop (.inr .depth) .leaf .fork .fork) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- The physical old-codec fork tag is written before either child. -/
theorem fork_push (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .fork (data bits n front hist) .low (data bits n front (true::hist)) := by
  apply one_base program .fork .low (.push (.inr .reversed) true .low) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- FALSE is physically prepended to the reverse-prefix before the first child. -/
theorem low_push (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .low (data bits n front hist) .high (data bits n (false::front) hist) := by
  apply one_base program .low .high (.push (.inr .prefix) false .high) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- The first child's physical prefix bit is consumed after its real return. -/
theorem low_pop (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .afterLow (data bits n (false::front) hist) .copySource (data bits n front hist) := by
  apply one_base program .afterLow .copySource (.pop (.inr .prefix) .bad .copySource .copySource) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- TRUE is physically prepended before the second child, in old table order. -/
theorem high_push (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .copySource (data bits n front hist) .afterHigh (data bits n (true::front) hist) := by
  apply one_base program .copySource .afterHigh (.push (.inr .prefix) true .afterHigh) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- The second child's actual prefix bit is popped after its real return. -/
theorem high_pop (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .restore (data bits n (true::front) hist) .returnDone (data bits n front hist) := by
  apply one_base program .restore .returnDone (.pop (.inr .prefix) .bad .returnDone .returnDone) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
/-- The original acquired depth marker is physically restored before return. -/
theorem depth_restore (bits : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs program 1 .returnDone (data bits n front hist) .leafReturn (data bits (n+1) front hist) := by
  apply one_base program .returnDone .leafReturn (.push (.inr .depth) true .leafReturn) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackProductTableDFSParts
