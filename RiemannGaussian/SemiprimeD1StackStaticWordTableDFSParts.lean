/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTableSpec
/-! # Literal product-table DFS transitions preserving exact local-port order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackStaticWordTableDFSParts
open SemiprimeD1StackStaticWordTable SemiprimeD1StackStaticWordTableSpec SemiprimeD1StackProcedureTrace
variable {K L : Type} [DecidableEq K] (s : Static K L)
/-- Actual depth EOF enters the real leaf checker procedure. -/
theorem visit_zero (original : K→List Bool) (bank front hist : List Bool) :
    Runs (program s) 1 .visit (data original bank 0 front hist) .leaf (data original bank 0 front hist) := by
  apply one_base (program s) .visit .leaf (.pop (counter .count) .leaf .fork .fork) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- One actual acquired depth marker is popped at an internal node. -/
theorem visit_succ (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .visit (data original bank (n+1) front hist) .fork (data original bank n front hist) := by
  apply one_base (program s) .visit .fork (.pop (counter .count) .leaf .fork .fork) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- The physical old-codec fork tag is written before either child. -/
theorem fork_push (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .fork (data original bank n front hist) .low (data original bank n front (true::hist)) := by
  apply one_base (program s) .fork .low (.push (aux .reversed) true .low) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- FALSE is physically prepended to the reverse-prefix before the first child. -/
theorem low_push (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .low (data original bank n front hist) .high (data original bank n (false::front) hist) := by
  apply one_base (program s) .low .high (.push (aux .prefix) false .high) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- The first child's physical prefix bit is consumed after its real return. -/
theorem low_pop (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .afterLow (data original bank n (false::front) hist) .setHigh (data original bank n front hist) := by
  apply one_base (program s) .afterLow .setHigh (.pop (aux .prefix) .bad .setHigh .setHigh) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- TRUE is physically prepended before the second child, in old table order. -/
theorem high_push (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .setHigh (data original bank n front hist) .afterHigh (data original bank n (true::front) hist) := by
  apply one_base (program s) .setHigh .afterHigh (.push (aux .prefix) true .afterHigh) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- The second child's actual prefix bit is popped after its real return. -/
theorem high_pop (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .restore (data original bank n (true::front) hist) .returnDone (data original bank n front hist) := by
  apply one_base (program s) .restore .returnDone (.pop (aux .prefix) .bad .returnDone .returnDone) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
/-- The original acquired depth marker is physically restored before return. -/
theorem depth_restore (original : K→List Bool) (bank : List Bool) (n : ℕ) (front hist : List Bool) :
    Runs (program s) 1 .returnDone (data original bank n front hist) .leafReturn (data original bank (n+1) front hist) := by
  apply one_base (program s) .returnDone .leafReturn (.push (counter .count) true .leafReturn) _ _ rfl
  · rfl
  · funext k;cases k with
    | inl k=>rfl
    | inr k=>
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackStaticWordTableDFSParts
