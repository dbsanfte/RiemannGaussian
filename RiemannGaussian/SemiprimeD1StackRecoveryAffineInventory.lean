/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffine
/-! # Fixed physical operand separation in the112-role affine source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineInventory
open SemiprimeD1StackRecoveryAffine
/-- Entire actual Grid104 inclusion is injective; no retained field is omitted. -/
theorem grid_injective:Function.Injective grid:=Sum.inl_injective
/-- Actual R36 is the same complete allocation inside the preserved Grid bank. -/
theorem rational_injective:Function.Injective rational:=grid_injective.comp SemiprimeD1StackRecoveryGrid.rational_injective
/-- True geometry aliases remain pairwise distinct under the outer inclusion. -/
theorem geometry_injective:Function.Injective geometry:=grid_injective.comp SemiprimeD1StackRecoveryGrid.geometry_injective
/-- Unary-product roles remain four distinct actual physical words. -/
theorem product_injective:Function.Injective product:=grid_injective.comp SemiprimeD1StackRecoveryGrid.product_injective
/-- Every actual copy source and target are distinct, including aliased sum destinations. -/
theorem copy_source_target (site:Copy):copySource site≠copyTarget site:=by
  cases site <;> first | decide | skip
  all_goals repeat' first | rename_i b;cases b
  all_goals decide
/-- Every actual copy source is disjoint from shared restoring scratch. -/
theorem copy_source_scratch (site:Copy):copySource site≠oldAux .copyScratch:=by
  cases site <;> first | decide | skip
  all_goals repeat' first | rename_i b;cases b
  all_goals decide
/-- Every actual copy target is disjoint from shared restoring scratch. -/
theorem copy_target_scratch (site:Copy):copyTarget site≠oldAux .copyScratch:=by
  cases site <;> first | decide | skip
  all_goals repeat' first | rename_i b;cases b
  all_goals decide
/-- All three physical operands of every fixed preserving copy are disjoint. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by
  intro a b h
  have hxy:=copy_source_target site
  have hxz:=copy_source_scratch site
  have hyz:=copy_target_scratch site
  fin_cases a <;> fin_cases b <;> first | rfl | exact (hxy h).elim | exact (hxy h.symm).elim | exact (hxz h).elim | exact (hxz h.symm).elim | exact (hyz h).elim | exact (hyz h.symm).elim
/-- All real field input/output/parser/validity operands are distinct. -/
theorem field_injective (site:Field):Function.Injective (fieldStack site):=by
  cases site <;> repeat' first | rename_i b;cases b
  all_goals decide
/-- Each real Frame has disjoint source, actual tail and restored scratch. -/
theorem frame_injective (site:Frame):Function.Injective (frameStack site):=by
  cases site <;> rename_i b <;> cases b <;> decide
/-- Every actual whole-array reversal has distinct consumed input and accumulating output. -/
theorem reverse_injective (second:Bool):Function.Injective (reverseStack second):=by cases second <;> decide
end RiemannGaussian.SemiprimeD1StackRecoveryAffineInventory
