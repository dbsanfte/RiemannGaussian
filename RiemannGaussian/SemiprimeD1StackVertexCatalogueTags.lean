/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueCaches

/-! # Literal constructor-tag acquisition and original source-role bounds -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueTags
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueComponents SemiprimeD1StackVertexCatalogueView
open SemiprimeD1StackVertexCataloguePrepare SemiprimeD1StackVertexCatalogueModes SemiprimeD1StackVertexCatalogueCaches
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeMacroParameters

/-- The finite tag counter is acquired by actual pushes, not encoded from an advised mode value. -/
theorem init_run (n i:ℕ) (hi:i+n=17) (base:Stack→List Bool) (limits:Fin 4→List Bool) (output:List Bool) :
    Runs program (n+1) (.inl (.initTag ⟨i,by omega⟩)) (view base limits (List.replicate i true) output)
      (.inl (.clearLimit .flagOr 0)) (view base limits (List.replicate 17 true) output) := by
  induction n generalizing i with
  | zero =>
    have he:i=17:=by omega
    subst i
    exact one_base program _ _ (.jump (.inl (.clearLimit .flagOr 0))) _ _ rfl rfl rfl
  | succ n ih =>
    have hit:i<17:=by omega
    have hcode:program (.inl (.initTag ⟨i,by omega⟩))=
        .base (.push (kernelStack (Kernel.aux 3)) true (.inl (.initTag ⟨i+1,by omega⟩))):=by
      simp [program,hit]
    have h0:=push_run (.inl (.initTag ⟨i,by omega⟩)) (.inl (.initTag ⟨i+1,by omega⟩))
      (kernelStack (Kernel.aux 3)) true (view base limits (List.replicate i true) output) hcode
    change Runs program 1 _ _ _ (Function.update (view base limits (List.replicate i true) output)
      (kernelStack (Kernel.aux 3)) (true::List.replicate i true)) at h0
    rw [view_tag,←List.replicate_succ] at h0
    have h1:=ih (i+1) (by omega)
    simpa only [show 1+(n+1)=n+1+1 by omega] using h0.trans h1

/-- The actual cached count has ORIGINAL raw-width digitCount, including all empty zero-digit fields. -/
theorem digitCount_raw (bits:List Bool) (hb:bits≠[]) : digitCountValue bits=digitCount bits.length := by
  exact SemiprimeD1StackDigitBankSpec.original_count bits.length (List.length_pos_iff.mpr hb) bits
    (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) rfl
    (SemiprimeD1BinaryDigitAcquisitionComponents.radix_length bits)

/-- One original-input bound covers every actually acquired readonly limit role. -/
theorem base_bound (bits:List Bool) (hb:bits≠[]) : RoleBound (64*bits.length+3) (base bits) := by
  have hell:0<bits.length:=List.length_pos_iff.mpr hb
  have hR:transformLength bits.length≤64*bits.length+1:=
    (SemiprimeD1StackTransformArithmetic.prefix_powers bits.length (transformExponent bits.length) (le_refl _)).1
  have hP:firstAxis bits.length≤transformLength bits.length:=
    Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hQ:secondAxis bits.length≤transformLength bits.length:=by
    rw [secondAxis_eq_power]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hD:digitCountValue bits≤transformLength bits.length:=by
    rw [digitCount_raw bits hb]
    exact ((digitCount_bounds hell).2).trans (Nat.div_le_self (transformLength bits.length) 4)
  intro role
  rw [base_format]
  rw [List.length_replicate]
  apply SemiprimeD1VertexCatalogueModes.dimension_le _ _ _ _ (by omega) (by omega) ?_ (by omega) (by omega) role
  rw [axes_product]
  omega

/-- The whole actual mode trace begins only after the physical17-marker tag is acquired. -/
theorem catalogue_run (bits:List Bool) (hb:bits≠[]) :
    ∃m≤18*blockBudget (64*bits.length+3),Runs program m (.inl (.clearLimit .flagOr 0))
      (view (base bits) (fun _=>[]) (List.replicate 17 true) []) (.inl .halt)
      (view (base bits) (preparedLimits (base bits) .input) []
        (SemiprimeD1VertexCatalogueEncoding.catalogue (firstAxis bits.length) (secondAxis bits.length) (digitCountValue bits) [])) := by
  have h:=mode_run (firstAxis bits.length) (secondAxis bits.length) (digitCountValue bits) (base bits)
    (64*bits.length+3) (base_scratch bits) (base_format bits) (base_bound bits hb) .flagOr (fun _=>[]) []
    (by intro axis;simp)
  simpa only [SemiprimeD1VertexCatalogueModes.code,prefix_full] using h
end RiemannGaussian.SemiprimeD1StackVertexCatalogueTags
