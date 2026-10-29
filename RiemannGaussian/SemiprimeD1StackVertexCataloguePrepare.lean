/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueView

/-! # Actual finite mode-limit preparation and closed Cartesian calls
Every stale limit is physically cleared and every new limit physically copied
from readonly acquired words. The Cartesian body is the concrete fixed code,
not a parameter supplied to this frontend.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCataloguePrepare
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueComponents SemiprimeD1StackVertexCatalogueView
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1VertexCatalogueModes (Mode Role roles)

/-- Exact physical copied limit words, selected by finite mode/role control. -/
def preparedLimits (base:Stack→List Bool) (mode:Mode) (axis:Fin 4) : List Bool := base (roleStack (roles mode axis))
/-- Every physically stored limit has its actual common cell-length bound. -/
def LimitBound (D:ℕ) (limits:Fin 4→List Bool) : Prop := ∀axis,(limits axis).length≤D
/-- Every readonly acquired source role has its actual common cell-length bound. -/
def RoleBound (D:ℕ) (base:Stack→List Bool) : Prop := ∀role,(base (roleStack role)).length≤D

/-- A real copied source word preserves the bound of all four actual limit cells. -/
theorem limit_update_bound (D:ℕ) (limits:Fin 4→List Bool) (axis:Fin 4) (word:List Bool)
    (hl:LimitBound D limits) (hw:word.length≤D) : LimitBound D (Function.update limits axis word) := by
  intro j
  by_cases h:j=axis
  · subst j;simpa only [Function.update_self] using hw
  · simpa only [Function.update_of_ne h] using hl j

/-- One exact physical clear+Copy operation; old contents are not discarded for free. -/
theorem prepare_axis (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output:List Bool)
    (mode:Mode) (axis:Fin 4) (hs:base scratchStack=[]) :
    Runs program ((limits axis).length+5*(preparedLimits base mode axis).length+5)
      (.inl (.clearLimit mode axis)) (view base limits tag output) (afterLimit mode axis)
      (view base (Function.update limits axis (preparedLimits base mode axis)) tag output) := by
  have h0:=clear_run (limits axis) (.inl (.clearLimit mode axis)) (.inl (.copyLimit mode axis))
    (kernelStack (Kernel.limitStack axis)) (view base limits tag output) rfl rfl
  rw [view_limit] at h0
  have h1:=copy_call (.limit mode axis) (view base (Function.update limits axis []) tag output)
    (by exact hs) (.inl (.copyLimit mode axis)) (afterLimit mode axis) rfl
  have hsrc:view base (Function.update limits axis []) tag output (copyInput (.limit mode axis))=
      preparedLimits base mode axis:=view_role _ _ _ _ _
  have hdst:view base (Function.update limits axis []) tag output (copyOutput (.limit mode axis))=[]:=by
    change Function.update limits axis [] axis=[]
    exact Function.update_self _ _ _
  rw [hsrc,hdst,List.append_nil] at h1
  change Runs program _ _ _ _
    (Function.update (view base (Function.update limits axis []) tag output) (kernelStack (Kernel.limitStack axis))
      (preparedLimits base mode axis)) at h1
  rw [view_limit,Function.update_idem] at h1
  have h:=h0.trans h1
  simpa only [show (limits axis).length+1+(5*(preparedLimits base mode axis).length+4)=
    (limits axis).length+5*(preparedLimits base mode axis).length+5 by omega] using h

/-- All four actual copied fields determine the whole finite limit tuple. -/
theorem four_updates (base:Stack→List Bool) (limits:Fin 4→List Bool) (mode:Mode) :
    Function.update (Function.update (Function.update (Function.update limits 0 (preparedLimits base mode 0))
      1 (preparedLimits base mode 1)) 2 (preparedLimits base mode 2)) 3 (preparedLimits base mode 3)=
      preparedLimits base mode := by
  funext axis
  fin_cases axis <;> simp [Function.update]

/-- The complete real four-limit preparation has one closed fixed polynomial bound. -/
theorem prepare_run (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output:List Bool)
    (mode:Mode) (D:ℕ) (hs:base scratchStack=[]) (hl:LimitBound D limits) (hb:RoleBound D base) :
    ∃m≤24*D+20,Runs program m (.inl (.clearLimit mode 0)) (view base limits tag output)
      (.inl (.runMode mode)) (view base (preparedLimits base mode) tag output) := by
  let l1:=Function.update limits 0 (preparedLimits base mode 0)
  let l2:=Function.update l1 1 (preparedLimits base mode 1)
  let l3:=Function.update l2 2 (preparedLimits base mode 2)
  have hl1:LimitBound D l1:=limit_update_bound D limits 0 _ hl (hb _)
  have hl2:LimitBound D l2:=limit_update_bound D l1 1 _ hl1 (hb _)
  have hl3:LimitBound D l3:=limit_update_bound D l2 2 _ hl2 (hb _)
  have h0:=prepare_axis base limits tag output mode 0 hs
  have h1:=prepare_axis base l1 tag output mode 1 hs
  have h2:=prepare_axis base l2 tag output mode 2 hs
  have h3:=prepare_axis base l3 tag output mode 3 hs
  have h:=h0.trans (h1.trans (h2.trans h3))
  change Runs program _ _ _ _
    (view base (Function.update (Function.update (Function.update (Function.update limits 0 (preparedLimits base mode 0))
      1 (preparedLimits base mode 1)) 2 (preparedLimits base mode 2)) 3 (preparedLimits base mode 3)) tag output) at h
  rw [four_updates] at h
  refine ⟨_,?_,h⟩
  have a0:=hl 0
  have a1:=hl1 1
  have a2:=hl2 2
  have a3:=hl3 3
  have b0:=hb (roles mode 0)
  have b1:=hb (roles mode 1)
  have b2:=hb (roles mode 2)
  have b3:=hb (roles mode 3)
  change _≤24*D+20
  dsimp only [preparedLimits] at *
  omega

/-- The actual Cartesian procedure changes only its physically emitted output bytes. -/
theorem kernel_done_update (dims:Fin 4→ℕ) (limits:Fin 4→List Bool) (tag output:List Bool) :
    (SemiprimeD1StackCartesian4Bounds.done dims limits tag output).data=
      Function.update (SemiprimeD1StackCartesian4Bounds.initial limits tag output).data (Kernel.aux 2)
        (SemiprimeD1StackCartesian4Execution.box0 dims SemiprimeD1StackCartesian4Bounds.emptyIndices tag output) := by
  exact (SemiprimeD1StackCartesian4Components.store_output limits
    SemiprimeD1StackCartesian4Bounds.emptyIndices tag output _).symm

/-- Actual closed Cartesian execution is invoked with real call/return, preserving all acquired data. -/
theorem kernel_call (base:Stack→List Bool) (dims:Fin 4→ℕ) (limits:Fin 4→List Bool) (tag output:List Bool)
    (mode:Mode) (D:ℕ) (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D) :
    ∃m≤43*(D+tag.length+1)^5+1,Runs program m (.inl (.runMode mode)) (view base limits tag output)
      (.inl (.afterMode mode)) (view base limits tag
        (SemiprimeD1StackCartesian4Execution.box0 dims SemiprimeD1StackCartesian4Bounds.emptyIndices tag output)) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackCartesian4Bounds.source_run_polynomial dims limits tag output D hl hd
  have hin:LinkB.DataRel kernelStack (view base limits tag output)
      (SemiprimeD1StackCartesian4Bounds.initial limits tag output).data (view base limits tag output):=by
    constructor
    · intro k;rfl
    · intro k _;rfl
  have hout:=SemiprimeD1StackMultiplierLink.data_update kernelStack kernelStack_injective
    (view base limits tag output) _ _ hin (Kernel.aux 2)
      (SemiprimeD1StackCartesian4Execution.box0 dims SemiprimeD1StackCartesian4Bounds.emptyIndices tag output)
  rw [←kernel_done_update,view_output] at hout
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program kernelStack kernelLabel kernelStack_injective
    Kernel.program (.inl .main) (fun _=>rfl) (.inl (.runMode mode)) (.inl (.afterMode mode)) rfl m
    (SemiprimeD1StackCartesian4Bounds.initial limits tag output) (SemiprimeD1StackCartesian4Bounds.done dims limits tag output)
    (view base limits tag output) _
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · exact hin
  · exact hout
end RiemannGaussian.SemiprimeD1StackVertexCataloguePrepare
