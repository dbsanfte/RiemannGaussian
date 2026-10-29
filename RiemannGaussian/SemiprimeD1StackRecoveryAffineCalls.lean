/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
/-! # Actual whole Grid, true geometry, retained-q product and scalar source calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineInventory SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackProcedureTrace
namespace PTrace
export SemiprimeD1StackRecoveryAffinePrimitives (join copy_call push_run pop_run peek_run drain_loop frame_call reverse_call field_read local_call)
end PTrace
/-- Honest five-word source executes the SAME sealed Grid104 once, preserving all eight actual caller words. -/
theorem grid_call (a M u:Nat) (t width:List Bool) (added:Aux→List Bool) :
    ∃q≤SemiprimeD1StackRecoveryGridBounds.polynomial a M u t width+1,
      Runs program q (.local .start)
        (Sum.elim (Q.input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) added)
        (.local .ready) (Sum.elim (SemiprimeD1StackRecoveryGridExecution.result a M u t width) added):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRecoveryGridBounds.source_run_bounded a M u t width
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program grid Label.grid grid_injective Q.program
    (.local .start) (fun _=>rfl) (.local .start) (.local .ready) rfl q
    (SemiprimeD1StackRecoveryGrid.initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
    (SemiprimeD1StackRecoveryGridExecution.done a M u t width) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro slot;rfl
    · intro slot hk;rcases slot with slot|slot
      · exact (hk slot rfl).elim
      · rfl
/-- Actual R36 source consumes only the four copied original fields and retained W; all76 foreign words are preserved. -/
theorem rational_call (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hi:w.rational=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width) :
    Runs program (SemiprimeD1StackRationalOperationExecution.runBound (operation site) sx xn xd sy yn yd width+1)
      (.operation site .call) (bank w) (.operation site .clearSigned)
      (bank {w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rational Label.rational rational_injective R.program
    (SemiprimeD1StackRationalOperation.localLabel .start (operation site) false false) (fun _=>rfl)
    (.operation site .call) (.operation site .clearSigned) rfl _
    (SemiprimeD1StackRationalOperation.initial (operation site) (sx::xn) xd (sy::yn) yd width)
    (SemiprimeD1StackRationalOperationExecution.done (operation site) sx xn xd sy yn yd width) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackRationalOperationExecution.source_run (operation site) sx xn xd sy yn yd width)
  · constructor
    · intro slot;exact congrFun hi slot
    · intro slot _;rfl
  · constructor
    · intro slot;rfl
    · intro role hk;rcases role with role|role
      · rcases role with role|role
        · exact (hk role rfl).elim
        · rfl
      · rfl
/-- Only physically acquired G14 fields and its shared raw point output change; original Grid caches are untouched. -/
def geometryResult (w:Words) (a t:List Bool):Words:=
  {w with rational:=Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .output) (SemiprimeD1StackPhaseGeometryComponents.result a t (SemiprimeD1StackPhaseGeometry.subStack .output)), geometry:=fun slot=>if slot=.exponent ∨slot=.index then w.geometry slot else SemiprimeD1StackPhaseGeometryComponents.result a t (.inr slot)}
/-- True actual geometry is acquired from actual a/t before retained q; no fitted rational or numerical geometry answer is input. -/
theorem geometry_call (w:Words) (a t:List Bool)
    (hi:∀slot,bank w (geometry slot)=SemiprimeD1StackPhaseGeometry.input a t slot) :
    ∃q≤SemiprimeD1StackPhaseGeometryComponents.runBound a t+1,
      Runs program q (.local .geometry) (bank w) (.local .clearPoint) (bank (geometryResult w a t)):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseGeometryExecution.source_run a t
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program geometry Label.geometry geometry_injective G.program
    .start (fun _=>rfl) (.local .geometry) (.local .clearPoint) rfl q (SemiprimeD1StackPhaseGeometry.initial a t)
    (SemiprimeD1StackPhaseGeometryExecution.done a t) _ _ rfl rfl rfl rfl hr
  · exact ⟨hi,fun _ _=>rfl⟩
  · constructor
    · intro slot;rcases slot with slot|slot
      · cases slot
        · exact hi (.inl .left)
        · exact hi (.inl .right)
        · exact hi (.inl .scratch)
        · rfl
      · cases slot
        · exact hi (.inr .exponent)
        · exact hi (.inr .index)
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
    · intro role hk;rcases role with role|role
      · rcases role with slot|slot
        · have hn:slot≠SemiprimeD1StackRationalOperation.adderStack .output:=by
            intro he
            exact (hk (.inl .output) (congrArg rational he.symm)).elim
          change Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .output)
            (SemiprimeD1StackPhaseGeometryComponents.result a t (SemiprimeD1StackPhaseGeometry.subStack .output)) slot=w.rational slot
          exact Function.update_of_ne hn _ _
        · rcases slot with slot|slot
          · cases slot
            · rfl
            · rfl
            · exact (hk (.inr .counter) rfl).elim
            · exact (hk (.inr .center) rfl).elim
            · exact (hk (.inr .alpha) rfl).elim
            · exact (hk (.inr .sign) rfl).elim
            · exact (hk (.inr .zero) rfl).elim
            · exact (hk (.inr .order) rfl).elim
            · exact (hk (.inr .scan) rfl).elim
            · exact (hk (.inr .scratch) rfl).elim
          · rfl
      · rfl
/-- Actual unary retained-q product uses copied height and physically truncated levels; every other108 word is retained. -/
theorem product_call (w:Words) (h levels:Nat) (hi:w.product=SemiprimeD1StackUnaryProduct.contents
    (List.replicate h true) (List.replicate levels true) [] []) :
    ∃q≤5*(h*(2*levels+3)+1)+1,Runs program q (.local .multiplyQ) (bank w) (.local .clearLevels)
      (bank {w with product:=SemiprimeD1StackUnaryProduct.contents [] (List.replicate levels true) [] (List.replicate (h*levels) true)}):=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackUnaryProduct.product_run h levels
  refine ⟨q+1,by omega,?_⟩
  apply included_call program product Label.product product_injective P.code P.entry (fun _=>rfl)
    (.local .multiplyQ) (.local .clearLevels) rfl q
    ⟨some P.entry,none,SemiprimeD1StackUnaryProduct.contents (List.replicate h true) (List.replicate levels true) [] []⟩
    ⟨none,none,SemiprimeD1StackUnaryProduct.contents [] (List.replicate levels true) [] (List.replicate (h*levels) true)⟩
    _ _ rfl rfl hr
  · constructor
    · intro slot;exact congrFun hi slot
    · intro slot _;rfl
  · constructor
    · intro slot;rfl
    · intro role hk;rcases role with role|role
      · rcases role with slot|slot
        · rfl
        · rcases slot with slot|slot
          · rfl
          · rcases slot with slot|slot
            · rfl
            · rcases slot with slot|slot
              · exact (hk slot rfl).elim
              · rfl
      · rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCalls
