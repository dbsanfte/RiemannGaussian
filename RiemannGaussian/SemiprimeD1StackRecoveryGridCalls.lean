/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridPrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryGridView
/-! # Actual geometry, height/product and normalized twice-fitted operation calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
open SemiprimeD1StackProcedureTrace
namespace PTrace
export SemiprimeD1StackRecoveryGridPrimitives (join copy_call push_run pop_run peek_run drain_loop frame_call local_call)
end PTrace
/-- Whole actual R36 source runs on the four physically copied operands and actual retained W, preserving every68 external word. -/
theorem rational_call (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hi:w.rational=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width) :
    Runs program (SemiprimeD1StackRationalOperationExecution.runBound (operation site) sx xn xd sy yn yd width+1)
      (.operation site .call) (bank w) (.operation site .clearSigned)
      (bank {w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rationalStack Label.rational rational_injective R.program
    (SemiprimeD1StackRationalOperation.localLabel .start (operation site) false false) (fun _=>rfl)
    (.operation site .call) (.operation site .clearSigned) rfl _
    (SemiprimeD1StackRationalOperation.initial (operation site) (sx::xn) xd (sy::yn) yd width)
    (SemiprimeD1StackRationalOperationExecution.done (operation site) sx xn xd sy yn yd width) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackRationalOperationExecution.source_run (operation site) sx xn xd sy yn yd width)
  · constructor
    · intro k;exact congrFun hi k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Exact acquired geometry outputs overwrite only their actual included fields; both displaced shadows remain untouched. -/
def geometryResult (w:Words) (a q:List Bool) :Words:=
  {w with rational:=Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .output) (SemiprimeD1StackPhaseGeometryComponents.result a q (SemiprimeD1StackPhaseGeometry.subStack .output)),geometry:=fun k=>if k=.exponent ∨ k=.index then w.geometry k else SemiprimeD1StackPhaseGeometryComponents.result a q (.inr k)}
/-- Actual true geometry acquisition, independent of all fitted rational registers and W. -/
theorem geometry_call (w:Words) (a q:List Bool) (pc next:Label)
    (hc:program pc=.call (.geometry .start) next)
    (hi:∀k,bank w (geometryStack k)=SemiprimeD1StackPhaseGeometry.input a q k) :
    ∃t ≤ SemiprimeD1StackPhaseGeometryComponents.runBound a q+1,
      Runs program t pc (bank w) next (bank (geometryResult w a q)):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPhaseGeometryExecution.source_run a q
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program geometryStack Label.geometry geometry_injective G.program
    .start (fun _=>rfl) pc next hc t (SemiprimeD1StackPhaseGeometry.initial a q)
    (SemiprimeD1StackPhaseGeometryExecution.done a q) _ _ rfl rfl rfl rfl hr
  · exact ⟨hi,fun _ _=>rfl⟩
  · constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hi (.inl .left)
        · exact hi (.inl .right)
        · exact hi (.inl .scratch)
        · rfl
      · cases k
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
    · intro k hk;rcases k with k|k
      · have hn:k≠SemiprimeD1StackRationalOperation.adderStack .output:=by
          intro he
          exact (hk (.inl .output) (congrArg rationalStack he.symm)).elim
        change Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .output)
          (SemiprimeD1StackPhaseGeometryComponents.result a q (SemiprimeD1StackPhaseGeometry.subStack .output)) k=w.rational k
        exact Function.update_of_ne hn _ _
      · rcases k with k|k
        · cases k
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
/-- Actual unary division of the physically built 3M+u−1 numerator by physically copied u. -/
theorem division_call (w:Words) (n d:Nat) (hi:w.division=SemiprimeD1StackUnaryDivmod.contents
    (List.replicate n true) (List.replicate d true) [] [] [] []) :
    ∃t ≤100*(n+d+1)+1,Runs program t (.local .divide) (bank w) (.local .clearRemainder)
      (bank {w with division:=SemiprimeD1StackUnaryDivmod.contents [] (List.replicate d true) [] [] (List.replicate (n/d) true) (List.replicate (n%d) true)}):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackUnaryDivmodBytecode.divide_run n d
  refine ⟨t+1,by omega,?_⟩
  apply included_call program divisionStack Label.division division_injective D.code D.entry (fun _=>rfl)
    (.local .divide) (.local .clearRemainder) rfl t
    ⟨some D.entry,none,SemiprimeD1StackUnaryDivmod.contents (List.replicate n true) (List.replicate d true) [] [] [] []⟩
    ⟨none,none,SemiprimeD1StackUnaryDivmod.contents [] (List.replicate d true) [] [] (List.replicate (n/d) true) (List.replicate (n%d) true)⟩
    _ _ rfl rfl hr
  · constructor
    · intro k;exact congrFun hi k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact (hk k rfl).elim
          · rfl
/-- Actual unary multiplicity product h*(u−order), after paid copies and physical truncated subtraction. -/
theorem product_call (w:Words) (h levels:Nat) (hi:w.product=SemiprimeD1StackUnaryProduct.contents
    (List.replicate h true) (List.replicate levels true) [] []) :
    ∃t ≤5*(h*(2*levels+3)+1)+1,Runs program t (.local .multiplicity) (bank w) (.local .clearLevels)
      (bank {w with product:=SemiprimeD1StackUnaryProduct.contents [] (List.replicate levels true) [] (List.replicate (h*levels) true)}):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackUnaryProduct.product_run h levels
  refine ⟨t+1,by omega,?_⟩
  apply included_call program productStack Label.product product_injective P.code P.entry (fun _=>rfl)
    (.local .multiplicity) (.local .clearLevels) rfl t
    ⟨some P.entry,none,SemiprimeD1StackUnaryProduct.contents (List.replicate h true) (List.replicate levels true) [] []⟩
    ⟨none,none,SemiprimeD1StackUnaryProduct.contents [] (List.replicate levels true) [] (List.replicate (h*levels) true)⟩
    _ _ rfl rfl hr
  · constructor
    · intro k;exact congrFun hi k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · exact (hk k rfl).elim
            · rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
