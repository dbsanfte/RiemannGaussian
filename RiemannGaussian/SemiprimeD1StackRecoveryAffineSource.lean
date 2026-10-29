/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineRetained
import RiemannGaussian.SemiprimeD1StackRecoveryAffineEncoding
/-! # Original five-word source through actual whole Grid and retained-q acquisition
All premises describe original physical words. The SAME program acquires every
Grid cache, true selected-node geometry and q internally before reading slopes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSource
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackProcedureTrace
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (original retained)
end E
namespace QSource
export SemiprimeD1StackRecoveryAffineRetained (runBound retained_run)
end QSource
/-- Actual completed Grid source is the exact original whole104-word bank, with all eight added words EMPTY. -/
theorem grid_ready (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃q≤SemiprimeD1StackRecoveryGridBounds.polynomial a M u t width+1,
      Runs program q (.local .start)
        (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
        (.local .ready) (bank (E.original a M u selected t width)):=by
  obtain ⟨q,hq,hr⟩:=grid_call a M u t width (fun _=>[])
  rw [SemiprimeD1StackRecoveryGridOriginal.result_original a M u selected t width ht] at hr
  exact ⟨q,hq,hr⟩
/-- All actual reused geometry/ripple/product/scratch words are physically EMPTY after the SAME full Grid call. -/
theorem grid_work (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    (∀slot,(E.original a M u selected t width).geometry slot=[]) ∧
    (∀slot,(E.original a M u selected t width).rational (SemiprimeD1StackRationalOperation.adderStack slot)=[]) ∧
    (E.original a M u selected t width).product=SemiprimeD1StackUnaryProduct.contents [] [] [] []:=by
  refine ⟨fun _=>rfl,?_,?_⟩
  · intro slot
    cases slot <;> rfl
  · funext slot
    cases slot <;> rfl
/-- No retained multiplicity or array was supplied at the actual original ready boundary. -/
def counted (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):Words:=
  {E.original a M u selected t width with added:=Function.update (fun _=>[]) .retainedQ (List.replicate (E.retained a M u selected) true)}
/-- This own budget includes the true whole Grid source, real caller return and newly executed q acquisition. -/
def entryBound (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):Nat:=
  SemiprimeD1StackRecoveryGridBounds.polynomial a M u t width+1+
    QSource.runBound (E.original a M u selected t width) a (SemiprimeD1TaperedLoss.height M u) u t
/-- The actual selected-node q comes from the true geometry and retained height, with every original104 word restored. -/
theorem ready_counted (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃q≤QSource.runBound (E.original a M u selected t width) a (SemiprimeD1TaperedLoss.height M u) u t,
      Runs program q (.local .ready) (bank (E.original a M u selected t width))
        (.local .copySlopes) (bank (counted a M u selected t width)):=by
  obtain ⟨hg,hr,hp⟩:=grid_work a M u selected t width
  obtain ⟨q,hq,h⟩:=QSource.retained_run (E.original a M u selected t width) a (SemiprimeD1TaperedLoss.height M u) u t
    rfl rfl rfl rfl hg hr hp rfl rfl rfl rfl
  have hv:=SemiprimeD1StackRecoveryAffineGeometry.retained_original a M u selected t ht
  change SemiprimeD1TaperedLoss.height M u*(u-SemiprimeD1StackRecoveryAffineRetained.order a t)=E.retained a M u selected at hv
  rw [hv] at h
  exact ⟨q,hq,h⟩
/-- Whole actual five-tape program reaches the physical affine fold with ALL Grid data and actual original q internally acquired. -/
theorem entry_trace (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃q≤entryBound a M u selected t width,Runs program q (.local .start)
      (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
      (.local .copySlopes) (bank (counted a M u selected t width)):=by
  obtain ⟨p,hp,h0⟩:=grid_ready a M u selected t width ht
  obtain ⟨q,hq,h1⟩:=ready_counted a M u selected t width ht
  refine ⟨p+q,?_,PTrace.join h0 h1⟩
  unfold entryBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSource
