/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCalls
/-! # Acquired multiplicity from actual height, u and true geometry order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineMultiplicity
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackProcedureTrace
/-- Actual product/level/order words, with every other physical word preserved. -/
def words (w:Words) (multiplier levels product order:List Bool) :Words:=
  {w with product:=SemiprimeD1StackUnaryProduct.contents multiplier levels [] product, auxiliary:=Function.update w.auxiliary .orderTodo order}
/-- A real multiplier write changes only its counted physical product word. -/
theorem update_multiplier (w:Words) (multiplier levels product order xs:List Bool) :
    Function.update (bank (words w multiplier levels product order)) (SemiprimeD1StackRecoveryAffine.product .multiplier) xs=
      bank (words w xs levels product order):=by
  rw [SemiprimeD1StackRecoveryAffineView.update_product]
  congr 1
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryProduct.contents]
/-- A real multiplicand write changes only its counted physical product word. -/
theorem update_multiplicand (w:Words) (multiplier levels product order xs:List Bool) :
    Function.update (bank (words w multiplier levels product order)) (SemiprimeD1StackRecoveryAffine.product .multiplicand) xs=
      bank (words w multiplier xs product order):=by
  rw [SemiprimeD1StackRecoveryAffineView.update_product]
  congr 1
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryProduct.contents]
/-- A real product write changes only its counted physical product word. -/
theorem update_product (w:Words) (multiplier levels product order xs:List Bool) :
    Function.update (bank (words w multiplier levels product order)) (SemiprimeD1StackRecoveryAffine.product .product) xs=
      bank (words w multiplier levels xs order):=by
  rw [SemiprimeD1StackRecoveryAffineView.update_product]
  congr 1
  congr 1
  congr 1
  funext k
  cases k <;> simp [words,SemiprimeD1StackUnaryProduct.contents]
/-- A real order-counter write preserves all original fields and actual product words. -/
theorem update_order (w:Words) (multiplier levels product order xs:List Bool) :
    Function.update (bank (words w multiplier levels product order)) (oldAux .orderTodo) xs=
      bank (words w multiplier levels product xs):=by
  rw [SemiprimeD1StackRecoveryAffineView.update_oldAux]
  unfold words
  rw [Function.update_idem]
/-- Truncated u−order is physically acquired by paired marker pops; every leftover order marker is drained. -/
theorem subtract_run (w:Words) (levels order:Nat) :
    ∃t≤2*order+2,Runs program t (.local .subtractOrder)
      (bank (words w [] (List.replicate levels true) [] (List.replicate order true)))
      (.local .height) (bank (words w [] (List.replicate (levels-order) true) [] [])):=by
  induction order generalizing levels with
  | zero=>
    have h:=PTrace.pop_run (.local .subtractOrder) (.local .height) (.local .abort) (.local .removeLevel)
      (oldAux .orderTodo) (bank (words w [] (List.replicate levels true) [] [])) [] rfl rfl
    rw [update_order] at h
    change Runs program 1 _ _ (.local .height) _ at h
    exact ⟨1,by omega,h⟩
  | succ order ih=>
    have h0:=PTrace.pop_run (.local .subtractOrder) (.local .height) (.local .abort) (.local .removeLevel)
      (oldAux .orderTodo) (bank (words w [] (List.replicate levels true) [] (List.replicate (order+1) true)))
      (true::List.replicate order true) rfl (by change List.replicate (order+1) true=true::List.replicate order true;exact List.replicate_succ)
    rw [update_order] at h0
    change Runs program 1 _ _ (.local .removeLevel) _ at h0
    cases levels with
    | zero=>
      have h1:=PTrace.pop_run (.local .removeLevel) (.local .clearOrder) (.local .abort) (.local .subtractOrder)
        (SemiprimeD1StackRecoveryAffine.product .multiplicand) (bank (words w [] [] [] (List.replicate order true))) [] rfl rfl
      rw [update_multiplicand] at h1
      change Runs program 1 _ _ (.local .clearOrder) _ at h1
      have h2:=PTrace.drain_loop (.local .clearOrder) (.local .height) (oldAux .orderTodo) rfl
        (bank (words w [] [] [] (List.replicate order true))) (List.replicate order true) rfl
      rw [update_order] at h2
      refine ⟨1+1+(order+1),by omega,?_⟩
      simpa only [List.length_replicate,Nat.zero_sub,List.replicate_zero] using PTrace.join (PTrace.join h0 h1) h2
    | succ levels=>
      have h1:=PTrace.pop_run (.local .removeLevel) (.local .clearOrder) (.local .abort) (.local .subtractOrder)
        (SemiprimeD1StackRecoveryAffine.product .multiplicand) (bank (words w [] (List.replicate (levels+1) true) [] (List.replicate order true)))
        (true::List.replicate levels true) rfl (by change List.replicate (levels+1) true=true::List.replicate levels true;exact List.replicate_succ)
      rw [update_multiplicand] at h1
      change Runs program 1 _ _ (.local .subtractOrder) _ at h1
      obtain ⟨t,ht,h2⟩:=ih levels
      refine ⟨1+1+t,by omega,?_⟩
      simpa only [Nat.add_sub_add_right] using PTrace.join (PTrace.join h0 h1) h2
/-- Own source clock pays the original u/order/height copies, every marker subtraction and the actual unary product. -/
def runBound (h u order:Nat) :Nat:=
  (5*u+4)+(5*order+4)+(2*order+2)+(5*h+4)+(5*(h*(2*(u-order)+3)+1)+1)+((u-order)+1)
/-- Actual whole multiplicity acquisition; no multiplicity, slope or order evaluator is supplied. -/
theorem multiplicity_run (w:Words) (h u order:Nat)
    (hu:w.auxiliary .originalU=List.replicate u true)
    (ho:w.geometry .order=List.replicate order true)
    (hh:w.division .quotient=List.replicate h true)
    (hs:w.auxiliary .copyScratch=[]) :
    ∃t≤runBound h u order,Runs program t (.local .levels) (bank (words w [] [] [] []))
      (.local .retained) (bank (words w [] [] (List.replicate (h*(u-order)) true) [])):=by
  have h0:=PTrace.copy_call .levels (.local .levels) (.local .order) rfl
    (bank (words w [] [] [] [])) (List.replicate u true) [] hu rfl hs
  change Runs program _ _ _ _ (Function.update _ (SemiprimeD1StackRecoveryAffine.product .multiplicand) (List.replicate u true++[])) at h0
  rw [List.append_nil,update_multiplicand] at h0
  have h1:=PTrace.copy_call .order (.local .order) (.local .subtractOrder) rfl
    (bank (words w [] (List.replicate u true) [] [])) (List.replicate order true) [] ho rfl hs
  change Runs program _ _ _ _ (Function.update _ (oldAux .orderTodo) (List.replicate order true++[])) at h1
  rw [List.append_nil,update_order] at h1
  obtain ⟨s,hsBound,h2⟩:=subtract_run w u order
  have h3:=PTrace.copy_call .height (.local .height) (.local .multiplyQ) rfl
    (bank (words w [] (List.replicate (u-order) true) [] [])) (List.replicate h true) [] hh rfl hs
  change Runs program _ _ _ _ (Function.update _ (SemiprimeD1StackRecoveryAffine.product .multiplier) (List.replicate h true++[])) at h3
  rw [List.append_nil,update_multiplier] at h3
  obtain ⟨q,hq,h4⟩:=product_call (words w (List.replicate h true) (List.replicate (u-order) true) [] []) h (u-order) rfl
  change Runs program q _ _ _ (bank (words w [] (List.replicate (u-order) true) (List.replicate (h*(u-order)) true) [])) at h4
  have h5:=PTrace.drain_loop (.local .clearLevels) (.local .retained) (SemiprimeD1StackRecoveryAffine.product .multiplicand) rfl
    (bank (words w [] (List.replicate (u-order) true) (List.replicate (h*(u-order)) true) []))
    (List.replicate (u-order) true) rfl
  rw [update_multiplicand] at h5
  have hrun:=PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4) h5
  simp only [List.length_replicate] at hrun
  refine ⟨(5*u+4)+(5*order+4)+s+(5*h+4)+q+((u-order)+1),?_,hrun⟩
  unfold runBound
  omega
/-- All literal multiplicity work has a fixed quadratic bound in the actual acquired VALUE metadata. -/
theorem runBound_le (h u order:Nat) :runBound h u order≤100*(h+u+order+1)^2:=by
  have hd:u-order≤u:=Nat.sub_le _ _
  unfold runBound
  nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryAffineMultiplicity
