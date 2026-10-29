/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueSlots
/-! # Actual order-major mode catalogue scan, including zero slots -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueOrders
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCataloguePrimitives SemiprimeD1StackWeightedModeCatalogueSlots
open SemiprimeD1StackWeightedModeView (unary unary_length unary_succ history history_append)
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl :Control→Label)
/-- Literal weight rows in the next acquired consecutive orders. -/
def orderWeights (slots first count:Nat):List (List Bool):=
  (List.range count).flatMap (fun k=>slotWeights (first+k) slots)
/-- Literal label rows in the next acquired consecutive orders. -/
def orderLabels (slots first count:Nat):List (List Bool):=
  (List.range count).flatMap (fun k=>slotLabels (first+k) 0 slots)
theorem orderWeights_cons (slots first count:Nat):
    orderWeights slots first (count+1)=slotWeights first slots++orderWeights slots (first+1) count:=by
  rw [orderWeights,List.range_succ_eq_map]
  simp only [List.flatMap_cons,List.flatMap_map,Nat.add_zero]
  congr 1
  apply congrArg ((List.range count).flatMap)
  funext k
  congr 1
  omega
theorem orderLabels_cons (slots first count:Nat):
    orderLabels slots first (count+1)=slotLabels first 0 slots++orderLabels slots (first+1) count:=by
  rw [orderLabels,List.range_succ_eq_map]
  simp only [List.flatMap_cons,List.flatMap_map,Nat.add_zero]
  congr 1
  apply congrArg ((List.range count).flatMap)
  funext k
  congr 1
  omega
/-- A nonempty order copies the computed slot product, emits every pair, then increments both metadata words. -/
theorem order_step (p t width n j:Nat) (wh lh:List Bool):
    ∃time ≤100*(p*t+1)*(j+p*t+2)+5*(p*t)+8,Runs program time (ctl .orderCheck)
      (store (scanning p t width (n+1) j 0 0 wh lh)) (ctl .orderCheck)
      (store (scanning p t width n (j+1) 0 0
        (history (slotWeights j (p*t)) wh) (history (slotLabels j 0 (p*t)) lh))):=by
  let a:=scanning p t width (n+1) j 0 0 wh lh
  let b:=scanning p t width (n+1) j (p*t) 0 wh lh
  let wh':=history (slotWeights j (p*t)) wh
  let lh':=history (slotLabels j 0 (p*t)) lh
  let c:=scanning p t width (n+1) j 0 0 wh' lh'
  let d:Words:={c with orders:=unary n}
  let e:Words:={d with order:=unary (j+1)}
  have h0:Runs program 1 (ctl .orderCheck) (store a) (ctl .copySlots) (store a):=by
    apply one_base program _ _ _ _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,store,aux,a,scanning,unary_succ,List.head?_cons,
        SemiprimeD1StackBytecode.choose]
    · rfl
  have h1:=copy_call true .copySlots .slotCheck rfl (store a) (unary (p*t)) [] rfl rfl rfl
  rw [List.append_nil,store_write,unary_length] at h1
  change Runs program (5*(p*t)+4) _ _ _ (store b) at h1
  obtain ⟨u,hu,h2⟩:=slots_run p t width (n+1) j (p*t) 0 wh lh
  change Runs program u _ (store b) _ (store c) at h2
  have h3:=pop_run .orderPop .catalogueSeed .incrementOrder .incrementOrder (aux .orders) (store c)
    (unary (n+1)) rfl rfl
  rw [unary_succ,store_write] at h3
  change Runs program 1 _ _ (ctl .incrementOrder) (store d) at h3
  have h4:=push_run .incrementOrder .incrementWeight (aux .order) true (store d) rfl
  rw [store_write] at h4
  change Runs program 1 _ _ _ (store e) at h4
  have h5:=push_run .incrementWeight .orderCheck (aux .weight) true (store e) rfl
  rw [store_write] at h5
  change Runs program 1 _ _ _ (store (scanning p t width n (j+1) 0 0 wh' lh')) at h5
  have h:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
  refine ⟨1+((5*(p*t)+4)+(u+(1+(1+1)))),?_,h⟩
  simp only [Nat.add_zero] at hu
  omega
/-- Fixed arithmetic closure for the actual per-order scan costs. -/
theorem order_overhead (slots j n:Nat):
    100*(slots+1)*(j+slots+2)+5*slots+8 ≤1000*(slots+1)*(j+n+slots+3):=by
  nlinarith
/-- Complete physical catalogue enumeration, with work polynomial in its actual finite dimensions. -/
theorem orders_run (p t width n j:Nat) (wh lh:List Bool):
    ∃time ≤1000*(n+1)*(p*t+1)*(j+n+p*t+2),Runs program time (ctl .orderCheck)
      (store (scanning p t width n j 0 0 wh lh)) (ctl .catalogueSeed)
      (store (scanning p t width 0 (j+n) 0 0
        (history (orderWeights (p*t) j n) wh) (history (orderLabels (p*t) j n) lh))):=by
  induction n generalizing j wh lh with
  | zero=>
    refine ⟨1,?_,?_⟩
    · have h:0 < 1000*(0+1)*(p*t+1)*(j+0+p*t+2):=by positivity
      omega
    ·
      have h:Runs program 1 (ctl .orderCheck) (store (scanning p t width 0 j 0 0 wh lh))
        (ctl .catalogueSeed) (store (scanning p t width 0 j 0 0 wh lh)):=
      one_base program _ _ _ _ _ rfl rfl rfl
      simpa only [Nat.add_zero,orderWeights,orderLabels,List.range_zero,List.flatMap_nil,history,
        List.foldr_nil,List.reverse_nil,List.nil_append] using h
  | succ n ih=>
    obtain ⟨u,hu,h0⟩:=order_step p t width n j wh lh
    obtain ⟨v,hv,h1⟩:=ih (j+1) (history (slotWeights j (p*t)) wh) (history (slotLabels j 0 (p*t)) lh)
    have h:=join h0 h1
    refine ⟨u+v,?_,?_⟩
    · have he:1000*(n+1+1)*(p*t+1)*(j+(n+1)+p*t+2)=
          1000*(n+1)*(p*t+1)*(j+1+n+p*t+2)+1000*(p*t+1)*(j+n+p*t+3):=by ring
      rw [he]
      have hh:=order_overhead (p*t) j n
      omega
    · rw [orderWeights_cons,orderLabels_cons,history_append,history_append]
      have he:(j+1)+n=j+(n+1):=by omega
      simpa only [he] using h
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueOrders
