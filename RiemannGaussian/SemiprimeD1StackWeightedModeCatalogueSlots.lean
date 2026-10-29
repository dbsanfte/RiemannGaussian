/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCataloguePrimitives
/-! # Actual slot-major catalogue records and their primitive execution costs -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueSlots
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCataloguePrimitives
open SemiprimeD1StackWeightedModeView (unary unary_length unary_succ history history_cons)
open SemiprimeD1StackWeightedModeSpec (history_single)
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => (Sum.inl :Control→Label)
/-- One slot is physically popped, both actual rows emitted, then its index incremented. -/
theorem slot_step (p t width remaining j todo i:Nat) (wh lh:List Bool) :
    ∃time ≤100*(j+i+1),Runs program time (ctl .slotCheck)
      (store (scanning p t width remaining j (todo+1) i wh lh)) (ctl .slotCheck)
      (store (scanning p t width remaining j todo (i+1)
        (history [unary (j+1)] wh) (history [modeWord i j] lh))):=by
  let a:=scanning p t width remaining j (todo+1) i wh lh
  let b:=scanning p t width remaining j todo i wh lh
  let c:Words:={b with weightHistory:=history [unary (j+1)] wh}
  let d:Words:={c with word:=frame (unary j) []}
  let e:Words:={d with word:=modeWord i j}
  let f:Words:={e with labelHistory:=history [modeWord i j] lh}
  let g:Words:={f with word:=[]}
  have h0:=pop_run .slotCheck .clearSlot .emitWeight .emitWeight (aux .slotsTodo) (store a)
    (unary (todo+1)) rfl rfl
  rw [unary_succ,store_write] at h0
  change Runs program 1 _ _ (ctl .emitWeight) (store b) at h0
  obtain ⟨u,hu,h1⟩:=body_call true .emitWeight .frameOrder rfl (store b) (unary (j+1)) wh rfl rfl rfl
  rw [store_write] at h1
  change Runs program u _ _ _ (store {b with weightHistory:=(SemiprimeD1StackWeightedModeView.row (unary (j+1))).reverse++wh}) at h1
  replace h1:Runs program u (ctl .emitWeight) (store b) (ctl .frameOrder) (store c):=by
    simpa only [c,history_single] using h1
  have h2:=frame_call false .frameOrder .frameSlot rfl (store c) (unary j) [] rfl rfl rfl
  rw [store_write,unary_length] at h2
  change Runs program (6*j+5) _ _ _ (store d) at h2
  have h3:=frame_call true .frameSlot .emitLabel rfl (store d) (unary i) (frame (unary j) []) rfl rfl rfl
  rw [store_write,unary_length] at h3
  change Runs program (6*i+5) _ _ _ (store e) at h3
  obtain ⟨v,hv,h4⟩:=body_call false .emitLabel .clearWord rfl (store e) (modeWord i j) lh rfl rfl rfl
  rw [store_write] at h4
  change Runs program v _ _ _ (store {e with labelHistory:=(SemiprimeD1StackWeightedModeView.row (modeWord i j)).reverse++lh}) at h4
  replace h4:Runs program v (ctl .emitLabel) (store e) (ctl .clearWord) (store f):=by
    simpa only [f,history_single] using h4
  have h5:=drain_loop .clearWord .incrementSlot (aux .word) rfl (store f) (modeWord i j) rfl
  rw [store_write,modeWord_length] at h5
  change Runs program (2*i+2*j+2+1) _ _ _ (store g) at h5
  have h6:=push_run .incrementSlot .slotCheck (aux .slot) true (store g) rfl
  rw [store_write] at h6
  change Runs program 1 _ _ _ (store (scanning p t width remaining j todo (i+1)
    (history [unary (j+1)] wh) (history [modeWord i j] lh))) at h6
  have h:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 h6)))))
  refine ⟨1+(u+((6*j+5)+((6*i+5)+(v+((2*i+2*j+2+1)+1))))),?_,h⟩
  rw [unary_length] at hu
  rw [modeWord_length] at hv
  omega
/-- EOF and actual slot-index draining reach the real next-order pop location. -/
theorem slots_end (p t width remaining j i:Nat) (wh lh:List Bool) :
    Runs program (i+2) (ctl .slotCheck) (store (scanning p t width remaining j 0 i wh lh))
      (ctl .orderPop) (store (scanning p t width remaining j 0 0 wh lh)):=by
  let v:=scanning p t width remaining j 0 i wh lh
  have h0:=pop_run .slotCheck .clearSlot .emitWeight .emitWeight (aux .slotsTodo) (store v) [] rfl rfl
  rw [store_write] at h0
  change Runs program 1 _ _ (ctl .clearSlot) (store v) at h0
  have h1:=drain_loop .clearSlot .orderPop (aux .slot) rfl (store v) (unary i) rfl
  rw [store_write,unary_length] at h1
  change Runs program (i+1) _ _ _ (store (scanning p t width remaining j 0 0 wh lh)) at h1
  have h:=join h0 h1
  convert h using 1;omega
/-- Every real slot contributes precisely its label/weight before the next order is entered. -/
theorem slots_run (p t width remaining j n i:Nat) (wh lh:List Bool) :
    ∃time ≤100*(n+1)*(j+i+n+2),Runs program time (ctl .slotCheck)
      (store (scanning p t width remaining j n i wh lh)) (ctl .orderPop)
      (store (scanning p t width remaining j 0 0
        (history (slotWeights j n) wh) (history (slotLabels j i n) lh))):=by
  induction n generalizing i wh lh with
  | zero=>
    refine ⟨i+2,by omega,?_⟩
    simpa only [slotWeights,slotLabels,List.replicate_zero,List.range_zero,List.map_nil,history,
      List.foldr_nil,List.reverse_nil,List.nil_append] using slots_end p t width remaining j i wh lh
  | succ n ih=>
    obtain ⟨u,hu,h0⟩:=slot_step p t width remaining j n i wh lh
    obtain ⟨v,hv,h1⟩:=ih (i+1) (history [unary (j+1)] wh) (history [modeWord i j] lh)
    have h:=join h0 h1
    refine ⟨u+v,?_,?_⟩
    · nlinarith only [hu,hv]
    · rw [slotWeights,List.replicate_succ,slotLabels_cons,history_cons,history_cons]
      simpa only [slotWeights,history_single] using h
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueSlots
