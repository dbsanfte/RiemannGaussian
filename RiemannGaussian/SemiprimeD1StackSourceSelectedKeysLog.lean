/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLookup
/-! # Real raw-tail joint framing, vector framing and one occurrence log -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLog
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact actual cost of both preserving Frame calls, true vector tag, and physical row-log reversal. -/
def frameTime (i:Inputs) (own fac:List Bool) :Nat :=
  (6*(readID i.ids own).length+5)+(6*(joint i.ids (own,fac)).length+5)+1+
    (2*(chunk i.ids (own,fac)).length+3)
/-- The factor ID is already an actual raw key tail; Frame prefixes only the owner field, then vector framing/logging is paid. -/
theorem frame_run (i:Inputs) (reader own fac hist:List Bool) :
    Runs program (frameTime i own fac) .frameJoint
      (view i [] [] [] reader own fac (readID i.ids own) (readID i.ids fac) [] [] hist []) .clearOwnerID
      (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] []
        ((chunk i.ids (own,fac)).reverse++hist) []) :=by
  have h0:=frame_call .joint .frameJoint .frameVector rfl
    (view i [] [] [] reader own fac (readID i.ids own) (readID i.ids fac) [] [] hist [])
    (readID i.ids own) (readID i.ids fac) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view i [] [] [] reader own fac (readID i.ids own) (readID i.ids fac) [] [] hist []) (aux .key) (joint i.ids (own,fac))) at h0
  rw [update_key] at h0
  have h1:=frame_call .vector .frameVector .tag rfl
    (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] [] hist [])
    (joint i.ids (own,fac)) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] [] hist [])
      (aux .frameBuffer) (frame (joint i.ids (own,fac)) [])) at h1
  rw [update_buffer] at h1
  have h2:=push_run .tag .reverseRow (aux .frameBuffer) true
    (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] (frame (joint i.ids (own,fac)) []) hist []) rfl
  change Runs program 1 _ _ _ (Function.update
    (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] (frame (joint i.ids (own,fac)) []) hist [])
      (aux .frameBuffer) (chunk i.ids (own,fac))) at h2
  rw [update_buffer] at h2
  have h3:=reverse_call .row .reverseRow .clearOwnerID rfl
    (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] (chunk i.ids (own,fac)) hist [])
    (chunk i.ids (own,fac)) hist rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (view i [] [] [] reader own fac (readID i.ids own) (joint i.ids (own,fac)) [] (chunk i.ids (own,fac)) hist [])
      (aux .frameBuffer) []) (aux .history) ((chunk i.ids (own,fac)).reverse++hist)) at h3
  rw [update_buffer,update_hist] at h3
  exact join (join (join h0 h1) h2) h3
/-- Every saved ID, joint key and parsed variable-key word is physically erased before the next occurrence. -/
theorem clear_run (i:Inputs) (reader own fac ownID key hist:List Bool) :
    Runs program ((ownID.length+1)+(key.length+1)+(own.length+1)+(fac.length+1)) .clearOwnerID
      (view i [] [] [] reader own fac ownID key [] [] hist []) .header
      (view i [] [] [] reader [] [] [] [] [] [] hist []) :=by
  have h0:=drain_loop .clearOwnerID .clearKey (aux .ownerID) rfl
    (view i [] [] [] reader own fac ownID key [] [] hist []) ownID rfl
  rw [update_ownID] at h0
  have h1:=drain_loop .clearKey .clearOwnerKey (aux .key) rfl
    (view i [] [] [] reader own fac [] key [] [] hist []) key rfl
  rw [update_key] at h1
  have h2:=drain_loop .clearOwnerKey .clearFactorKey (aux .ownerKey) rfl
    (view i [] [] [] reader own fac [] [] [] [] hist []) own rfl
  rw [update_own] at h2
  have h3:=drain_loop .clearFactorKey .header (aux .factorKey) rfl
    (view i [] [] [] reader [] fac [] [] [] [] hist []) fac rfl
  rw [update_fac] at h3
  exact join (join (join h0 h1) h2) h3
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLog
