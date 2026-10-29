/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationRowView
/-! # Actual preserving copies of the two acquired row vectors and binary index -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationPrepare
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationView SemiprimeD1StackPacketOrientationRowView
open SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Proof notation for exactly the three retained original source words. -/
def originals (left right index:List Bool) (i:Fin 3):List Bool:=if i=0 then left else if i=1 then right else index
/-- Complete physical initial bank, including every empty real helper role. -/
theorem initial_data (left right index:List Bool):
    (initial left right index).data=view left right index [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- All three original inputs are physically copied and restored before any row/index bit is consumed. -/
theorem prepare_run (left right index:List Bool):
    Runs program (5*left.length+5*right.length+5*index.length+12) (ctl .start) (initial left right index).data
      (ctl .leftTag) (rowView (originals left right index) (fun side=>if side then right else left) index
        (fun _=>[]) [] [] [] [] []) :=by
  have h0:=copy_call (.input 0) .start .copyRight rfl
    (view left right index [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []) left [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view left right index [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []) (aux .leftReader) (left++[])) at h0
  rw [List.append_nil,update_leftReader] at h0
  have h1:=copy_call (.input 1) .copyRight .copyIndex rfl
    (view left right index left [] [] [] [] [] [] [] [] [] [] [] [] [] [] []) right [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view left right index left [] [] [] [] [] [] [] [] [] [] [] [] [] [] []) (aux .rightReader) (right++[])) at h1
  rw [List.append_nil,update_rightReader] at h1
  have h2:=copy_call (.input 2) .copyIndex .leftTag rfl
    (view left right index left right [] [] [] [] [] [] [] [] [] [] [] [] [] []) index [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view left right index left right [] [] [] [] [] [] [] [] [] [] [] [] [] []) (aux .indexCursor) (index++[])) at h2
  rw [List.append_nil,update_indexCursor] at h2
  have h:=join (join h0 h1) h2
  rw [initial_data]
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackPacketOrientationPrepare
