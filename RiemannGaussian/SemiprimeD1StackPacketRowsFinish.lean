/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsRowView
import RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
/-! # Both actual history reversals produce chronological colour vectors
Histories are physically consumed, and the originally pushed false vector
terminators remain the actual output tails. No native reverse-vector answer is
an input or opcode of the source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsFinish
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsRowView
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Both complete real reversal calls preserve the original inputs and clear their actual histories. -/
theorem finish_run (key catalogue:List Bool) (histories:Bool→List Bool) :
    Runs program (2*(histories false).length+2*(histories true).length+6) (ctl .reverseLeft)
      (rowView key catalogue (fun _=>[]) (fun _=>[]) histories (fun _=>[false]) [])
      (ctl .accept)
      (rowView key catalogue (fun _=>[]) (fun _=>[]) (fun _=>[])
        (fun side=>(histories side).reverse++[false]) []) :=by
  have h0:=reverse_call (.finish false) .reverseLeft .reverseRight rfl
    (rowView key catalogue (fun _=>[]) (fun _=>[]) histories (fun _=>[false]) []) (histories false) [false] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (rowView key catalogue (fun _=>[]) (fun _=>[]) histories (fun _=>[false]) [])
    (history false) []) (output false) ((histories false).reverse++[false])) at h0
  rw [update_histories,update_outputs] at h0
  let midHistories:=Function.update histories false []
  let midOutputs:=Function.update (fun _ :Bool=>[false]) false ((histories false).reverse++[false])
  have h1:=reverse_call (.finish true) .reverseRight .accept rfl
    (rowView key catalogue (fun _=>[]) (fun _=>[]) midHistories midOutputs []) (histories true) [false] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (rowView key catalogue (fun _=>[]) (fun _=>[]) midHistories midOutputs [])
    (history true) []) (output true) ((histories true).reverse++[false])) at h1
  rw [update_histories,update_outputs] at h1
  have hh:Function.update midHistories true []=(fun _ :Bool=>[]) :=by funext side;cases side <;> rfl
  have ho:Function.update midOutputs true ((histories true).reverse++[false])=
      (fun side=>(histories side).reverse++[false]):=by funext side;cases side <;> rfl
  rw [hh,ho] at h1
  have h:=join h0 h1
  have ht:(2*(histories false).length+3)+(2*(histories true).length+3)=
      2*(histories false).length+2*(histories true).length+6:=by omega
  simpa only [ht] using h
end RiemannGaussian.SemiprimeD1StackPacketRowsFinish
