/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsView
/-! # Real joint-key copy and one owner-ID Field parse
The factor ID is the physically unconsumed raw tail, never a second framed
field or supplied decoded ID. Both original input words remain retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsPrepare
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Exactly the two input words are supplied before any physical seed/copy/parser stage. -/
theorem initial_data (key catalogue:List Bool) :
    (initial key catalogue).data=view key catalogue [] [] [] [] [] [] [] [] [] [] [] [] [] [] :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- True actual key front-end, including both empty-vector seeds, the preserving copy and actual valid-byte pop. -/
theorem prepare_run (owner factor catalogue:List Bool) :
    Runs program (5*(frame owner factor).length+8*owner.length+14) (ctl .start)
      (initial (frame owner factor) catalogue).data (ctl (.copyMenu false))
      (view (frame owner factor) catalogue factor [] [] owner [] [] [] [] [] [] [] [] [false] [false]) :=by
  rw [initial_data]
  have h0:=push_run .start (ctl .seedRight) (output false) false
    (view (frame owner factor) catalogue [] [] [] [] [] [] [] [] [] [] [] [] [] []) rfl
  change Runs program 1 _ _ _ (Function.update
    (view (frame owner factor) catalogue [] [] [] [] [] [] [] [] [] [] [] [] [] []) (output false) [false]) at h0
  rw [update_leftOutput] at h0
  have h1:=push_run .seedRight (ctl .copyKey) (output true) false
    (view (frame owner factor) catalogue [] [] [] [] [] [] [] [] [] [] [] [] [false] []) rfl
  change Runs program 1 _ _ _ (Function.update
    (view (frame owner factor) catalogue [] [] [] [] [] [] [] [] [] [] [] [] [false] []) (output true) [false]) at h1
  rw [update_rightOutput] at h1
  have h2:=copy_call .key .copyKey .parseKey rfl
    (view (frame owner factor) catalogue [] [] [] [] [] [] [] [] [] [] [] [] [false] [false]) (frame owner factor) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (view (frame owner factor) catalogue [] [] [] [] [] [] [] [] [] [] [] [] [false] [false]) (aux .keyReader) (frame owner factor++[])) at h2
  rw [List.append_nil,update_keyReader] at h2
  have h3:=field_valid .owner .parseKey .keyValid (ctl (.copyMenu false)) rfl rfl
    (view (frame owner factor) catalogue (frame owner factor) [] [] [] [] [] [] [] [] [] [] [] [false] [false]) owner factor rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (view (frame owner factor) catalogue (frame owner factor) [] [] [] [] [] [] [] [] [] [] [] [false] [false])
    (aux .keyReader) factor) query owner) at h3
  rw [update_keyReader,update_queryWord] at h3
  have h:=join (join (join h0 h1) h2) h3
  have ht:1+1+(5*(frame owner factor).length+4)+(8*owner.length+8)=5*(frame owner factor).length+8*owner.length+14:=by omega
  simpa only [ht] using h
end RiemannGaussian.SemiprimeD1StackPacketRowsPrepare
