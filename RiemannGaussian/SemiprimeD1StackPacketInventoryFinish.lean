/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
/-! # Paid complete placement reversal and physical successful stop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryFinish
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryClass
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl"=>Label.local
/-- Complete result is exactly the finite physical view after history transfer and true-success push. -/
theorem result_eq (source alphabet:List Bool) (s:Summary):
    result source alphabet s=
      view ({(fresh source [] [] (Dict.dictionary s.classes) s.edge) with
        trimScratch:=vectorBits (s.placements.map placementBytes),comparison:=[true]})
        (reader (vectorBits s.packets) [] [] [] [])
        (orientation alphabet (Dict.dictionary s.seen) (Dict.dictionary s.slots) [] [] [] []):=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
/-- Literal terminator push, real entire history reversal, and true-success push; the final halt is charged separately. -/
theorem finish_run (source alphabet:List Bool) (s:Summary):
    Runs program (2*(history s.placements).length+5) (ctl .seedOutput)
      (boundary source alphabet [] s) (ctl .done) (result source alphabet s):=by
  let f:=fresh source [] [] (Dict.dictionary s.classes) s.edge
  let r:=reader (vectorBits s.packets) (history s.placements).reverse [] [] []
  let o:=orientation alphabet (Dict.dictionary s.seen) (Dict.dictionary s.slots) [] [] [] []
  have h0:=push_run .seedOutput (ctl .reverseOutput) output false (view f r o) rfl
  change Runs program 1 _ _ _ (Function.update (view f r o) (frequencyStack (F.aux .trimScratch)) [false]) at h0
  rw [update_trimScratch] at h0
  let f1:W.Words:={f with trimScratch:=[false]}
  have h1:=reverse_call .finish .reverseOutput .accept rfl (view f1 r o) (history s.placements).reverse [false] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view f1 r o)
    (readerAllocation (.inr .catalogue)) []) (frequencyStack (F.aux .trimScratch))
    ((history s.placements).reverse.reverse++[false])) at h1
  rw [update_readerAllocation,reader_update_history,update_trimScratch,List.reverse_reverse,history_vector] at h1
  let f2:W.Words:={f with trimScratch:=vectorBits (s.placements.map placementBytes)}
  let r2:=reader (vectorBits s.packets) [] [] [] []
  have h2:=push_run .accept (ctl .done) success true (view f2 r2 o) rfl
  change Runs program 1 _ _ _ (Function.update (view f2 r2 o) (frequencyStack (F.lookupStack (.inl .output))) [true]) at h2
  rw [update_comparison] at h2
  have h:=join (join h0 h1) h2
  change Runs program (2*(history s.placements).length+5) (ctl .seedOutput) (view f r o) (ctl .done) (result source alphabet s)
  rw [result_eq]
  convert h using 1
  simp only [List.length_reverse]
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryFinish
