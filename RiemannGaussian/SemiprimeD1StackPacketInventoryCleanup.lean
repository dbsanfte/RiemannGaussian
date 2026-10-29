/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
/-! # Complete actual reader/orientation cleanup, retaining all physical globals
Every empty-word branch and every nonempty output byte is physically visited.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryCleanup
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- All seventeen actual reader work/output words are drained while packet/history and every other bank survive. -/
theorem reader_run (f:W.Words) (o:O.Stack→List Bool) (packets hist left right:List Bool):
    Runs program (left.length+right.length+17) (ctl (.clearReader .leftWord))
      (view f (reader packets hist left right []) o) (ctl (.clearOrientation .leftOperand))
      (view f (reader packets hist [] [] []) o) :=by
  let before:=view f (reader packets hist left right []) o
  have h0:=drain_loop (.clearReader .leftWord) (ctl (.clearReader .rightWord))
    (readerStack (R.workStack .leftWord)) rfl before [] rfl
  have e0:Function.update before (readerStack (R.workStack .leftWord)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e0] at h0
  have h1:=drain_loop (.clearReader .rightWord) (ctl (.clearReader .unused))
    (readerStack (R.workStack .rightWord)) rfl before [] rfl
  have e1:Function.update before (readerStack (R.workStack .rightWord)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e1] at h1
  have h2:=drain_loop (.clearReader .unused) (ctl (.clearReader .success))
    (readerStack (R.workStack .unused)) rfl before [] rfl
  have e2:Function.update before (readerStack (R.workStack .unused)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e2] at h2
  have h3:=drain_loop (.clearReader .success) (ctl (.clearReader .query))
    (readerStack (R.workStack .success)) rfl before [] rfl
  have e3:Function.update before (readerStack (R.workStack .success)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e3] at h3
  have h4:=drain_loop (.clearReader .query) (ctl (.clearReader .reader))
    (readerStack (R.workStack .query)) rfl before [] rfl
  have e4:Function.update before (readerStack (R.workStack .query)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e4] at h4
  have h5:=drain_loop (.clearReader .reader) (ctl (.clearReader .parserScratch))
    (readerStack (R.workStack .reader)) rfl before [] rfl
  have e5:Function.update before (readerStack (R.workStack .reader)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e5] at h5
  have h6:=drain_loop (.clearReader .parserScratch) (ctl (.clearReader .valid))
    (readerStack (R.workStack .parserScratch)) rfl before [] rfl
  have e6:Function.update before (readerStack (R.workStack .parserScratch)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e6] at h6
  have h7:=drain_loop (.clearReader .valid) (ctl (.clearReader .copyScratch))
    (readerStack (R.workStack .valid)) rfl before [] rfl
  have e7:Function.update before (readerStack (R.workStack .valid)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e7] at h7
  have h8:=drain_loop (.clearReader .copyScratch) (ctl (.clearReader .frame))
    (readerStack (R.workStack .copyScratch)) rfl before [] rfl
  have e8:Function.update before (readerStack (R.workStack .copyScratch)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e8] at h8
  have h9:=drain_loop (.clearReader .frame) (ctl (.clearReader .rightBytes))
    (readerStack (R.workStack .frame)) rfl before [] rfl
  have e9:Function.update before (readerStack (R.workStack .frame)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e9] at h9
  have h10:=drain_loop (.clearReader .rightBytes) (ctl (.clearReader .keyReader))
    (readerStack (R.workStack .rightBytes)) rfl before [] rfl
  have e10:Function.update before (readerStack (R.workStack .rightBytes)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e10] at h10
  have h11:=drain_loop (.clearReader .keyReader) (ctl (.clearReader .leftBytes))
    (readerStack (R.workStack .keyReader)) rfl before [] rfl
  have e11:Function.update before (readerStack (R.workStack .keyReader)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e11] at h11
  have h12:=drain_loop (.clearReader .leftBytes) (ctl (.clearReader .leftHistory))
    (readerStack (R.workStack .leftBytes)) rfl before [] rfl
  have e12:Function.update before (readerStack (R.workStack .leftBytes)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e12] at h12
  have h13:=drain_loop (.clearReader .leftHistory) (ctl (.clearReader .rightHistory))
    (readerStack (R.workStack .leftHistory)) rfl before [] rfl
  have e13:Function.update before (readerStack (R.workStack .leftHistory)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e13] at h13
  have h14:=drain_loop (.clearReader .rightHistory) (ctl (.clearReader .leftOutput))
    (readerStack (R.workStack .rightHistory)) rfl before [] rfl
  have e14:Function.update before (readerStack (R.workStack .rightHistory)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e14] at h14
  have h15:=drain_loop (.clearReader .leftOutput) (ctl (.clearReader .rightOutput))
    (readerStack (R.workStack .leftOutput)) rfl before left rfl
  change Runs program _ _ _ _ (Function.update (view f (reader packets hist left right []) o)
    (readerAllocation (.inr .leftOutput)) []) at h15
  rw [update_readerAllocation] at h15
  rw [reader_update_left] at h15
  have h16:=drain_loop (.clearReader .rightOutput) (ctl (.clearOrientation .leftOperand))
    (readerStack (R.workStack .rightOutput)) rfl (view f (reader packets hist [] right []) o) right rfl
  change Runs program _ _ _ _ (Function.update (view f (reader packets hist [] right []) o)
    (readerAllocation (.inr .rightOutput)) []) at h16
  rw [update_readerAllocation] at h16
  rw [reader_update_right] at h16
  have h:=(join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16)
  simp only [List.length_nil] at h
  convert h using 1; first | rfl | omega
/-- All sixteen actual orientation work/output words are drained while catalogue/seen/slots and every other bank survive. -/
theorem orientation_run (f:W.Words) (r:R.Stack→List Bool) (cat seen slots packet slot:List Bool):
    Runs program (packet.length+slot.length+16) (ctl (.clearOrientation .leftOperand))
      (view f r (orientation cat seen slots packet slot [] [])) (ctl .header)
      (view f r (orientation cat seen slots [] [] [] [])) :=by
  let before:=view f r (orientation cat seen slots packet slot [] [])
  have h0:=drain_loop (.clearOrientation .leftOperand) (ctl (.clearOrientation .rightOperand))
    (orientationStack (O.work .leftOperand)) rfl before [] rfl
  have e0:Function.update before (orientationStack (O.work .leftOperand)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e0] at h0
  have h1:=drain_loop (.clearOrientation .rightOperand) (ctl (.clearOrientation .scratch))
    (orientationStack (O.work .rightOperand)) rfl before [] rfl
  have e1:Function.update before (orientationStack (O.work .rightOperand)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e1] at h1
  have h2:=drain_loop (.clearOrientation .scratch) (ctl (.clearOrientation .buffer))
    (orientationStack (O.work .scratch)) rfl before [] rfl
  have e2:Function.update before (orientationStack (O.work .scratch)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e2] at h2
  have h3:=drain_loop (.clearOrientation .buffer) (ctl (.clearOrientation .answer))
    (orientationStack (O.work .buffer)) rfl before [] rfl
  have e3:Function.update before (orientationStack (O.work .buffer)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e3] at h3
  have h4:=drain_loop (.clearOrientation .answer) (ctl (.clearOrientation .leftReader))
    (orientationStack (O.work .answer)) rfl before [] rfl
  have e4:Function.update before (orientationStack (O.work .answer)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e4] at h4
  have h5:=drain_loop (.clearOrientation .leftReader) (ctl (.clearOrientation .rightReader))
    (orientationStack (O.work .leftReader)) rfl before [] rfl
  have e5:Function.update before (orientationStack (O.work .leftReader)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e5] at h5
  have h6:=drain_loop (.clearOrientation .rightReader) (ctl (.clearOrientation .indexCursor))
    (orientationStack (O.work .rightReader)) rfl before [] rfl
  have e6:Function.update before (orientationStack (O.work .rightReader)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e6] at h6
  have h7:=drain_loop (.clearOrientation .indexCursor) (ctl (.clearOrientation .leftColour))
    (orientationStack (O.work .indexCursor)) rfl before [] rfl
  have e7:Function.update before (orientationStack (O.work .indexCursor)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e7] at h7
  have h8:=drain_loop (.clearOrientation .leftColour) (ctl (.clearOrientation .rightColour))
    (orientationStack (O.work .leftColour)) rfl before [] rfl
  have e8:Function.update before (orientationStack (O.work .leftColour)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e8] at h8
  have h9:=drain_loop (.clearOrientation .rightColour) (ctl (.clearOrientation .copyScratch))
    (orientationStack (O.work .rightColour)) rfl before [] rfl
  have e9:Function.update before (orientationStack (O.work .rightColour)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e9] at h9
  have h10:=drain_loop (.clearOrientation .copyScratch) (ctl (.clearOrientation .keyHistory))
    (orientationStack (O.work .copyScratch)) rfl before [] rfl
  have e10:Function.update before (orientationStack (O.work .copyScratch)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e10] at h10
  have h11:=drain_loop (.clearOrientation .keyHistory) (ctl (.clearOrientation .slotHistory))
    (orientationStack (O.work .keyHistory)) rfl before [] rfl
  have e11:Function.update before (orientationStack (O.work .keyHistory)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e11] at h11
  have h12:=drain_loop (.clearOrientation .slotHistory) (ctl (.clearOrientation .keyOutput))
    (orientationStack (O.work .slotHistory)) rfl before [] rfl
  have e12:Function.update before (orientationStack (O.work .slotHistory)) []=before:=by
    exact Function.update_eq_self _ _
  rw [e12] at h12
  have h13:=drain_loop (.clearOrientation .keyOutput) (ctl (.clearOrientation .slotOutput))
    (orientationStack (O.work .keyOutput)) rfl before packet rfl
  change Runs program _ _ _ _ (Function.update (view f r (orientation cat seen slots packet slot [] []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .keyOutput)) []) at h13
  rw [update_orientationAllocation] at h13
  dsimp only [orientation] at h13
  rw [SemiprimeD1StackPacketOrientationView.update_keyOutput] at h13
  have h14:=drain_loop (.clearOrientation .slotOutput) (ctl (.clearOrientation .highOutput))
    (orientationStack (O.work .slotOutput)) rfl (view f r (orientation cat seen slots [] slot [] [])) slot rfl
  change Runs program _ _ _ _ (Function.update (view f r (orientation cat seen slots [] slot [] []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .slotOutput)) []) at h14
  rw [update_orientationAllocation] at h14
  dsimp only [orientation] at h14
  rw [SemiprimeD1StackPacketOrientationView.update_slotOutput] at h14
  let after:=view f r (orientation cat seen slots [] [] [] [])
  have h15:=drain_loop (.clearOrientation .highOutput) (ctl .header) (orientationStack (O.work .highOutput)) rfl after [] rfl
  have e15:Function.update after (orientationStack (O.work .highOutput)) []=after:=by exact Function.update_eq_self _ _
  rw [e15] at h15
  have h:=(join (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15)
  simp only [List.length_nil] at h
  convert h using 1; first | rfl | omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryCleanup
