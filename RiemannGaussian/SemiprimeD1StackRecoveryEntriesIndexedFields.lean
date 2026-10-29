/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedPrimitives
import RiemannGaussian.SemiprimeD1TensorTapeCodec
/-! # Actual selected/skipped Field acquisition and complete EOF cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedFields
open SemiprimeD1StackRecoveryEntriesIndexed SemiprimeD1StackRecoveryEntriesIndexedState
open SemiprimeD1StackRecoveryEntriesIndexedPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Complete actual parser call, materializing the actual field and actual true validity bit. -/
theorem field_call (take:Bool) (cache query counter word tail:List Bool):
    Runs program (8*word.length+7) (.local (.field take)) (view cache query counter (frame word tail) [])
      (.local (.parsed take)) (store [] [] [] [] cache query counter tail [] word [true] []):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  apply included_call program fieldStack Label.field field_injective F.code (F.active .tagPop (none,false))
    (fun _=>rfl) (.local (.field take)) (.local (.parsed take)) rfl (8*word.length+6)
    before after _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail [])
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k with
        | reader=>exact (hk (.inl .input) rfl).elim
        | value=>exact (hk (.inl .output) rfl).elim
        | valid=>exact (hk (.inr ()) rfl).elim
        | cache|query|counter|parser|copy=>rfl
/-- Real validity pop and its finite branch, after actual parser execution. -/
theorem read_run (take:Bool) (cache query counter word tail:List Bool):
    Runs program (8*word.length+8) (.local (.field take)) (view cache query counter (frame word tail) [])
      (if take then .local .clearReader else .local .clearValue) (view cache query counter tail word):=by
  have h0:=field_call take cache query counter word tail
  have h1:=pop_run (.local (.parsed take)) (.local .abort) (.local .abort)
    (if take then .local .clearReader else .local .clearValue) (aux .valid)
    (store [] [] [] [] cache query counter tail [] word [true] []) [true] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  dsimp only [aux] at h1
  rw [update_valid] at h1
  have h:=join h0 h1
  convert h using 1;rfl
/-- Every skipped payload byte is physically erased before the ordinal is incremented. -/
theorem skip_run (cache query counter word tail:List Bool):
    Runs program (9*word.length+9) (.local (.field false)) (view cache query counter (frame word tail) [])
      (.local .increment) (view cache query counter tail []):=by
  have h0:=read_run false cache query counter word tail
  have h1:=drain_run (.local .clearValue) (.local .increment) (aux .value) (view cache query counter tail word) word rfl rfl
  dsimp only [view,aux] at h1
  rw [update_value] at h1
  have h:=join h0 h1
  convert h using 1 <;> first | rfl | omega
/-- Complete actual unread-suffix and ordinal cleanup after either take or vector EOF. -/
theorem cleanup_run (cache query counter reader value:List Bool):
    Runs program ((reader.length+1)+(counter.length+1)) (.local .clearReader) (view cache query counter reader value)
      (.local .done) (view cache query [] [] value):=by
  have h0:=drain_run (.local .clearReader) (.local .clearCounter) (aux .reader) (view cache query counter reader value) reader rfl rfl
  dsimp only [view,aux] at h0
  rw [update_reader] at h0
  have h1:=drain_run (.local .clearCounter) (.local .done) (aux .counter) (view cache query counter [] value) counter rfl rfl
  dsimp only [view,aux] at h1
  rw [update_counter] at h1
  exact join h0 h1
/-- Actual final false vector marker is consumed; no work follows the numeric query value. -/
theorem eof_run (cache query counter:List Bool):
    Runs program (counter.length+3) (.local .loop) (view cache query counter [false] [])
      (.local .done) (view cache query [] [] []):=by
  have h0:=pop_run (.local .loop) (.local .clearCounter) (.local .clearReader) (.local .query)
    (aux .reader) (view cache query counter [false] []) [false] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  dsimp only [view,aux] at h0
  rw [update_reader] at h0
  have h1:=cleanup_run cache query counter [] []
  have h:=join h0 h1
  simp only [List.length_nil] at h
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedFields
