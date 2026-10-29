/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueEmit
/-! # Actual local-port counter loop; every emitted occurrence is physically counted -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueLoop
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackPortCatalogueEmit
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1EdgeCatalogueEncoding (Record)
/-- Literal increasing local/occurrence ordinal records. No catalogue is consulted at runtime. -/
def records (words:Record) : ℕ→ℕ→ℕ→ℕ→List Bool→List Bool
  | 0,_,_,_,tail => tail
  | fuel+1,occurrence,factor,slot,tail =>
      record8 words (unary slot) (unary factor) (unary occurrence)
        (records words fuel (occurrence+1) factor (slot+1) tail)
/-- Exact sum of the actual eight-field emission and three local control transitions. -/
def loopTime (words:Record) : ℕ→ℕ→ℕ→ℕ→ℕ
  | 0,_,_,_ => 1
  | fuel+1,occurrence,factor,slot =>
      (10*mass8 words (unary slot) (unary factor) (unary occurrence)+83)+
        loopTime words fuel (occurrence+1) factor (slot+1)
/-- The actual EOF loop changes no cache or ordinal. -/
theorem loop_nil (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw slot edges factor occurrence:List Bool) :
    Runs program 1 (.local .loop) (clean base tape words raw slot edges factor occurrence [])
      (.local .clearSlot) (clean base tape words raw slot edges factor occurrence []) := by
  apply one_base program (.local .loop) (.local .clearSlot)
    (.pop (aux .remaining) (.local .clearSlot) (.local (.emitFrame 0)) (.local (.emitFrame 0))) _ _ rfl
  · rfl
  · change Function.update (clean base tape words raw slot edges factor occurrence []) (aux .remaining) []=_
    rw [clean_remaining]
/-- Each emitted port advances BOTH physically distinct counters by exactly one marker. -/
theorem increment_run (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw edges remaining:List Bool) (slot factor occurrence:ℕ) :
    Runs program 2 (.local .incrementSlot)
      (clean base tape words raw (unary slot) edges (unary factor) (unary occurrence) remaining)
      (.local .loop)
      (clean base tape words raw (unary (slot+1)) edges (unary factor) (unary (occurrence+1)) remaining) := by
  have h0:=push_run (.local .incrementSlot) (.local .incrementOccurrence) (oldAux .side) true
    (clean base tape words raw (unary slot) edges (unary factor) (unary occurrence) remaining) rfl
  change Runs program _ _ _ _ (Function.update
    (clean base tape words raw (unary slot) edges (unary factor) (unary occurrence) remaining)
      (oldAux .side) (unary (slot+1))) at h0
  rw [clean_slot] at h0
  have h1:=push_run (.local .incrementOccurrence) (.local .loop) (aux .occurrenceOrdinal) true
    (clean base tape words raw (unary (slot+1)) edges (unary factor) (unary occurrence) remaining) rfl
  change Runs program _ _ _ _ (Function.update
    (clean base tape words raw (unary (slot+1)) edges (unary factor) (unary occurrence) remaining)
      (aux .occurrenceOrdinal) (unary (occurrence+1))) at h1
  rw [clean_occurrence] at h1
  exact h0.trans h1
/-- Framing preserves the actual suffix, including empty fields. -/
theorem record8_append (words:Record) (slot factor occurrence tail:List Bool) :
    record8 words slot factor occurrence tail=record8 words slot factor occurrence []++tail := by
  unfold record8
  rw [SemiprimeD1StackEdgeCatalogueEmit.record_append,
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail,
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail,
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail]
/-- The entire actual remaining-port loop emits all and only the acquired number of ports. -/
theorem loop_run (base:V.Stack→List Bool) (tape:List Bool) (words:Record)
    (raw edges:List Bool) (fuel occurrence factor slot:ℕ) :
    Runs program (loopTime words fuel occurrence factor slot) (.local .loop)
      (clean base tape words raw (unary slot) edges (unary factor) (unary occurrence) (unary fuel))
      (.local .clearSlot)
      (clean base tape words ((records words fuel occurrence factor slot []).reverse++raw)
        (unary (slot+fuel)) edges (unary factor) (unary (occurrence+fuel)) []) := by
  induction fuel generalizing raw occurrence slot with
  | zero => simpa only [loopTime,records,show unary 0=[] from rfl,List.reverse_nil,List.nil_append,Nat.add_zero] using
      loop_nil base tape words raw (unary slot) edges (unary factor) (unary occurrence)
  | succ fuel ih =>
    let before:=clean base tape words raw (unary slot) edges (unary factor) (unary occurrence) (unary (fuel+1))
    have hp:Runs program 1 (.local .loop) before (.local (.emitFrame 0))
        (clean base tape words raw (unary slot) edges (unary factor) (unary occurrence) (unary fuel)):=by
      apply one_base program (.local .loop) (.local (.emitFrame 0))
        (.pop (aux .remaining) (.local .clearSlot) (.local (.emitFrame 0)) (.local (.emitFrame 0))) before _ rfl
      · rfl
      · change Function.update before (aux .remaining) (unary fuel)=_
        exact clean_remaining _ _ _ _ _ _ _ _ _ _
    let emitted:=(record8 words (unary slot) (unary factor) (unary occurrence) []).reverse++raw
    have he:=record_run base tape words raw (unary slot) edges (unary factor) (unary occurrence) (unary fuel)
    have hi:=increment_run base tape words emitted edges (unary fuel) slot factor occurrence
    have ht:=ih emitted (occurrence+1) (slot+1)
    have h:=hp.trans (he.trans (hi.trans ht))
    have hout:(records words fuel (occurrence+1) factor (slot+1) []).reverse++emitted=
        (records words (fuel+1) occurrence factor slot []).reverse++raw:=by
      rw [records,record8_append]
      simp only [List.reverse_append,List.append_assoc,emitted]
    rw [hout] at h
    simpa only [loopTime,show slot+1+fuel=slot+(fuel+1) by omega,
      show occurrence+1+fuel=occurrence+(fuel+1) by omega,
      show 1+(10*mass8 words (unary slot) (unary factor) (unary occurrence)+80+(2+
        loopTime words fuel (occurrence+1) factor (slot+1)))=
        (10*mass8 words (unary slot) (unary factor) (unary occurrence)+83)+
        loopTime words fuel (occurrence+1) factor (slot+1) by omega] using h
end RiemannGaussian.SemiprimeD1StackPortCatalogueLoop
