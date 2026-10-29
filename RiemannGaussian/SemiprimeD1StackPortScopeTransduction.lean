/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeScan
/-! # Whole actual equal-length port/ID stream transduction -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeTransduction
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeView
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1PortScopeEncoding (Port portFrame portTape scopeFrame output portMass)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame_length)
/-- Exact local actual transition sum over the physically matched streams. -/
def scanTime : List Port→List (List Bool)→ℕ
  | w::ws,id::ids => SemiprimeD1StackPortScopeScan.recordTime w id+scanTime ws ids
  | _,_ => 0
/-- Both streams are consumed in their actual order; no provided index inverse or gather answer. -/
theorem scan_run (ports:List Port) (ids:List (List Bool)) (hlen:ports.length=ids.length)
    (base:S.Stack→List Bool) (raw:List Bool) :
    Runs program (scanTime ports ids) (.local .parse)
      (clean base (portTape ports []) (vectorBits ids) (fun _=>[]) raw) (.local .parse)
      (clean base [] [false] (fun _=>[]) ((output ports ids []).reverse++raw)) := by
  induction ports generalizing ids raw with
  | nil =>
    have he:ids=[]:=List.eq_nil_of_length_eq_zero hlen.symm
    subst ids
    simpa only [scanTime,portTape,List.foldr_nil,vectorBits,output,List.reverse_nil,List.nil_append] using
      Runs.refl program (.local .parse) (clean base [] [false] (fun _=>[]) raw)
  | cons w ws ih =>
    cases ids with
    | nil => simp at hlen
    | cons id ids =>
      have hr:ws.length=ids.length:=by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
      have h0:=SemiprimeD1StackPortScopeScan.record_run base w id (portTape ws []) (vectorBits ids) raw
      let nextRaw:=(scopeFrame w id []).reverse++raw
      have h1:=ih ids hr nextRaw
      have h:=h0.trans h1
      have hout:(output ws ids []).reverse++nextRaw=(output (w::ws) (id::ids) []).reverse++raw:=by
        rw [output,SemiprimeD1PortScopeEncoding.scopeFrame_append]
        simp only [List.reverse_append,List.append_assoc,nextRaw]
      rw [hout] at h
      exact h
/-- All actual loop transitions are bounded by actual input bytes, including ID widths and every copy. -/
theorem scanTime_le (ports:List Port) (ids:List (List Bool)) (hlen:ports.length=ids.length) :
    scanTime ports ids≤100*((portTape ports []).length+(vectorBits ids).length) := by
  induction ports generalizing ids with
  | nil => cases ids <;> simp_all [scanTime]
  | cons w ws ih =>
    cases ids with
    | nil => simp at hlen
    | cons id ids =>
      have hr:ws.length=ids.length:=by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
      have h:=ih ids hr
      change SemiprimeD1StackPortScopeScan.recordTime w id+scanTime ws ids≤
        100*((portFrame w (portTape ws [])).length+(true::SemiprimeSourceHistogramKeyBits.frame id (vectorBits ids)).length)
      rw [SemiprimeD1PortScopeEncoding.portFrame_length,List.length_cons,frame_length]
      unfold SemiprimeD1StackPortScopeScan.recordTime
      omega
/-- Every emitted ID-tagged record is bounded by its actual two source streams. -/
theorem output_length_le (ports:List Port) (ids:List (List Bool)) (hlen:ports.length=ids.length) :
    (output ports ids []).length≤(portTape ports []).length+(vectorBits ids).length := by
  induction ports generalizing ids with
  | nil => cases ids <;> simp_all [output,portTape,vectorBits]
  | cons w ws ih =>
    cases ids with
    | nil => simp at hlen
    | cons id ids =>
      have hr:ws.length=ids.length:=by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
      have h:=ih ids hr
      change (SemiprimeSourceHistogramKeyBits.frame id (portFrame w (output ws ids []))).length≤
        (portFrame w (portTape ws [])).length+(true::SemiprimeSourceHistogramKeyBits.frame id (vectorBits ids)).length
      rw [frame_length,SemiprimeD1PortScopeEncoding.portFrame_length,
        SemiprimeD1PortScopeEncoding.portFrame_length,List.length_cons,frame_length]
      omega
/-- Exact final physical data after both copied readers and every field were consumed. -/
def finalData (base:S.Stack→List Bool) (out:List Bool) : Stack→List Bool :=
  Function.update (clean base [] [] (fun _=>[]) []) (aux .output) out
/-- Three real EOF/tag checks consume the actual vector nil marker. -/
theorem eof_run (base:S.Stack→List Bool) (raw:List Bool) :
    Runs program 3 (.local .parse) (clean base [] [false] (fun _=>[]) raw)
      (.local .finalReverse) (clean base [] [] (fun _=>[]) raw) := by
  have h0:Runs program 1 (.local .parse) (clean base [] [false] (fun _=>[]) raw)
      (.local .bankEnd) (clean base [] [false] (fun _=>[]) raw):=by
    apply one_base program _ _ (.peek (aux .readerPorts) (.local .bankEnd) (.local (.field 0)) (.local (.field 0))) _ _ rfl <;> rfl
  have h1:Runs program 1 (.local .bankEnd) (clean base [] [false] (fun _=>[]) raw)
      (.local .bankEOF) (clean base [] [] (fun _=>[]) raw):=by
    apply one_base program _ _ (.pop (aux .readerIds) (.local .abort) (.local .bankEOF) (.local .abort)) _ _ rfl
    · rfl
    · change Function.update (clean base [] [false] (fun _=>[]) raw) (aux .readerIds) []=_
      rw [clean_ids]
  have h2:Runs program 1 (.local .bankEOF) (clean base [] [] (fun _=>[]) raw)
      (.local .finalReverse) (clean base [] [] (fun _=>[]) raw):=by
    apply one_base program _ _ (.peek (aux .readerIds) (.local .finalReverse) (.local .abort) (.local .abort)) _ _ rfl <;> rfl
  exact h0.trans (h1.trans h2)
/-- Complete actual one-pass zipper, including the literal final reversal. -/
theorem ready (ports:List Port) (ids:List (List Bool)) (hlen:ports.length=ids.length)
    (base:S.Stack→List Bool) :
    ∃ time ≤ 102*((portTape ports []).length+(vectorBits ids).length)+6,
      Runs program time (.local .parse) (clean base (portTape ports []) (vectorBits ids) (fun _=>[]) [])
        (.local .halt) (finalData base (output ports ids [])) := by
  have h0:=scan_run ports ids hlen base []
  rw [List.append_nil] at h0
  have h1:=eof_run base (output ports ids []).reverse
  have h2:=SemiprimeD1StackPortScopePrimitives.reverse_call true
    (clean base [] [] (fun _=>[]) (output ports ids []).reverse) (.local .finalReverse) (.local .halt) rfl
  change Runs program (2*(output ports ids []).reverse.length+3) _ _ _
    (Function.update (Function.update (clean base [] [] (fun _=>[]) (output ports ids []).reverse)
      (aux .reversed) []) (aux .output) ((output ports ids []).reverse.reverse++[])) at h2
  rw [List.length_reverse,List.reverse_reverse,List.append_nil,clean_raw] at h2
  have h:=h0.trans (h1.trans h2)
  refine ⟨scanTime ports ids+(3+(2*(output ports ids []).length+3)),?_,h⟩
  have hs:=scanTime_le ports ids hlen
  have ho:=output_length_le ports ids hlen
  omega
end RiemannGaussian.SemiprimeD1StackPortScopeTransduction
