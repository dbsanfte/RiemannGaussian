/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeParse
import RiemannGaussian.SemiprimeD1StackPortScopeClear
/-! # Exact actual one-record physical scope association -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeScan
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeView
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1PortScopeEncoding (Port portFrame portTape scopeFrame cached portMass)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual per-record transition count from all real component calls and cache pops. -/
def recordTime (w:Port) (id:List Bool) : ℕ := 19*(portMass w+id.length)+173
/-- A present original port has a physical first delimiter, even when ordinal zero is empty. -/
theorem record_head (base:S.Stack→List Bool) (w:Port) (tail ids raw:List Bool) :
    Runs program 1 (.local .parse) (clean base (portFrame w tail) ids (fun _=>[]) raw)
      (.local (.field 0)) (clean base (portFrame w tail) ids (fun _=>[]) raw) := by
  apply one_base program _ _ (.peek (aux .readerPorts) (.local .bankEnd)
    (.local (.field 0)) (.local (.field 0))) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (Label.local .bankEnd) (.local (.field 0))
      (.local (.field 0)) (portFrame w tail).head?)=some (.local (.field 0))
    cases hw:w 0 with
    | nil => simp [SemiprimeD1StackBytecode.choose,portFrame,frame,hw]
    | cons bit word => simp [SemiprimeD1StackBytecode.choose,portFrame,frame,hw]
  · rfl
/-- The eight cached original fields have exactly their actual source mass. -/
theorem portMass_cached (w:Port) (id:List Bool) :
    SemiprimeD1StackPortScopeParse.portMass (cached w id)=portMass w := rfl
/-- All nine physically consumed cached fields have original mass plus actual ID width. -/
theorem wordMass_cached (w:Port) (id:List Bool) :
    SemiprimeD1StackPortScopeEmit.wordMass (cached w id)=portMass w+id.length := by
  change id.length+(w 0).length+(w 1).length+(w 2).length+(w 3).length+
    (w 4).length+(w 5).length+(w 6).length+(w 7).length=portMass w+id.length
  unfold portMass
  omega
/-- One actual original record consumes ONE physically next ID and emits their exact nine-field association. -/
theorem record_run (base:S.Stack→List Bool) (w:Port) (id:List Bool) (tail rest raw:List Bool) :
    Runs program (recordTime w id) (.local .parse)
      (clean base (portFrame w tail) (true::frame id rest) (fun _=>[]) raw) (.local .parse)
      (clean base tail rest (fun _=>[]) ((scopeFrame w id []).reverse++raw)) := by
  have h0:=record_head base w tail (true::frame id rest) raw
  have h1:=SemiprimeD1StackPortScopeParse.ports_run base (cached w id) tail (true::frame id rest) raw
  have h2:=SemiprimeD1StackPortScopeParse.id_run base (cached w id) tail rest raw
  have h3:=SemiprimeD1StackPortScopeEmit.record_run base tail rest (cached w id) raw
  have h4:=SemiprimeD1StackPortScopeClear.caches_run base tail rest (cached w id) ((scopeFrame w id []).reverse++raw)
  have hh:SemiprimeD1StackPortScopeParse.suffix (cached w id) 0 tail=portFrame w tail:=rfl
  rw [hh,portMass_cached] at h1
  rw [SemiprimeD1StackPortScopeEmit.record_cached,wordMass_cached] at h3
  rw [wordMass_cached] at h4
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  change Runs program (1+((8*portMass w+64)+((8*id.length+9)+
    ((10*(portMass w+id.length)+90)+(portMass w+id.length+9))))) _ _ _ _ at h
  unfold recordTime
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackPortScopeScan
