/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureFragments
import RiemannGaussian.SemiprimeD1PortOwnerEndpointEncoding
/-! # Physical equality-endpoint key from the acquired original edge record
This internal stage physically prepends the sentinel to its output and calls
preserving Copy on the actual six-field record. It has no endpoint/key answer.
The original-N outer routing loop remains a separate integration obligation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackOwnerEqualityKey
namespace C
export SemiprimeD1StackCalls (Instruction State run step execute)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction)
end Link
open SemiprimeD1StackProcedureFragments (Runs included_call one_base)
/-- Input, destination and physical scratch are three fixed Boolean roles. -/
abbrev Stack := Fin 3
/-- Static local control plus the actual immutable Copy procedure. -/
abbrev Label := Fin 3 ⊕ Fin 9
/-- Literal sentinel push, real Copy call, final halt. -/
def program : Label→C.Instruction Stack Label
  | .inr pc => Link.instruction id Sum.inr (SemiprimeD1StackCopy.code pc)
  | .inl pc => if pc=0 then .base (.push 1 true (.inl 1))
      else if pc=1 then .call (.inr 0) (.inl 2) else .base .halt
/-- Actual acquired record and fresh work; not a source descriptor constructor. -/
def initial (record:List Bool) : C.State Stack Label :=
  ⟨some (.inl 0),none,none,SemiprimeD1StackCopy.payload record [] [],[]⟩
/-- Original record retained and exact new compact-key bytes returned. -/
def done (record:List Bool) : C.State Stack Label :=
  ⟨none,none,none,SemiprimeD1StackCopy.payload record (record++[true]) [],[]⟩
/-- The sentinel cell is actually pushed, not preloaded as an advised key. -/
theorem sentinel (record:List Bool) : Runs program 1 (.inl 0)
    (SemiprimeD1StackCopy.payload record [] []) (.inl 1)
    (SemiprimeD1StackCopy.payload record [true] []) := by
  apply one_base program (.inl 0) (.inl 1) (.push 1 true (.inl 1)) _ _ rfl rfl
  funext k;fin_cases k <;> rfl
/-- Real nested preserving Copy and all three original/scratch data roles. -/
theorem copy_call (record:List Bool) : Runs program (5*record.length+4) (.inl 1)
    (SemiprimeD1StackCopy.payload record [true] []) (.inl 2)
    (SemiprimeD1StackCopy.payload record (record++[true]) []) := by
  apply included_call program id Sum.inr Function.injective_id SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.inl 1) (.inl 2) rfl (5*record.length+3)
    (SemiprimeD1StackCopy.state 0 none record [true] [])
    (SemiprimeD1StackCopy.done record (record++[true]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words record [true] none
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · exact ⟨fun _=>rfl,fun k hk=>False.elim (hk k rfl)⟩
/-- Actual complete fixed-program trace, preserving the original acquired record. -/
theorem source_run (record:List Bool) :
    C.run program (5*record.length+6) (initial record)=some (done record) := by
  have h:Runs program (1+(5*record.length+4)) (.inl 0)
      (SemiprimeD1StackCopy.payload record [] []) (.inl 2)
      (SemiprimeD1StackCopy.payload record (record++[true]) []) :=
    (sentinel record).trans (copy_call record)
  obtain ⟨finish,hr,hout⟩:=h [] (initial record) ⟨rfl,rfl,rfl⟩
  have he:5*record.length+6=(1+(5*record.length+4))+1:=by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done record)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,
    SemiprimeD1StackCalls.execute,hdata,hframes,done]
/-- A single fixed finite machine, with all three alphabets Boolean. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine 0 1 (.inl 0) program
/-- Every stack alphabet is finite, including scratch and output. -/
theorem all_alphabets_finite : ∀ k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite 0 1 (.inl 0) program
/-- Framing appends a literal tail; this proof does not execute a key decoder. -/
theorem frame_append (xs ys zs:List Bool) :
    SemiprimeSourceHistogramKeyBits.frame xs ys++zs=
      SemiprimeSourceHistogramKeyBits.frame xs (ys++zs) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [SemiprimeSourceHistogramKeyBits.frame,List.cons_append,ih]
/-- The physical sentinel-copy output on an actual original edge is exactly
its original equality-endpoint key. -/
theorem original_key {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (e:SemiprimeMacroGraph.Edge r t digits) :
    (done (SemiprimeD1EdgeCatalogueEncoding.edge e [])).data 1=
      SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e true) := by
  rw [SemiprimeD1PortOwnerEndpointEncoding.equality_key]
  change SemiprimeD1EdgeCatalogueEncoding.edge e []++[true]=_
  simp only [SemiprimeD1EdgeCatalogueEncoding.edge,SemiprimeD1EdgeCatalogueEncoding.half,
    SemiprimeD1EdgeCatalogueEncoding.record,frame_append,List.nil_append]
end RiemannGaussian.SemiprimeD1StackOwnerEqualityKey
