/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAssignmentEnumeration

/-! # Canonical finite-machine assignment output and all-prefix storage
The output is the actual framed assignment vector, with every auxiliary and
return stack empty. Time counts real included instructions/calls, not reports.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackAssignmentEnumerationBounds
open SemiprimeD1StackAssignmentLoop SemiprimeD1StackAssignmentEnumeration
open SemiprimeD1StackAssignmentOrder
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => SemiprimeD1StackAssignmentLoop.control

/-- Canonical one-word input has no prepared auxiliary or return payload. -/
theorem initial_eq (word : List Bool) :
    SemiprimeD1StackCalls.initial Stack.word (ctl .bodyCall) word=
      state (ctl .bodyCall) none none word [] [] [] [] := by
  unfold SemiprimeD1StackCalls.initial state
  congr 1
  funext k
  cases k <;> rfl

/-- Final output is canonical: ALL data/return stacks other than output are empty. -/
theorem final_eq (output : List Bool) :
    SemiprimeD1StackCalls.final Stack.output output=
      (⟨none,none,none,data [] [] [] [] output,[]⟩ : C.State Stack Label) := by
  unfold SemiprimeD1StackCalls.final
  congr 1
  funext k
  cases k <;> rfl

/-- Exact original binary-word input/output execution, with zero acquired on input. -/
theorem zero_source_run (width : ℕ) :
    ∃m≤100*(width+1)*2^width+10,C.run code m
      (SemiprimeD1StackCalls.initial Stack.word (ctl .bodyCall) (List.replicate width false))=
      some (SemiprimeD1StackCalls.final Stack.output
        (vectorBits (assignments (2^width) (List.replicate width false)))) := by
  rw [initial_eq,final_eq]
  exact zero_run width

/-- Genuine full canonical TM2 input/output certificate for the fixed program.
The noncomputability concerns proof-only path-length selection, never code/data. -/
noncomputable def outputsInTime (width : ℕ) :
    Turing.TM2OutputsInTime machine (List.replicate width false)
      (some (vectorBits (assignments (2^width) (List.replicate width false))))
      (100*(width+1)*2^width+10) := by
  have hx := zero_source_run width
  let m := Classical.choose hx
  have hm := Classical.choose_spec hx
  apply SemiprimeD1StackCalls.outputsOfSource Stack.word Stack.output (ctl .bodyCall) code
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- The physically emitted vector has exactly 2^width raw assignment records. -/
theorem output_count (width : ℕ) :
    (SemiprimeD1TensorTapeCodec.parseVector
      (vectorBits (assignments (2^width) (List.replicate width false)))).words.length=2^width := by
  have h := (SemiprimeD1TensorTapeCodec.parseVector_correct
    (assignments (2^width) (List.replicate width false)) []).1
  simpa only [List.append_nil,assignments_length] using congrArg List.length h

/-- All actual source-prefix data and real return frames are counted. -/
theorem prefix_cells (word : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (h : C.run code fuel (state (ctl .bodyCall) none none word [] [] [] [])=some out) :
    (out.data .word).length+(out.data .scratch).length+(out.data .next).length+
      (out.data .history).length+(out.data .output).length+out.frames.length≤6*(word.length+fuel) := by
  have hd := SemiprimeD1StackReturnLink.run_data_bound code fuel word.length _ out (by
    intro k
    cases k <;> simp [state,data]) h
  have hf := SemiprimeD1StackCalls.run_frame_bound code fuel _ out h
  change out.frames.length≤0+fuel at hf
  have h0 := hd .word
  have h1 := hd .scratch
  have h2 := hd .next
  have h3 := hd .history
  have h4 := hd .output
  omega

/-- Every actually reached target-machine prefix has a fixed-polynomial cell bound.
The sixth stack is the real return stack over the FIXED finite label alphabet. -/
theorem machine_prefix_cells (word : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (h : (fun c => c.bind machine.step)^[fuel]
      (some (Turing.initList machine word))=some cfg) :
    (cfg.stk (some Stack.word)).length+(cfg.stk (some Stack.scratch)).length+
      (cfg.stk (some Stack.next)).length+(cfg.stk (some Stack.history)).length+
      (cfg.stk (some Stack.output)).length+(cfg.stk none).length≤6*(word.length+fuel) := by
  dsimp only [SemiprimeD1StackAssignmentLoop.machine] at cfg h ⊢
  let start := state (ctl .bodyCall) none none word [] [] [] []
  have he := SemiprimeD1StackCalls.run_correct Stack.word Stack.output (ctl .bodyCall) code fuel start
  have hi : SemiprimeD1StackCalls.configuration start=Turing.initList machine word := by
    change SemiprimeD1StackCalls.configuration
      (state (ctl .bodyCall) none none word [] [] [] [])=Turing.initList machine word
    rw [←initial_eq]
    exact SemiprimeD1StackCalls.initial_correct Stack.word Stack.output (ctl .bodyCall) code word
  change (C.run code fuel start).map SemiprimeD1StackCalls.configuration=
    (fun c => c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  rw [hi] at he
  have hefinal := he.trans h
  cases hs : C.run code fuel start with
  | none => rw [hs] at hefinal; cases hefinal
  | some out =>
    rw [hs] at hefinal
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hefinal
    rw [←hcfg]
    exact prefix_cells word fuel out hs

end RiemannGaussian.SemiprimeD1StackAssignmentEnumerationBounds
