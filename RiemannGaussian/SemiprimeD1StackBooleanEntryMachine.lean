/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanEntryOriginal
/-! # Actual finite-machine time and all-prefix cells for Boolean root cases
The tiny ordered assignment is the ONLY data input. Mode is one of three fixed
finite entry points, not a supplied result or evaluator.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackBooleanEntryMachine
open SemiprimeD1StackBooleanEntry SemiprimeD1StackBooleanEntryExecution
open SemiprimeD1StackBooleanEntryOriginal

/-- Original literal arities, used in the specification only. -/
abbrev arity : Mode→ℕ | .orGate => 3 | .inputCheck => 1 | .equality => 2
/-- Original Boolean semantics, not a machine argument or opcode. -/
def value : (mode : Mode)→(Fin (arity mode)→Bool)→Bool
  | .orGate,input => decide (input 2=(input 0 || input 1))
  | .inputCheck,input => input 0
  | .equality,input => decide (input 0=input 1)
/-- Exact executed time INCLUDING Copy, reads, result push and halt. -/
def time : Mode→ℕ | .orGate => 25 | .inputCheck => 13 | .equality => 19

/-- One closed trace covering ALL fourteen original local assignments. -/
theorem source_run (mode : Mode) (input : Fin (arity mode)→Bool) :
    C.run program (time mode) (initial mode (List.ofFn input))=
      some (done (List.ofFn input) (value mode input)) := by
  cases mode with
  | orGate => simpa only [time,arity,value,ofFn_three] using or_run (input 0) (input 1) (input 2)
  | inputCheck => simpa only [time,arity,value,ofFn_one] using input_run (input 0)
  | equality => simpa only [time,arity,value,ofFn_two] using equality_run (input 0) (input 1)

/-- Real prepared raw-word initialization, all workspace empty. -/
theorem initial_eq (mode : Mode) (bits : List Bool) :
    Turing.initList (machine mode) bits=SemiprimeD1StackCalls.configuration (initial mode bits) := by
  have hs : initial mode bits=SemiprimeD1StackCalls.initial .assignment (.inl (.start mode)) bits := by
    unfold initial SemiprimeD1StackCalls.initial
    congr 1
    funext k
    cases k <;> simp [data]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct .assignment .output (.inl (.start mode)) program bits).symm

/-- Genuine fixed finite-alphabet execution, rather than a report-to-time premise. -/
def entryInTime (mode : Mode) (input : Fin (arity mode)→Bool) :
    StateTransition.EvalsToInTime (machine mode).step (Turing.initList (machine mode) (List.ofFn input))
      (some (SemiprimeD1StackCalls.configuration (done (List.ofFn input) (value mode input)))) (time mode) := by
  have cert : StateTransition.EvalsToInTime (machine mode).step
      (SemiprimeD1StackCalls.configuration (initial mode (List.ofFn input)))
      (some (SemiprimeD1StackCalls.configuration (done (List.ofFn input) (value mode input)))) (time mode) :=
    SemiprimeD1StackCalls.evalsCorrect .assignment .output (.inl (.start mode)) program _ _ _
      ⟨⟨time mode,source_run mode input⟩,Nat.le_refl _⟩
  exact (initial_eq mode (List.ofFn input)).symm ▸ cert

/-- The literal three entries have a constant bound, before all input assignments. -/
theorem time_le (mode : Mode) : time mode≤25 := by cases mode <;> decide
/-- Each literal original local assignment has at most three bits. -/
theorem arity_le (mode : Mode) : arity mode≤3 := by cases mode <;> decide

/-- A successful actually executed prefix cannot pass this program's own halt. -/
theorem prefix_fuel_le (mode : Mode) (input : Fin (arity mode)→Bool) (fuel : ℕ)
    (out : C.State Stack Label)
    (hr : C.run program fuel (initial mode (List.ofFn input))=some out) : fuel≤time mode := by
  have he:=source_run mode input
  by_contra hn
  have h : fuel=time mode+(1+(fuel-(time mode+1))) := by omega
  rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done (List.ofFn input) (value mode input))=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr

/-- ALL four Boolean stacks plus actual return frames at EVERY executed prefix. -/
theorem prefix_cells (mode : Mode) (input : Fin (arity mode)→Bool) (fuel : ℕ)
    (out : C.State Stack Label)
    (hr : C.run program fuel (initial mode (List.ofFn input))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤200 := by
  have hi : ∀k:Stack,((initial mode (List.ofFn input)).data k).length≤arity mode := by
    intro k
    cases k <;> simp [initial,data]
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (arity mode) _ out hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length)≤4*(arity mode+fuel) := by
    calc
      _≤∑_k:Stack,(arity mode+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by
        have hcard : Fintype.card Stack=4 := by decide
        simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hcard]
  have ht:=(prefix_fuel_le mode input fuel out hr).trans (time_le mode)
  have ha:=arity_le mode
  omega

/-- Same bound for the ACTUAL compiled-machine prefixes and encoded returns. -/
theorem machine_prefix_cells (mode : Mode) (input : Fin (arity mode)→Bool) (fuel : ℕ)
    (cfg : (machine mode).Cfg)
    (hr : (fun q=>q.bind (machine mode).step)^[fuel]
      (some (Turing.initList (machine mode) (List.ofFn input)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤200 := by
  have he:=SemiprimeD1StackCalls.run_correct .assignment .output (.inl (.start mode)) program fuel
    (initial mode (List.ofFn input))
  change (C.run program fuel (initial mode (List.ofFn input))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind (machine mode).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial mode (List.ofFn input)))) at he
  have hh : (C.run program fuel (initial mode (List.ofFn input))).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start:(machine mode).Cfg=>
      (fun q:Option (machine mode).Cfg=>q.bind (machine mode).step)^[fuel] (some start))
        (initial_eq mode (List.ofFn input)).symm).trans hr)
  cases hrun:C.run program fuel (initial mode (List.ofFn input)) with
  | none => rw [hrun] at hh; cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells mode input fuel out hrun

end RiemannGaussian.SemiprimeD1StackBooleanEntryMachine
