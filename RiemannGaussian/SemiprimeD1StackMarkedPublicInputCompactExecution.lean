/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompact
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual66 source followed by paid reverse and high-zero trimming -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompactExecution
open SemiprimeD1StackMarkedPublicInputCompact SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- The entire immutable66-role marked source executes as a real call. -/
theorem marked_call (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    ∃ t ≤ SemiprimeD1StackMarkedPublicInputCost.polynomial bits raw indexWord+1,
      Runs program t (ctl .start) (initial bits raw indexWord side).data (ctl .reverse)
        (SemiprimeD1StackMarkedPublicInputEncoding.result bits raw indexWord side) := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackMarkedPublicInputBounds.source_run_bounded bits raw indexWord side hb
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program id sourceLabel Function.injective_id
    M.program (SemiprimeD1StackMarkedPublicInput.ctl .start) (fun _ => rfl) (ctl .start) (ctl .reverse) rfl
    t (M.initial bits raw indexWord [side]) (SemiprimeD1StackMarkedPublicInputEncoding.done bits raw indexWord side)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;exact False.elim (hk k rfl)
/-- The actual reverse consumes the padded coefficient and materializes every
bit in the borrowed physical shadow; no decoded or reencoded word is supplied. -/
theorem reverse_call (before : Stack → List Bool) (xs : List Bool)
    (ho : before (M.aux .output)=xs) (hs : before (M.word 1)=[]) :
    Runs program (2*xs.length+3) (ctl .reverse) before (ctl .trim)
      (Function.update (Function.update before (M.aux .output) []) (M.word 1) xs.reverse) := by
  let start := SemiprimeD1StackReverseWord.state none xs []
  let stop := SemiprimeD1StackReverseWord.done xs.reverse
  have hi : Link.DataRel reverseStack before start.store before := by
    constructor
    · intro k;fin_cases k
      · exact ho
      · exact hs
    · intro k _;rfl
  have h0 := Link.data_update reverseStack reverse_injective before start.store before hi (0:Fin 2) []
  have h1 := Link.data_update reverseStack reverse_injective before _ _ h0 (1:Fin 2) xs.reverse
  have he : Function.update (Function.update start.store 0 []) 1 xs.reverse=stop.store := by
    funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program reverseStack reverseLabel reverse_injective
    SemiprimeD1StackReverseWord.code 0 (fun _ => rfl) (ctl .reverse) (ctl .trim) rfl
    (2*xs.length+2) start stop before _ rfl rfl
    (by simpa only [List.append_nil] using SemiprimeD1StackReverseWord.reverse_run xs [] none) hi h1
/-- Real trim restores every borrowed work/shadow field to empty, changes
only the coefficient output, and preserves the complete stopped checker bank. -/
theorem trim_call (before : Stack → List Bool) (xs : List Bool)
    (h0 : before (M.word 0)=[]) (h1 : before (M.word 1)=[]) (h3 : before (M.word 3)=[]) :
    Runs program (SemiprimeD1StackReduceExecution.trimTime xs.reverse+1) (ctl .trim)
      (Function.update (Function.update before (M.aux .output) []) (M.word 1) xs.reverse)
      (ctl .done) (Function.update before (M.aux .output)
        (SemiprimeD1StackReduceExecution.trimReverse xs.reverse)) := by
  let start := SemiprimeD1StackReduce.state (some .trim) none [] [] xs.reverse []
  let stop := SemiprimeD1StackReduce.state none none [] [] []
    (SemiprimeD1StackReduceExecution.trimReverse xs.reverse)
  let ready := Function.update (Function.update before (M.aux .output) []) (M.word 1) xs.reverse
  have hi : Link.DataRel trimStack ready start.store ready := by
    constructor
    · intro k;cases k
      · change ready (M.word 0)=[]
        simpa only [ready,Function.update_of_ne (by decide : M.word 0≠M.word 1),
          Function.update_of_ne (by decide : M.word 0≠M.aux .output)] using h0
      · change ready (M.word 3)=[]
        simpa only [ready,Function.update_of_ne (by decide : M.word 3≠M.word 1),
          Function.update_of_ne (by decide : M.word 3≠M.aux .output)] using h3
      · change ready (M.word 1)=xs.reverse
        exact Function.update_self _ _ _
      · change ready (M.aux .output)=[]
        rw [show ready=Function.update (Function.update before (M.aux .output) []) (M.word 1) xs.reverse from rfl,
          Function.update_of_ne (by decide : M.aux .output≠M.word 1),Function.update_self]
    · intro k _;rfl
  have hout : Link.DataRel trimStack ready stop.store
      (Function.update before (M.aux .output) (SemiprimeD1StackReduceExecution.trimReverse xs.reverse)) := by
    constructor
    · intro k;cases k
      · change Function.update before (M.aux .output) _ (M.word 0)=[]
        simpa only [Function.update_of_ne (by decide : M.word 0≠M.aux .output)] using h0
      · change Function.update before (M.aux .output) _ (M.word 3)=[]
        simpa only [Function.update_of_ne (by decide : M.word 3≠M.aux .output)] using h3
      · change Function.update before (M.aux .output) _ (M.word 1)=[]
        simpa only [Function.update_of_ne (by decide : M.word 1≠M.aux .output)] using h1
      · exact Function.update_self _ _ _
    · intro k hk
      have ho : k≠M.aux .output := by intro he;exact hk .output he.symm
      have hs : k≠M.word 1 := by intro he;exact hk .scratch he.symm
      simp only [ready,Function.update_of_ne ho,Function.update_of_ne hs]
  exact included_call program trimStack trimLabel trim_injective
    SemiprimeD1StackReduce.code .trim (fun _ => rfl) (ctl .trim) (ctl .done) rfl
    (SemiprimeD1StackReduceExecution.trimTime xs.reverse) start stop _ _ rfl rfl
    (by simpa only [List.append_nil] using SemiprimeD1StackReduceExecution.trim_run xs.reverse [] none)
    hi hout
/-- Complete own source cap includes all three actual calls and final halt. -/
def runBound (bits raw indexWord : List Bool) (side : Bool) : Nat :=
  SemiprimeD1StackMarkedPublicInputCost.polynomial bits raw indexWord+1+
  (2*(SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side).length+3)+
  (SemiprimeD1StackReduceExecution.trimTime
    (SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side).reverse+1)+1
/-- Complete actual source; the borrowed shadow is physically restored empty. -/
theorem source_run (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    ∃ t ≤ runBound bits raw indexWord side,
      C.run program t (initial bits raw indexWord side)=some (done bits raw indexWord side) := by
  obtain ⟨a,ha,h0⟩ := marked_call bits raw indexWord side hb
  let before := SemiprimeD1StackMarkedPublicInputEncoding.result bits raw indexWord side
  let xs := SemiprimeD1StackMarkedPublicInputEncoding.coefficient bits raw indexWord side
  have h1 := reverse_call before xs rfl rfl
  have h2 := trim_call before xs rfl rfl rfl
  have hh := runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨stop,hr,hs⟩ := hh [] (initial bits raw indexWord side) ⟨rfl,rfl,rfl⟩
  have hf := halt_run program (ctl .done) rfl (result bits raw indexWord side) [] stop hs
  refine ⟨a+(2*xs.length+3)+(SemiprimeD1StackReduceExecution.trimTime xs.reverse+1)+1,?_,?_⟩
  · exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right ha _) _) 1
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    exact hf
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompactExecution

