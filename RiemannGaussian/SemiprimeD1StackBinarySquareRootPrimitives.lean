/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootEncoding
/-! # Real included copy, adder, multiplier, comparison and metadata traces -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootPrimitives
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact actual fragment concatenation preserves all real outer return frames. -/
theorem join {m n : ℕ} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after := runs_trans program m n pc mid next before between after h g
/-- Actual preserving copy, including restoration of its borrowed metadata scratch. -/
theorem copy_call (site : Copy) (pc next : Label)
    (hc : program pc=.call (copyLabel site 0) next)
    (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before (copyStack site 0)=xs) (hy : before (copyStack site 1)=ys)
    (hs : before (copyStack site 2)=[]) :
    Runs program (5*xs.length+4) pc before next (Function.update before (copyStack site 1) (xs++ys)) := by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi : Link.DataRel (copyStack site) before start.store before := by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack site) (copy_injective site) before start.store before hi (1:Fin 3) (xs++ys)
  have he : Function.update start.store 1 (xs++ys)=stop.store := by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _ => rfl) pc next hc (5*xs.length+3)
    start stop before _ rfl rfl (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Actual candidate-adder clock, including its real caller return. -/
def addTime (r p : List Bool) : ℕ :=
  3*(max r.length p.length+1)+2*(E.trial r p).length+3
/-- Whole actual adder source consumes only its copied operands. -/
theorem add_call (m : M.Stack→List Bool) (x : X.Stack→List Bool) (w : W.Stack→List Bool)
    (u : Aux→List Bool) (r p : List Bool) :
    Runs program (addTime r p) (ctl .add) (bank m (A.store r p [] []) x w u)
      (ctl .trialInputCopy) (bank m (A.store [] [] [] (E.trial r p)) x w u) := by
  let source:=SemiprimeD1StackAdder.state (some (.start false)) none r p [] []
  let stop:=SemiprimeD1StackAdder.state none none [] [] [] (E.trial r p)
  let before:=bank m (A.store r p [] []) x w u
  let after:=bank m (A.store [] [] [] (E.trial r p)) x w u
  have hi : Link.DataRel adder before source.store before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel adder before stop.store after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
      · rfl
  exact included_call program adder adderLabel adder_injective A.code (.start false) (fun _ => rfl)
    (ctl .add) (ctl .trialInputCopy) rfl _ source stop before after rfl rfl
    (SemiprimeD1StackAdderExecution.source_run r p false) hi ho
/-- Actual multiplier clock, including all internal arithmetic and its real return. -/
def multiplyTime (a b : List Bool) : ℕ :=
  2*a.length+1+SemiprimeD1StackMultiplierExecution.loopClock b a.reverse []+1
/-- Whole nine-word actual multiplication, not a supplied square/result oracle. -/
theorem multiply_call (m : M.Stack→List Bool) (a : A.Stack→List Bool) (w : W.Stack→List Bool)
    (u : Aux→List Bool) (r p : List Bool) :
    Runs program (multiplyTime (E.trial r p) (E.trial r p)) (ctl .square)
      (bank m a (X.payload (E.trial r p) (E.trial r p) [] [] [] [] [] [] []) w u)
      (ctl .discriminantCopy) (bank m a (X.payload [] [] [] [] (E.square r p) [] [] [] []) w u) := by
  let t:=E.trial r p
  let source:=SemiprimeD1StackMultiplier.state (some (.control .start)) none none t t [] [] [] [] [] [] []
  let stop:=SemiprimeD1StackMultiplier.state none none none [] [] [] [] (E.square r p) [] [] [] []
  let before:=bank m a source.data w u
  let after:=bank m a stop.data w u
  have hi : Link.DataRel multiply before source.data before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel multiply before stop.data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program multiply multiplyLabel multiply_injective
    X.code (.control .start) (fun _ => rfl) (ctl .square) (ctl .discriminantCopy) rfl _
    source stop before after rfl rfl rfl rfl (SemiprimeD1StackMultiplierExecution.source_run t t) hi ho
/-- Real comparison clock includes subtractor, borrow read, cleanup and return. -/
def compareTime (d s : List Bool) : ℕ := SemiprimeD1StackWordLessExecution.totalTime d s+1
/-- The actual discriminant and actual square are compared as binary integers. -/
theorem compare_call (m : M.Stack→List Bool) (a : A.Stack→List Bool) (x : X.Stack→List Bool)
    (u : Aux→List Bool) (d s : List Bool) :
    Runs program (compareTime d s) (ctl .compare) (bank m a x (W.store d s [] [] []) u)
      (ctl .decide) (bank m a x (W.store [] [] [] [] [SemiprimeD1StackWordLessExecution.answer d s]) u) := by
  let source:=SemiprimeD1StackWordLess.initial d s
  let stop:=SemiprimeD1StackWordLessExecution.done d s
  let before:=bank m a x source.data u
  let after:=bank m a x stop.data u
  have hi : Link.DataRel compare before source.data before := ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel compare before stop.data after := by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k
      · rfl
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program compare compareLabel compare_injective
    W.program .start (fun _ => rfl) (ctl .compare) (ctl .decide) rfl _ source stop before after
    rfl rfl rfl rfl (SemiprimeD1StackWordLessExecution.source_run d s) hi ho
/-- The entire metadata source runs ONCE from the sole original binary input. -/
theorem metadata_call (bits : List Bool) :
    ∃ t ≤ SemiprimeD1StackPackedRootMetadataExecution.polynomial bits+1,
      Runs program t (ctl .start) (input bits) (ctl .rootCopy) (ready bits).data := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPackedRootMetadataExecution.source_run_bounded bits
  have hi : Link.DataRel metadata (input bits) (SemiprimeD1StackPackedRootMetadata.initial bits).data (input bits) :=
    ⟨fun _ => rfl,fun _ _ => rfl⟩
  have ho : Link.DataRel metadata (input bits) (SemiprimeD1StackPackedRootMetadataEncoding.done bits).data (ready bits).data := by
    constructor
    · intro k
      change retained bits _ k=SemiprimeD1StackPackedRootMetadataEncoding.result bits k
      rw [retained_original]
    · intro k hk
      rcases k with k|k|k|k|k
      · exact False.elim (hk k rfl)
      · rfl
      · rfl
      · rfl
      · cases k <;> rfl
  exact ⟨t+1,by omega,SemiprimeD1StackProcedureCallsTrace.included_call program metadata metadataLabel metadata_injective
    M.program (.local .start) (fun _ => rfl) (ctl .start) (ctl .rootCopy) rfl t
    (SemiprimeD1StackPackedRootMetadata.initial bits) (SemiprimeD1StackPackedRootMetadataEncoding.done bits)
    (input bits) (ready bits).data rfl rfl rfl rfl hr hi ho⟩
end RiemannGaussian.SemiprimeD1StackBinarySquareRootPrimitives
