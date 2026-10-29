/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleState
/-! # Executed original root acquisition, selector and width-counted padding -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleAcquire
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState SemiprimeD1StackPublicScalePrimitives
open SemiprimeD1StackProcedureTrace
/-- Selected acquired code source; only a proof view of literal retained stacks. -/
def sourceCode (root : R.Stack→List Bool) (inverse : Bool) : List Bool :=
  root (.inr (if inverse then .root else .forwardRoot))
/-- All real preparation copies, selector, padding iterations and literal pushes. -/
def prepBudget (root : R.Stack→List Bool) (raw : List Bool) (inverse : Bool) : ℕ :=
  1+(5*(sourceCode root inverse).length+4)+(5*(root (.inl R.modulusKey)).length+4)+
    (5*raw.length+4)+(5*(root (.inl R.modulusKey)).length+4)+
    (2*(root (.inl R.modulusKey)).length+1)+2
/-- Literal selector pop selects only the physically read singleton Boolean. -/
theorem select_run (root : R.Stack→List Bool) (raw stride frequency : List Bool) (inverse : Bool) :
    Runs program 1 .select (stage root raw stride frequency [inverse] [] [] [] [] [])
      (if inverse then .chooseInverse else .chooseForward) (stage root raw stride frequency [] [] [] [] [] []) := by
  have h:=pop .select .bad .chooseForward .chooseInverse (auxRole .selector) rfl
    (stage root raw stride frequency [inverse] [] [] [] [] [])
  have he : (stage root raw stride frequency [inverse] [] [] [] [] [] (auxRole .selector))=[inverse] := rfl
  rw [he,stage_selector] at h
  cases inverse <;> exact h
/-- A real source-code copy is selected by the actual selector, not supplied code. -/
theorem source_copy (root : R.Stack→List Bool) (raw stride frequency : List Bool) (inverse : Bool) :
    Runs program (5*(sourceCode root inverse).length+4)
      (if inverse then .chooseInverse else .chooseForward) (stage root raw stride frequency [] [] [] [] [] [])
      .copyModulus (stage root raw stride frequency [] (sourceCode root inverse) [] [] [] []) := by
  cases inverse
  · have h:=copy_call 2 .chooseForward .copyModulus rfl (stage root raw stride frequency [] [] [] [] [] []) rfl rfl
    change Runs program (5*(sourceCode root false).length+4) .chooseForward _ .copyModulus
      (Function.update (stage root raw stride frequency [] [] [] [] [] []) (dotStack baseRole) (sourceCode root false)) at h
    rw [stage_base] at h;exact h
  · have h:=copy_call 3 .chooseInverse .copyModulus rfl (stage root raw stride frequency [] [] [] [] [] []) rfl rfl
    change Runs program (5*(sourceCode root true).length+4) .chooseInverse _ .copyModulus
      (Function.update (stage root raw stride frequency [] [] [] [] [] []) (dotStack baseRole) (sourceCode root true)) at h
    rw [stage_base] at h;exact h
/-- A real copy supplies the dot's actual modulus cache; the original remains. -/
theorem modulus_copy (root : R.Stack→List Bool) (raw stride frequency base : List Bool) :
    Runs program (5*(root (.inl R.modulusKey)).length+4) .copyModulus
      (stage root raw stride frequency [] base [] [] [] []) .copyRaw
      (stage root raw stride frequency [] base (root (.inl R.modulusKey)) [] [] []) := by
  have h:=copy_call 4 .copyModulus .copyRaw rfl (stage root raw stride frequency [] base [] [] [] []) rfl rfl
  change Runs program (5*(root (.inl R.modulusKey)).length+4) .copyModulus _ .copyRaw
    (Function.update (stage root raw stride frequency [] base [] [] [] [])
      (dotStack (.inl SemiprimeD1StackInputDotEvaluate.modulusRole)) (root (.inl R.modulusKey))) at h
  rw [stage_modulus] at h;exact h
/-- Original raw assignment is physically copied and separately retained. -/
theorem raw_copy (root : R.Stack→List Bool) (raw stride frequency base cached : List Bool) :
    Runs program (5*raw.length+4) .copyRaw (stage root raw stride frequency [] base cached [] [] [])
      .copyWidth (stage root raw stride frequency [] base cached raw [] []) := by
  have h:=copy_call 0 .copyRaw .copyWidth rfl (stage root raw stride frequency [] base cached [] [] []) rfl rfl
  change Runs program (5*raw.length+4) .copyRaw _ .copyWidth
    (Function.update (stage root raw stride frequency [] base cached [] [] []) (dotStack I.rawRole) raw) at h
  rw [stage_raw] at h;exact h
/-- Actual modulus WORD cells are copied for the physical padding loop. -/
theorem width_copy (root : R.Stack→List Bool) (raw stride frequency base cached : List Bool) :
    Runs program (5*(root (.inl R.modulusKey)).length+4) .copyWidth
      (stage root raw stride frequency [] base cached raw [] []) .zeroPop
      (stage root raw stride frequency [] base cached raw (root (.inl R.modulusKey)) []) := by
  have h:=copy_call 1 .copyWidth .zeroPop rfl (stage root raw stride frequency [] base cached raw [] []) rfl rfl
  change Runs program (5*(root (.inl R.modulusKey)).length+4) .copyWidth _ .zeroPop
    (Function.update (stage root raw stride frequency [] base cached raw [] []) (auxRole .padding) (root (.inl R.modulusKey))) at h
  rw [stage_padding] at h;exact h
/-- Actual loop padding viewed on complete physical stages. -/
theorem pad_stage (root : R.Stack→List Bool) (raw stride frequency base cached count : List Bool) :
    Runs program (2*count.length+1) .zeroPop (stage root raw stride frequency [] base cached raw count [])
      (.seed 0) (stage root raw stride frequency [] base cached (List.replicate count.length false++raw) [] []) := by
  have h:=zero_padding (stage root raw stride frequency [] base cached [] [] []) count raw
  simpa only [padData,stage_padding,stage_raw] using h
/-- Two actual literal pushes drive the acquired dot's own two-word producer. -/
theorem seed_run (root : R.Stack→List Bool) (raw stride frequency base cached work : List Bool) :
    Runs program 2 (.seed 0) (stage root raw stride frequency [] base cached work [] []) .compute
      (stage root raw stride frequency [] base cached work [] [true,true]) := by
  have h0:=push (.seed 0) (.seed 1) (dotStack countRole) true rfl (stage root raw stride frequency [] base cached work [] [])
  have h1:=push (.seed 1) .compute (dotStack countRole) true rfl (stage root raw stride frequency [] base cached work [] [true])
  have he0 : stage root raw stride frequency [] base cached work [] [] (dotStack countRole)=[] := rfl
  have he1 : stage root raw stride frequency [] base cached work [] [true] (dotStack countRole)=[true] := rfl
  rw [he0,stage_count] at h0
  rw [he1,stage_count] at h1
  exact runs_trans program _ _ _ _ _ _ _ _ h0 h1
/-- Whole actual selection/copies/width-counted padding/literal2 preparation.
The root cache is a proof-side view here; the closed caller acquires it itself. -/
theorem prep_run (root : R.Stack→List Bool) (raw stride frequency : List Bool) (inverse : Bool) :
    Runs program (prepBudget root raw inverse) .select
      (stage root raw stride frequency [inverse] [] [] [] [] []) .compute
      (stage root raw stride frequency [] (sourceCode root inverse) (root (.inl R.modulusKey))
        (List.replicate (root (.inl R.modulusKey)).length false++raw) [] [true,true]) := by
  have h0:=select_run root raw stride frequency inverse
  have h1:=source_copy root raw stride frequency inverse
  have h2:=modulus_copy root raw stride frequency (sourceCode root inverse)
  have h3:=raw_copy root raw stride frequency (sourceCode root inverse) (root (.inl R.modulusKey))
  have h4:=width_copy root raw stride frequency (sourceCode root inverse) (root (.inl R.modulusKey))
  have h5:=pad_stage root raw stride frequency (sourceCode root inverse) (root (.inl R.modulusKey)) (root (.inl R.modulusKey))
  have h6:=seed_run root raw stride frequency (sourceCode root inverse) (root (.inl R.modulusKey))
    (List.replicate (root (.inl R.modulusKey)).length false++raw)
  exact runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6
/-- Original root-source acquisition executes ONCE from actual binary N; all
raw/descriptor fields remain physically retained during that acquisition. -/
theorem roots_call (bits raw stride frequency : List Bool) (inverse : Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackRootSourceBounds.timeBound bits+1,
      Runs program t .start (initial bits raw stride frequency inverse).data .select
        (acquired bits raw stride frequency inverse) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootSourceBounds.source_run_bounded bits hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.roots Sum.inl_injective
    R.program .start (fun _=>rfl) .start .select rfl t (R.initial bits)
    (SemiprimeD1StackRootSourceExecution.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Entire real original-input preparation reaches exactly the whole-dot initial
state with actual source, actual M, actual padded raw and literal2 count. -/
theorem acquire_run (bits raw stride frequency : List Bool) (inverse : Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackRootSourceBounds.timeBound bits+1+prepBudget (roots bits) raw inverse,
      Runs program t .start (initial bits raw stride frequency inverse).data .compute
        (prepared bits raw stride frequency inverse) := by
  obtain ⟨t,ht,h0⟩:=roots_call bits raw stride frequency inverse hb
  have h1:=prep_run (roots bits) raw stride frequency inverse
  exact ⟨t+prepBudget (roots bits) raw inverse,Nat.add_le_add_right ht _,
    runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
end RiemannGaussian.SemiprimeD1StackPublicScaleAcquire
