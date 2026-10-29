/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceLoopView
/-! # Actual caller-query save/drain and one paid outer occurrence-stream copy -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSetup
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackProcedureTrace
/-- Actual save/drain/copy source clock, with both copies' restoration loops and real returns. -/
def setupTime (i:Inputs) :Nat :=6*i.query.length+5*(tape i).length+9
/-- Exact complete program prefix preserves the caller's arbitrary original query by paid physical saving. -/
theorem setup_run (i:Inputs) :
    Runs program (setupTime i) .start (source i).data .outerHeader
      (bank i (tape i) [] [] [] [] [] [] [] [] [] []) :=by
  have h0:=copy_call .saveQuery .start .clearOriginalQuery rfl (source i).data rfl rfl
  change Runs program (5*i.query.length+4) _ _ _
    (Function.update (source i).data (aux .savedQuery) i.query) at h0
  have h1:=drain_loop .clearOriginalQuery .copyOuter query rfl
    (Function.update (source i).data (aux .savedQuery) i.query) i.query rfl
  have he:Function.update (Function.update (source i).data (aux .savedQuery) i.query) query []=
      bank i [] [] [] [] [] [] [] [] [] [] []:=by
    funext k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h1
  have h2:=copy_call .outer .copyOuter .outerHeader rfl (bank i [] [] [] [] [] [] [] [] [] [] []) rfl rfl
  change Runs program (5*(tape i).length+4) _ _ _
    (Function.update (bank i [] [] [] [] [] [] [] [] [] [] []) (aux .outerReader) (tape i)) at h2
  rw [update_outer] at h2
  have h:=join (join h0 h1) h2
  have ht:(5*i.query.length+4)+(i.query.length+1)+(5*(tape i).length+4)=setupTime i:=by unfold setupTime;omega
  simpa only [ht] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSetup
