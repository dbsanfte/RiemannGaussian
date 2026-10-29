/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldProduct
/-! # Whole actual native-order mode sum of actual ordered child products -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldSum
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldWords
open SemiprimeD1StackJetFoldPrimitives SemiprimeD1StackJetFoldFrames SemiprimeD1StackJetFoldMoves
open SemiprimeD1StackJetFoldOperators SemiprimeD1StackJetFoldSpec SemiprimeD1StackJetFoldProduct
open SemiprimeD1StackProcedureTrace
open SemiprimeD1JetAxes (Context)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
attribute [local irreducible] sumBudget sumEdge addCost productBudget
/-- Each actual mode is physically saved and restored, its complete product executed, then added to the actual tail sum. -/
theorem sum_run (ctx:Context) (hp:ctx.Positive) (h:Header) (hc:Matches ctx h)
    (modes:Modes) (frames:List Bool):
    ∃time ≤ sumBudget ctx h modes,Runs program time (ctl .sumVisit)
      (data (sumNode h modes frames)) (ctl .returning) (data (sumOut h (sumWords ctx modes) frames)):=by
  have hr:h.rank.length=ctx.rank:=by rw [hc.rank];exact List.length_replicate
  induction modes generalizing frames with
  | nil=>
    let v:=sumNode h [] frames
    let a:=bank h [] [] frames [] [] [] [] [] []
    let b:=bank h [] [] frames [] [false] [] [] [] []
    let c:=bank h [] [] frames [] [false] [] [false] [] []
    have h0:=pop_view .sumVisit .abort .zeroLeft .sumRead .modes v [false] rfl rfl
    change Runs program 1 _ _ (ctl .zeroLeft) (data a) at h0
    have h1:=push_view .zeroLeft .zeroRight .product false a rfl
    change Runs program 1 _ _ _ (data b) at h1
    have h2:=push_view .zeroRight .add .tailSum false b rfl
    change Runs program 1 _ _ _ (data c) at h2
    have h3:=add_call ctx c [] [] rfl rfl hc.width hr rfl
    rw [add_empty_zero] at h3
    change Runs program (SemiprimeD1StackJetAddExecution.totalTime h.width h.rank [] []+1) _ _ _
      (data (sumOut h (sumWords ctx []) frames)) at h3
    have hh:=join h0 (join h1 (join h2 h3))
    refine ⟨1+(1+(1+(SemiprimeD1StackJetAddExecution.totalTime h.width h.rank [] []+1))),?_,hh⟩
    rw [sumBudget]
    omega
  | cons x xs ih=>
    let v:=sumNode h (x::xs) frames
    have h0:=enter false v (groupTape x) (modeTape xs) rfl rfl rfl
    change Runs program (15*(groupTape x).length+15) _ _ (ctl .sumChild)
      (data (sumNode h xs (frame (groupTape x) frames))) at h0
    obtain ⟨u,hu,hTail⟩:=ih (frame (groupTape x) frames)
    have h1:=recursive_call .sumChild .sumVisit .sumRestore _ _ u rfl hTail
    let a:=sumOut h (sumWords ctx xs) (frame (groupTape x) frames)
    let b:=bank h [] (groupTape x) frames [] [] [] [] (jetTape (sumWords ctx xs)) []
    let c:=productNode h [] (jetTape (sumWords ctx xs)) [] x frames
    let d:=productOut h [] (jetTape (sumWords ctx xs)) [] (productWords ctx x) frames
    have h2:=restore false a (groupTape x) frames rfl rfl rfl
    change Runs program (8*(groupTape x).length+8) _ _ (ctl .copySum) (data b) at h2
    have h3:=move_sum b rfl
    change Runs program (6*(jetTape (sumWords ctx xs)).length+5) _ _ _ (data c) at h3
    obtain ⟨p,hpTime,hProduct⟩:=product_run ctx hp h hc [] (jetTape (sumWords ctx xs)) [] x frames
    have h4:=recursive_call .productCall .productVisit .add _ _ p rfl hProduct
    have h5:=add_call ctx d (productWords ctx x) (sumWords ctx xs) rfl rfl hc.width hr rfl
    change Runs program (SemiprimeD1StackJetAddExecution.totalTime h.width h.rank (productWords ctx x) (sumWords ctx xs)+1)
      _ _ _ (data (sumOut h (sumWords ctx (x::xs)) frames)) at h5
    have hh:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
    refine ⟨(15*(groupTape x).length+15)+((u+2)+((8*(groupTape x).length+8)+
      ((6*(jetTape (sumWords ctx xs)).length+5)+((p+2)+
        (SemiprimeD1StackJetAddExecution.totalTime h.width h.rank (productWords ctx x) (sumWords ctx xs)+1))))),?_,hh⟩
    rw [sumBudget]
    unfold sumEdge addCost
    omega
end RiemannGaussian.SemiprimeD1StackJetFoldSum
