/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldSpec
import RiemannGaussian.SemiprimeD1StackJetFoldFrames
import RiemannGaussian.SemiprimeD1StackJetFoldMoves
/-! # Whole actual ordered product with real saved heads and recursive returns
No product answer, rank supplier or callback is supplied. Every child is parsed
from the physical input, saved, restored, and multiplied in literal right-fold
order by the frozen whole dense multiplier.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldProduct
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldWords
open SemiprimeD1StackJetFoldPrimitives SemiprimeD1StackJetFoldFrames SemiprimeD1StackJetFoldMoves
open SemiprimeD1StackJetFoldOperators SemiprimeD1StackJetFoldSpec SemiprimeD1StackProcedureTrace
open SemiprimeD1JetAxes (Context)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
attribute [local irreducible] productBudget productEdge multiplyCost
/-- Every actual ordered child vector is consumed once, with a real physical recursive stack. -/
theorem product_run (ctx:Context) (hp:ctx.Positive) (h:Header) (hc:Matches ctx h)
    (modes tailSum sum:List Bool) (children:Group) (frames:List Bool):
    ∃time ≤ productBudget ctx h children,Runs program time (ctl .productVisit)
      (data (productNode h modes tailSum sum children frames)) (ctl .returning)
      (data (productOut h modes tailSum sum (productWords ctx children) frames)):=by
  induction children generalizing frames with
  | nil=>
    let v:=productNode h modes tailSum sum [] frames
    let a:=bank h modes [] frames [] [] [] tailSum sum []
    have h0:=pop_view .productVisit .abort .unit .productRead .group v [false] rfl rfl
    change Runs program 1 _ _ (ctl .unit) (data a) at h0
    have hr:h.rank.length=ctx.rank:=by rw [hc.rank];exact List.length_replicate
    have h1:=unit_call ctx a hc.width hr rfl
    change Runs program (SemiprimeD1StackJetUnitExecution.totalTime h.width h.rank+1) _ _ _
      (data (productOut h modes tailSum sum (productWords ctx []) frames)) at h1
    have hh:=join h0 h1
    refine ⟨1+(SemiprimeD1StackJetUnitExecution.totalTime h.width h.rank+1),?_,hh⟩
    rw [productBudget]
    omega
  | cons x xs ih=>
    let v:=productNode h modes tailSum sum (x::xs) frames
    obtain ⟨u,hu,hChild⟩:=ih (frame (jetTape x) frames)
    have h0:=enter true v (jetTape x) (groupTape xs) rfl rfl rfl
    change Runs program (15*(jetTape x).length+15) _ _ (ctl .productChild)
      (data (productNode h modes tailSum sum xs (frame (jetTape x) frames))) at h0
    have h1:=recursive_call .productChild .productVisit .productRestore _ _ u rfl hChild
    let a:=productOut h modes tailSum sum (productWords ctx xs) (frame (jetTape x) frames)
    let b:=bank h modes [] frames (jetTape x) (jetTape (productWords ctx xs)) [] tailSum sum []
    let c:=bank h modes [] frames (jetTape x) (jetTape (productWords ctx xs))
      (jetTape (productWords ctx (x::xs))) tailSum sum []
    have h2:=restore true a (jetTape x) frames rfl rfl rfl
    change Runs program (8*(jetTape x).length+8) _ _ (ctl .multiply) (data b) at h2
    obtain ⟨m,hm,h3⟩:=multiply_call ctx hp b x (productWords ctx xs) rfl rfl hc.axes hc.width hc.rank rfl
    have hcost:mulBound ctx b=multiplyCost ctx h x (productWords ctx xs):=by
      unfold multiplyCost
      rfl
    rw [hcost] at hm
    change Runs program m _ _ _ (data c) at h3
    have h4:=move_product c
    change Runs program ((jetTape x).length+(jetTape (productWords ctx xs)).length+
      6*(jetTape (productWords ctx (x::xs))).length+7) _ _ _
      (data (productOut h modes tailSum sum (productWords ctx (x::xs)) frames)) at h4
    have hh:=join h0 (join h1 (join h2 (join h3 h4)))
    refine ⟨(15*(jetTape x).length+15)+((u+2)+((8*(jetTape x).length+8)+
      (m+((jetTape x).length+(jetTape (productWords ctx xs)).length+
        6*(jetTape (productWords ctx (x::xs))).length+7)))),?_,hh⟩
    rw [productBudget]
    unfold productEdge
    omega
end RiemannGaussian.SemiprimeD1StackJetFoldProduct
