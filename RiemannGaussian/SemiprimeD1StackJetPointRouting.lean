/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointExecution
import RiemannGaussian.SemiprimeD1StackJetRouteExecution
/-! # Actual original mixed-radix routing inside the coefficient controller
The literal included router acquires its own suffix products and all digits.
No route, rank, compatibility bit, or component execution budget is supplied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeD1StackJetPointRouting
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution
open SemiprimeD1StackProcedureTrace (Runs)
open SemiprimeD1StackUnaryDivmod (unary)
namespace R
export SemiprimeD1StackJetRouteExecution (initial final budget route_run final_value)
end R

/-- Declarative routing-stage invariant; the original program obtains these
registers by its three literal physical copies. Persistent caches stay live. -/
def staged (c : Cache) (i j acc : List Bool) (localData : SemiprimeD1StackJetRoute.Stack → List Bool) :
    Stack → List Bool
  | .inl k => localData k
  | .inr k => resting c i j acc (.inr k)

/-- Actual persistent-axis and current-index copies prepare the router inputs;
no per-pair routing/context answer is installed by this proof invariant. -/
theorem prepare_route (ctx : SemiprimeD1JetAxes.Context) (c : Cache) (i j : ℕ) (acc : List Bool)
    (ha : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary)) :
    Runs program (5*c.axes.length+5*i+5*j+12) .axesCopy (resting c (unary i) (unary j) acc)
      .routeCall (staged c (unary i) (unary j) acc (R.initial ctx.axes i j).data) := by
  let d0:=resting c (unary i) (unary j) acc
  let d1:=Function.update d0 (copyTarget .axes) c.axes
  let d2:=Function.update d1 (copyTarget .routeI) (unary i)
  let d3:=Function.update d2 (copyTarget .routeJ) (unary j)
  have h1:=copy_call .axes .axesCopy .leftCopy d0 rfl (by rfl) (by rfl)
  change Runs program (5*c.axes.length+4) .axesCopy d0 .leftCopy d1 at h1
  have h2:=copy_call .routeI .leftCopy .rightCopy d1 rfl (by rfl) (by rfl)
  change Runs program (5*(unary i).length+4) .leftCopy d1 .rightCopy d2 at h2
  have h3:=copy_call .routeJ .rightCopy .routeCall d2 rfl (by rfl) (by rfl)
  change Runs program (5*(unary j).length+4) .rightCopy d2 .routeCall d3 at h3
  have hd : d3=staged c (unary i) (unary j) acc (R.initial ctx.axes i j).data := by
    funext k
    rcases k with k|k
    · cases k <;> simp [d3,d2,d1,d0,copyTarget,resting,staged,
        SemiprimeD1StackJetRouteExecution.initial,SemiprimeD1StackJetRouteCalls.bank,ha]
    · rfl
  have hh:=SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
    (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3
  rw [hd] at hh
  simpa only [d0,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate,
    show (5*c.axes.length+4)+(5*i+4)+(5*j+4)=5*c.axes.length+5*i+5*j+12 by omega] using hh

/-- The actual original router, with its complete nested-call transition count,
is executed inside the coefficient program and preserves every outside byte. -/
theorem route_call (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (c : Cache) (i j : ℕ) (acc : List Bool) :
    ∃m≤R.budget ctx.axes i j+2,
      Runs program m .routeCall
        (staged c (unary i) (unary j) acc (R.initial ctx.axes i j).data) .routeDone
        (staged c (unary i) (unary j) acc (R.final ctx.axes i j).data) := by
  obtain ⟨m,hm,hr⟩:=R.route_run ctx hp i j
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program Sum.inl Label.route
    Sum.inl_injective SemiprimeD1StackJetRoute.code (SemiprimeD1StackJetRoute.control .copyLeft)
    (fun _=>rfl) .routeCall .routeDone rfl m (R.initial ctx.axes i j) (R.final ctx.axes i j)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k
      rfl
    · intro k hk
      rfl
  · constructor
    · intro k
      rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- The acquired route registers used by the controller carry the exact old
route, including rejection and out-of-range inputs, without a native getter. -/
theorem acquired_route (ctx : SemiprimeD1JetAxes.Context) (c : Cache) (i j : ℕ) (acc : List Bool) :
    (if staged c (unary i) (unary j) acc (R.final ctx.axes i j).data (.inl .valid)=[true] then
      some (staged c (unary i) (unary j) acc (R.final ctx.axes i j).data (.inl .result)).length else none)=
      (SemiprimeD1JetRouting.route ctx.axes i j).value := R.final_value ctx.axes i j

end RiemannGaussian.SemiprimeD1StackJetPointRouting
