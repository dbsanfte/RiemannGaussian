/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointRouting
/-! # Physical routed-index selection inside convolution
The controller copies its actual target counter and consumes the acquired route
counter in the fixed paired-pop comparator. No matching bit is supplied.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetPointDecision
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
namespace E
export SemiprimeD1StackJetIndexEq (state code source_run)
end E

/-- Actual routing-result register before target acquisition. -/
def withResult (c : Cache) (i j acc word : List Bool) : Stack → List Bool :=
  Function.update (resting c i j acc) (.inl .result) word
/-- Actual acquired target next to the router's original result bytes. -/
def withTarget (c : Cache) (i j acc word : List Bool) : Stack → List Bool :=
  Function.update (withResult c i j acc word) (aux .eqRight) c.target

/-- Real comparator call consumes both metadata counters and acquires its flag. -/
theorem equal_call (c : Cache) (i j acc word : List Bool) :
    Runs program (word.length+c.target.length+5) .equalCall (withTarget c i j acc word) .equalDone
      (Function.update (resting c i j acc) (aux .eqValid) [decide (word.length=c.target.length)]) := by
  apply SemiprimeD1StackProcedureTrace.included_call program equalStack Label.equal equalStack_injective
    E.code .loop (fun _=>rfl) .equalCall .equalDone rfl (word.length+c.target.length+4)
    (E.state (some .loop) none word c.target []) (E.state none none [] [] [decide (word.length=c.target.length)])
  · rfl
  · rfl
  · exact E.source_run word c.target none
  · constructor
    · intro k
      cases k <;> simp [withTarget,withResult,equalStack,aux,resting,E.state,SemiprimeD1StackAdder.store]
    · intro k hk
      rfl
  · constructor
    · intro k
      cases k <;> simp [equalStack,aux,resting,E.state,SemiprimeD1StackAdder.store]
    · intro k hk
      have hl : k ≠ Sum.inl SemiprimeD1StackJetRoute.Stack.result := fun he=>hk .left he.symm
      have hr : k ≠ aux .eqRight := fun he=>hk .right he.symm
      have ho : k ≠ aux .eqValid := fun he=>hk .output he.symm
      simp only [withTarget,withResult,Function.update_of_ne ho,Function.update_of_ne hr,
        Function.update_of_ne hl]

/-- The actual comparison flag is popped and all comparator workspace is clean. -/
theorem equal_done (c : Cache) (i j acc : List Bool) (bit : Bool) :
    Runs program 1 .equalDone (Function.update (resting c i j acc) (aux .eqValid) [bit])
      (if bit then .readLeftCopy else .inner) (resting c i j acc) := by
  apply one_base program .equalDone (if bit then .readLeftCopy else .inner)
    (.pop (aux .eqValid) .inner .inner .readLeftCopy) _ _ rfl
  · cases bit <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp only [SemiprimeD1StackBytecode.execute,Function.update_self,List.tail_cons,
      Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl

/-- Complete actual target acquisition/comparison, preserving all other input
bytes and selecting a successor solely from its physically obtained flag. -/
theorem select_run (c : Cache) (i j acc word : List Bool) :
    Runs program (word.length+6*c.target.length+10) .targetCopy (withResult c i j acc word)
      (if word.length=c.target.length then .readLeftCopy else .inner) (resting c i j acc) := by
  have h1:=copy_call .target .targetCopy .equalCall (withResult c i j acc word) rfl (by rfl) (by rfl)
  change Runs program (5*c.target.length+4) .targetCopy (withResult c i j acc word)
    .equalCall (withTarget c i j acc word) at h1
  have h2:=equal_call c i j acc word
  have h3:=equal_done c i j acc (decide (word.length=c.target.length))
  have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h1 h2) h3
  simpa only [decide_eq_true_eq,show (5*c.target.length+4)+(word.length+c.target.length+5)+1=
    word.length+6*c.target.length+10 by omega] using hh

/-- Actual successful router flag is consumed, retaining only its acquired index. -/
theorem route_true (c : Cache) (i j acc word : List Bool) :
    Runs program 1 .routeDone (Function.update (withResult c i j acc word) (.inl .valid) [true])
      .targetCopy (withResult c i j acc word) := by
  apply one_base program .routeDone .targetCopy (.pop (.inl .valid) .inner .inner .targetCopy) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp only [SemiprimeD1StackBytecode.execute,Function.update_self,List.tail_cons,Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl

/-- Actual rejected router flag is consumed with no index/payload left behind. -/
theorem route_false (c : Cache) (i j acc : List Bool) :
    Runs program 1 .routeDone (Function.update (resting c i j acc) (.inl .valid) [false])
      .inner (resting c i j acc) := by
  apply one_base program .routeDone .inner (.pop (.inl .valid) .inner .inner .targetCopy) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp only [SemiprimeD1StackBytecode.execute,Function.update_self,List.tail_cons,Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl

/-- The original router's final physical bank is precisely the decision invariant. -/
theorem routed_data (ctx : SemiprimeD1JetAxes.Context) (c : Cache) (i j : ℕ) (acc : List Bool) :
    SemiprimeD1StackJetPointRouting.staged c (SemiprimeD1StackUnaryDivmod.unary i)
      (SemiprimeD1StackUnaryDivmod.unary j) acc (SemiprimeD1StackJetRouteExecution.final ctx.axes i j).data=
    if SemiprimeD1JetRouting.admissible ctx.axes i j then
      Function.update (withResult c (SemiprimeD1StackUnaryDivmod.unary i)
        (SemiprimeD1StackUnaryDivmod.unary j) acc (SemiprimeD1StackUnaryDivmod.unary (i+j))) (.inl .valid) [true]
    else Function.update (resting c (SemiprimeD1StackUnaryDivmod.unary i)
        (SemiprimeD1StackUnaryDivmod.unary j) acc) (.inl .valid) [false] := by
  funext k
  by_cases ha : SemiprimeD1JetRouting.admissible ctx.axes i j
  · rcases k with k|k
    · cases k <;> simp [SemiprimeD1StackJetPointRouting.staged,
        SemiprimeD1StackJetRouteExecution.final,SemiprimeD1StackJetRouteBase.answer,
        SemiprimeD1StackJetRouteCalls.bank,withResult,resting,ha]
    · simp [SemiprimeD1StackJetPointRouting.staged,withResult,ha]
  · rcases k with k|k
    · cases k <;> simp [SemiprimeD1StackJetPointRouting.staged,
        SemiprimeD1StackJetRouteExecution.final,SemiprimeD1StackJetRouteBase.answer,
        SemiprimeD1StackJetRouteCalls.bank,resting,ha]
    · simp [SemiprimeD1StackJetPointRouting.staged,ha]

/-- Closed routed selection: both flags and target matching are physically
acquired, and all metadata temporaries are cleared on both branches. -/
theorem route_select (ctx : SemiprimeD1JetAxes.Context) (c : Cache) (i j : ℕ) (acc : List Bool) :
    ∃ m ≤ i+j+6*c.target.length+11,
      Runs program m .routeDone
        (SemiprimeD1StackJetPointRouting.staged c (SemiprimeD1StackUnaryDivmod.unary i)
          (SemiprimeD1StackUnaryDivmod.unary j) acc (SemiprimeD1StackJetRouteExecution.final ctx.axes i j).data)
        (if SemiprimeD1JetRouting.admissible ctx.axes i j ∧ i+j=c.target.length then .readLeftCopy else .inner)
        (resting c (SemiprimeD1StackUnaryDivmod.unary i) (SemiprimeD1StackUnaryDivmod.unary j) acc) := by
  rw [routed_data]
  by_cases ha : SemiprimeD1JetRouting.admissible ctx.axes i j
  · simp only [ha,ite_true,true_and]
    have h1:=route_true c (SemiprimeD1StackUnaryDivmod.unary i) (SemiprimeD1StackUnaryDivmod.unary j)
      acc (SemiprimeD1StackUnaryDivmod.unary (i+j))
    have h2:=select_run c (SemiprimeD1StackUnaryDivmod.unary i) (SemiprimeD1StackUnaryDivmod.unary j)
      acc (SemiprimeD1StackUnaryDivmod.unary (i+j))
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
    refine ⟨_,le_refl _,?_⟩
    simpa only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate,
      show 1+(i+j+6*c.target.length+10)=i+j+6*c.target.length+11 by omega] using hh
  · simp only [ha,ite_false,false_and]
    exact ⟨1,by omega,route_false c _ _ acc⟩

end RiemannGaussian.SemiprimeD1StackJetPointDecision
