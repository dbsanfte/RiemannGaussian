/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformRead
/-! # Exact cleanup and real per-output query aggregation
Actual producer/result caches are retained explicitly. No old/new clock equality
or externally supplied query word, verdict, evaluator or cost is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformQueryClosure
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformWords SemiprimeD1StackPublicTransformGuards
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformLoopState
open SemiprimeD1StackPublicTransformPrimitives SemiprimeD1StackPublicTransformQuery SemiprimeD1StackPublicTransformRead
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
private theorem dot_clear (c : SemiprimeD1StackExprDot.Cache) (cached : List Bool)
    (base : SemiprimeMacroEntryBitPrimitives.Expr) (words : List (List Bool)) (stride frequency n : ℕ) :
    Function.update (SemiprimeD1StackDotEvaluateExecution.done c cached base words stride frequency n []).data D.output []=
      (D.initial c cached []).data := by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
private theorem mul_clear (a b cached : List Bool) :
    Function.update (SemiprimeD1StackResidueMulExecution.done a b cached).data M.output []=(M.initial [] [] cached).data := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
/-- The actual dot-result drain restores the original argument cache exactly. -/
theorem dot_restored (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    (popped bits raw second inverse k).dot=(steady bits raw second inverse k k).dot := by
  rw [steady_dot]
  exact dot_clear _ _ _ _ _ _ _
/-- Actual copied/drained modular residue leaves only its acquired M cache. -/
theorem multiplier_restored (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    (popped bits raw second inverse k).multiplication=(steady bits raw second inverse k k).multiplication := by
  rw [steady_multiply]
  exact mul_clear _ _ _
/-- ENTIRE actual query restores every source/cache/remaining/frequency byte;
only its returned Boolean was consumed for actual loop/reject control. -/
theorem query_clean (bits raw : List Bool) (second inverse : Bool) (k : ℕ) :
    data (popped bits raw second inverse k)=data (steady bits raw second inverse k k) := by
  funext role
  cases role with
  | roots q=>rfl
  | dot q=>exact congrFun (dot_restored bits raw second inverse k) q
  | multiply q=>exact congrFun (multiplier_restored bits raw second inverse k) q
  | inputVector q=>rfl
  | outputVector q=>rfl
  | guard q=>rfl
  | read q=>cases q <;> rfl
  | equal q=>cases q <;> rfl
  | aux q=>cases q <;> rfl
/-- Actual query allowance is the sum of OWN visited component allowances,
physical source/result copies, complete drains, comparison and Boolean branch. -/
def queryBudget (bits raw : List Bool) (second inverse : Bool) (k : ℕ) : ℕ :=
  (SemiprimeD1StackDotEvaluateExecution.timeBound (queryCache bits raw second inverse k) (cached bits)
    (expression bits inverse) (inputs (rootData bits) raw second) (size bits (!second)) k (size bits second)+1)+
  (5*(dotWord bits raw second inverse k).length+4)+((dotWord bits raw second inverse k).length+1)+
  (5*(normalizer bits second inverse).length+4)+
  (SemiprimeD1StackResidueMulExecution.totalTime (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits)+1)+
  (5*(productWord bits raw second inverse k).length+4)+((productWord bits raw second inverse k).length+1)+
  (5*(unary k).length+4)+(SemiprimeD1StackJetReadExecution.totalTime (unary k) (outputs (rootData bits) raw second)+1)+
  (5*(outputWord bits raw second k).length+4)+((outputWord bits raw second k).length+1)+
  (SemiprimeD1StackWordEqualExecution.executionTime (productWord bits raw second inverse k) (outputWord bits raw second k)+1)+1
/-- WHOLE fixed actual per-output query: source acquisition/evaluation, physical
normalization, physical output read and actual comparison branch. Guard truth
here is local to the actually selected frontend branch, not a final input premise. -/
theorem query_run (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hg : inputFlag (rootData bits) raw second=true) :
    ∃t≤queryBudget bits raw second inverse k,Runs program t .evaluate (data (steady bits raw second inverse k k))
      (if queryAnswer bits raw second inverse k then .loop else .reject) (data (steady bits raw second inverse k k)) := by
  obtain ⟨t,ht,h0⟩:=dot_call bits raw second inverse k hc hN hg
  have h1:=copy_dot bits raw second inverse k
  have h2:=clear_dot bits raw second inverse k
  have h3:=copy_normalizer bits raw second inverse k
  have h4:=multiply_call bits raw second inverse k
  have h5:=copy_product bits raw second inverse k
  have h6:=clear_product bits raw second inverse k
  have h7:=copy_index bits raw second inverse k
  have h8:=read_call bits raw second inverse k
  have h9:=copy_output bits raw second inverse k
  have h10:=clear_output bits raw second inverse k
  have h11:=compare_call bits raw second inverse k
  have h12:=compare_branch bits raw second inverse k
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _
      (runs_trans program _ _ _ _ _ _ _ _
        (runs_trans program _ _ _ _ _ _ _ _
          (runs_trans program _ _ _ _ _ _ _ _
            (runs_trans program _ _ _ _ _ _ _ _
              (runs_trans program _ _ _ _ _ _ _ _
                (runs_trans program _ _ _ _ _ _ _ _
                  (runs_trans program _ _ _ _ _ _ _ _
                    (runs_trans program _ _ _ _ _ _ _ _
                      (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12
  rw [query_clean] at h
  refine ⟨_,?_,h⟩
  unfold queryBudget
  omega
end RiemannGaussian.SemiprimeD1StackPublicTransformQueryClosure
