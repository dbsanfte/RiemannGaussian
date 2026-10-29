/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformLoopControl
/-! # Whole descending physical transform query loop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformLoop
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformLoopState SemiprimeD1StackPublicTransformLoopControl
open SemiprimeD1StackPublicTransformQueryClosure SemiprimeD1StackPublicTransformRead
open SemiprimeD1StackPublicTransformGuards SemiprimeD1StackPublicTransformMetadata
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackPublicTransformQuery SemiprimeBitArithmetic
/-- Specification of the actual descending, short-circuit physical loop. -/
def answer (bits raw : List Bool) (second inverse : Bool) : ℕ→Bool
  | 0=>true
  | n+1=>queryAnswer bits raw second inverse n && answer bits raw second inverse n
/-- Conservative sum of the actual copy/call/drain bounds, including rejection. -/
def budget (bits raw : List Bool) (second inverse : Bool) : ℕ→ℕ→ℕ
  | 0,f=>1+(f+3)
  | n+1,f=>1+(f+1)+(5*n+4)+queryBudget bits raw second inverse n+
      budget bits raw second inverse n n+(2*n+3)
/-- Whole execution, with computed per-query equality and no evaluator supplier. -/
theorem loop_run (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hg : inputFlag (rootData bits) raw second=true) (n f : ℕ) :
    ∃t≤budget bits raw second inverse n f,
      Runs program t .loop (data (steady bits raw second inverse n f)) .done
        (data (finished (steady bits raw second inverse 0 0) (answer bits raw second inverse n))) := by
  induction n generalizing f with
  | zero=>
    have h0:=empty bits raw second inverse f
    have h1:=finish (steady bits raw second inverse 0 f) true (by rfl)
    rw [remaining_value,frequency_value] at h1
    simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] at h1
    rw [finished_steady] at h1
    refine ⟨1+(1+(0+1)+(f+1)),?_,?_⟩
    · simp only [budget]; omega
    · exact runs_trans program _ _ _ _ _ _ _ _ h0 h1
  | succ n ih=>
    have h0:=prepare bits raw second inverse n f
    obtain ⟨t,ht,h1⟩:=query_run bits raw second inverse n hc hN hg
    cases hq : queryAnswer bits raw second inverse n with
    | false=>
      simp only [hq,Bool.false_eq_true,ite_false] at h1
      have h2:=finish (steady bits raw second inverse n n) false (by rfl)
      rw [remaining_value,frequency_value] at h2
      simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] at h2
      rw [finished_steady] at h2
      refine ⟨(1+(f+1)+(5*n+4))+t+(1+(n+1)+(n+1)),?_,?_⟩
      · simp only [budget]; omega
      · simpa only [answer,hq,Bool.false_and] using
          runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
    | true=>
      simp only [hq,ite_true] at h1
      obtain ⟨u,hu,h2⟩:=ih n
      refine ⟨(1+(f+1)+(5*n+4))+t+u,?_,?_⟩
      · simp only [budget]; omega
      · simpa only [answer,hq,Bool.true_and] using
          runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
end RiemannGaussian.SemiprimeD1StackPublicTransformLoop
