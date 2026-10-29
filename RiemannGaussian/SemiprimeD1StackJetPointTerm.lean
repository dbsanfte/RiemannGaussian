/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointDecision
import RiemannGaussian.SemiprimeD1StackJetPointRead
import RiemannGaussian.SemiprimeD1StackJetPointOrder
/-! # Closed actual physical convolution-pair execution
Both route/matching flags, both coefficients, the product and modular partial sum
are acquired by literal included finite procedures. Arrays are proof-side input
encoding relations only. There is no routing, coefficient, fit or time supplier.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetPointTerm
open SemiprimeD1StackJetPoint SemiprimeD1StackJetPointExecution
open SemiprimeD1StackJetPointRouting SemiprimeD1StackJetPointDecision SemiprimeD1StackJetPointRead
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Concrete retained per-pair transition bound, including rejected pairs. -/
def pairBudget (ctx : SemiprimeD1JetAxes.Context) (c : Cache) (i j : ℕ)
    (acc : List Bool) (a b : List (List Bool)) : ℕ :=
  (5*c.axes.length+5*i+5*j+12)+(SemiprimeD1StackJetRouteExecution.budget ctx.axes i j+2)+
    (i+j+6*c.target.length+11)+readPipelineTime c.width (unary i) (unary j) acc a b

/-- One actual original pair is routed, selected, read and accumulated, with
all temporary data consumed on both branches and every included call paid. -/
theorem pair_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (c : Cache)
    (i j k : ℕ) (acc : List Bool) (a b : List (List Bool))
    (ha : c.a=SemiprimeD1TensorTapeCodec.vectorBits a)
    (hb : c.b=SemiprimeD1TensorTapeCodec.vectorBits b)
    (haxes : c.axes=SemiprimeD1TensorTapeCodec.vectorBits (ctx.axes.map unary))
    (hwidth : c.width.length=ctx.precision) (htarget : c.target.length=k) :
    ∃ m ≤ pairBudget ctx c i j acc a b,
      Runs program m .axesCopy (resting c (unary i) (unary j) acc) .inner
        (resting c (unary i) (unary j) (SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,j) acc)) := by
  have hprepare:=prepare_route ctx c i j acc haxes
  obtain ⟨mr,hr,hroute⟩:=route_call ctx hp c i j acc
  obtain ⟨ms,hs,hselect⟩:=route_select ctx c i j acc
  have hpre:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ hprepare hroute) hselect
  have hguard : (SemiprimeD1JetRouting.admissible ctx.axes i j ∧ SemiprimeD1JetRouting.sumIndex ctx.axes i j=k) ↔
      (SemiprimeD1JetRouting.admissible ctx.axes i j ∧ i+j=c.target.length) := by
    by_cases had : SemiprimeD1JetRouting.admissible ctx.axes i j
    · rw [SemiprimeD1StackRouteArithmetic.sumIndex_eq_add ctx.axes i j had,htarget]
    · simp [had]
  by_cases hmatch : SemiprimeD1JetRouting.admissible ctx.axes i j ∧ i+j=c.target.length
  · rw [ite_eq_left hmatch] at hpre
    have hread:=read_pipeline c (unary i) (unary j) acc a b ha hb
    have hh:=runs_trans program _ _ _ _ _ _ _ _ hpre hread
    have hstep : SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,j) acc=
        SemiprimeD1StackJetScalarAddExecution.result
          (SemiprimeD1StackJetScalarMulExecution.result ((a[(unary i).length]?).getD [])
            ((b[(unary j).length]?).getD []) c.width) acc c.width := by
      simp only [SemiprimeD1StackJetPointOrder.pairStep,ite_eq_left (hguard.mpr hmatch),
        SemiprimeD1StackJetScalarAddExecution.result,SemiprimeD1StackJetScalarMulExecution.result,
        hwidth,SemiprimeD1JetRingBits.read_bits,unary,List.length_replicate]
    rw [hstep]
    refine ⟨_,?_,hh⟩
    unfold pairBudget
    omega
  · rw [ite_eq_right hmatch] at hpre
    have hstep : SemiprimeD1StackJetPointOrder.pairStep ctx a b k (i,j) acc=acc := by
      simp only [SemiprimeD1StackJetPointOrder.pairStep,ite_eq_right (fun he=>hmatch (hguard.mp he))]
    rw [hstep]
    refine ⟨_,?_,hpre⟩
    unfold pairBudget
    omega

end RiemannGaussian.SemiprimeD1StackJetPointTerm
