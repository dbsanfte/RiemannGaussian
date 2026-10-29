/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeOriginalResources
import RiemannGaussian.SemiprimeD1WordTapeEnvelopeArithmetic
import RiemannGaussian.SemiprimeD1ActualCallReachableAggregation
import RiemannGaussian.SemiprimeD1WordTapeRecursiveReport
import RiemannGaussian.SemiprimeD1TensorTapeLeafBudget

/-! # Closed actual original-input word/tape counter report
All active sources, full eager tables, repeated child constructors, every
coordinate recovery and actual stopped/fuel-zero tape leaf are retained. This
is the actual mixed physical/native report, not a primitive machine-time claim.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1WordTapeOriginalCounterBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCallTree
open SemiprimeD1OriginalStateResources SemiprimeD1PackingReady
open SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1WordTapeRecursiveReport
open SemiprimeD1RecursiveCounter (activeTest)

/-- Fixed constants precede every original binary input and prefix. The actual
closed counter obeys the whole-call envelope, with no cost/height/entry or
packing/precision answer premise. Real remaining-fuel states alone are used. -/
theorem eventually_original_clock : ∃ C k : ℕ,∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)),
      (SemiprimeD1WordTapeRecursiveCounter.run (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) 0
        (originalCall N hN fixed).ctx (originalCall N hN fixed).net).clock ≤
      envelope C k (SemiprimeD1PublicPackingReady.scale ell)
        (count (SemiprimeD1PublicPackingReady.scale ell)
          (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)) := by
  obtain ⟨A,ka,hactiveFamily⟩:=SemiprimeD1WordTapeOriginalResources.eventually_original_active
  obtain ⟨B,kb,hleafPolynomial⟩:=SemiprimeD1OriginalInventoryScalar.tape_original_polynomial
  let C:=A+B+16
  let K:=ka+kb+1
  refine ⟨C,K,?_⟩
  have ht : Filter.Tendsto logarithm Filter.atTop Filter.atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (Filter.tendsto_add_atTop_nat 2)
  filter_upwards [hactiveFamily,eventually_original,
    SemiprimeD1TensorTapeLeafBudget.eventually_original_stopped,
    SemiprimeD1TensorTapeLeafBudget.eventually_original_zero,
    (ht.comp scale_tendsto).eventually (Filter.eventually_ge_atTop (1000:ℕ))]
    with ell hactive hstate hstopped hzero hl
  intro N hN hEll fixed
  let s:=SemiprimeD1PublicPackingReady.scale ell
  let root:=originalCall N hN fixed
  let fuel:=logarithm s+1
  let E:=localEnvelope C K s
  have hroot:=original_shape N hN fixed
  have shape (call : Call) (hr : Reach s root call) :
      call.ctx.Positive ∧ SemiprimeD1TensorNetwork.WellFormed call.net ∧
        SemiprimeD1TensorNetwork.Good call.ctx call.net :=
    SemiprimeD1RecursiveCallState.reach_shape _ _ _ hr hroot.1 hroot.2.1 hroot.2.2.1
  have hleafPoly:=hleafPolynomial s hl
  have raise_leaf (leaf : ℕ)
      (hleaf : leaf ≤ SemiprimeD1TensorTapeLeafBudget.originalPolynomial s*
        2^SemiprimeD1Schedule.leafSize s (logarithm s)) :
      leaf ≤ B*(scalar s+1)^kb*2^(B*degreeCap s)*2^SemiprimeD1Schedule.leafSize s (logarithm s) :=
    hleaf.trans (Nat.mul_le_mul_right _ hleafPoly)
  have controls (call : Call) (hr : Reach s root call) :
      s+logarithm s+call.depth+edgeCount call.net+8 ≤ 4*scalar s+8 := by
    have hb:=hstate N hN hEll fixed call hr
    have hbase:=SemiprimeD1OriginalScalarResources.base_caps s hl
    have hd:=hb.depth.trans hbase.2.2
    have hm:=hb.edge_count.trans hbase.1
    omega
  have leaf_zero (call : Call) (hr : Reach s root call) (hd : logarithm s+1 ≤ call.depth) :
      localWork s 0 call ≤ E := by
    have hz:=hzero N hN hEll fixed call hr (by omega)
    change (SemiprimeD1TensorTapeLeaf.leaf call.ctx call.net).clock+5 ≤ E
    exact SemiprimeD1WordTapeEnvelopeArithmetic.leaf_control_le A ka B kb s _ 5
      (raise_leaf _ hz) (by omega)
  have local_bound (call : Call) (hr : Reach s root call) : ∀ f ≤ fuel,
      logarithm s+1 ≤ call.depth+f → localWork s f call ≤ E*((children s call).length+1)^2 := by
    intro f _hf hi
    cases f with
    | zero =>
      have hz:=leaf_zero call hr (by omega)
      have hh : 1 ≤ ((children s call).length+1)^2 := Nat.one_le_pow _ _ (by omega)
      exact hz.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left E hh)
    | succ f =>
      have hb:=SemiprimeD1WordTapeFrameBudget.localWork_bound s (f+1) call (shape call hr).1 (by intro h;omega)
      by_cases ha : activeTest s (logarithm s) call.depth (edgeCount call.net)=true
      · have hactiveBound:=hactive N hN hEll fixed call hr ha
        have hraise:=SemiprimeD1WordTapeEnvelopeArithmetic.active_raise A ka B kb s
        exact hb.trans (hactiveBound.trans (Nat.mul_le_mul_right _ hraise))
      · have hstop : activeTest s (logarithm s) call.depth (edgeCount call.net)=false := Bool.eq_false_iff.mpr ha
        have hleaf:=hstopped N hN hEll fixed call hr hstop
        have henv:=SemiprimeD1WordTapeEnvelopeArithmetic.leaf_control_le A ka B kb s _
          (s+logarithm s+call.depth+edgeCount call.net+8) (raise_leaf _ hleaf) (controls call hr)
        have hbudget : SemiprimeD1WordTapeFrameBudget.budget s call ≤ E := by
          simpa only [SemiprimeD1WordTapeFrameBudget.budget,hstop,Bool.false_eq_true,ite_false,E,C,K,Nat.add_assoc] using henv
        have hh : 1 ≤ ((children s call).length+1)^2 := Nat.one_le_pow _ _ (by omega)
        exact hb.trans (hbudget.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left E hh))
  have hreport:=SemiprimeD1ActualCallReachableAggregation.report_le_count_cube s fuel (logarithm s+1) E root
    (fun f call => (SemiprimeD1WordTapeRecursiveCounter.run s f call.depth call.ctx call.net).clock)
    (localWork s)
    (by intro call _hr;exact run_zero_clock s call)
    (by intro f call hr;exact run_clock s f call (shape call hr).1)
    (by dsimp only [root,originalCall,fuel];omega)
    leaf_zero local_bound
  have hcount : (count s fuel root)^3 ≤ (count s fuel root+1)^3 := Nat.pow_le_pow_left (Nat.le_succ _) 3
  exact hreport.trans (Nat.mul_le_mul_left E hcount)

end RiemannGaussian.SemiprimeD1WordTapeOriginalCounterBudget
