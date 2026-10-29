import RiemannGaussian.SemiprimeD1HybridActiveBudget
import RiemannGaussian.SemiprimeD1BoundaryCheckedPolynomial
import RiemannGaussian.SemiprimeD1OriginalCallBounds
import RiemannGaussian.SemiprimeD1WordTapeOriginalResources
import RiemannGaussian.SemiprimeD1WordTapeEnvelopeArithmetic
import RiemannGaussian.SemiprimeD1ActualCallReachableAggregation
import RiemannGaussian.SemiprimeD1RecursiveLeafBounds

/-! Actual boundary recursion and the fixed original-family call envelope. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace RiemannGaussian.SemiprimeD1HybridOriginalCounterBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCallTree
open SemiprimeD1OriginalStateResources SemiprimeD1PackingReady
open SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1HybridRecursiveCounter (localWork)
open SemiprimeD1RecursiveCounter (activeTest)
/-- Internal actual-state aggregation from a uniform stopped-leaf reserve.
The final closed family theorem below discharges this proof-only premise;
real remaining-fuel states retain every actual child occurrence. -/
theorem original_clock_of_leaf_reserve (B kb : Nat)
    (hleafFamily : ∀ᶠ ell : Nat in Filter.atTop,
      ∀ (N : Nat) (hN : 0 < N), SemiprimeMacroParameters.bitLength N = ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N) × Bool)) (call : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) call →
      activeTest (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)) call.depth (edgeCount call.net) = false →
      (SemiprimeD1BoundaryLeaf.checked call.ctx call.net).clock ≤
        B*(scalar (SemiprimeD1PublicPackingReady.scale ell)+1)^kb*
          2^(B*degreeCap (SemiprimeD1PublicPackingReady.scale ell))*
          2^SemiprimeD1Schedule.leafSize (SemiprimeD1PublicPackingReady.scale ell)
            (logarithm (SemiprimeD1PublicPackingReady.scale ell))) : ∃ C k : ℕ,∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)),
      (SemiprimeD1HybridRecursiveCounter.run (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) 0
        (originalCall N hN fixed).ctx (originalCall N hN fixed).net).clock ≤
      envelope C k (SemiprimeD1PublicPackingReady.scale ell)
        (count (SemiprimeD1PublicPackingReady.scale ell)
          (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)) := by
  obtain ⟨A,ka,hactiveFamily⟩:=SemiprimeD1WordTapeOriginalResources.eventually_original_active
  let C:=A+B+16
  let K:=ka+kb+1
  refine ⟨C,K,?_⟩
  have ht : Filter.Tendsto logarithm Filter.atTop Filter.atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (Filter.tendsto_add_atTop_nat 2)
  filter_upwards [hactiveFamily,eventually_original,
    hleafFamily,
    (ht.comp scale_tendsto).eventually (Filter.eventually_ge_atTop (1000:ℕ))]
    with ell hactive hstate hleaf hl
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
  have controls (call : Call) (hr : Reach s root call) :
      s+logarithm s+call.depth+edgeCount call.net+8 ≤ 4*scalar s+8 := by
    have hb:=hstate N hN hEll fixed call hr
    have hbase:=SemiprimeD1OriginalScalarResources.base_caps s hl
    have hd:=hb.depth.trans hbase.2.2
    have hm:=hb.edge_count.trans hbase.1
    omega
  have leaf_zero (call : Call) (hr : Reach s root call) (hd : logarithm s+1 ≤ call.depth) :
      localWork s 0 call ≤ E := by
    have hz := hleaf N hN hEll fixed call hr
      (SemiprimeD1RecursiveLeafBounds.zero_fuel_inactive s call.depth (by omega) (edgeCount call.net))
    change (SemiprimeD1BoundaryLeaf.checked call.ctx call.net).clock+5 ≤ E
    exact SemiprimeD1WordTapeEnvelopeArithmetic.leaf_control_le A ka B kb s _ 5
      hz (by omega)
  have local_bound (call : Call) (hr : Reach s root call) : ∀ f ≤ fuel,
      logarithm s+1 ≤ call.depth+f → localWork s f call ≤ E*((children s call).length+1)^2 := by
    intro f _hf hi
    cases f with
    | zero =>
      have hz:=leaf_zero call hr (by omega)
      have hh : 1 ≤ ((children s call).length+1)^2 := Nat.one_le_pow _ _ (by omega)
      exact hz.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left E hh)
    | succ f =>
      by_cases ha : activeTest s (logarithm s) call.depth (edgeCount call.net)=true
      · have hb := SemiprimeD1HybridActiveBudget.active_localWork_le s f call (shape call hr).1 ha
        have hactiveBound:=hactive N hN hEll fixed call hr ha
        have hraise:=SemiprimeD1WordTapeEnvelopeArithmetic.active_raise A ka B kb s
        exact hb.trans (hactiveBound.trans (Nat.mul_le_mul_right _ hraise))
      · have hstop : activeTest s (logarithm s) call.depth (edgeCount call.net)=false := Bool.eq_false_iff.mpr ha
        have hleafBound := hleaf N hN hEll fixed call hr hstop
        have henv := SemiprimeD1WordTapeEnvelopeArithmetic.leaf_control_le A ka B kb s _
          (s+logarithm s+call.depth+edgeCount call.net+8) hleafBound (controls call hr)
        have hlocal : localWork s (f+1) call ≤ E := by
          change (SemiprimeD1HybridRecursiveKernel.frame SemiprimeD1BoundaryLeaf.checked s call
            (SemiprimeD1PhysicalRecursiveClock.eraseClock
              (SemiprimeD1HybridRecursiveCounter.run s f (call.depth+1)))).clock ≤ E
          rw [SemiprimeD1HybridRecursiveKernel.frame_inactive _ _ _ _ hstop]
          simpa only [Nat.add_assoc,E,C,K] using henv
        have hh : 1 ≤ ((children s call).length+1)^2 := Nat.one_le_pow _ _ (by omega)
        exact hlocal.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left E hh)
  have hreport:=SemiprimeD1ActualCallReachableAggregation.report_le_count_cube s fuel (logarithm s+1) E root
    (fun f call => (SemiprimeD1HybridRecursiveCounter.run s f call.depth call.ctx call.net).clock)
    (localWork s)
    (by intro call _hr;rfl)
    (by intro f call hr;exact SemiprimeD1HybridRecursiveCounter.run_clock s f call (shape call hr).1)
    (by dsimp only [root,originalCall,fuel];omega)
    leaf_zero local_bound
  have hcount : (count s fuel root)^3 ≤ (count s fuel root+1)^3 := Nat.pow_le_pow_left (Nat.le_succ _) 3
  exact hreport.trans (Nat.mul_le_mul_left E hcount)

/-- Closed original-family native counter envelope. Constants precede every
input and prefix; actual partition validation and every stopped leaf are paid. -/
theorem eventually_original_clock : ∃ C k : Nat, ∀ᶠ ell : Nat in Filter.atTop,
    ∀ (N : Nat) (hN : 0 < N), SemiprimeMacroParameters.bitLength N = ell →
    ∀ fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N) × Bool),
    (SemiprimeD1HybridRecursiveCounter.run (SemiprimeD1PublicPackingReady.scale ell)
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) 0
      (originalCall N hN fixed).ctx (originalCall N hN fixed).net).clock ≤
      envelope C k (SemiprimeD1PublicPackingReady.scale ell)
        (count (SemiprimeD1PublicPackingReady.scale ell)
          (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)) := by
  obtain ⟨B,k,hB,hbudget⟩ := SemiprimeD1BoundaryCheckedPolynomial.checked_original_polynomial
  apply original_clock_of_leaf_reserve B k
  have ht : Filter.Tendsto logarithm Filter.atTop Filter.atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (Filter.tendsto_add_atTop_nat 2)
  filter_upwards [eventually_original,SemiprimeD1OriginalCallBounds.eventually_original_stopped_leaf,
    (ht.comp scale_tendsto).eventually (Filter.eventually_ge_atTop (1000:Nat))]
    with ell hstate hstopped hl
  intro N hN hEll fixed call hr hstop
  let s := SemiprimeD1PublicPackingReady.scale ell
  have hb := hstate N hN hEll fixed call hr
  have hroot := original_shape N hN fixed
  have hshape := SemiprimeD1RecursiveCallState.reach_shape _ _ _ hr
    hroot.1 hroot.2.1 hroot.2.2.1
  have hM := (hstopped N hN hEll fixed call hr hstop).1
  have hV : (SemiprimeD1BoundaryPlan.graph call.net).vertices ≤ 5*s := by
    simpa only [SemiprimeD1BoundaryPlan.graph,SemiprimeD1TensorNetwork.vertices,
      List.length_append,Vector.length_toList,SemiprimeD1NetworkStateResources.vertexCount] using hb.vertex_count
  have hleaf := hbudget s call.ctx call.net hl hshape.2.1 hshape.2.2 hV
    (by simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using hb.edge_count.trans (Nat.le_succ s))
    (by simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using hM)
    (hb.axes_length.trans_le hb.depth) hb.axes hb.rank hb.precision
  apply hleaf.trans
  have hp : 1 ≤ 2^(B*degreeCap s) := Nat.one_le_two_pow
  nlinarith only [Nat.mul_le_mul_right (B*(scalar s+1)^k*2^SemiprimeD1Schedule.leafSize s (logarithm s)) hp]

end RiemannGaussian.SemiprimeD1HybridOriginalCounterBudget
