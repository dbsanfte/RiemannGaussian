/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapePublicRate
import RiemannGaussian.SemiprimeD1WordTapeOriginalCounterBudget
import RiemannGaussian.SemiprimeD1RootTapeAcquisitionEnvelope

/-! # Closed original-input quantitative rate of the executed word/tape report
Counter acquisition, physical kernel/mode/table work, serialized leaves, every
prefix root acquisition and physical factor recovery are all retained. The
family endpoints have no counter/resource/clock oracle premise. They bound
this actual mixed report; full primitive source/memory simulation is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapeOriginalRate
open Filter SemiprimeD1OriginalCallRate SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1OriginalStateResources SemiprimeD1PackingReady
open SemiprimeD1RootStateResources SemiprimeMacroParameters SemiprimePublicAcquiredExecution
open SemiprimeD1WordTapePublicRate SemiprimeD1RecursiveCallTree
open scoped Topology
attribute [local irreducible] SemiprimeD1RootTapeNetwork.acquirePositive
  SemiprimeD1WordTapePublicCounter.prefixRun SemiprimeD1RootNetwork.acquirePositive
noncomputable section

/-- Actual original-root counter invocation retained by each new public query. -/
def counterClock (N : ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) : ℕ :=
  let s:=SemiprimeD1PublicPackingReady.scale (bitLength N)
  (SemiprimeD1WordTapeRecursiveCounter.run s (logarithm s+1) 0
    (originalCall N hN fixed).ctx (originalCall N hN fixed).net).clock

/-- Exact query report uses its own new root report and own counter report.
Only literal input-network data, not an old/new clock, are identified. -/
theorem prefix_clock (N : ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1WordTapePublicCounter.prefixRun N hN fixed).clock=
      (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock+counterClock N hN fixed+
        10*(wireCount N+fixed.length+bitLength N+1) := by
  unfold SemiprimeD1WordTapePublicCounter.prefixRun
  dsimp only
  rw [SemiprimeD1RootTapeNetwork.acquirePositive_network]
  rfl

/-- CLOSED counter rate for every original N and prefix, including all actual
child acquisition and local work rather than counting recursive calls alone. -/
theorem eventually_counter_rate : ∃C:ℕ,∀ᶠ ell:ℕ in atTop,
    ∀(N:ℕ)(hN:0<N),bitLength N=ell→∀fixed:List (Fin (wireCount N)×Bool),
      (counterClock N hN fixed:ℝ) ≤ (2:ℝ)^((C:ℝ)*inputScale ell) := by
  obtain ⟨C,k,hcost⟩:=SemiprimeD1WordTapeOriginalCounterBudget.eventually_original_clock
  refine ⟨rateConstant C k,?_⟩
  filter_upwards [hcost,eventually_original_envelope_rate C k] with ell hc hr
  intro N hN hEll fixed
  have h:=hc N hN hEll fixed
  have h':counterClock N hN fixed ≤ envelope C k (SemiprimeD1PublicPackingReady.scale ell)
      (count (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)):=by
    simpa only [counterClock,hEll] using h
  exact (show (counterClock N hN fixed:ℝ) ≤ (envelope C k (SemiprimeD1PublicPackingReady.scale ell)
      (count (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)):ℝ)
      by exact_mod_cast h').trans (hr N hN hEll fixed _)

/-- CLOSED root acquisition plus query controls at original input length.
Every repeated query root remains paid, including both actual scope factors. -/
theorem eventually_setup_rate : ∃R:ℕ,∀ᶠ ell:ℕ in atTop,
    ∀(N:ℕ)(hN:0<N),bitLength N=ell→∀fixed:List (Fin (wireCount N)×Bool),
      fixed.length ≤ wireCount N→
      ((SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock+
        10*(wireCount N+fixed.length+bitLength N+1):ℕ) ≤ (2:ℝ)^((R:ℝ)*inputScale ell) := by
  obtain ⟨A,d,hroot⟩:=SemiprimeD1RootTapeAcquisitionEnvelope.exists_query_clock
  let C:=A+32
  let k:=d+1
  refine ⟨localConstant C k,?_⟩
  have ht:Tendsto logarithm atTop atTop:=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [scale_tendsto.eventually SemiprimeD1AuxiliaryRate.eventually_auxiliary_rate,
    scale_tendsto.eventually eventually_mainScale_ge_one,
    (ht.comp scale_tendsto).eventually (eventually_ge_atTop (1000:ℕ)),
    eventually_ge_atTop (2:ℕ)] with ell haux hmain hl hell
  intro N hN hEll fixed hf
  let s:=SemiprimeD1PublicPackingReady.scale ell
  let S:=scalar s
  let T:=(S+1)^k
  let D:=2^(2*degreeCap s)
  change 1000 ≤ logarithm s at hl
  have hbase:=SemiprimeD1OriginalScalarResources.base_caps s hl
  have he:ell ≤ s:=by dsimp only [s];unfold SemiprimeD1PublicPackingReady.scale;norm_num;omega
  have hn:wireCount N ≤ s:=by
    have h:=root_edges_le_scale N hN []
    rw [root_edges,hEll] at h
    change 2*wireCount N ≤ s at h
    omega
  have hES:ell ≤ S:=he.trans hbase.1
  have hnS:wireCount N ≤ S:=hn.trans hbase.1
  have hD:1 ≤ D:=Nat.one_le_two_pow
  have hTk:d ≤ k:=by dsimp only [k];omega
  have hP:(ell+1)^d ≤ T:=by
    dsimp only [T]
    exact (Nat.pow_le_pow_left (Nat.add_le_add_right hES 1) d).trans
      (Nat.pow_le_pow_right (by omega:0<S+1) hTk)
  have hT:S+1 ≤ T:=by
    have h:=Nat.pow_le_pow_right (by omega:0<S+1) (show 1 ≤ k by dsimp only [k];omega)
    simpa only [pow_one] using h
  have hscope:scopeBound ell ≤ degreeCap s:=SemiprimeD1PublicPackingReady.actual_scope ell (by omega)
  have hp:2^(2*scopeBound ell) ≤ D:=Nat.pow_le_pow_right (by decide:0<(2:ℕ))
    (Nat.mul_le_mul_left 2 hscope)
  have hr0:=hroot N hN fixed hf
  rw [hEll] at hr0
  have hr:(SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock ≤ A*T*D:=
    hr0.trans (Nat.mul_le_mul (Nat.mul_le_mul_left A hP) hp)
  have hctl:10*(wireCount N+fixed.length+bitLength N+1) ≤ 30*T:=by
    rw [hEll]
    omega
  have h30:30*T ≤ 30*T*D:=by nlinarith only [hD]
  have hexp:2*degreeCap s ≤ C*degreeCap s+SemiprimeD1Schedule.leafSize s (logarithm s):=by
    have hc:2 ≤ C:=by dsimp only [C];omega
    nlinarith only [hc,Nat.zero_le (degreeCap s),Nat.zero_le (SemiprimeD1Schedule.leafSize s (logarithm s))]
  have hsetup:(SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock+
      10*(wireCount N+fixed.length+bitLength N+1) ≤ localEnvelope C k s:=by
    calc
      _  ≤  A*T*D+30*T := Nat.add_le_add hr hctl
      _  ≤  (A+30)*T*D := by nlinarith only [h30]
      _  ≤  C*T*2^(C*degreeCap s+SemiprimeD1Schedule.leafSize s (logarithm s)) := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_right T (by dsimp only [C];omega)
        · exact Nat.pow_le_pow_right (by decide:0<(2:ℕ)) hexp
      _ = _ := rfl
  have haux':((degreeCap s+(logarithm s+1)^3:ℕ):ℝ) ≤ 2*mainScale s:=by
    simpa only [mainScale,mul_div_assoc] using haux
  have hleaf:(SemiprimeD1Schedule.leafSize s (logarithm s):ℝ) ≤ mainScale s+1:=by
    simpa only [mainScale] using SemiprimeD1LeafRate.leafSize_real s (logarithm s) (by omega)
  exact (show ((SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock+
      10*(wireCount N+fixed.length+bitLength N+1):ℕ) ≤ (localEnvelope C k s:ℝ)
      by exact_mod_cast hsetup).trans (original_local_rate C k ell hmain haux' hleaf)

/-- CLOSED whole original-query report at the requested quantitative rate. -/
theorem eventually_prefix_rate : ∃C:ℕ,∀ᶠ ell:ℕ in atTop,
    ∀(N:ℕ)(hN:0<N),bitLength N=ell→∀fixed:List (Fin (wireCount N)×Bool),
      fixed.length ≤ wireCount N→
      ((SemiprimeD1WordTapePublicCounter.prefixRun N hN fixed).clock:ℝ) ≤
        (2:ℝ)^((C:ℝ)*inputScale ell) := by
  obtain ⟨A,ha⟩:=eventually_setup_rate
  obtain ⟨B,hb⟩:=eventually_counter_rate
  refine ⟨A+B+1,?_⟩
  filter_upwards [ha,hb,eventually_ge_atTop (2:ℕ)] with ell hroot hcounter hell
  intro N hN hEll fixed hf
  have hr:=hroot N hN hEll fixed hf
  have hc:=hcounter N hN hEll fixed
  have he:(SemiprimeD1WordTapePublicCounter.prefixRun N hN fixed).clock=
      ((SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock+
        10*(wireCount N+fixed.length+bitLength N+1))+counterClock N hN fixed:=by
    rw [prefix_clock]
    omega
  rw [he]
  push_cast
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using
    (add_le_add hr hc).trans (add_rate A B (inputScale ell) (inputScale_ge_one ell hell))

/-- CLOSED actual original-binary factor program's retained report. All source,
prefix acquisitions, recursion and factor/cofactor recovery are included.
Native/control/allocation/heap bit-machine simulation remains a separate proof. -/
theorem eventually_public_report_rate : ∃C:ℕ,∀ᶠ ell:ℕ in atTop,
    ∀input:List Bool,SemiprimeSourceCompactBits.Compact input→
      ∀_hN:0<SemiprimeBitArithmetic.bitValue input,bitLength (SemiprimeBitArithmetic.bitValue input)=ell→
        (SemiprimeD1WordTapePublicReport.work input:ℝ) ≤ (2:ℝ)^((C:ℝ)*inputScale ell) := by
  obtain ⟨C,hC⟩:=eventually_prefix_rate
  exact eventually_from_prefix C hC

end
end RiemannGaussian.SemiprimeD1WordTapeOriginalRate
