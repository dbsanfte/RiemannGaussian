import RiemannGaussian.SemiprimeD1HybridPublicReport
import RiemannGaussian.SemiprimeD1HybridOriginalCounterBudget
import RiemannGaussian.SemiprimeD1HybridCallReport

/-! Closed quantitative composition for the changed boundary public reports. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1HybridOriginalRate
open Filter SemiprimeD1OriginalCallRate SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1OriginalStateResources SemiprimeD1PackingReady SemiprimeD1RecursiveCallTree
open SemiprimeD1RootStateResources SemiprimeMacroParameters SemiprimePublicAcquiredExecution
open SemiprimeBitArithmetic SemiprimeD1WordTapePublicRate
open scoped Topology
noncomputable section
attribute [local irreducible] SemiprimeD1HybridPublicExecution.run
  SemiprimeD1HybridPublicExecution.prefixRun SemiprimeD1BinaryFactorExecution.run
  SemiprimeD1RootTapeNetwork.acquirePositive SemiprimeD1RootNetwork.acquirePositive
  SemiprimeD1HybridRecursiveCounter.run

/-- All actual selected prefix query reports are bounded by their literal count. -/
theorem run_queryWork_bound (input : List Bool) (hN : 0 < bitValue input) (C : Nat)
    (hC : ∀ f : List (Fin (wireCount (bitValue input)) × Bool),
      f.length ≤ wireCount (bitValue input) →
      (SemiprimeD1HybridPublicExecution.prefixRun (bitValue input) hN f).clock ≤ C) :
    (SemiprimeD1HybridPublicExecution.run input).queryWork ≤ (wireCount (bitValue input)+1)*C := by
  rw [SemiprimeD1HybridPublicExecution.run_queryWork_eq input hN,
    ←SemiprimeD1HybridPublicExecution.search_queryWork_eq (bitValue input) hN]
  exact SemiprimeD1HybridPublicExecution.search_queryWork (bitValue input) hN C hC

/-- Internal whole-public transfer from an actual uniform prefix-rate theorem.
All prefix acquisitions and local physical recovery remain on the left. -/
theorem eventually_from_prefix (C : ℕ)
    (hprefix:∀ᶠ ell:ℕ in atTop,∀(N:ℕ)(hN:0<N),bitLength N=ell→
      ∀fixed:List (Fin (wireCount N)×Bool),fixed.length ≤ wireCount N→
        ((SemiprimeD1HybridPublicExecution.prefixRun N hN fixed).clock:ℝ) ≤
          (2:ℝ)^((C:ℝ)*inputScale ell)) :
    ∃D:ℕ,∀ᶠ ell:ℕ in atTop,∀input:List Bool,SemiprimeSourceCompactBits.Compact input→
      ∀_hN:0<bitValue input,bitLength (bitValue input)=ell→
        (SemiprimeD1HybridPublicExecution.work input:ℝ) ≤ (2:ℝ)^((D:ℝ)*inputScale ell) := by
  obtain ⟨A,d,hlocal⟩:=SemiprimeD1PublicRecoveryBudget.exists_original_local_work
  refine ⟨localConstant 1 1+C+1+localConstant A d+1,?_⟩
  have ht:Tendsto logarithm atTop atTop:=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [hprefix,scale_tendsto.eventually SemiprimeD1AuxiliaryRate.eventually_auxiliary_rate,
    scale_tendsto.eventually eventually_mainScale_ge_one,
    (ht.comp scale_tendsto).eventually (eventually_ge_atTop (1000:ℕ)),
    eventually_ge_atTop (2:ℕ)] with ell hp haux hmain hl hell
  intro input hc hN hEll
  let N:=bitValue input
  let s:=SemiprimeD1PublicPackingReady.scale ell
  let B:=inputScale ell
  have hB:1 ≤ B:=inputScale_ge_one ell hell
  change 1000 ≤ logarithm s at hl
  have hbase:=SemiprimeD1OriginalScalarResources.base_caps s hl
  have haux':((degreeCap s+(logarithm s+1)^3:ℕ):ℝ) ≤ 2*mainScale s:=by
    simpa only [mainScale,mul_div_assoc] using haux
  have hleaf:(SemiprimeD1Schedule.leafSize s (logarithm s):ℝ) ≤ mainScale s+1:=by
    simpa only [mainScale] using SemiprimeD1LeafRate.leafSize_real s (logarithm s) (by omega)
  have he:ell ≤ s:=by dsimp only [s];unfold SemiprimeD1PublicPackingReady.scale;norm_num;omega
  have hn:wireCount N ≤ s:=by
    have h:=root_edges_le_scale N hN []
    rw [root_edges,hEll] at h
    change 2*wireCount N ≤ s at h
    omega
  have hw0:wireCount N+1 ≤ localEnvelope 1 1 s:=by
    simpa only [Nat.one_mul,pow_one] using polynomial_le_local 1 1 (wireCount N) s (hn.trans hbase.1)
  have hw:(wireCount N+1:ℕ) ≤ (2:ℝ)^((localConstant 1 1:ℝ)*B):=
    (show (wireCount N+1:ℕ) ≤ (localEnvelope 1 1 s:ℝ) by exact_mod_cast hw0).trans
      (original_local_rate 1 1 ell hmain haux' hleaf)
  have hrec:((SemiprimeD1HybridPublicExecution.run input).arithmeticClock+
      (SemiprimeD1HybridPublicExecution.run input).metadataWork:ℕ) ≤
        (2:ℝ)^((localConstant A d:ℝ)*B):=by
    rw [SemiprimeD1HybridPublicExecution.run_local_eq_tape]
    have h:=hlocal input hc hN
    rw [←SemiprimeD1WordTapePublicReport.run_local_eq input,hEll] at h
    apply (show ((SemiprimeD1WordTapeBinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1WordTapeBinaryFactorExecution.run input).metadataWork:ℕ) ≤
        (localEnvelope A d s:ℝ) by exact_mod_cast h.trans (polynomial_le_local A d ell s (he.trans hbase.1))).trans
    exact original_local_rate A d ell hmain haux' hleaf
  let R:ℝ:=(2:ℝ)^((C:ℝ)*B)
  have hR:1 ≤ R:=Real.one_le_rpow (by norm_num) (by positivity)
  have hpNat:∀fixed:List (Fin (wireCount N)×Bool),fixed.length ≤ wireCount N→
      (SemiprimeD1HybridPublicExecution.prefixRun N hN fixed).clock ≤ ⌈R⌉₊:=by
    intro fixed hf
    exact_mod_cast (hp N hN hEll fixed hf).trans (Nat.le_ceil R)
  have hq:=run_queryWork_bound input hN ⌈R⌉₊ hpNat
  have hceil:(⌈R⌉₊:ℝ) ≤ (2:ℝ)^(((C+1:ℕ):ℝ)*B):=by
    apply (Nat.ceil_lt_add_one (by positivity:0 ≤ R)).le.trans
    calc
      R+1  ≤  R*2 := by linarith
      _ = (2:ℝ)^((C:ℝ)*B+1) := by dsimp only [R];rw [Real.rpow_add (by norm_num:0<(2:ℝ)),Real.rpow_one]
      _  ≤  _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1 ≤ (2:ℝ))
        push_cast
        nlinarith only [hB]
  have hqR:((SemiprimeD1HybridPublicExecution.run input).queryWork:ℝ) ≤
      (2:ℝ)^(((localConstant 1 1+C+1:ℕ):ℝ)*B):=by
    have hq':((SemiprimeD1HybridPublicExecution.run input).queryWork:ℝ) ≤
        (wireCount N+1:ℕ)*(⌈R⌉₊:ℝ):=by exact_mod_cast hq
    apply hq'.trans
    apply (mul_le_mul hw hceil (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add (by norm_num:0<(2:ℝ))]
    congr 1
    push_cast
    ring
  have hsum:=add_rate (localConstant 1 1+C+1) (localConstant A d) B hB
  have hwork:(SemiprimeD1HybridPublicExecution.work input:ℝ) ≤
      (2:ℝ)^(((localConstant 1 1+C+1:ℕ):ℝ)*B)+(2:ℝ)^((localConstant A d:ℝ)*B):=by
    unfold SemiprimeD1HybridPublicExecution.work
    dsimp only
    push_cast at hqR hrec ⊢
    linarith only [hqR,hrec]
  exact hwork.trans hsum

/-- Actual changed counter report invoked by every original prefix. -/
def counterClock (N : Nat) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) : Nat :=
  let s := SemiprimeD1PublicPackingReady.scale (bitLength N)
  (SemiprimeD1HybridRecursiveCounter.run s (logarithm s+1) 0
    (originalCall N hN fixed).ctx (originalCall N hN fixed).net).clock

/-- Exact root acquisition and changed counter clock, with no query-clock transfer. -/
theorem prefix_clock (N : Nat) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) :
    (SemiprimeD1HybridPublicExecution.prefixRun N hN fixed).clock =
      (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock + counterClock N hN fixed +
        10*(wireCount N+fixed.length+bitLength N+1) := by
  unfold SemiprimeD1HybridPublicExecution.prefixRun
  dsimp only
  rw [SemiprimeD1RootTapeNetwork.acquirePositive_network]
  rfl

/-- The actual changed boundary counter report obeys the improved exact envelope with
its cubic call reserve. All local clocks are this changed program’s own executed report;
this is neither an assumed cost premise nor a primitive-machine time theorem. -/
theorem eventually_counter_exact : ∃ C k : ℕ,∀ᶠ ell : ℕ in atTop,
    ∀ (N : ℕ) (hN : 0<N),bitLength N=ell → ∀fixed:List (Fin (wireCount N)×Bool),
      (counterClock N hN fixed:ℝ) ≤
        (localEnvelope C k (SemiprimeD1PublicPackingReady.scale ell):ℝ)*
          (SemiprimeD1HybridCallReport.treeBound (SemiprimeD1PublicPackingReady.scale ell)+1)^3 := by
  obtain ⟨C,k,hcost⟩ := SemiprimeD1HybridOriginalCounterBudget.eventually_original_clock
  refine ⟨C,k,?_⟩
  filter_upwards [hcost,SemiprimeD1HybridCallOriginal.eventually_original_count] with ell hc hb
  intro N hN hEll fixed
  let s := SemiprimeD1PublicPackingReady.scale ell
  let calls := count s (logarithm s+1) (originalCall N hN fixed)
  have hcost' : counterClock N hN fixed ≤ envelope C k s calls := by
    simpa only [counterClock,hEll,s,calls] using hc N hN hEll fixed
  have hcount : (calls:ℝ) ≤ SemiprimeD1HybridCallReport.treeBound s := by
    simpa only [SemiprimeD1HybridCallReport.treeBound,mainScale,mul_div_assoc,s,calls] using
      hb N hN hEll fixed (logarithm s+1)
  have hplus : (calls:ℝ)+1 ≤ SemiprimeD1HybridCallReport.treeBound s+1 := by linarith only [hcount]
  have hcube := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (calls:ℝ)+1) hplus 3
  calc
    _ ≤ (envelope C k s calls:ℝ) := by exact_mod_cast hcost'
    _ = (localEnvelope C k s:ℝ)*((calls:ℝ)+1)^3 := by
      simp only [envelope,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by positivity)


/-- Closed actual changed counter rate with the improved all-child call bound.
The same explicit cubic call reserve remains paid. -/
theorem eventually_counter_rate : ∃ C : Nat, ∀ᶠ ell : Nat in atTop,
    ∀ (N : Nat) (hN : 0 < N), bitLength N = ell →
    ∀ fixed : List (Fin (wireCount N) × Bool),
      (counterClock N hN fixed : Real) ≤ (2:Real)^((C:Real)*inputScale ell) := by
  obtain ⟨C,k,hcost⟩ := SemiprimeD1HybridOriginalCounterBudget.eventually_original_clock
  refine ⟨SemiprimeD1HybridCallReport.rateConstant C k,?_⟩
  filter_upwards [hcost,SemiprimeD1HybridCallReport.eventually_original_envelope_rate C k] with ell hc hr
  intro N hN hEll fixed
  have h := hc N hN hEll fixed
  have h' : counterClock N hN fixed ≤ envelope C k (SemiprimeD1PublicPackingReady.scale ell)
      (count (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)) := by
    simpa only [counterClock,hEll] using h
  exact (show (counterClock N hN fixed:Real) ≤ (envelope C k (SemiprimeD1PublicPackingReady.scale ell)
      (count (SemiprimeD1PublicPackingReady.scale ell)
        (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1) (originalCall N hN fixed)):Real)
    by exact_mod_cast h').trans (hr N hN hEll fixed _)

/-- Every actual original-prefix report includes its own acquired root and recursion. -/
theorem eventually_prefix_rate : ∃ C : Nat, ∀ᶠ ell : Nat in atTop,
    ∀ (N : Nat) (hN : 0 < N), bitLength N = ell →
    ∀ fixed : List (Fin (wireCount N) × Bool), fixed.length ≤ wireCount N →
      ((SemiprimeD1HybridPublicExecution.prefixRun N hN fixed).clock:Real) ≤
        (2:Real)^((C:Real)*inputScale ell) := by
  obtain ⟨A,ha⟩ := SemiprimeD1WordTapeOriginalRate.eventually_setup_rate
  obtain ⟨B,hb⟩ := eventually_counter_rate
  refine ⟨A+B+1,?_⟩
  filter_upwards [ha,hb,eventually_ge_atTop (2:Nat)] with ell hroot hcounter hell
  intro N hN hEll fixed hf
  have hr := hroot N hN hEll fixed hf
  have hc := hcounter N hN hEll fixed
  have he : (SemiprimeD1HybridPublicExecution.prefixRun N hN fixed).clock =
      ((SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock+
        10*(wireCount N+fixed.length+bitLength N+1))+counterClock N hN fixed := by
    rw [prefix_clock]
    omega
  rw [he]
  push_cast
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using
    (add_le_add hr hc).trans (add_rate A B (inputScale ell) (inputScale_ge_one ell hell))

/-- Closed original-binary boundary-hybrid retained report rate. All acquired
prefixes, actual recursion, partition checks, contraction and decoder are paid.
This concerns the mixed native report, not a primitive bit-machine simulation. -/
theorem eventually_public_report_rate : ∃ C : Nat, ∀ᶠ ell : Nat in atTop,
    ∀ input : List Bool, SemiprimeSourceCompactBits.Compact input →
    ∀ _hN : 0 < bitValue input, bitLength (bitValue input) = ell →
      (SemiprimeD1HybridPublicExecution.work input:Real) ≤ (2:Real)^((C:Real)*inputScale ell) := by
  obtain ⟨C,hC⟩ := eventually_prefix_rate
  exact eventually_from_prefix C hC

end
end RiemannGaussian.SemiprimeD1HybridOriginalRate
