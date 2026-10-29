/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridCallOriginal
import RiemannGaussian.SemiprimeD1WordTapeOriginalRate

/-! # Improved cubic envelope and the existing actual public retained report
The unchanged mixed word/tape report inherits the stronger actual call count.
The cubic multiplicity reserve remains explicit. No complete primitive-machine
bit-time, source simulation, or new fast-leaf implementation is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1HybridCallReport
open Filter SemiprimeD1OriginalCallRate SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1OriginalCallBounds SemiprimeD1OriginalStateResources
open SemiprimeD1PackingReady SemiprimeD1RootStateResources
open SemiprimeMacroParameters SemiprimePublicAcquiredExecution
open SemiprimeD1WordTapePublicRate SemiprimeD1WordTapeOriginalRate
open SemiprimeD1RecursiveCallTree SemiprimeD1Schedule
open scoped Topology
attribute [local irreducible] SemiprimeD1RootTapeNetwork.acquirePositive
  SemiprimeD1WordTapePublicCounter.prefixRun SemiprimeD1RootNetwork.acquirePositive
noncomputable section

/-- Exact improved all-child tree envelope before auxiliary absorption. -/
noncomputable def treeBound (s : ℕ) : ℝ :=
  (logarithm s+2:ℕ)*Real.exp ((393216/7:ℝ)*mainScale s+
    (((4*logarithm s+7)*(logarithm s+1):ℕ):ℝ))

/-- The existing actual counter report obeys the improved exact envelope with
its cubic call reserve. All local clocks remain the unchanged executed report;
this is neither an assumed cost premise nor a primitive-machine time theorem. -/
theorem eventually_counter_exact : ∃ C k : ℕ,∀ᶠ ell : ℕ in atTop,
    ∀ (N : ℕ) (hN : 0<N),bitLength N=ell → ∀fixed:List (Fin (wireCount N)×Bool),
      (counterClock N hN fixed:ℝ) ≤
        (localEnvelope C k (SemiprimeD1PublicPackingReady.scale ell):ℝ)*
          (treeBound (SemiprimeD1PublicPackingReady.scale ell)+1)^3 := by
  obtain ⟨C,k,hcost⟩ := SemiprimeD1WordTapeOriginalCounterBudget.eventually_original_clock
  refine ⟨C,k,?_⟩
  filter_upwards [hcost,SemiprimeD1HybridCallOriginal.eventually_original_count] with ell hc hb
  intro N hN hEll fixed
  let s := SemiprimeD1PublicPackingReady.scale ell
  let calls := count s (logarithm s+1) (originalCall N hN fixed)
  have hcost' : counterClock N hN fixed ≤ envelope C k s calls := by
    simpa only [counterClock,hEll,s,calls] using hc N hN hEll fixed
  have hcount : (calls:ℝ) ≤ treeBound s := by
    simpa only [treeBound,mainScale,mul_div_assoc,s,calls] using
      hb N hN hEll fixed (logarithm s+1)
  have hplus : (calls:ℝ)+1 ≤ treeBound s+1 := by linarith only [hcount]
  have hcube := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (calls:ℝ)+1) hplus 3
  calc
    _ ≤ (envelope C k s calls:ℝ) := by exact_mod_cast hcost'
    _ = (localEnvelope C k s:ℝ)*((calls:ℝ)+1)^3 := by
      simp only [envelope,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by positivity)

/-- Uniform explicit exponent constant for this numeric whole-call envelope. -/
def rateConstant (C k : ℕ) : ℕ :=
  1048576*(3*C+3*k+2)+3*SemiprimeD1HybridCallOriginal.callConstant+3

/-- For the same local-budget witnesses, the whole fixed exponent constant
is strictly smaller; the unchanged cubic multiplicity is still paid. -/
theorem rateConstant_lt_original (C k : ℕ) :
    rateConstant C k < SemiprimeD1OriginalEnvelopeRate.rateConstant C k := by
  unfold rateConstant SemiprimeD1OriginalEnvelopeRate.rateConstant
  have h := SemiprimeD1HybridCallOriginal.callConstant_lt_original
  omega

/-- The whole envelope preserves the requested quantitative rate when the
literal call count has its already proved original-input bound. -/
theorem envelope_rate (C k ell calls : ℕ)
    (hmain:1  ≤  mainScale (SemiprimeD1PublicPackingReady.scale ell))
    (haux:((degreeCap (SemiprimeD1PublicPackingReady.scale ell)+
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1)^3:ℕ):ℝ)  ≤
        2*mainScale (SemiprimeD1PublicPackingReady.scale ell))
    (hleaf:(leafSize (SemiprimeD1PublicPackingReady.scale ell)
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)):ℝ)  ≤
        mainScale (SemiprimeD1PublicPackingReady.scale ell)+1)
    (hinput:1  ≤  inputScale ell)
    (hcalls:(calls:ℝ)  ≤  (2:ℝ)^((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell)) :
    (envelope C k (SemiprimeD1PublicPackingReady.scale ell) calls:ℝ)  ≤
      (2:ℝ)^((rateConstant C k:ℝ)*inputScale ell) := by
  have hlocal:=localEnvelope_rate C k (SemiprimeD1PublicPackingReady.scale ell) haux hleaf hmain
  have hs:=mainScale_public ell
  have hlocal':(localEnvelope C k (SemiprimeD1PublicPackingReady.scale ell):ℝ)  ≤
      (2:ℝ)^((1048576*(3*C+3*k+2:ℕ):ℝ)*inputScale ell):=by
    apply hlocal.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
    push_cast
    nlinarith [show (0:ℝ)  ≤  3*(C:ℝ)+3*(k:ℝ)+2 by positivity]
  have hone:(1:ℝ)  ≤  (2:ℝ)^((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell):=
    Real.one_le_rpow (by norm_num) (by unfold inputScale;positivity)
  have hplus:(calls:ℝ)+1  ≤  (2:ℝ)^((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell+1):=by
    rw [Real.rpow_add (by norm_num:0<(2:ℝ)),Real.rpow_one]
    linarith
  have hcub:=pow_le_pow_left₀ (by positivity:(0:ℝ)  ≤  (calls:ℝ)+1) hplus 3
  have hprod:=mul_le_mul hlocal' hcub (by positivity) (by positivity)
  have hpow:((2:ℝ)^((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell+1))^3=
      (2:ℝ)^(3*((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell+1)):=by
    rw [←Real.rpow_mul_natCast (by norm_num:0 ≤ (2:ℝ))]
    congr 1
    ring
  rw [hpow,←Real.rpow_add (by norm_num:0<(2:ℝ))] at hprod
  have hprod':(envelope C k (SemiprimeD1PublicPackingReady.scale ell) calls:ℝ)  ≤
      (2:ℝ)^((1048576*(3*C+3*k+2:ℕ):ℝ)*inputScale ell+
        3*((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell+1)):=by
    simpa only [envelope,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hprod
  apply hprod'.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
  unfold rateConstant
  push_cast
  nlinarith

/-- CLOSED original-family conversion of the entire numeric envelope, uniformly
over every prefix and actual fuel. Actual program-to-envelope joins remain
explicitly separate and can instantiate this endpoint without new rate loss. -/
theorem eventually_original_envelope_rate (C k:ℕ) : ∀ᶠ ell:ℕ in atTop,
    ∀(N:ℕ)(hN:0<N),bitLength N=ell→
      ∀(fixed:List (Fin (wireCount N)×Bool))(fuel:ℕ),
        (envelope C k (SemiprimeD1PublicPackingReady.scale ell)
          (count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed)):ℝ)  ≤
          (2:ℝ)^((rateConstant C k:ℝ)*inputScale ell) := by
  have ht:Tendsto logarithm atTop atTop:=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [SemiprimeD1HybridCallOriginal.eventually_original_call_rate,
    scale_tendsto.eventually SemiprimeD1AuxiliaryRate.eventually_auxiliary_rate,
    scale_tendsto.eventually eventually_mainScale_ge_one,
    (ht.comp scale_tendsto).eventually (eventually_ge_atTop (1:ℕ)),
    eventually_ge_atTop (2:ℕ)] with ell hcalls haux hmain hl hell
  intro N hN hEll fixed fuel
  change 1 ≤ logarithm (SemiprimeD1PublicPackingReady.scale ell) at hl
  have hcalls':(count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ)  ≤
      (2:ℝ)^((SemiprimeD1HybridCallOriginal.callConstant:ℝ)*inputScale ell):=by
    simpa only [inputScale,mul_div_assoc] using hcalls N hN hEll fixed fuel
  apply envelope_rate C k ell _ hmain _ _ (inputScale_ge_one ell hell) hcalls'
  · simpa only [mainScale,mul_div_assoc] using haux
  · simpa only [mainScale] using SemiprimeD1LeafRate.leafSize_real
      (SemiprimeD1PublicPackingReady.scale ell) (logarithm (SemiprimeD1PublicPackingReady.scale ell))
      (by omega)
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
end RiemannGaussian.SemiprimeD1HybridCallReport
