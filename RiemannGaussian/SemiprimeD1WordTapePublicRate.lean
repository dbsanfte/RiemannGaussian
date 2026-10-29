/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapePublicReport
import RiemannGaussian.SemiprimeD1OriginalInventoryScalar

/-! # Quantitative public report composition for the actual word/tape caller
Every queried prefix retains its own root acquisition and recursion. Fixed
recovery work and the actual number of queries are paid at original input
length. The prefix-rate premise below is an internal theorem to discharge
from the concrete counter, never an argument to the factoring algorithm.
This concerns retained reports, not a complete primitive-machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapePublicRate
open Filter SemiprimeD1OriginalCallRate SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1OriginalStateResources SemiprimeD1PackingReady
open SemiprimeD1RootStateResources SemiprimeMacroParameters SemiprimePublicAcquiredExecution
open SemiprimeBitArithmetic
open scoped Topology
noncomputable section
attribute [local irreducible] SemiprimeD1WordTapeBinaryFactorExecution.run
  SemiprimeD1WordTapePublicCounter.prefixRun SemiprimeD1BinaryFactorExecution.run

/-- Scalar-resource polynomial, with the original table/leaf factor retained. -/
theorem polynomial_le_local (A d n s : ℕ) (hn:n ≤ scalar s) :
    A*(n+1)^d ≤ localEnvelope A d s := by
  have hP:=Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) d
  have hE:1 ≤ 2^(A*degreeCap s+SemiprimeD1Schedule.leafSize s (logarithm s)):=Nat.one_le_two_pow
  unfold localEnvelope
  calc
    _  ≤  A*(scalar s+1)^d := Nat.mul_le_mul_left A hP
    _  ≤  _ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A*(scalar s+1)^d) hE

/-- Fixed original-input exponent constant for a concrete local envelope. -/
def localConstant (A d : ℕ) : ℕ := 1048576*(3*A+3*d+2)

/-- Actual local envelope at the requested original-length scale. -/
theorem original_local_rate (A d ell : ℕ)
    (hmain:1 ≤ mainScale (SemiprimeD1PublicPackingReady.scale ell))
    (haux:((degreeCap (SemiprimeD1PublicPackingReady.scale ell)+
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)+1)^3:ℕ):ℝ) ≤
        2*mainScale (SemiprimeD1PublicPackingReady.scale ell))
    (hleaf:(SemiprimeD1Schedule.leafSize (SemiprimeD1PublicPackingReady.scale ell)
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)):ℝ) ≤
        mainScale (SemiprimeD1PublicPackingReady.scale ell)+1) :
    (localEnvelope A d (SemiprimeD1PublicPackingReady.scale ell):ℝ) ≤
      (2:ℝ)^((localConstant A d:ℝ)*inputScale ell) := by
  apply (localEnvelope_rate A d _ haux hleaf hmain).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1 ≤ (2:ℝ))
  have hs:=mainScale_public ell
  unfold localConstant
  push_cast
  nlinarith [show (0:ℝ) ≤ 3*(A:ℝ)+3*(d:ℝ)+2 by positivity]

/-- A real prefix budget can be used in the actual natural report sum, with a
ceiling appearing in the proof only. The executed program receives no budget. -/
theorem work_real (input : List Bool) (hc:SemiprimeSourceCompactBits.Compact input)
    (hN:0<bitValue input) (R : ℝ) (hR:0 ≤ R)
    (hprefix:∀fixed:List (Fin (wireCount (bitValue input))×Bool),fixed.length ≤ wireCount (bitValue input)→
      ((SemiprimeD1WordTapePublicCounter.prefixRun (bitValue input) hN fixed).clock:ℝ) ≤ R) :
    (SemiprimeD1WordTapePublicReport.work input:ℝ) ≤
      (wireCount (bitValue input)+1:ℕ)*(R+1)+
        SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)) := by
  have hnat:∀fixed:List (Fin (wireCount (bitValue input))×Bool),fixed.length ≤ wireCount (bitValue input)→
      (SemiprimeD1WordTapePublicCounter.prefixRun (bitValue input) hN fixed).clock ≤ ⌈R⌉₊:=by
    intro fixed hf
    exact_mod_cast (hprefix fixed hf).trans (Nat.le_ceil R)
  have hwork:=SemiprimeD1WordTapePublicReport.work_le input hc hN ⌈R⌉₊ hnat
  have hcast:(SemiprimeD1WordTapePublicReport.work input:ℝ) ≤
      (wireCount (bitValue input)+1:ℕ)*(⌈R⌉₊:ℝ)+
        SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)):=by exact_mod_cast hwork
  apply hcast.trans
  have hceil: (⌈R⌉₊:ℝ) ≤ R+1:=(Nat.ceil_lt_add_one hR).le
  gcongr

/-- Sum of two nonnegative-rate powers costs one further scale unit. -/
theorem add_rate (A D : ℕ) (B : ℝ) (hB:1 ≤ B) :
    (2:ℝ)^((A:ℝ)*B)+(2:ℝ)^((D:ℝ)*B) ≤ (2:ℝ)^(((A+D+1:ℕ):ℝ)*B) := by
  have hA:(1:ℝ) ≤ (2:ℝ)^((A:ℝ)*B):=Real.one_le_rpow (by norm_num) (by positivity)
  have hD:(1:ℝ) ≤ (2:ℝ)^((D:ℝ)*B):=Real.one_le_rpow (by norm_num) (by positivity)
  have hm1:=mul_le_mul_of_nonneg_left hD (show 0≤(2:ℝ)^((A:ℝ)*B) by positivity)
  have hm2:=mul_le_mul_of_nonneg_right hA (show 0≤(2:ℝ)^((D:ℝ)*B) by positivity)
  calc
    _  ≤  2*((2:ℝ)^((A:ℝ)*B)*(2:ℝ)^((D:ℝ)*B)) := by nlinarith
    _ = (2:ℝ)^((A:ℝ)*B+(D:ℝ)*B+1) := by
      rw [Real.rpow_add (by norm_num:0<(2:ℝ)),Real.rpow_one,
        Real.rpow_add (by norm_num:0<(2:ℝ))]
      ring
    _  ≤  _ := by apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1 ≤ (2:ℝ));push_cast;nlinarith

/-- Internal whole-public transfer from an actual uniform prefix-rate theorem.
All prefix acquisitions and local physical recovery remain on the left. -/
theorem eventually_from_prefix (C : ℕ)
    (hprefix:∀ᶠ ell:ℕ in atTop,∀(N:ℕ)(hN:0<N),bitLength N=ell→
      ∀fixed:List (Fin (wireCount N)×Bool),fixed.length ≤ wireCount N→
        ((SemiprimeD1WordTapePublicCounter.prefixRun N hN fixed).clock:ℝ) ≤
          (2:ℝ)^((C:ℝ)*inputScale ell)) :
    ∃D:ℕ,∀ᶠ ell:ℕ in atTop,∀input:List Bool,SemiprimeSourceCompactBits.Compact input→
      ∀_hN:0<bitValue input,bitLength (bitValue input)=ell→
        (SemiprimeD1WordTapePublicReport.work input:ℝ) ≤ (2:ℝ)^((D:ℝ)*inputScale ell) := by
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
  have hrec:((SemiprimeD1WordTapeBinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1WordTapeBinaryFactorExecution.run input).metadataWork:ℕ) ≤
        (2:ℝ)^((localConstant A d:ℝ)*B):=by
    have h:=hlocal input hc hN
    rw [←SemiprimeD1WordTapePublicReport.run_local_eq input,hEll] at h
    apply (show ((SemiprimeD1WordTapeBinaryFactorExecution.run input).arithmeticClock+
      (SemiprimeD1WordTapeBinaryFactorExecution.run input).metadataWork:ℕ) ≤
        (localEnvelope A d s:ℝ) by exact_mod_cast h.trans (polynomial_le_local A d ell s (he.trans hbase.1))).trans
    exact original_local_rate A d ell hmain haux' hleaf
  let R:ℝ:=(2:ℝ)^((C:ℝ)*B)
  have hR:1 ≤ R:=Real.one_le_rpow (by norm_num) (by positivity)
  have hpNat:∀fixed:List (Fin (wireCount N)×Bool),fixed.length ≤ wireCount N→
      (SemiprimeD1WordTapePublicCounter.prefixRun N hN fixed).clock ≤ ⌈R⌉₊:=by
    intro fixed hf
    exact_mod_cast (hp N hN hEll fixed hf).trans (Nat.le_ceil R)
  have hq:=SemiprimeD1WordTapePublicReport.run_queryWork input hN ⌈R⌉₊ hpNat
  have hceil:(⌈R⌉₊:ℝ) ≤ (2:ℝ)^(((C+1:ℕ):ℝ)*B):=by
    apply (Nat.ceil_lt_add_one (by positivity:0 ≤ R)).le.trans
    calc
      R+1  ≤  R*2 := by linarith
      _ = (2:ℝ)^((C:ℝ)*B+1) := by dsimp only [R];rw [Real.rpow_add (by norm_num:0<(2:ℝ)),Real.rpow_one]
      _  ≤  _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1 ≤ (2:ℝ))
        push_cast
        nlinarith only [hB]
  have hqR:((SemiprimeD1WordTapeBinaryFactorExecution.run input).queryWork:ℝ) ≤
      (2:ℝ)^(((localConstant 1 1+C+1:ℕ):ℝ)*B):=by
    have hq':((SemiprimeD1WordTapeBinaryFactorExecution.run input).queryWork:ℝ) ≤
        (wireCount N+1:ℕ)*(⌈R⌉₊:ℝ):=by exact_mod_cast hq
    apply hq'.trans
    apply (mul_le_mul hw hceil (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add (by norm_num:0<(2:ℝ))]
    congr 1
    push_cast
    ring
  have hsum:=add_rate (localConstant 1 1+C+1) (localConstant A d) B hB
  have hwork:(SemiprimeD1WordTapePublicReport.work input:ℝ) ≤
      (2:ℝ)^(((localConstant 1 1+C+1:ℕ):ℝ)*B)+(2:ℝ)^((localConstant A d:ℝ)*B):=by
    unfold SemiprimeD1WordTapePublicReport.work
    dsimp only
    push_cast at hqR hrec ⊢
    linarith only [hqR,hrec]
  exact hwork.trans hsum

end
end RiemannGaussian.SemiprimeD1WordTapePublicRate
