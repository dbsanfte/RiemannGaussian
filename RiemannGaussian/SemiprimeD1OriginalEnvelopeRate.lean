/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalCallRate
import RiemannGaussian.SemiprimeD1LeafRate

/-! # Quantitative absorption of the whole-call resource envelope
The literal resource factor has its leaf enumeration, full-table exponent and
context polynomial all present. The actual original call count is also present,
with a cubic multiplicity reserve. This converts that numeric envelope to the
requested original-input rate; it does not assert that any unjoined program
or machine already satisfies the envelope.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalEnvelopeRate
open Filter SemiprimeD1PackingReady SemiprimeD1OriginalCallRate
open SemiprimeD1OriginalCallBounds SemiprimeD1OriginalStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1Schedule
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open scoped Topology

/-- Actual polynomial resource scalar, before the leaf and table exponents. -/
def scalar (s : ℕ) : ℕ := 2^((logarithm s+1)^3)

/-- Fixed local polynomial with actual full-table and stopped-leaf exponents. -/
def localEnvelope (C k s : ℕ) : ℕ :=
  C*(scalar s+1)^k*2^(C*degreeCap s+leafSize s (logarithm s))

/-- Whole-call bound retaining the actual count and a cubic aggregation reserve. -/
def envelope (C k s calls : ℕ) : ℕ := localEnvelope C k s*(calls+1)^3

/-- A fixed explicit binary exponent pays every local factor. -/
theorem localEnvelope_pow (C k s : ℕ) :
    localEnvelope C k s   ≤
      2^(C+((logarithm s+1)^3+1)*k+C*degreeCap s+leafSize s (logarithm s)) := by
  have hC:C  ≤  2^C:=Nat.le_of_lt (Nat.lt_two_pow_self)
  have hscalar:scalar s+1  ≤  2^((logarithm s+1)^3+1):=by
    unfold scalar
    have h:=Nat.one_le_two_pow (n:=(logarithm s+1)^3)
    calc
      _  ≤  2^((logarithm s+1)^3)*2 := by omega
      _ = _ := by rw [pow_add,pow_one]
  calc
    _   ≤   2^C*(2^((logarithm s+1)^3+1))^k*
        2^(C*degreeCap s+leafSize s (logarithm s)) := by
      unfold localEnvelope
      gcongr
    _ = _ := by rw [←pow_mul,←pow_add,←pow_add];congr 1;ring

noncomputable section

/-- The exact original input scale is at least one beyond two bits. -/
theorem inputScale_ge_one (ell : ℕ) (hell : 2  ≤  ell) : 1  ≤  inputScale ell := by
  have hellR:(2:ℝ)  ≤  ell:=by exact_mod_cast hell
  have hlog:0<Real.log (ell+2:ℕ):=Real.log_pos (by exact_mod_cast (by omega:1<ell+2))
  have hbound:=Real.log_le_sub_one_of_pos (show (0:ℝ)<(ell+2:ℕ) by positivity)
  have hsqrt:Real.sqrt (Real.log (ell+2:ℕ))  ≤  (ell:ℝ):=by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast at hbound ⊢
    nlinarith
  unfold inputScale
  exact (one_le_div (Real.sqrt_pos.mpr hlog)).mpr hsqrt

/-- The actual local resource exponent fits the main rate with fixed constants. -/
theorem localEnvelope_rate (C k s : ℕ)
    (haux:((degreeCap s+(logarithm s+1)^3:ℕ):ℝ)  ≤  2*mainScale s)
    (hleaf:(leafSize s (logarithm s):ℝ)  ≤  mainScale s+1)
    (hmain:1  ≤  mainScale s) :
    (localEnvelope C k s:ℝ)  ≤  (2:ℝ)^(((3*C+3*k+2:ℕ):ℝ)*mainScale s) := by
  have hnat:=localEnvelope_pow C k s
  have hreal:(localEnvelope C k s:ℝ)  ≤
      (2:ℝ)^((C+((logarithm s+1)^3+1)*k+C*degreeCap s+
        leafSize s (logarithm s):ℕ):ℝ):=by
    simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using
      (show (localEnvelope C k s:ℝ)  ≤
        (2^(C+((logarithm s+1)^3+1)*k+C*degreeCap s+
          leafSize s (logarithm s)):ℕ) by exact_mod_cast hnat)
  apply hreal.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
  have hd:(degreeCap s:ℝ)  ≤  2*mainScale s:=by
    push_cast at haux
    linarith [show (0:ℝ)  ≤  ((logarithm s:ℝ)+1)^3 by positivity]
  have hg:(((logarithm s+1)^3:ℕ):ℝ)  ≤  2*mainScale s:=by
    push_cast at haux ⊢
    linarith [show (0:ℝ)  ≤  degreeCap s by positivity]
  have hkmul:=mul_le_mul_of_nonneg_right hg (show (0:ℝ)  ≤  k by positivity)
  have hCmul:=mul_le_mul_of_nonneg_left hd (show (0:ℝ)  ≤  C by positivity)
  have hCmain:=mul_le_mul_of_nonneg_left hmain (show (0:ℝ)  ≤  C by positivity)
  have hkmain:=mul_le_mul_of_nonneg_left hmain (show (0:ℝ)  ≤  k by positivity)
  push_cast at hkmul ⊢
  nlinarith

/-- Uniform explicit exponent constant for this numeric whole-call envelope. -/
def rateConstant (C k : ℕ) : ℕ :=
  1048576*(3*C+3*k+2)+3*callConstant+3

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
    (hcalls:(calls:ℝ)  ≤  (2:ℝ)^((callConstant:ℝ)*inputScale ell)) :
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
  have hone:(1:ℝ)  ≤  (2:ℝ)^((callConstant:ℝ)*inputScale ell):=
    Real.one_le_rpow (by norm_num) (by unfold inputScale;positivity)
  have hplus:(calls:ℝ)+1  ≤  (2:ℝ)^((callConstant:ℝ)*inputScale ell+1):=by
    rw [Real.rpow_add (by norm_num:0<(2:ℝ)),Real.rpow_one]
    linarith
  have hcub:=pow_le_pow_left₀ (by positivity:(0:ℝ)  ≤  (calls:ℝ)+1) hplus 3
  have hprod:=mul_le_mul hlocal' hcub (by positivity) (by positivity)
  have hpow:((2:ℝ)^((callConstant:ℝ)*inputScale ell+1))^3=
      (2:ℝ)^(3*((callConstant:ℝ)*inputScale ell+1)):=by
    rw [←Real.rpow_mul_natCast (by norm_num:0 ≤ (2:ℝ))]
    congr 1
    ring
  rw [hpow,←Real.rpow_add (by norm_num:0<(2:ℝ))] at hprod
  have hprod':(envelope C k (SemiprimeD1PublicPackingReady.scale ell) calls:ℝ)  ≤
      (2:ℝ)^((1048576*(3*C+3*k+2:ℕ):ℝ)*inputScale ell+
        3*((callConstant:ℝ)*inputScale ell+1)):=by
    simpa only [envelope,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hprod
  apply hprod'.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
  unfold rateConstant
  push_cast
  nlinarith

/-- The actual rounded main scale is eventually at least one. -/
theorem eventually_mainScale_ge_one : ∀ᶠ s:ℕ in atTop,1  ≤  mainScale s := by
  have ht:Tendsto logarithm atTop atTop:=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [SemiprimeD1AuxiliaryRate.eventually_log_power 1,
    ht.eventually (eventually_ge_atTop (1:ℕ))] with s hs hl
  have hlR:(1:ℝ)  ≤  logarithm s:=by exact_mod_cast hl
  have hsR:(logarithm s:ℝ)  ≤  s:=by
    exact_mod_cast (show logarithm s  ≤  s by simpa only [pow_one] using hs)
  have hroot:Real.sqrt (logarithm s:ℕ)  ≤  (logarithm s:ℝ):=by
    nlinarith [Real.sq_sqrt (show (0:ℝ)  ≤  logarithm s by positivity),
      Real.sqrt_nonneg (logarithm s:ℕ)]
  unfold mainScale
  exact (one_le_div (Real.sqrt_pos.mpr (by positivity))).mpr (hroot.trans hsR)

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
  filter_upwards [eventually_original_call_rate,
    scale_tendsto.eventually SemiprimeD1AuxiliaryRate.eventually_auxiliary_rate,
    scale_tendsto.eventually eventually_mainScale_ge_one,
    (ht.comp scale_tendsto).eventually (eventually_ge_atTop (1:ℕ)),
    eventually_ge_atTop (2:ℕ)] with ell hcalls haux hmain hl hell
  intro N hN hEll fixed fuel
  change 1 ≤ logarithm (SemiprimeD1PublicPackingReady.scale ell) at hl
  have hcalls':(count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ)  ≤
      (2:ℝ)^((callConstant:ℝ)*inputScale ell):=by
    simpa only [inputScale,mul_div_assoc] using hcalls N hN hEll fixed fuel
  apply envelope_rate C k ell _ hmain _ _ (inputScale_ge_one ell hell) hcalls'
  · simpa only [mainScale,mul_div_assoc] using haux
  · simpa only [mainScale] using SemiprimeD1LeafRate.leafSize_real
      (SemiprimeD1PublicPackingReady.scale ell) (logarithm (SemiprimeD1PublicPackingReady.scale ell))
      (by omega)

end
end RiemannGaussian.SemiprimeD1OriginalEnvelopeRate
