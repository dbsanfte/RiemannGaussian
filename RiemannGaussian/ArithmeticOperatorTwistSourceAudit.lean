/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCommutatorAudit
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import RiemannGaussian.EtaZetaPrimeProduct
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Source-sensitive linear twist commutator and its scalar-collapse gate

The prime-leg-only discrepancy retains the actual matched zero residue,
unlike the fully phased Gamma convolution. Its literal cutoff still joins
to one complex kernel against arbitrary denominator weights. Retaining the
source is therefore not an independent arithmetic estimate. The nonlinear
successor discrepancy is NOT covered by this linear collapse theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorTwistSourceAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorCommutatorAudit ArithmeticOperatorDilationAudit
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Full cofactor-phase defect for arbitrary denominator data. -/
def defect (w : ℕ → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  divisorConvolution (fun d => w d*primePhase y d) (fun a => 1-primePhase y a) n

/-- Exact literal cutoff of the defect, with every prime power retained
at its actual Mangoldt specialization. -/
def cutoffDefect (w : ℕ → ℂ) (y : ℝ) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, defect w y n

/-- The fully joined scalar kernel includes the entire quotient fiber. -/
def defectKernel (y : ℝ) (X d : ℕ) : ℂ :=
  primePhase y d*prefixSum (fun a => 1-primePhase y a) (X/d)

theorem defect_eq_commutator (y : ℝ) (n : ℕ) :
    defect (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y n =
      twistCommutator (primePhase y) n := by
  unfold defect divisorConvolution twistCommutator
  rw [Nat.sum_divisorsAntidiagonal (fun d a =>
    (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*(1-primePhase y a))]

/-- All finite scalar bookkeeping survives replacement by arbitrary
complex weights. This is the collapse, not an actual-prime inequality. -/
theorem cutoffDefect_eq_scalar (w : ℕ → ℂ) (y : ℝ) (X : ℕ) :
    cutoffDefect w y X = ∑ d ∈ Finset.Icc 1 X, w d*defectKernel y X d := by
  change cutoffConvolution (fun d => w d*primePhase y d)
    (fun a => 1-primePhase y a) X = _
  rw [cutoffConvolution_eq_quotient]
  exact Finset.sum_congr rfl (fun d _ => by unfold defectKernel; ring)

/-- A free-weight upper bound cannot follow from the finite identities
unless the complete joined kernel is zero. Actual Mangoldt data are not
being replaced in any claimed arithmetic estimate. -/
theorem cutoffDefect_bound_forall_weights_iff (y : ℝ) (X : ℕ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖cutoffDefect w y X‖ ≤ B) ↔
      0 ≤ B ∧ ∀ d ∈ Finset.Icc 1 X, defectKernel y X d = 0 := by
  simp_rw [cutoffDefect_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

private theorem primeLeg_eq_convolution (y : ℝ) :
    primeLegDivisor (primePhase y) = LSeries.convolution
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) (1 : ℕ → ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  simp only [primeLegDivisor, Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun d _ =>
    (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)]

private theorem coupled_eq_convolution (y : ℝ) :
    coupledDivisor (primePhase y) = LSeries.convolution
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) (primePhase y) := by
  funext n
  rw [LSeries.convolution_def]
  unfold coupledDivisor
  dsimp
  rw [Nat.sum_divisorsAntidiagonal (fun d a =>
    (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*primePhase y a)]

/-- Actual prime-only divisor data have a genuine convergent Euler
response. Its cofactor zeta factor is unshifted, and must not be confused
with the source-annihilating fully phased Gamma evaluation. -/
theorem primeLeg_euler_response (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeLegDivisor (primePhase y)) s =
      riemannZeta s*(-logDeriv riemannZeta (s+I*y)) := by
  have ht : 1 < (s+I*y).re := by simpa using hs
  have hf := (LSeriesSummable_primePhase_iff
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) y s).mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt ht)
  rw [primeLeg_eq_convolution, LSeries_convolution' hf (LSeriesSummable_one_iff.mpr hs),
    LSeries_primePhase, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div ht,
    LSeries_one_eq_riemannZeta hs]
  simp only [logDeriv_apply, neg_div]
  ring

/-- The linear commutator's Euler continuation, with both contributions
joined and genuine absolute convergence before continuation. -/
theorem commutator_euler_response (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistCommutator (primePhase y)) s =
      riemannZeta s*(-logDeriv riemannZeta (s+I*y))+deriv riemannZeta (s+I*y) := by
  have ht : 1 < (s+I*y).re := by simpa using hs
  have hf := (LSeriesSummable_primePhase_iff
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) y s).mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt ht)
  have hp : LSeriesSummable (primeLegDivisor (primePhase y)) s := by
    rw [primeLeg_eq_convolution]
    exact hf.convolution (LSeriesSummable_one_iff.mpr hs)
  have ho : LSeriesSummable (primePhase y) s := by
    have hh := (LSeriesSummable_primePhase_iff (1 : ℕ → ℂ) y s).mpr
      (LSeriesSummable_one_iff.mpr ht)
    simpa only [Pi.one_apply, one_mul] using hh
  have hc : LSeriesSummable (coupledDivisor (primePhase y)) s := by
    rw [coupled_eq_convolution]
    exact hf.convolution ho
  have he : twistCommutator (primePhase y) =
      primeLegDivisor (primePhase y)-coupledDivisor (primePhase y) :=
    funext (fun n => (primeLegDivisor_sub_coupled (primePhase y) n).symm)
  rw [he, LSeries_sub hp hc, primeLeg_euler_response y hs,
    coupled_series_eq_shifted_derivative hs y, sub_neg_eq_add]

/-- Exact continuation in the original zeta coordinate. -/
def response (y : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (z-I*y)*(-logDeriv riemannZeta z)+deriv riemannZeta z

/-- The real strip has no zeta zeros, using the existing positive eta
mass theorem rather than any RH premise. -/
theorem real_strip_zeta_ne_zero {beta : ℝ} (hb0 : 0 < beta) (hb1 : beta < 1) :
    riemannZeta (beta : ℂ) ≠ 0 := by
  intro hz
  let rho : NontrivialZetaZero := ⟨(beta : ℂ), hz, by
    rintro ⟨n, hn⟩
    have hh := congrArg Complex.re hn
    norm_num [Complex.mul_re] at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) n], by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith⟩
  exact NontrivialZetaZero.im_ne_zero_of_eta_mass rho (by rfl)

/-- Every actual zero leaves a nonzero matched residue in the linear
prime-leg commutator. The analytic multiplicity is retained exactly. -/
theorem tendsto_commutator_source (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*response rho.1.im z) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ))) := by
  have he : rho.1-I*rho.1.im = (rho.1.re : ℂ) := by apply Complex.ext <;> simp
  have hb : (rho.1.re : ℂ) ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hc : ContinuousAt (fun z : ℂ => riemannZeta (z-I*rho.1.im)) rho.1 := by
    have ha := analyticOn_riemannZeta (rho.1-I*rho.1.im) (by rwa [he])
    exact ContinuousAt.comp' (f := fun z : ℂ => z-I*rho.1.im) (g := riemannZeta)
      (x := rho.1) ha.continuousAt
      (show ContinuousAt (fun z : ℂ => z-I*rho.1.im) rho.1 from
        (continuous_id.sub continuous_const).continuousAt)
  have hz : Tendsto (fun z : ℂ => riemannZeta (z-I*rho.1.im)) (𝓝[≠] rho.1)
      (𝓝 (riemannZeta (rho.1-I*rho.1.im))) := hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [he] at hz
  have hl := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg
  have hd : Tendsto (deriv riemannZeta) (𝓝[≠] rho.1) (𝓝 (deriv riemannZeta rho.1)) :=
    (analyticAt_riemannZeta_nontrivialZero rho).deriv.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hsub : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht := (hl.mul hz).add (hsub.mul hd)
  simp only [zero_mul, add_zero] at ht
  simp only [analyticZetaZeroMultiplicity]
  convert ht using 1
  funext z
  unfold response
  ring

theorem commutator_source_ne_zero (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ) ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))))
    (real_strip_zeta_ne_zero (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho))

/-- Exact dilation eigenvalue of a power mode. -/
def scaleRoot (s : ℂ) : ℂ := Complex.exp (s*(Real.log 2 : ℂ))

/-- The cubic `(D-scaleRoot(p))^2*(D-scaleRoot(q))`. The repeated
root removes the logarithmic companion of the first density channel. -/
def poleCode (p q : ℂ) (i : ℕ) : ℂ :=
  if i = 0 then -(scaleRoot p)^2*scaleRoot q
  else if i = 1 then (scaleRoot p)^2+2*scaleRoot p*scaleRoot q
  else if i = 2 then -(2*scaleRoot p+scaleRoot q)
  else if i = 3 then 1 else 0

theorem poleCode_polynomial (p q b : ℂ) :
    (∑ i ∈ Finset.range 4, poleCode p q i*b^i) =
      (b-scaleRoot p)^2*(b-scaleRoot q) := by
  norm_num [Finset.sum_range_succ, poleCode]
  ring

theorem poleCode_repeated_root (p q : ℂ) :
    (∑ i ∈ Finset.range 4, poleCode p q i*(i : ℂ)*(scaleRoot p)^i) = 0 := by
  norm_num [Finset.sum_range_succ, poleCode]
  ring

private theorem powerResponse_dyadic {H : ℝ} (hH : 0 < H) (s : ℂ) (i : ℕ) :
    powerResponse s ((2 : ℝ)^i*H) = (scaleRoot s)^i*powerResponse s H := by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [pow_succ, show (2 : ℝ)^i*2*H = 2*((2 : ℝ)^i*H) by ring,
      powerResponse_two_scale (by positivity), hi, pow_succ]
    unfold scaleRoot
    ring

/-- The entire diagnostic source/pole code is joined before taking a
norm. This equality is exact, with no phase or endpoint approximation. -/
theorem coded_power_response {H : ℝ} (hH : 0 < H) (p q s : ℂ) :
    (∑ i ∈ Finset.range 4, poleCode p q i*powerResponse s ((2 : ℝ)^i*H)) =
      (scaleRoot s-scaleRoot p)^2*(scaleRoot s-scaleRoot q)*powerResponse s H := by
  simp_rw [powerResponse_dyadic hH, ← mul_assoc]
  rw [← Finset.sum_mul, poleCode_polynomial]

/-- Simple density mode at the second root cancels exactly. -/
theorem coded_density_response {H : ℝ} (hH : 0 < H) (p q : ℂ) :
    (∑ i ∈ Finset.range 4, poleCode p q i*powerResponse q ((2 : ℝ)^i*H)) = 0 := by
  rw [coded_power_response hH]
  simp

/-- A repeated density pole also has a logarithmic power companion.
Both are killed by the same finite code, without touching the source. -/
theorem coded_log_density_response {H : ℝ} (hH : 0 < H) (p q : ℂ) :
    (∑ i ∈ Finset.range 4, poleCode p q i*
      (Real.log ((2 : ℝ)^i*H) : ℂ)*powerResponse p ((2 : ℝ)^i*H)) = 0 := by
  have hlog (i : ℕ) :
      (Real.log ((2 : ℝ)^i*H) : ℂ) = (i : ℂ)*(Real.log 2 : ℂ)+(Real.log H : ℂ) := by
    rw [Real.log_mul (by positivity : (2 : ℝ)^i ≠ 0) hH.ne', Real.log_pow]
    push_cast
    rfl
  simp_rw [hlog, powerResponse_dyadic hH]
  have he (i : ℕ) : poleCode p q i*((i : ℂ)*(Real.log 2 : ℂ)+(Real.log H : ℂ))*
      ((scaleRoot p)^i*powerResponse p H) =
    (poleCode p q i*(i : ℂ)*(scaleRoot p)^i)*(Real.log 2 : ℂ)*powerResponse p H+
      (poleCode p q i*(scaleRoot p)^i)*(Real.log H : ℂ)*powerResponse p H := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul, ← Finset.sum_mul, poleCode_repeated_root, poleCode_polynomial]
  simp

/-- The same code retains every matched source with a different real
exponent, including all actual campaign multiplicities. -/
theorem coded_source_nonzero {H : ℝ} (hH : 0 < H) {p q s v : ℂ}
    (hps : s.re ≠ p.re) (hqs : s.re ≠ q.re) (hv : v ≠ 0) :
    v*(∑ i ∈ Finset.range 4, poleCode p q i*powerResponse s ((2 : ℝ)^i*H)) ≠ 0 := by
  rw [coded_power_response hH]
  exact mul_ne_zero hv (mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (SuzukiCarryPhaseScaleGate.scale_factor_ne_zero hps))
    (SuzukiCarryPhaseScaleGate.scale_factor_ne_zero hqs)) (Complex.exp_ne_zero _))

/-- The density exponents of the actual linear commutator are `1-i*y`
(with its logarithmic companion) and `1`. Their exact diagnostic code
retains the matched residue of every actual nontrivial zero. This is not
an assertion of a literal prime cutoff asymptotic or arithmetic bound. -/
theorem matched_commutator_code_nonzero (rho : NontrivialZetaZero) {H : ℝ} (hH : 0 < H) :
    (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ))*
      (∑ i ∈ Finset.range 4, poleCode (1-I*rho.1.im) 1 i*
        powerResponse (rho.1.re : ℂ) ((2 : ℝ)^i*H)) ≠ 0 := by
  apply coded_source_nonzero hH
  · simp only [Complex.ofReal_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.one_re, mul_zero, zero_mul, sub_zero]
    exact (NontrivialZetaZero.re_lt_one rho).ne
  · simpa using (NontrivialZetaZero.re_lt_one rho).ne
  · exact commutator_source_ne_zero rho

/-- Actual finite cutoff code; none of its quotient boundaries is
completed into an Euler integral. -/
def codedCutoff (p q : ℂ) (w : ℕ → ℂ) (y : ℝ) (H : ℕ) : ℂ :=
  ∑ i ∈ Finset.range 4, poleCode p q i*cutoffDefect w y (2^i*H)

/-- The full finite signed scalar kernel, including all four masks. -/
def codedKernel (p q : ℂ) (y : ℝ) (H d : ℕ) : ℂ :=
  ∑ i ∈ Finset.range 4, poleCode p q i*
    (if d ≤ 2^i*H then defectKernel y (2^i*H) d else 0)

private theorem cutoffDefect_extended {X Y : ℕ} (hXY : X ≤ Y) (w : ℕ → ℂ) (y : ℝ) :
    cutoffDefect w y X = ∑ d ∈ Finset.Icc 1 Y,
      w d*(if d ≤ X then defectKernel y X d else 0) := by
  classical
  have he : (Finset.Icc 1 Y).filter (fun d => d ≤ X) = Finset.Icc 1 X := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [cutoffDefect_eq_scalar]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, he]

/-- Pole centering has not rescued the linear interaction from its
arbitrary-weight scalar collapse. All masks/phases remain exact. -/
theorem codedCutoff_eq_scalar (p q : ℂ) (w : ℕ → ℂ) (y : ℝ) (H : ℕ) :
    codedCutoff p q w y H = ∑ d ∈ Finset.Icc 1 (8*H), w d*codedKernel p q y H d := by
  unfold codedCutoff
  have hbound (i : ℕ) (h : i ∈ Finset.range 4) : 2^i*H ≤ 8*H := by
    have : i < 4 := Finset.mem_range.mp h
    interval_cases i <;> norm_num <;> omega
  have he : (∑ i ∈ Finset.range 4, poleCode p q i*cutoffDefect w y (2^i*H)) =
      ∑ i ∈ Finset.range 4, poleCode p q i*(∑ d ∈ Finset.Icc 1 (8*H),
        w d*(if d ≤ 2^i*H then defectKernel y (2^i*H) d else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [cutoffDefect_extended (hbound i hi)]
  rw [he]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  unfold codedKernel
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- No bounded estimate uniform in all complex denominator arrays can
be furnished by this source-retaining finite code unless its entire
kernel vanishes. Actual-prime cancellation remains genuinely new input. -/
theorem codedCutoff_bound_forall_weights_iff (p q : ℂ) (y : ℝ) (H : ℕ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖codedCutoff p q w y H‖ ≤ B) ↔
      0 ≤ B ∧ ∀ d ∈ Finset.Icc 1 (8*H), codedKernel p q y H d = 0 := by
  simp_rw [codedCutoff_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

end
end RiemannGaussian.ArithmeticOperatorTwistSourceAudit
