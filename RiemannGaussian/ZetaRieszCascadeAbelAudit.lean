/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeWindowLocalization
import RiemannGaussian.ZetaRieszParityWindow
import RiemannGaussian.RosserSchoenfeldLargeChebyshev

/-!
# Source-scale audit of absolute-variation Abel transport

The phase is retained inside the test function. Its derivative nevertheless
costs at least `|y|` times the amplitude when a pointwise Chebyshev error is
paired with absolute variation. The corresponding inverse-log allowance
grows at source scale even inside the retained core window. This is a
quantitative obstruction to that error estimate, not a lower bound for the
actual signed prime error or a disproof of all-count arithmetic cancellation.
-/

namespace RiemannGaussian.ZetaRieszCascadeAbelAudit
noncomputable section
open Filter MeasureTheory Set Topology

/-- Keeping the phase does not remove its cost from absolute variation.
The amplitude derivative is real and cannot cancel the imaginary phase derivative. -/
theorem phase_derivative_cost (a a' y t : ℝ) :
    |y| * |a| ≤ ‖((a' : ℂ)-Complex.I*y*a)*Complex.exp (-Complex.I*y*t)‖ := by
  have hp : ‖Complex.exp (-Complex.I*y*t)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [norm_mul, hp, mul_one]
  have h := Complex.abs_im_le_norm ((a' : ℂ)-Complex.I*y*a)
  simpa [abs_mul] using h

/-- Actual derivative of a real amplitude with the full fixed phase. -/
theorem hasDerivAt_phased {a : ℝ → ℝ} {a' t : ℝ} (ha : HasDerivAt a a' t) (y : ℝ) :
    HasDerivAt (fun x : ℝ => (a x : ℂ)*Complex.exp (-Complex.I*y*x))
      (((a' : ℂ)-Complex.I*y*a t)*Complex.exp (-Complex.I*y*t)) t := by
  have hh := ha.ofReal_comp.mul
    (((hasDerivAt_id t).ofReal_comp.const_mul (-Complex.I*y)).cexp)
  apply hh.congr_deriv
  simp only [id_eq, Complex.ofReal_one, mul_one]
  ring

/-- The factorial amplitude after the continuous prime density has been inserted. -/
def factorialEnvelope (N : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t/2)*t^N/(N.factorial : ℝ)

theorem factorialEnvelope_nonneg (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ factorialEnvelope N t := by unfold factorialEnvelope; positivity

/-- A unit interval around the saddle already retains the exponential
mass. No part outside the proved core window is used. -/
theorem factorialEnvelope_unit_lower {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : 2*(N : ℝ) ≤ t) (ht' : t ≤ 2*N+1) :
    Real.exp (-(1/2 : ℝ))*2^N/(6*N) ≤ factorialEnvelope N t := by
  have hbase := PrimeWindow.local_monomial_lower hN (by norm_num : (0 : ℝ) ≤ 2)
  have hgrowth : PrimeWindow.localGrowth 2 = 2 := by norm_num [PrimeWindow.localGrowth]
  rw [hgrowth] at hbase
  have hpow : (2*(N : ℝ))^N ≤ t^N := pow_le_pow_left₀ (by positivity) ht N
  have he : Real.exp (-(1/2 : ℝ))*Real.exp (-(2*(N : ℝ))/2) ≤ Real.exp (-t/2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (-(1/2 : ℝ))).le
  calc
    _ = Real.exp (-(1/2 : ℝ))*(2^N/(6*(N : ℝ))) := by ring
    _ ≤ Real.exp (-(1/2 : ℝ))*(Real.exp (-(2*(N : ℝ))/2)*
        (2*(N : ℝ))^N/(N.factorial : ℝ)) := hmul
    _ ≤ factorialEnvelope N t := by
      unfold factorialEnvelope
      rw [← mul_div_assoc, ← mul_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul he hpow (by positivity) (Real.exp_pos _).le) (by positivity)

/-- The first inverse-log Chebyshev allowance on exactly the retained window. -/
def coreLogAllowance (N : ℕ) : ℝ :=
  ∫ t : ℝ in (39/20 : ℝ)*N..(203/100 : ℝ)*N, factorialEnvelope N t/t

private theorem intervalIntegrable_envelope_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (N : ℕ) : IntervalIntegrable (fun t => factorialEnvelope N t/t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div (by unfold factorialEnvelope; fun_prop) continuousOn_id
  intro t ht
  exact (ha.trans_le ht.1).ne'

/-- Quantitative lower bound for that allowance, wholly inside the core. -/
theorem coreLogAllowance_lower {N : ℕ} (hN : 34 ≤ N) :
    Real.exp (-(1/2 : ℝ))*2^N/(6*N*(2*N+1)) ≤ coreLogAllowance N := by
  have hNR : (34 : ℝ) ≤ N := by exact_mod_cast hN
  have hNl : 1 ≤ N := by omega
  have hint := intervalIntegrable_envelope_div (by linarith : 0 < 2*(N : ℝ))
    (by linarith : 2*(N : ℝ) ≤ 2*N+1) N
  have hcore := intervalIntegrable_envelope_div (by linarith : 0 < (39/20 : ℝ)*N)
    (by linarith : (39/20 : ℝ)*N ≤ (203/100 : ℝ)*N) N
  have hpoint (t : ℝ) (ht : t ∈ Icc (2*(N : ℝ)) (2*N+1)) :
      Real.exp (-(1/2 : ℝ))*2^N/(6*N*(2*N+1)) ≤ factorialEnvelope N t/t := by
    have ht0 : 0 < t := by linarith [ht.1]
    calc
      _ = (Real.exp (-(1/2 : ℝ))*2^N/(6*(N : ℝ)))/(2*N+1) := by rw [div_div]
      _ ≤ factorialEnvelope N t/(2*N+1) :=
        div_le_div_of_nonneg_right (factorialEnvelope_unit_lower hNl ht.1 ht.2) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (factorialEnvelope_nonneg N ht0.le) ht0 ht.2
  have hunit := intervalIntegral.integral_mono_on (by linarith : 2*(N : ℝ) ≤ 2*N+1)
    (intervalIntegrable_const) hint hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hunit
  have hinc : (∫ t : ℝ in 2*(N : ℝ)..2*N+1, factorialEnvelope N t/t) ≤
      coreLogAllowance N := by
    apply intervalIntegral.integral_mono_interval (by linarith)
      (by linarith) (by linarith) _ hcore
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    exact div_nonneg (factorialEnvelope_nonneg N ht0) ht0
  have he : 2*(N : ℝ)+1-2*N = 1 := by ring
  rw [he, one_mul] at hunit
  exact hunit.trans hinc

/-- The inverse-log allowance cannot be made source-small by taking N
larger, at any one fixed radius above one half. -/
theorem normalized_coreLogAllowance_tendsto {u : ℝ} (hu : 1/2 < u) :
    Tendsto (fun N : ℕ => u^(N+1)*coreLogAllowance N) atTop atTop := by
  have hu0 : 0 < u := by linarith
  have hrate : 1 < 2*u := by linarith
  have hg := (tendsto_exp_mul_div_rpow_atTop (2 : ℝ) (Real.log (2*u))
    (Real.log_pos hrate)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hg' : Tendsto (fun N : ℕ => (2*u)^N/(N : ℝ)^2) atTop atTop := by
    convert hg using 1
    ext N
    dsimp only [Function.comp_def]
    rw [Real.rpow_two, mul_comm (Real.log (2*u)), Real.exp_nat_mul,
      Real.exp_log (by positivity : 0 < 2*u)]
  have hc : 0 < u*Real.exp (-(1/2 : ℝ))/18 := by positivity
  apply Filter.tendsto_atTop_mono' _ ?_ (hg'.const_mul_atTop hc)
  filter_upwards [eventually_ge_atTop (34 : ℕ)] with N hN
  have hNR : (34 : ℝ) ≤ N := by exact_mod_cast hN
  have hbound := mul_le_mul_of_nonneg_left (coreLogAllowance_lower hN) (pow_nonneg hu0.le (N+1))
  calc
    _ = u^(N+1)*(Real.exp (-(1/2 : ℝ))*2^N/(18*(N : ℝ)^2)) := by
      rw [pow_succ, mul_pow]
      ring
    _ ≤ u^(N+1)*(Real.exp (-(1/2 : ℝ))*2^N/(6*N*(2*N+1))) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu0.le _)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    _ ≤ _ := hbound

/-- The factor |y| from preserving and differentiating the phase leaves
the same growing allowance at every fixed nonzero height. -/
theorem phased_coreLogAllowance_tendsto {u : ℝ} (hu : 1/2 < u)
    {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun N : ℕ => |y| * (u^(N+1)*coreLogAllowance N)) atTop atTop :=
  (normalized_coreLogAllowance_tendsto hu).const_mul_atTop (abs_pos.mpr hy)

/-- The literal factorial/Dirichlet test before insertion of prime density. -/
def primeAbelAmplitude (N : ℕ) (t : ℝ) : ℝ :=
  t^N/(N.factorial : ℝ)*Real.exp (-(3/2 : ℝ)*t)

/-- The real amplitude derivative, kept separate from the phase derivative. -/
def primeAbelAmplitudeSlope (N : ℕ) (t : ℝ) : ℝ :=
  ((N : ℝ)*t^(N-1)-(3/2 : ℝ)*t^N)/(N.factorial : ℝ)*Real.exp (-(3/2 : ℝ)*t)

/-- The smooth factorial test with its full fixed complex phase. -/
def primeAbelTest (N : ℕ) (y t : ℝ) : ℂ :=
  (primeAbelAmplitude N t : ℂ)*Complex.exp (-Complex.I*y*t)

/-- The exact complex derivative charged by absolute-variation Abel bounds. -/
def primeAbelSlope (N : ℕ) (y t : ℝ) : ℂ :=
  ((primeAbelAmplitudeSlope N t : ℂ)-Complex.I*y*primeAbelAmplitude N t)*
    Complex.exp (-Complex.I*y*t)

theorem hasDerivAt_primeAbelTest (N : ℕ) (y t : ℝ) :
    HasDerivAt (primeAbelTest N y) (primeAbelSlope N y t) t := by
  apply hasDerivAt_phased
  have h := (((hasDerivAt_id t).pow N).div_const (N.factorial : ℝ)).mul
    (((hasDerivAt_id t).const_mul (-(3/2 : ℝ))).exp)
  apply h.congr_deriv
  simp only [id_eq, mul_one, Pi.pow_apply]
  unfold primeAbelAmplitudeSlope
  ring

/-- The precise phase derivative term in global Abel transport. -/
theorem primeAbelSlope_cost (N : ℕ) (y : ℝ) {t : ℝ} (ht : 0 < t) :
    |y| * (factorialEnvelope N t/t) ≤ Real.exp t/t*‖primeAbelSlope N y t‖ := by
  have ha : 0 ≤ primeAbelAmplitude N t := by unfold primeAbelAmplitude; positivity
  have h := phase_derivative_cost (primeAbelAmplitude N t) (primeAbelAmplitudeSlope N t) y t
  rw [abs_of_nonneg ha] at h
  have he : Real.exp t*primeAbelAmplitude N t = factorialEnvelope N t := by
    unfold primeAbelAmplitude factorialEnvelope
    have hex : Real.exp t*Real.exp (-(3/2 : ℝ)*t) = Real.exp (-t/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp t*Real.exp (-(3/2 : ℝ)*t))*t^N/(N.factorial : ℝ) := by ring
      _ = _ := by rw [hex]
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ Real.exp t/t)
  change Real.exp t/t*(|y| * primeAbelAmplitude N t) ≤ _ at hh
  calc
    _ = |y| * (Real.exp t*primeAbelAmplitude N t)/t := by rw [he]; ring
    _ = Real.exp t/t*(|y| * primeAbelAmplitude N t) := by ring
    _ ≤ _ := hh

/-- The standard global-Abel absolute-variation allowance using the
proved relative Chebyshev error 41/(100 log x). -/
def coreAbelAllowance (N : ℕ) (y : ℝ) : ℝ :=
  (41/100 : ℝ)*∫ t : ℝ in (39/20 : ℝ)*N..(203/100 : ℝ)*N,
    Real.exp t/t*‖primeAbelSlope N y t‖

theorem coreAbelAllowance_lower {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    (41/100 : ℝ) * |y| * coreLogAllowance N ≤ coreAbelAllowance N y := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hab : (39/20 : ℝ)*N ≤ (203/100 : ℝ)*N := by linarith
  have hl := (intervalIntegrable_envelope_div (by linarith : 0 < (39/20 : ℝ)*N) hab N).const_mul |y|
  have hr : IntervalIntegrable (fun t => Real.exp t/t*‖primeAbelSlope N y t‖) volume
      ((39/20 : ℝ)*N) ((203/100 : ℝ)*N) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.mul
    · apply ContinuousOn.div (by fun_prop) continuousOn_id
      intro t ht
      exact (show 0 < t by linarith [ht.1]).ne'
    · unfold primeAbelSlope primeAbelAmplitude primeAbelAmplitudeSlope
      fun_prop
  have hh := intervalIntegral.integral_mono_on hab hl hr
    (fun t ht => primeAbelSlope_cost N y (by linarith [ht.1]))
  rw [intervalIntegral.integral_const_mul] at hh
  simpa only [coreLogAllowance, coreAbelAllowance, mul_assoc] using
    mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 41/100)

/-- Even the one-logarithm, one-phase derivative allowance diverges
on the actual retained window. Higher-dimensional absolute-variation
bounds must overcome this cost rather than treating 1/N as source-small. -/
theorem normalized_coreAbelAllowance_tendsto {u : ℝ} (hu : 1/2 < u)
    {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun N : ℕ => u^(N+1)*coreAbelAllowance N y) atTop atTop := by
  have ht := (phased_coreLogAllowance_tendsto hu hy).const_mul_atTop
    (by norm_num : (0 : ℝ) < 41/100)
  apply Filter.tendsto_atTop_mono' _ ?_ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hh := mul_le_mul_of_nonneg_left (coreAbelAllowance_lower hN y)
    (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  nlinarith only [hh]

end
end RiemannGaussian.ZetaRieszCascadeAbelAudit
