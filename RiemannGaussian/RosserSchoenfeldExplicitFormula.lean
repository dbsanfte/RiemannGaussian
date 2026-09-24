/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldPrimePrimitive
import RiemannGaussian.RosserSchoenfeldTrivialPrimitive
import RiemannGaussian.ZetaGlobalSignedBudget

/-!
# The actual logarithmically smoothed prime explicit formula

The finite von-Mangoldt sum equals its pole term, the complete nontrivial
zero primitive and the complete trivial-zero correction. Uniqueness of
the absolutely convergent Laplace transform proves the identity without
assuming a contour remainder, prime-error estimate or zero table.
-/

namespace RiemannGaussian.RosserSchoenfeldExplicitFormula
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open RosserSchoenfeldLaplace

/-- The pole contribution and its exact linear correction. -/
def mainTerm (t : ℝ) : ℂ :=
  Complex.exp (t : ℂ)-1-(Complex.log 2+Complex.log Real.pi)*t

/-- The complete spectral expression retains every zero and correction. -/
def spectral (t : ℝ) : ℂ :=
  mainTerm t-RosserSchoenfeldZeroPrimitive.value t+RosserSchoenfeldTrivialPrimitive.value t

private lemma integrable_one {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)) (Ioi 0) := by
  simpa only [zero_mul, Complex.exp_zero, mul_one] using
    (integrable_exponential (s := s) (z := 0) (by simpa using hs))

private lemma integrable_exp {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*Complex.exp (t : ℂ)) (Ioi 0) := by
  simpa only [one_mul] using (integrable_exponential (s := s) (z := 1) (by simpa using hs))

private lemma integrable_linear {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*((Complex.log 2+Complex.log Real.pi)*t))
      (Ioi 0) := by
  have hh := (RosserSchoenfeldPrimeKernel.integrable_time_exponential hs).const_mul
    (Complex.log 2+Complex.log Real.pi)
  apply hh.congr
  filter_upwards with t
  ring

/-- The entire elementary contribution has an absolutely convergent transform. -/
theorem integrable_mainTerm {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*mainTerm t) (Ioi 0) := by
  have hh := ((integrable_exp hs).sub (integrable_one (by linarith : 0 < s.re))).sub
    (integrable_linear (by linarith : 0 < s.re))
  apply hh.congr
  filter_upwards with t
  dsimp only [mainTerm, Pi.sub_apply]
  ring

/-- Exact transform of the elementary pole contribution. -/
theorem transform_mainTerm {s : ℂ} (hs : 1 < s.re) :
    transform s mainTerm = 1/(s*(s-1))-(Complex.log 2+Complex.log Real.pi)/s^2 := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs1 : s-1 ≠ 0 := ne_zero_of_re_pos (by simpa using sub_pos.mpr hs)
  have h0 := transform_exponential (s := s) (z := 0) (by simpa using (show 0 < s.re by linarith))
  have h1 := transform_exponential (s := s) (z := 1) (by simpa using hs)
  simp only [transform, one_mul, zero_mul, Complex.exp_zero, mul_one, sub_zero] at h0 h1
  have ht := RosserSchoenfeldPrimeKernel.integral_hinge
    (s := s) (by linarith : 0 < s.re) (b := 0) (by norm_num)
  simp only [sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at ht
  have he : (fun t : ℝ => Complex.exp (-s*t)*mainTerm t) =
      (fun t : ℝ => Complex.exp (-s*t)*Complex.exp (t : ℂ)-Complex.exp (-s*t)-
        Complex.exp (-s*t)*((Complex.log 2+Complex.log Real.pi)*t)) := by
    funext t
    unfold mainTerm
    ring
  have he' : (fun t : ℝ => Complex.exp (-s*t)*((Complex.log 2+Complex.log Real.pi)*t)) =
      (fun t : ℝ => (Complex.log 2+Complex.log Real.pi)*(Complex.exp (-s*t)*t)) := by
    funext t
    ring
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*Complex.exp (t : ℂ)-
      Complex.exp (-s*t)) (Ioi 0) := by
    apply ((integrable_exp hs).sub (integrable_one (s := s) (by linarith))).congr
    filter_upwards with t
    rfl
  rw [transform, he, integral_sub hi
      (integrable_linear (s := s) (by linarith)),
    integral_sub (integrable_exp hs) (integrable_one (s := s) (by linarith)), he', integral_const_mul,
    h0, h1, ht]
  field_simp
  ring

private theorem xi_log_zero : logDeriv riemannXi 0 =
    -1-(Real.eulerMascheroniConstant : ℂ)/2+Complex.log 2+Complex.log Real.pi/2 := by
  have he : logDeriv riemannXi 0 = -logDeriv riemannXi 1 := by
    have hh : logDeriv riemannXi (1-(1 : ℂ)) = -logDeriv riemannXi 1 := by
      simp only [logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]
    simpa only [sub_self] using hh
  rw [he, RosserSchoenfeldZeroMass.xi_log_one]
  ring

/-- Integrability of the complete spectral expression, with no omitted tail. -/
theorem integrable_spectral {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*spectral t) (Ioi 0) := by
  have hh := ((integrable_mainTerm hs).sub (RosserSchoenfeldZeroPrimitive.integrable_value hs)).add
    (RosserSchoenfeldTrivialPrimitive.integrable_value (by linarith : 0 < s.re))
  apply hh.congr
  filter_upwards with t
  dsimp only [spectral, Pi.sub_apply, Pi.add_apply]
  ring

/-- The complete zero expansion has exactly the actual prime transform. -/
theorem transform_spectral {s : ℂ} (hs : 1 < s.re) :
    transform s spectral = -logDeriv riemannZeta s/s^2 := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs1 : s-1 ≠ 0 := ne_zero_of_re_pos (by simpa using sub_pos.mpr hs)
  have hg := zeta_global_complex_budget hs
  unfold zetaGlobalRegularCorrection at hg
  have hshift : Complex.digamma (1+s/2) = Complex.digamma (s/2)+2/s := by
    have hnot (n : ℕ) : s/2 ≠ -(n : ℂ) := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    simpa only [add_comm, inv_div] using Complex.digamma_apply_add_one (s/2) hnot
  have he : (fun t : ℝ => Complex.exp (-s*t)*spectral t) =
      (fun t : ℝ => Complex.exp (-s*t)*mainTerm t-
        Complex.exp (-s*t)*RosserSchoenfeldZeroPrimitive.value t+
        Complex.exp (-s*t)*RosserSchoenfeldTrivialPrimitive.value t) := by
    funext t
    unfold spectral
    ring
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*mainTerm t-
      Complex.exp (-s*t)*RosserSchoenfeldZeroPrimitive.value t) (Ioi 0) := by
    apply ((integrable_mainTerm hs).sub (RosserSchoenfeldZeroPrimitive.integrable_value hs)).congr
    filter_upwards with t
    rfl
  rw [transform, he, integral_add
      hi
      (RosserSchoenfeldTrivialPrimitive.integrable_value (s := s) (by linarith)),
    integral_sub (integrable_mainTerm hs) (RosserSchoenfeldZeroPrimitive.integrable_value hs)]
  change transform s mainTerm-transform s RosserSchoenfeldZeroPrimitive.value+
    transform s RosserSchoenfeldTrivialPrimitive.value = _
  rw [transform_mainTerm hs, RosserSchoenfeldZeroPrimitive.transform_value hs,
    RosserSchoenfeldTrivialPrimitive.transform_value (by linarith), xi_log_zero, hshift]
  have hxi : logDeriv riemannXi s = logDeriv riemannZeta s+
      (1/(s-1)+(1/s-Complex.log Real.pi/2+Complex.digamma (s/2)/2)) := by
    linear_combination hg
  rw [hxi]
  field_simp
  ring

/-- Continuity of the complete spectral side on positive logarithmic time. -/
theorem continuousOn_spectral : ContinuousOn spectral (Ioi 0) :=
  (((show Continuous mainTerm by unfold mainTerm; fun_prop).continuousOn.sub
    RosserSchoenfeldZeroPrimitive.continuousOn_value).add
      (RosserSchoenfeldTrivialPrimitive.continuousOn_value.mono Ioi_subset_Ici_self))

/-- The unconditional smoothed explicit formula for the literal finite prime sum. -/
theorem prime_eq_spectral {t : ℝ} (ht : 0 ≤ t) :
    (RosserSchoenfeldPrimePrimitive.value t : ℂ) = spectral t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [spectral, mainTerm]
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-(2 : ℂ)*t)*
      ((RosserSchoenfeldPrimePrimitive.value t : ℂ)-spectral t)) (Ioi 0) := by
    apply ((RosserSchoenfeldPrimePrimitive.integrable_value (s := 2) (by norm_num)).sub
      (integrable_spectral (s := 2) (by norm_num))).congr
    filter_upwards with t
    dsimp only [Pi.sub_apply]
    ring
  have hc : ContinuousOn (fun t : ℝ =>
      (RosserSchoenfeldPrimePrimitive.value t : ℂ)-spectral t) (Ioi 0) :=
    (Complex.continuous_ofReal.comp RosserSchoenfeldPrimePrimitive.continuous_value).continuousOn.sub
      continuousOn_spectral
  have hz (y : ℝ) : transform ((2 : ℂ)+(y : ℂ)*I) (fun t : ℝ =>
      (RosserSchoenfeldPrimePrimitive.value t : ℂ)-spectral t) = 0 := by
    have hs : 1 < ((2 : ℂ)+(y : ℂ)*I).re := by simp
    simp only [transform, mul_sub]
    rw [integral_sub (RosserSchoenfeldPrimePrimitive.integrable_value hs) (integrable_spectral hs)]
    change transform _ (fun t => (RosserSchoenfeldPrimePrimitive.value t : ℂ))-
      transform _ spectral = 0
    rw [RosserSchoenfeldPrimePrimitive.transform_value hs, transform_spectral hs, sub_self]
  exact sub_eq_zero.mp (zero_of_vertical_transform (a := 2) hi hc hz ht)

/-- Evaluated unconditional error bound for the actual smoothed prime sum.
The exact signed zero expansion is retained separately in `prime_eq_spectral`. -/
theorem norm_prime_sub_main_lt {t : ℝ} (ht : 0 ≤ t) :
    ‖(RosserSchoenfeldPrimePrimitive.value t : ℂ)-mainTerm t‖ <
      (463/10000 : ℝ)*(Real.exp t+1)+Real.pi^2/24 := by
  have he : (RosserSchoenfeldPrimePrimitive.value t : ℂ)-mainTerm t =
      -RosserSchoenfeldZeroPrimitive.value t+RosserSchoenfeldTrivialPrimitive.value t := by
    rw [prime_eq_spectral ht]
    unfold spectral
    ring
  rw [he]
  calc
    _ ≤ ‖RosserSchoenfeldZeroPrimitive.value t‖+‖RosserSchoenfeldTrivialPrimitive.value t‖ := by
      simpa only [norm_neg] using norm_add_le
        (-RosserSchoenfeldZeroPrimitive.value t) (RosserSchoenfeldTrivialPrimitive.value t)
    _ < _ := add_lt_add_of_lt_of_le (RosserSchoenfeldZeroPrimitive.norm_value_lt ht)
      (RosserSchoenfeldTrivialPrimitive.norm_value_le ht)

/-- The elementary contribution in the usual real normalization. -/
theorem mainTerm_eq (t : ℝ) : mainTerm t =
    ((Real.exp t-1-Real.log (2*Real.pi)*t : ℝ) : ℂ) := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  unfold mainTerm
  push_cast
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_log Real.pi_pos.le]
  rfl

/-- The actual arithmetic side at a real prime cutoff. -/
theorem value_log_eq {x : ℝ} (hx : 0 < x) :
    RosserSchoenfeldPrimePrimitive.value (Real.log x) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n*Real.log (x/n) := by
  rw [RosserSchoenfeldPrimePrimitive.value_eq_sum, Real.exp_log hx]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
  rw [Real.log_div hx.ne' hn0]

/-- The explicit formula for the literal prime-power sum at every real cutoff `x >= 1`. -/
theorem finite_prime_explicitFormula {x : ℝ} (hx : 1 ≤ x) :
    ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n*Real.log (x/n) : ℝ) : ℂ) =
      ((x-1-Real.log (2*Real.pi)*Real.log x : ℝ) : ℂ)-
        RosserSchoenfeldZeroPrimitive.value (Real.log x)+
        RosserSchoenfeldTrivialPrimitive.value (Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hh := prime_eq_spectral (Real.log_nonneg hx)
  simpa only [value_log_eq hx0, spectral, mainTerm_eq, Real.exp_log hx0] using hh

/-- An evaluated real error bound for the actual finite smoothed prime sum. -/
theorem abs_finite_prime_sub_main_lt {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n*Real.log (x/n))-
      (x-1-Real.log (2*Real.pi)*Real.log x)| <
        (463/10000 : ℝ)*(x+1)+Real.pi^2/24 := by
  have hx0 : 0 < x := by linarith
  have hh := norm_prime_sub_main_lt (Real.log_nonneg hx)
  simpa only [value_log_eq hx0, mainTerm_eq, Real.exp_log hx0, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hh

end
end RiemannGaussian.RosserSchoenfeldExplicitFormula
