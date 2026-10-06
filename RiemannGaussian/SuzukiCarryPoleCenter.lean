/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryFejer

/-!
# Exact two-scale pole centering for the literal Fejer carry packet

The complex Mellin response uses the unchanged finite triangular weights.
The density mode cancels exactly, without assuming an exact finite-length
scaling law. The scaling defect and the unpaid signed arithmetic kernel
remain explicit. No actual-prime one-zero asymptotic is asserted.
-/

namespace RiemannGaussian.SuzukiCarryPoleCenter
noncomputable section
open Complex MeasureTheory Set
open SuzukiCarryCorrelation SuzukiCarryGram SuzukiCarryGramSource SuzukiCarryFejer
open scoped BigOperators ComplexConjugate

/-- Complex Mellin response of the unchanged finite carry packet. -/
def mellin (S : Finset ℕ) (alpha : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (s*t)*(realMass S alpha t : ℂ)

/-- The complex response is genuinely integrable throughout `Re s>0`. -/
theorem integrable_mellin {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {s : ℂ}
    (hs : 0 < s.re) (hS : ∀ N ∈ S, N ≤ B) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(realMass S alpha t : ℂ)) := by
  have hi := integrable_source (alpha := alpha) hs hS
  apply hi.mono'
    (((Complex.continuous_exp.measurable.comp
      (measurable_const.mul Complex.measurable_ofReal))).mul
      (Complex.measurable_ofReal.comp (measurable_realMass S alpha))).aestronglyMeasurable
  filter_upwards with t
  change ‖Complex.exp (s*t)*(realMass S alpha t : ℂ)‖ ≤
    Real.exp (s.re*t)*realMass S alpha t
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact le_rfl

/-- Restriction to the positive real axis is the previously proved response. -/
theorem mellin_ofReal (S : Finset ℕ) (alpha : ℕ → ℂ) (beta : ℝ) :
    mellin S alpha (beta : ℂ) = (sourceCoefficient S alpha beta : ℂ) := by
  unfold mellin sourceCoefficient
  have he (t : ℝ) : Complex.exp ((beta : ℂ)*t)*(realMass S alpha t : ℂ) =
      ((Real.exp (beta*t)*realMass S alpha t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  simp_rw [he]
  exact integral_complex_ofReal

/-- Twisting a specified logarithmic power density subtracts `i*y` from
its exponent. This is not a single-zero asymptotic of actual primes. -/
theorem twisted_power_response (S : Finset ℕ) (alpha : ℕ → ℂ) (rho : ℂ) (y : ℝ) :
    (∫ t : ℝ, Complex.exp (rho*t)*Complex.exp (-(I*y)*t)*
      (realMass S alpha t : ℂ)) = mellin S alpha (rho-I*y) := by
  unfold mellin
  congr 1
  funext t
  rw [← Complex.exp_add]
  congr 2
  ring

/-- The density/pole mode after the literal fixed-height twist. -/
def poleExponent (y : ℝ) : ℂ := 1-I*y

/-- The literal Fejer weights at their growing location `A=H`. -/
def weight (H d : ℕ) : ℝ :=
  packetMass (Finset.range (H+2*H)) (coefficient H H) d

/-- The same kernel in the continuous denominator variable. -/
def realWeight (H : ℕ) (t : ℝ) : ℝ :=
  realMass (Finset.range (H+2*H)) (coefficient H H) t

/-- Exact finite-length complex response, with no continuum replacement. -/
def C (H : ℕ) (s : ℂ) : ℂ :=
  mellin (Finset.range (H+2*H)) (coefficient H H) s

/-- Complete literal prime-power Fejer statistic. -/
def Q (H : ℕ) (y : ℝ) : ℂ :=
  fullQuadratic (Finset.range (H+2*H)) (coefficient H H) (primePhase y)

/-- Exact arithmetic endpoint/gcd expansion, before either scale is
estimated. The phase remains inside each divisor observation. -/
theorem Q_eq_gcd_sum (H : ℕ) (y : ℝ) :
    Q H y = ∑ N ∈ Finset.range (H+2*H), ∑ M ∈ Finset.range (H+2*H),
      coefficient H H N*conj (coefficient H H M)*
        (∑ i : Fin 3, ∑ j : Fin 3, ((endpointSign i*endpointSign j : ℝ) : ℂ)*
          divisorPhase (primePhase y) (Nat.gcd (endpoint N i) (endpoint M j))) := by
  unfold Q fullQuadratic
  simp_rw [fullGram_eq_gcd_sum]

/-- The exact integer-denominator packet weight, without a continuous
sampling approximation. -/
theorem weight_eq_value_sq (H d : ℕ) : weight H d = (value H H d)^2 := by
  rw [weight, packetMass, packet_eq_value, Complex.normSq_eq_norm_sq,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A literal regression: finite Fejer weights are not exactly invariant
under simultaneous doubling of packet length and denominator. -/
theorem finite_dilation_mismatch : weight 2 6 ≠ weight 1 3 := by
  rw [weight_eq_value_sq, weight_eq_value_sq]
  norm_num [value, Finset.sum_range_succ, SuzukiIntegerCarry.carry]

/-- The density-canceling determinant with its native, unnormalized scale. -/
def statistic (H : ℕ) (y : ℝ) : ℂ :=
  C (2*H) (poleExponent y)*Q H y-C H (poleExponent y)*Q (2*H) y

/-- Joint response to a specified twisted exponent. -/
def response (H : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  C (2*H) (poleExponent y)*C H s-C H (poleExponent y)*C (2*H) s

/-- The exact density/pole contribution vanishes at every finite length. -/
theorem response_pole_eq_zero (H : ℕ) (y : ℝ) :
    response H y (poleExponent y) = 0 := by
  unfold response
  ring

/-- The pole exponent has real part one; its Mellin integral is genuine. -/
theorem poleExponent_re (y : ℝ) : (poleExponent y).re = 1 := by
  simp [poleExponent]

/-- The real positive matched exponent uses the existing source coefficient. -/
theorem C_ofReal (H : ℕ) (beta : ℝ) :
    C H (beta : ℂ) =
      (sourceCoefficient (Finset.range (H+2*H)) (coefficient H H) beta : ℂ) :=
  mellin_ofReal _ _ _

/-- Exact matched-zero component response; all finite-length corrections
remain inside the two Mellin coefficients. -/
theorem matched_zero_response (H : ℕ) (beta y : ℝ) (m : ℕ) :
    C (2*H) (poleExponent y)*
      (∫ t : ℝ, -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
        Complex.exp (-(I*y)*t)*(realWeight H t : ℂ))-
    C H (poleExponent y)*
      (∫ t : ℝ, -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
        Complex.exp (-(I*y)*t)*(realWeight (2*H) t : ℂ)) =
      -(m : ℂ)*response H y (beta : ℂ) := by
  have he (K : ℕ) :
      (∫ t : ℝ, -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
        Complex.exp (-(I*y)*t)*(realWeight K t : ℂ)) = -(m : ℂ)*C K (beta : ℂ) := by
    rw [show (fun t : ℝ => -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
        Complex.exp (-(I*y)*t)*(realWeight K t : ℂ)) =
      (fun t : ℝ => -(m : ℂ)*(Complex.exp (((beta : ℂ)+I*y)*t)*
        Complex.exp (-(I*y)*t)*(realWeight K t : ℂ))) by funext t; ring]
    rw [integral_const_mul]
    change -(m : ℂ)*(∫ t : ℝ, Complex.exp (((beta : ℂ)+I*y)*t)*
      Complex.exp (-(I*y)*t)*(realMass _ _ t : ℂ)) = _
    rw [twisted_power_response]
    simp only [add_sub_cancel_right]
    rfl
  rw [he H, he (2*H)]
  unfold response
  ring

/-- The finite sampling defect; it is not assumed to be zero or small. -/
def scaleDefect (H : ℕ) (s : ℂ) : ℂ :=
  C (2*H) s-Complex.exp (s*(Real.log 2 : ℂ))*C H s

/-- Exact separation of the ideal dilation factor from the literal
finite-length correction. It does not assume `C_H(s)=kappa(s)*H^s`. -/
theorem response_eq_scaleDefects (H : ℕ) (y : ℝ) (beta : ℝ) :
    response H y (beta : ℂ) =
      (Complex.exp (poleExponent y*(Real.log 2 : ℂ))-
        Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ)))*
          C H (poleExponent y)*C H (beta : ℂ)+
      scaleDefect H (poleExponent y)*C H (beta : ℂ)-
        C H (poleExponent y)*scaleDefect H (beta : ℂ) := by
  unfold response scaleDefect
  ring

/-- The ideal two-scale factor cannot vanish when `beta<1`; the full
finite determinant still requires its explicit sampling defects paid. -/
theorem ideal_scale_factor_norm_lower (beta y : ℝ) :
    2-Real.exp (beta*Real.log 2) ≤
      ‖Complex.exp (poleExponent y*(Real.log 2 : ℂ))-
        Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ))‖ := by
  have h1 : ‖Complex.exp (poleExponent y*(Real.log 2 : ℂ))‖ = 2 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, poleExponent_re, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, mul_zero, sub_zero]
    exact Real.exp_log (by norm_num)
  have h2 : ‖Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ))‖ = Real.exp (beta*Real.log 2) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simpa only [h1, h2] using norm_sub_norm_le
    (Complex.exp (poleExponent y*(Real.log 2 : ℂ)))
    (Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ)))

/-- A strict modulus gap exists for every fixed `beta<1`. -/
theorem ideal_scale_factor_ne_zero {beta : ℝ} (hb : beta < 1) (y : ℝ) :
    Complex.exp (poleExponent y*(Real.log 2 : ℂ))-
      Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ)) ≠ 0 := by
  have hh : Real.exp (beta*Real.log 2) < 2 := by
    calc
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr
        (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
      _ = _ := Real.exp_log (by norm_num)
  exact norm_pos_iff.mp ((sub_pos.mpr hh).trans_le (ideal_scale_factor_norm_lower beta y))

/-- Quantitative finite-length source gate. The two sampling corrections
are explicit; no assertion that they vanish is built into this theorem. -/
theorem response_norm_lower (H : ℕ) (beta y : ℝ) :
    (2-Real.exp (beta*Real.log 2))*‖C H (poleExponent y)‖*‖C H (beta : ℂ)‖-
      ‖scaleDefect H (poleExponent y)‖*‖C H (beta : ℂ)‖-
      ‖C H (poleExponent y)‖*‖scaleDefect H (beta : ℂ)‖ ≤
        ‖response H y (beta : ℂ)‖ := by
  let B := (Complex.exp (poleExponent y*(Real.log 2 : ℂ))-
    Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ)))*C H (poleExponent y)*C H (beta : ℂ)
  let E := scaleDefect H (poleExponent y)*C H (beta : ℂ)
  let F := C H (poleExponent y)*scaleDefect H (beta : ℂ)
  have he : B = response H y (beta : ℂ)-E+F := by
    rw [response_eq_scaleDefects]
    dsimp [B, E, F]
    ring
  have hn : ‖B‖ ≤ ‖response H y (beta : ℂ)‖+‖E‖+‖F‖ := by
    rw [he]
    calc
      _ ≤ ‖response H y (beta : ℂ)-E‖+‖F‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  have hl : (2-Real.exp (beta*Real.log 2))*‖C H (poleExponent y)‖*‖C H (beta : ℂ)‖ ≤ ‖B‖ := by
    dsimp [B]
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ideal_scale_factor_norm_lower beta y) (norm_nonneg _))
      (norm_nonneg _)
  have hE : ‖E‖ = ‖scaleDefect H (poleExponent y)‖*‖C H (beta : ℂ)‖ := norm_mul _ _
  have hF : ‖F‖ = ‖C H (poleExponent y)‖*‖scaleDefect H (beta : ℂ)‖ := norm_mul _ _
  rw [hE, hF] at hn
  linarith

/-- A checkable sufficient nondegeneracy criterion for the exact finite
Fejer determinant, without replacing it by its ideal scaling model. -/
theorem response_ne_zero_of_defect_gap (H : ℕ) (beta y : ℝ)
    (hgap : ‖scaleDefect H (poleExponent y)‖*‖C H (beta : ℂ)‖+
      ‖C H (poleExponent y)‖*‖scaleDefect H (beta : ℂ)‖ <
        (2-Real.exp (beta*Real.log 2))*‖C H (poleExponent y)‖*‖C H (beta : ℂ)‖) :
    response H y (beta : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  have h := response_norm_lower H beta y
  linarith

/-- Combined literal kernel, retaining the phase outside the joined
two-scale weight. There is no termwise absolute-value substitution. -/
def kernel (H : ℕ) (y : ℝ) (d : ℕ) : ℂ :=
  C (2*H) (poleExponent y)*(weight H d : ℂ)-
    C H (poleExponent y)*(weight (2*H) d : ℂ)

/-- Exact expansion through the complete carry-Gram, on one physical
support containing both scales. All prime powers and phases survive. -/
theorem statistic_eq_joined (H : ℕ) (y : ℝ) :
    statistic H y = ∑ d ∈ Finset.Icc 1 (12*H),
      (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*kernel H y d := by
  have he (K : ℕ) (hK : K ≤ 2*H) :
      Q K y = ∑ d ∈ Finset.Icc 1 (12*H),
        (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*(weight K d : ℂ) := by
    unfold Q
    rw [fullQuadratic_eq_quadratic (X := 12*H) _ _ _ (fun N hN => by
      have := Finset.mem_range.mp hN
      omega), primePhase_quadratic_eq_joined]
    rfl
  rw [statistic, he H (by omega), he (2*H) le_rfl,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold kernel
  ring

/-- Continuous version of the already joined two-scale kernel. -/
def realKernel (H : ℕ) (y t : ℝ) : ℂ :=
  C (2*H) (poleExponent y)*(realWeight H t : ℂ)-
    C H (poleExponent y)*(realWeight (2*H) t : ℂ)

/-- The full joint physical response is the exact determinant, with
genuine integrability before the interchange/subtraction. -/
theorem integral_realKernel_eq_response (H : ℕ) (y : ℝ) {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (s*t)*realKernel H y t) = response H y s := by
  have hi (K : ℕ) : Integrable (fun t : ℝ => Complex.exp (s*t)*(realWeight K t : ℂ)) :=
    integrable_mellin hs (fun N hN => (Finset.mem_range.mp hN).le)
  have he (t : ℝ) : Complex.exp (s*t)*realKernel H y t =
      C (2*H) (poleExponent y)*(Complex.exp (s*t)*(realWeight H t : ℂ))-
      C H (poleExponent y)*(Complex.exp (s*t)*(realWeight (2*H) t : ℂ)) := by
    unfold realKernel
    ring
  simp_rw [he]
  rw [integral_sub ((hi H).const_mul _) ((hi (2*H)).const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

/-- Exact full positive-denominator density cancellation. A lower endpoint
at denominator one, if imposed, is a separate explicit boundary. -/
theorem integral_pole_realKernel_eq_zero (H : ℕ) (y : ℝ) :
    (∫ t : ℝ, Complex.exp (poleExponent y*t)*realKernel H y t) = 0 := by
  rw [integral_realKernel_eq_response H y (by rw [poleExponent_re]; norm_num), response_pole_eq_zero]

/-- Every exact triangular packet has amplitude at most one, irrespective
of its length; used for endpoint and Mellin integrability budgets only. -/
theorem realWeight_le_one (H : ℕ) (t : ℝ) : realWeight H t ≤ 1 := by
  have hb (N : ℕ) : 0 ≤ realCarry N t ∧ realCarry N t ≤ 1 := by
    unfold realCarry
    split_ifs <;> norm_num
  have hn : |∑ v ∈ Finset.range H, (realCarry (H+v+H) t-realCarry (H+v) t)| ≤ (H : ℝ) := by
    have he := norm_sum_le (Finset.range H) (fun v => realCarry (H+v+H) t-realCarry (H+v) t)
    simp only [Real.norm_eq_abs] at he
    apply he.trans
    calc
      _ ≤ ∑ _v ∈ Finset.range H, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        rw [abs_le]
        have h1 := hb (H+v+H)
        have h2 := hb (H+v)
        constructor <;> linarith
      _ = _ := by simp
  rw [realWeight, realMass, realPacket_eq_average, Complex.norm_real, Real.norm_eq_abs,
    abs_div, show |(H : ℝ)| = H from abs_of_nonneg (Nat.cast_nonneg H)]
  have hh : |∑ v ∈ Finset.range H, (realCarry (H+v+H) t-realCarry (H+v) t)|/(H : ℝ) ≤ 1 :=
    div_le_one_of_le₀ hn (Nat.cast_nonneg H)
  nlinarith [div_nonneg (abs_nonneg (∑ v ∈ Finset.range H,
    (realCarry (H+v+H) t-realCarry (H+v) t))) (Nat.cast_nonneg H)]

/-- The complex pole coefficient has a linear support budget. This is
not used to norm-pay the full central prime statistic. -/
theorem norm_C_pole_le {H : ℕ} (hH : 0 < H) (y : ℝ) :
    ‖C H (poleExponent y)‖ ≤ 6*(H : ℝ) := by
  have hi : Integrable (fun t : ℝ => Real.exp t*realWeight H t) := by
    simpa only [one_mul, realWeight] using integrable_source (beta := 1) (by norm_num)
      (alpha := coefficient H H) (fun N hN => (Finset.mem_range.mp hN).le)
  have hc : Integrable ((Iic (Real.log (6*(H : ℝ)))).indicator Real.exp) :=
    (integrable_indicator_iff measurableSet_Iic).mpr (integrableOn_exp_mul_Iic (a := 1)
      (by norm_num) _ |>.congr_fun (by intro t _; simp) measurableSet_Iic)
  have hn : (∫ t : ℝ, Real.exp t*realWeight H t) ≤ 6*(H : ℝ) := by
    calc
      _ ≤ ∫ t : ℝ, (Iic (Real.log (6*(H : ℝ)))).indicator Real.exp t := by
        apply integral_mono hi hc
        intro t
        change Real.exp t*realWeight H t ≤ (Iic (Real.log (6*(H : ℝ)))).indicator Real.exp t
        by_cases ht : t ≤ Real.log (6*(H : ℝ))
        · rw [Set.indicator_of_mem (show t ∈ Iic (Real.log (6*(H : ℝ))) from ht)]
          exact (mul_le_mul_of_nonneg_left (realWeight_le_one H t) (Real.exp_pos _).le).trans_eq (mul_one _)
        · have he : 6*(H : ℝ) < Real.exp t :=
            (Real.log_lt_iff_lt_exp (by positivity)).mp (lt_of_not_ge ht)
          have hz : realWeight H t = 0 := by
            apply realMass_eq_zero_above (B := H+2*H-1)
              (fun N hN => by have := Finset.mem_range.mp hN; omega)
            have hb : ((H+2*H-1 : ℕ) : ℝ)+1 = 3*(H : ℝ) := by
              have h := show H+2*H-1+1 = 3*H by omega
              exact_mod_cast h
            rw [hb]
            linarith
          rw [hz, mul_zero, Set.indicator_of_notMem (show t ∉ Iic (Real.log (6*(H : ℝ))) from ht)]
      _ = _ := by
        rw [integral_indicator measurableSet_Iic, integral_exp_Iic,
          Real.exp_log (by positivity)]
  unfold C mellin
  apply (norm_integral_le_integral_norm _).trans
  have he : (∫ t : ℝ, ‖Complex.exp (poleExponent y*t)*
      (realMass (Finset.range (H+2*H)) (coefficient H H) t : ℂ)‖) =
      ∫ t : ℝ, Real.exp t*realWeight H t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ realMass _ _ t from sq_nonneg _)]
    simp only [Complex.mul_re, poleExponent_re, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, mul_zero, sub_zero]
    rfl
  rw [he]
  exact hn

/-- If density is restricted to denominators at least one, the omitted
endpoint of each full Mellin coefficient has an absolute unit budget. -/
theorem norm_lower_pole_endpoint_le_one (H : ℕ) (y : ℝ) :
    ‖∫ t : ℝ in Iic 0, Complex.exp (poleExponent y*t)*(realWeight H t : ℂ)‖ ≤ 1 := by
  have hi : Integrable (fun t : ℝ => Real.exp t*realWeight H t) := by
    simpa only [one_mul, realWeight] using integrable_source (beta := 1) (by norm_num)
      (alpha := coefficient H H) (fun N hN => (Finset.mem_range.mp hN).le)
  calc
    _ ≤ ∫ t : ℝ in Iic 0, ‖Complex.exp (poleExponent y*t)*(realWeight H t : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ in Iic 0, Real.exp t*realWeight H t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ realWeight H t from sq_nonneg _)]
      simp only [Complex.mul_re, poleExponent_re, Complex.ofReal_re,
        Complex.ofReal_im, one_mul, mul_zero, sub_zero]
    _ ≤ ∫ t : ℝ in Iic 0, Real.exp t :=
      setIntegral_mono_on hi.integrableOn (by
        simpa only [one_mul] using integrableOn_exp_mul_Iic (a := 1) (by norm_num) 0)
        measurableSet_Iic (fun t _ => by
          exact (mul_le_mul_of_nonneg_left (realWeight_le_one H t) (Real.exp_pos _).le).trans_eq (mul_one _))
    _ = 1 := by rw [integral_exp_Iic, Real.exp_zero]

/-- Divide by the deterministic pole scale `H`, not by a potentially zero
Mellin coefficient. The matched source scale is then `H^beta`. -/
def normalizedStatistic (H : ℕ) (y : ℝ) : ℂ := statistic H y/(H : ℂ)

/-- The same two-scale combination on the already-paid low sector. -/
def lowStatistic (H D : ℕ) (y : ℝ) : ℂ :=
  (C (2*H) (poleExponent y)*lowPacket H H D y-
    C H (poleExponent y)*lowPacket (2*H) (2*H) D y)/(H : ℂ)

/-- Explicit signed complement of the paid sector, with both prime-power
supports and phases unchanged. -/
def highStatistic (H D : ℕ) (y : ℝ) : ℂ :=
  (C (2*H) (poleExponent y)*highPacket H H D y-
    C H (poleExponent y)*highPacket (2*H) (2*H) D y)/(H : ℂ)

/-- Pole centering retains the exact paid/unpaid ledger. -/
theorem normalizedStatistic_eq_low_high {H D : ℕ} (hD : D ≤ 6*H) (y : ℝ) :
    normalizedStatistic H y = lowStatistic H D y+highStatistic H D y := by
  unfold normalizedStatistic statistic Q lowStatistic highStatistic
  rw [fullQuadratic_eq_low_high (by omega : D ≤ 2*(H+2*H)),
    fullQuadratic_eq_low_high (by omega : D ≤ 2*(2*H+2*(2*H)))]
  ring

/-- The original arithmetic low-sector saving survives deterministic
two-scale pole centering; no whole-matrix norm is taken. -/
theorem norm_lowStatistic_le {H : ℕ} (hH : 0 < H) (D : ℕ) (y : ℝ) :
    ‖lowStatistic H D y‖ ≤ (27/2 : ℝ)*(Real.log 4+4)*(D : ℝ)^3/(H : ℝ)^2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hc1 := norm_C_pole_le hH y
  have hc2 := norm_C_pole_le (by omega : 0 < 2*H) y
  have hl1 := norm_lowPacket_le hH H D y
  have hl2 := norm_lowPacket_le (by omega : 0 < 2*H) (2*H) D y
  unfold lowStatistic
  rw [norm_div, Complex.norm_natCast]
  calc
    _ ≤ (‖C (2*H) (poleExponent y)‖*‖lowPacket H H D y‖+
      ‖C H (poleExponent y)‖*‖lowPacket (2*H) (2*H) D y‖)/(H : ℝ) := by
      apply div_le_div_of_nonneg_right _ hHR.le
      simpa only [norm_mul] using norm_sub_le
        (C (2*H) (poleExponent y)*lowPacket H H D y)
        (C H (poleExponent y)*lowPacket (2*H) (2*H) D y)
    _ ≤ (6*((2*H : ℕ) : ℝ)*((Real.log 4+4)*(D : ℝ)*((D : ℝ)/H)^2)+
      6*(H : ℝ)*((Real.log 4+4)*(D : ℝ)*((D : ℝ)/((2*H : ℕ) : ℝ))^2))/(H : ℝ) := by
      gcongr
    _ = _ := by push_cast; field_simp; ring

/-- The original campaign power saving survives in the same centered
statistic. This pays only the explicit low sector, not `highStatistic`. -/
theorem norm_cofinal_lowStatistic_le {N : ℕ} (hN : 0 < N) (y : ℝ)
    {beta : ℝ} (hb : (19999/20000 : ℝ) ≤ beta) :
    ‖lowStatistic (N^20000) (N^19998) y‖/(((N^20000 : ℕ) : ℝ)^beta) ≤
      (27/2 : ℝ)*(Real.log 4+4)/(N : ℝ)^5 := by
  have hbase : (1 : ℝ) ≤ (N^20000 : ℕ) := by
    have hp : 1 ≤ N^20000 := one_le_pow₀ (by omega : 1 ≤ N)
    simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hp
  have hp := Real.rpow_le_rpow_of_exponent_le hbase hb
  have hl : (0 : ℝ) < (((N^20000 : ℕ) : ℝ)^(19999/20000 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  apply (div_le_div_of_nonneg_left (norm_nonneg _) hl hp).trans
  rw [cofinal_campaign_source]
  calc
    _ ≤ ((27/2 : ℝ)*(Real.log 4+4)*(((N^19998 : ℕ) : ℝ)^3)/
        (((N^20000 : ℕ) : ℝ)^2))/(N : ℝ)^19999 :=
      div_le_div_of_nonneg_right (norm_lowStatistic_le (pow_pos hN 20000) (N^19998) y)
        (pow_nonneg (Nat.cast_nonneg N) 19999)
    _ = _ := by
      have hnR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      push_cast
      field_simp

/-- The physical lower-denominator endpoint is bounded after deterministic
normalization; it is not a new source-scale channel. -/
theorem norm_normalized_lower_endpoint_le {H : ℕ} (hH : 0 < H) (y : ℝ) :
    ‖(C (2*H) (poleExponent y)*
        (∫ t : ℝ in Iic 0, Complex.exp (poleExponent y*t)*(realWeight H t : ℂ))-
      C H (poleExponent y)*
        (∫ t : ℝ in Iic 0, Complex.exp (poleExponent y*t)*(realWeight (2*H) t : ℂ)))/(H : ℂ)‖ ≤ 18 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hc1 := norm_C_pole_le hH y
  have hc2 := norm_C_pole_le (by omega : 0 < 2*H) y
  have he1 := norm_lower_pole_endpoint_le_one H y
  have he2 := norm_lower_pole_endpoint_le_one (2*H) y
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hHR).mpr
  calc
    _ ≤ ‖C (2*H) (poleExponent y)‖*‖∫ t : ℝ in Iic 0,
        Complex.exp (poleExponent y*t)*(realWeight H t : ℂ)‖+
      ‖C H (poleExponent y)‖*‖∫ t : ℝ in Iic 0,
        Complex.exp (poleExponent y*t)*(realWeight (2*H) t : ℂ)‖ := by
      simpa only [norm_mul] using norm_sub_le
        (C (2*H) (poleExponent y)*(∫ t : ℝ in Iic 0,
          Complex.exp (poleExponent y*t)*(realWeight H t : ℂ)))
        (C H (poleExponent y)*(∫ t : ℝ in Iic 0,
          Complex.exp (poleExponent y*t)*(realWeight (2*H) t : ℂ)))
    _ ≤ 6*((2*H : ℕ) : ℝ)*1+6*(H : ℝ)*1 := by gcongr
    _ = _ := by push_cast; ring

/-- One macroscopic outer cell belongs only to the doubled packet.
Pole centering does not create pointwise cancellation on that cell. -/
theorem realKernel_outer_cell {H : ℕ} (hH : 0 < H) {y t : ℝ}
    (ht : t ∈ Ioo (Real.log (8*(H : ℝ))) (Real.log (9*(H : ℝ)))) :
    realKernel H y t = -C H (poleExponent y)*(realWeight (2*H) t : ℂ) ∧
      ‖C H (poleExponent y)‖/9 ≤ ‖realKernel H y t‖ := by
  have hlo : 8*(H : ℝ) < Real.exp t := (Real.log_lt_iff_lt_exp (by positivity)).mp ht.1
  have hz : realWeight H t = 0 := by
    apply realMass_eq_zero_above (B := H+2*H-1)
      (fun N hN => by have := Finset.mem_range.mp hN; omega)
    have hb : ((H+2*H-1 : ℕ) : ℝ)+1 = 3*(H : ℝ) := by
      have he : H+2*H-1+1 = 3*H := by omega
      exact_mod_cast he
    rw [hb]
    linarith
  have hs : (1/9 : ℝ) ≤ realWeight (2*H) t := by
    apply realMass_on_macroscopic_cell (by omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      show (4 : ℝ)*(2*(H : ℝ)) = 8*H by ring,
      show (9/2 : ℝ)*(2*(H : ℝ)) = 9*H by ring] using ht
  have he : realKernel H y t = -C H (poleExponent y)*(realWeight (2*H) t : ℂ) := by
    simp [realKernel, hz, neg_mul]
  refine ⟨he, ?_⟩
  rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ realWeight (2*H) t from sq_nonneg _)]
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hs (norm_nonneg (C H (poleExponent y)))

/-- The continuous joined kernel is the literal arithmetic one at every
integer denominator, including all quotient endpoints. -/
theorem realKernel_log {d : ℕ} (hd : 0 < d) (H : ℕ) (y : ℝ) :
    realKernel H y (Real.log d) = kernel H y d := by
  unfold realKernel kernel realWeight weight
  rw [realMass_log hd, realMass_log hd]

/-- The unmatched outer band is present in the actual integer kernel,
not merely in its continuum diagnostic. -/
theorem kernel_outer_band {H d : ℕ} (hH : 0 < H) (hlo : 8*H < d) (hhi : d < 9*H)
    (y : ℝ) : ‖C H (poleExponent y)‖/9 ≤ ‖kernel H y d‖ := by
  have hd : 0 < d := by omega
  rw [← realKernel_log hd]
  apply (realKernel_outer_cell hH ?_).2
  constructor
  · apply Real.log_lt_log (by positivity)
    exact_mod_cast hlo
  · apply Real.log_lt_log (by positivity)
    exact_mod_cast hhi

/-- Positive budget of the already joined physical kernel. It is an
audit of a proposed norm payment, not a bound on the signed prime sum. -/
def absoluteEnvelope (H : ℕ) (y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp t*‖realKernel H y t‖

private theorem integrable_absoluteEnvelope (H : ℕ) (y : ℝ) :
    Integrable (fun t : ℝ => Real.exp t*‖realKernel H y t‖) := by
  have hi (K : ℕ) : Integrable (fun t : ℝ => Complex.exp ((1 : ℂ)*t)*(realWeight K t : ℂ)) :=
    integrable_mellin (by norm_num) (fun N hN => (Finset.mem_range.mp hN).le)
  have hj : Integrable (fun t : ℝ => Complex.exp ((1 : ℂ)*t)*realKernel H y t) := by
    convert ((hi H).const_mul (C (2*H) (poleExponent y))).sub
      ((hi (2*H)).const_mul (C H (poleExponent y))) using 1
    funext t
    change Complex.exp ((1 : ℂ)*t)*realKernel H y t =
      C (2*H) (poleExponent y)*(Complex.exp ((1 : ℂ)*t)*(realWeight H t : ℂ))-
        C H (poleExponent y)*(Complex.exp ((1 : ℂ)*t)*(realWeight (2*H) t : ℂ))
    unfold realKernel
    ring
  apply hj.norm.congr
  filter_upwards with t
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Even after exact pole centering, the joint positive budget has an
unmatched macroscopic outer contribution. A norm-based main-range payment
therefore has no automatic saving from the determinant cancellation. -/
theorem absoluteEnvelope_lower {H : ℕ} (hH : 0 < H) (y : ℝ) :
    (8*Real.log (9/8 : ℝ)/9)*(H : ℝ)*‖C H (poleExponent y)‖ ≤ absoluteEnvelope H y := by
  let a := Real.log (8*(H : ℝ))
  let b := Real.log (9*(H : ℝ))
  let c := 8*(H : ℝ)*‖C H (poleExponent y)‖/9
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hab : a < b := Real.log_lt_log (by positivity) (by linarith)
  have hi : Integrable ((Ioo a b).indicator (fun _ : ℝ => c)) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have he : (∫ t : ℝ, (Ioo a b).indicator (fun _ : ℝ => c) t) = (b-a)*c := by
    rw [integral_indicator_const _ measurableSet_Ioo]
    simp [hab.le, smul_eq_mul]
  have hd : b-a = Real.log (9/8 : ℝ) := by
    dsimp [a, b]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hle : (∫ t : ℝ, (Ioo a b).indicator (fun _ : ℝ => c) t) ≤ absoluteEnvelope H y := by
    apply integral_mono hi (integrable_absoluteEnvelope H y)
    intro t
    change (Ioo a b).indicator (fun _ : ℝ => c) t ≤ Real.exp t*‖realKernel H y t‖
    by_cases ht : t ∈ Ioo a b
    · rw [Set.indicator_of_mem ht]
      have hexp : 8*(H : ℝ) ≤ Real.exp t :=
        ((Real.log_lt_iff_lt_exp (by positivity)).mp ht.1).le
      have hk := (realKernel_outer_cell (y := y) hH ht).2
      dsimp [c]
      simpa only [div_eq_mul_inv, mul_assoc] using mul_le_mul hexp hk (by positivity)
        (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem ht]
      exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  rw [he, hd] at hle
  convert hle using 1
  dsimp [c]
  ring

end
end RiemannGaussian.SuzukiCarryPoleCenter
