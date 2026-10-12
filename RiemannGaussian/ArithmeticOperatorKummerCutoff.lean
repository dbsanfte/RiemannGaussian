/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryCorrelation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Exact Kummer/Gamma cutoff gate

The mixed finite difference is taken before summing the prime powers.
Its arbitrary-weight form is retained for the collapse audit; the
untwisted von Mangoldt specialization genuinely uses integer factorization.
No RH estimate is asserted.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerCutoff
noncomputable section
open scoped BigOperators
open SuzukiIntegerCarry SuzukiCarryCorrelation

/-- Carry of two arbitrary integer cutoffs at one denominator. -/
def binomialCarry (a b d : ℕ) : ℕ := (a+b)/d-a/d-b/d

/-- Joined mixed cutoff difference with no endpoint removed. -/
def mixedCarry (a b d : ℕ) : ℤ :=
  (binomialCarry (a+1) (b+1) d : ℤ)-binomialCarry (a+1) b d-
    binomialCarry a (b+1) d+binomialCarry a b d

/-- The full prime-power observation on a common finite support. -/
def weightedHessian (X a b : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X, (mixedCarry a b d : ℂ)*w d

/-- Arbitrary-weight divisor observation at a literal integer endpoint. -/
def divisorObservation (w : ℕ → ℂ) (n : ℕ) : ℂ := ∑ d ∈ n.divisors, w d

/-- Archimedean logarithm of the literal binomial coefficient. -/
def logBinomial (a b : ℕ) : ℝ :=
  Real.log ((a+b).factorial : ℝ)-Real.log (a.factorial : ℝ)-Real.log (b.factorial : ℝ)

/-- The identical Gamma expression at the literal integer cutoffs. -/
def gammaLogBinomial (a b : ℕ) : ℝ :=
  Real.log (Real.Gamma (a+b+1))-Real.log (Real.Gamma (a+1))-
    Real.log (Real.Gamma (b+1))

/-- The prime-power twist is applied before any Hessian or real-part estimate. -/
def twistedHessian (a b : ℕ) (y : ℝ) : ℂ :=
  weightedHessian (a+b+2) a b (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*
    Complex.exp (-(Complex.I*y*(Real.log d : ℂ))))

theorem logBinomial_eq_log_choose (a b : ℕ) :
    logBinomial a b = Real.log ((a+b).choose b : ℝ) := by
  have hf : ((a+b).choose b : ℝ)*(a.factorial : ℝ)*(b.factorial : ℝ) =
      ((a+b).factorial : ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial a b
  have hc : (0 : ℝ) < (a+b).choose b := by
    exact_mod_cast Nat.choose_pos (by omega : b ≤ a+b)
  have hl := congrArg Real.log hf
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul hc.ne' (by positivity)] at hl
  unfold logBinomial
  linarith

theorem binomialCarry_eq_sub (a b d : ℕ) :
    (binomialCarry a b d : ℤ) = ((a+b)/d : ℕ)- (a/d : ℕ)-(b/d : ℕ) := by
  have h := Nat.div_add_div_le_add_div (x := a) (y := b) (z := d)
  unfold binomialCarry
  omega

theorem binomialCarry_binary (a d : ℕ) : binomialCarry a a d = carry a d := by
  unfold binomialCarry carry
  rw [← two_mul]
  omega

theorem mixedCarry_eq_indicators (a b d : ℕ) :
    mixedCarry a b d = (if d ∣ a+b+2 then (1 : ℤ) else 0)-
      (if d ∣ a+b+1 then (1 : ℤ) else 0) := by
  unfold mixedCarry
  simp_rw [binomialCarry_eq_sub]
  rw [show a+1+(b+1) = a+b+1+1 by omega,
    show a+1+b = a+b+1 by omega, show a+(b+1) = a+b+1 by omega,
    show a+b+2 = a+b+1+1 by omega]
  have h1 := @Nat.succ_div (a+b) d
  have h2 := @Nat.succ_div (a+b+1) d
  have ha := @Nat.succ_div a d
  have hb := @Nat.succ_div b d
  split_ifs <;> simp_all <;> omega

/-- Kummer's theorem on the same literal arbitrary-cutoff binomial. -/
theorem valuation_eq_carry_count {p a b B : ℕ} [Fact p.Prime]
    (hB : Nat.log p (a+b) < B) :
    padicValNat p ((a+b).choose b) =
      ((Finset.Ico 1 B).filter (fun i => p^i ≤ b % p^i+a % p^i)).card := by
  exact padicValNat_choose' hB

private theorem sum_indicator {n X : ℕ} (hn : 0 < n) (hnX : n ≤ X) (w : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 X, (if d ∣ n then (1 : ℂ) else 0)*w d) =
      divisorObservation w n := by
  classical
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hn.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnX⟩,hd⟩
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter,he]
  rfl

/-- Complete collapse for every complex denominator weight. No primality,
positivity or smooth-density premise is used in this identity. -/
theorem weightedHessian_eq_divisor_difference {X a b : ℕ}
    (hX : a+b+2 ≤ X) (w : ℕ → ℂ) :
    weightedHessian X a b w =
      divisorObservation w (a+b+2)-divisorObservation w (a+b+1) := by
  classical
  unfold weightedHessian
  simp_rw [mixedCarry_eq_indicators]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, sum_indicator (by omega) hX w,
    sum_indicator (by omega) (by omega) w]

/-- The actual untwisted factorization compatibility, with every prime power. -/
theorem divisorObservation_vonMangoldt (n : ℕ) :
    divisorObservation (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) n =
      (Real.log n : ℂ) := by
  simp only [divisorObservation, ← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]

theorem weightedHessian_vonMangoldt {X a b : ℕ} (hX : a+b+2 ≤ X) :
    weightedHessian X a b (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) =
      ((Real.log (a+b+2 : ℕ)-Real.log (a+b+1 : ℕ) : ℝ) : ℂ) := by
  rw [weightedHessian_eq_divisor_difference hX]
  simp only [divisorObservation_vonMangoldt, Complex.ofReal_sub]

/-- The Gamma/factorial mixed Hessian is exactly the same endpoint logarithm. -/
theorem logBinomial_mixed_difference (a b : ℕ) :
    logBinomial (a+1) (b+1)-logBinomial (a+1) b-
      logBinomial a (b+1)+logBinomial a b =
        Real.log (a+b+2 : ℕ)-Real.log (a+b+1 : ℕ) := by
  have he (n : ℕ) : Real.log ((n+1).factorial : ℝ) =
      Real.log (n+1 : ℕ)+Real.log (n.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  unfold logBinomial
  rw [show a+1+(b+1) = (a+b+1)+1 by omega,
    show a+1+b = (a+b)+1 by omega, show a+(b+1) = (a+b)+1 by omega]
  simp_rw [he]
  ring

theorem gammaLogBinomial_eq (a b : ℕ) : gammaLogBinomial a b = logBinomial a b := by
  unfold gammaLogBinomial logBinomial
  rw [show (a : ℝ)+b+1 = ((a+b : ℕ) : ℝ)+1 by push_cast; ring]
  simp only [Real.Gamma_nat_eq_factorial]

/-- The phase-retaining object has no Gamma simplification: it is exactly
the difference of the two twisted divisor observations. -/
theorem twistedHessian_eq (a b : ℕ) (y : ℝ) :
    twistedHessian a b y =
      divisorObservation (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*
        Complex.exp (-(Complex.I*y*(Real.log d : ℂ)))) (a+b+2)-
      divisorObservation (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*
        Complex.exp (-(Complex.I*y*(Real.log d : ℂ)))) (a+b+1) := by
  exact weightedHessian_eq_divisor_difference le_rfl _

theorem weightedHessian_origin (w : ℕ → ℂ) : weightedHessian 2 0 0 w = w 2 := by
  rw [weightedHessian_eq_divisor_difference (by norm_num)]
  norm_num [divisorObservation, Nat.prime_two.divisors]

/-- An actual-prime counterexample, not a free-weight countermodel:
twisting destroys the proposed Hessian positivity at arbitrarily selectable
nonzero campaign heights. A Gaussian Schur factor with diagonal one cannot
repair this negative diagonal. -/
theorem exists_campaign_negative_twisted_diagonal :
    ∃ y : ℝ, 54 ≤ y ∧ (twistedHessian 0 0 y).re < 0 := by
  let y : ℝ := 21*Real.pi/Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hy : 54 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hlog).mpr
    nlinarith [Real.pi_gt_three]
  refine ⟨y,hy,?_⟩
  have he : y*Real.log 2 = 21*Real.pi := by dsimp [y]; field_simp
  rw [twistedHessian, show 0+0+2 = 2 by rfl, weightedHessian_origin,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, one_mul, zero_add, mul_zero]
  norm_num only [Nat.cast_ofNat, neg_zero, Real.exp_zero, one_mul]
  rw [he, Real.cos_neg, show (21 : ℝ)*Real.pi = (21 : ℕ)*Real.pi by norm_num,
    Real.cos_nat_mul_pi]
  norm_num
  linarith

/-- Gaussian Schur coupling cannot repair the source-preserving twist's
negative diagonal when the Gaussian has its usual unit diagonal. -/
theorem exists_negative_twisted_schur_diagonal (g : ℕ → ℕ → ℂ) (hg : g 0 0 = 1) :
    ∃ y : ℝ, 54 ≤ y ∧ (g 0 0*twistedHessian 0 0 y).re < 0 := by
  obtain ⟨y,hy,hn⟩ := exists_campaign_negative_twisted_diagonal
  exact ⟨y,hy,by simpa only [hg,one_mul] using hn⟩

/-- The previously checked linear carry response, including all finite
dilations and coefficients, remains blind at an actual zeta zero. -/
theorem finite_linear_Gamma_carry_source_vanishes {rho : ℂ}
    (hr : 0 < rho.re) (hr1 : rho ≠ 1) (hz : riemannZeta rho = 0)
    (S : Finset ℕ) (scale coefficient : ℕ → ℂ) :
    (∑ j ∈ S, coefficient j*scale j^rho*
      SuzukiIntegerCarryMellinAudit.carryTransform rho) = 0 := by
  exact SuzukiIntegerCarryMellinAudit.finite_scaled_carry_tests_eq_zero hr hr1 hz S scale coefficient

end
end RiemannGaussian.ArithmeticOperatorKummerCutoff
