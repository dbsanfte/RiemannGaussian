/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourierCarrier

/-!
# The original composite Riesz carrier as a prime-factor Fourier integral

The complete divisor measure of every squarefree nonunit composite has
zero signed mass and zero logarithmic moment. Proving those cancellations
first gives one integrable prime-factor response for the literal filtered
band. Its exact sine factors retain the central phase and prime count.
The hypothetical-zero source is unchanged; its independent floor is open.
-/

namespace RiemannGaussian.ZetaRieszPrimeFourier
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius
open FiniteSignedFourierHinge

/-- The complete nonunit divisor measure has exactly zero signed mass. -/
theorem sum_moebius_eq_zero {n : ℕ} (h1 : n ≠ 1) :
    (∑ d ∈ n.divisors, (μ d : ℂ)) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, if_neg h1] using h

/-- The complete squarefree composite measure also cancels its signed
logarithmic moment. Prime powers are excluded by actual arithmetic support. -/
theorem sum_moebius_log_eq_zero {n : ℕ} (hn : Squarefree n) (hp : ¬ n.Prime) :
    (∑ d ∈ n.divisors, (μ d : ℂ) * (Real.log d : ℂ)) = 0 := by
  have hLambda : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h =>
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, h⟩))
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  rw [hLambda, neg_zero] at h
  exact_mod_cast h

/-- The first moment cancels for the complete divisor measure of each
squarefree nonunit composite before any norm or band average is taken. -/
theorem riesz_eq_paired_integral (L : ℝ) {n : ℕ} (hn : Squarefree n)
    (h1 : n ≠ 1) (hp : ¬ n.Prime) :
    (VaughanLogAverage.riesz L n : ℂ) =
      (1 / (Real.pi : ℂ)) * ∫ xi : ℝ in Ioi 0,
        pairedNumerator n.divisors (fun d => (μ d : ℂ))
          (fun d => -Real.log d) (-L) xi / (xi : ℂ) ^ 2 := by
  have h := finite_hinge_eq_paired_integral n.divisors
    (fun d => (μ d : ℂ)) (fun d => -Real.log d) (-L)
  simp only [neg_sub_neg] at h
  have hm : (∑ d ∈ n.divisors, ((L - Real.log d : ℝ) : ℂ) * (μ d : ℂ)) = 0 := by
    simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    rw [sum_moebius_eq_zero h1, mul_zero]
    rw [zero_sub, neg_eq_zero]
    calc
      _ = ∑ d ∈ n.divisors, (μ d : ℂ) * (Real.log d : ℂ) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = 0 := sum_moebius_log_eq_zero hn hp
  rw [hm, zero_div, zero_add] at h
  convert h using 1
  unfold VaughanLogAverage.riesz
  push_cast
  exact Finset.sum_congr rfl (fun d _hd => mul_comm _ _)

/-- The full prime-factor Fourier product keeps every distinct prime
of the observed integer and its exact logarithmic phase. -/
def primeProduct (n : ℕ) (xi : ℝ) : ℂ :=
  ∏ p ∈ n.primeFactors, (1 - zetaPrimeFeature (Complex.I * xi) p)

private def featureArithmetic (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else zetaPrimeFeature s n, by simp⟩

private theorem featureArithmetic_multiplicative (s : ℂ) :
    (featureArithmetic s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [featureArithmetic, zetaPrimeFeature], ?_⟩
  intro m n hm hn _hcop
  simp only [featureArithmetic, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
    if_neg (Nat.mul_ne_zero hm hn)]
  exact CoprimeEulerPhase.feature_mul s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

/-- The full divisor Fourier character factors exactly over the prime
support of the observed squarefree integer. -/
theorem divisorCharacter_eq_primeProduct {n : ℕ} (hn : Squarefree n) (xi : ℝ) :
    finiteCharacter n.divisors (fun d => (μ d : ℂ)) (fun d => -Real.log d) xi =
      primeProduct n xi := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (featureArithmetic (Complex.I * xi)) (featureArithmetic_multiplicative _) hn
  have hl : (∏ p ∈ n.primeFactors, (1 - featureArithmetic (Complex.I * xi) p)) =
      primeProduct n xi := by
    apply Finset.prod_congr rfl
    intro p hp
    simp only [featureArithmetic, ArithmeticFunction.coe_mk,
      if_neg (Nat.prime_of_mem_primeFactors hp).ne_zero]
  rw [hl] at h
  rw [h, finiteCharacter]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [featureArithmetic, ArithmeticFunction.coe_mk,
    if_neg (Nat.pos_of_mem_divisors hd).ne']
  congr 1
  unfold zetaPrimeFeature
  congr 1
  push_cast
  ring

/-- Both centered prime-factor frequencies of the same observed integer. -/
def primePair (n : ℕ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) * primeProduct n xi +
  Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) * primeProduct n (-xi)

/-- Zero total divisor mass removes the constant term from the exact
paired Fourier numerator, keeping the full prime product at both signs. -/
theorem divisor_pairedNumerator_eq_primePair {n : ℕ} (hn : Squarefree n)
    (h1 : n ≠ 1) (L xi : ℝ) :
    pairedNumerator n.divisors (fun d => (μ d : ℂ))
      (fun d => -Real.log d) (-L) xi = -primePair n L xi / 2 := by
  simp only [pairedNumerator, sum_moebius_eq_zero h1,
    divisorCharacter_eq_primeProduct hn, neg_mul, mul_neg, neg_neg, zero_sub,
    primePair, neg_div]

/-- The full coupled prime-factor quotient is genuinely integrable.
This keeps cancellation at zero before taking a norm. -/
theorem integrable_primePair_div_sq {n : ℕ} (hn : Squarefree n)
    (h1 : n ≠ 1) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => primePair n L xi / (xi : ℂ) ^ 2) (Ioi 0) := by
  have h := integrable_pairedNumerator_div_sq n.divisors (fun d => (μ d : ℂ))
    (fun d => -Real.log d) (-L)
  have he (xi : ℝ) : primePair n L xi / (xi : ℂ) ^ 2 =
      (-2 : ℂ) * (pairedNumerator n.divisors (fun d => (μ d : ℂ))
        (fun d => -Real.log d) (-L) xi / (xi : ℂ) ^ 2) := by
    rw [divisor_pairedNumerator_eq_primePair hn h1]
    ring
  simp_rw [he]
  exact h.const_mul (-2)

/-- Every squarefree nonunit composite has a pure prime-factor Fourier
formula: both discarded endpoint moments are proved to cancel first. -/
theorem riesz_eq_primePair_integral (L : ℝ) {n : ℕ} (hn : Squarefree n)
    (h1 : n ≠ 1) (hp : ¬ n.Prime) :
    (VaughanLogAverage.riesz L n : ℂ) =
      (-(1 / (2 * (Real.pi : ℂ)))) * ∫ xi : ℝ in Ioi 0,
        primePair n L xi / (xi : ℂ) ^ 2 := by
  rw [riesz_eq_paired_integral L hn h1 hp]
  have he (xi : ℝ) : pairedNumerator n.divisors (fun d => (μ d : ℂ))
      (fun d => -Real.log d) (-L) xi / (xi : ℂ) ^ 2 =
      (-(1 / 2 : ℂ)) * (primePair n L xi / (xi : ℂ) ^ 2) := by
    rw [divisor_pairedNumerator_eq_primePair hn h1]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- The literal composite coefficient has a pure prime-factor integral.
The unit, primes and nonsquarefree integers are deleted exactly. -/
theorem coefficient_eq_primePair_integral (L : ℝ) (n : ℕ) :
    SquarefreeVaughanLogSource.coefficient L n =
      if Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime then
        (Real.log n : ℂ) / (2 * (Real.pi : ℂ) * (L : ℂ)) *
          ∫ xi : ℝ in Ioi 0, primePair n L xi / (xi : ℂ) ^ 2
      else 0 := by
  by_cases hn : Squarefree n
  · by_cases hp : n.Prime
    · simp [SquarefreeVaughanLogSource.coefficient, hp]
    · by_cases h1 : n = 1
      · subst n
        simp [SquarefreeVaughanLogSource.coefficient]
      · rw [if_pos ⟨hn, h1, hp⟩, SquarefreeVaughanLogSource.coefficient, if_pos ⟨hn, hp⟩]
        push_cast
        rw [riesz_eq_primePair_integral L hn h1 hp]
        ring
  · simp [SquarefreeVaughanLogSource.coefficient, hn]

/-- The full finite signed arithmetic frequency response retains each
observed integer's original filter and all of its prime-factor phases. -/
def bandPrimePair (T : Finset ℕ) (f : ℕ → ℂ) (L xi : ℝ) : ℂ :=
  ∑ n ∈ T.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime),
    ((Real.log n : ℂ) / (L : ℂ) * f n) * (primePair n L xi / (xi : ℂ) ^ 2)

/-- Every finite original observation gives a genuinely integrable
prime-factor response after the actual arithmetic deletions. -/
theorem integrable_bandPrimePair (T : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) :
    IntegrableOn (bandPrimePair T f L) (Ioi 0) := by
  unfold bandPrimePair
  apply integrable_finsetSum
  intro n hn
  rcases (Finset.mem_filter.mp hn).2 with ⟨hsf, h1, _hp⟩
  exact (integrable_primePair_div_sq hsf h1 L).const_mul _

/-- The original finite carrier is a single integrable prime-factor
response. The moment and ordinary-prime deletions are proved arithmetically,
while every signed observation and cross-prime phase stays coupled. -/
theorem sum_original_eq_primePair_integral (T : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) :
    (∑ n ∈ T, SquarefreeVaughanLogSource.coefficient L n * f n) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Ioi 0, bandPrimePair T f L xi := by
  have hi (n : ℕ) (hn : n ∈ T.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime)) :
      IntegrableOn (fun xi : ℝ => ((Real.log n : ℂ) / (L : ℂ) * f n) *
        (primePair n L xi / (xi : ℂ) ^ 2)) (Ioi 0) :=
    (integrable_primePair_div_sq (Finset.mem_filter.mp hn).2.1
      (Finset.mem_filter.mp hn).2.2.1 L).const_mul _
  unfold bandPrimePair
  rw [integral_finsetSum _ hi, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [coefficient_eq_primePair_integral]
  by_cases h : Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime
  · rw [if_pos h, if_pos h, integral_const_mul]
    ring
  · rw [if_neg h, if_neg h, zero_mul]

/-- The original factorial-filtered band is exactly the signed
prime-factor integral. The physical length and base order stay fixed. -/
theorem actual_band_eq_primePair_integral (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Ioi 0,
        bandPrimePair (zetaPrimeLogBand N)
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) L xi :=
  sum_original_eq_primePair_integral _ _ L

/-- The exact phase of a single prime difference is kept alongside its
real sine factor. No absolute value is taken in this identity. -/
theorem one_sub_exp_neg_eq_sine (x : ℝ) :
    1 - Complex.exp (-(x : ℂ) * Complex.I) =
      2 * Complex.I * Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) *
        (Real.sin (x / 2) : ℂ) := by
  have hsin := Complex.two_sin ((x / 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_sin] at hsin
  have hn : Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(x : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp : Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero]
  calc
    _ = -(Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I)) := by rw [hn, hp]; ring
    _ = _ := by
      rw [show 2 * Complex.I * Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) *
          (Real.sin (x / 2) : ℂ) =
          (2 * (Real.sin (x / 2) : ℂ)) * Complex.I *
            Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) by ring, hsin]
      simp only [mul_assoc, Complex.I_mul_I, mul_neg_one, neg_mul]
      ring

/-- The original imaginary-power feature is a real-frequency phase at
each logarithmic prime coordinate. -/
theorem one_sub_feature_eq_sine (xi : ℝ) (p : ℕ) :
    1 - zetaPrimeFeature (Complex.I * xi) p =
      2 * Complex.I * Complex.exp (-((xi * Real.log p / 2 : ℝ) : ℂ) * Complex.I) *
        (Real.sin (xi * Real.log p / 2) : ℂ) := by
  rw [← one_sub_exp_neg_eq_sine]
  congr 1
  unfold zetaPrimeFeature
  congr 1
  push_cast
  ring

/-- The full product keeps its exact central phase, distinct-prime count
and the sign of every real sine factor. -/
theorem primeProduct_eq_centered_sine {n : ℕ} (hn : Squarefree n) (xi : ℝ) :
    primeProduct n xi =
      (2 * Complex.I) ^ n.primeFactors.card *
        Complex.exp (-((xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I) *
        ((∏ p ∈ n.primeFactors, Real.sin (xi * Real.log p / 2) : ℝ) : ℂ) := by
  have he : (∑ p ∈ n.primeFactors,
      -((xi * Real.log p / 2 : ℝ) : ℂ) * Complex.I) =
      -((xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
    simp only [Finset.mul_sum, Finset.sum_div, Complex.ofReal_sum, neg_mul,
      Finset.sum_neg_distrib, Finset.sum_mul]
  unfold primeProduct
  simp_rw [one_sub_feature_eq_sine]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    ← Complex.exp_sum, he, ← Complex.ofReal_prod]

/-- The exact pointwise amplitude retains every logarithmic prime coordinate
through its sine factor. It is not a bound for their signed band sum. -/
theorem norm_primeProduct_eq_sine_product (n : ℕ) (xi : ℝ) :
    ‖primeProduct n xi‖ =
      2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, |Real.sin (xi * Real.log p / 2)| := by
  have h (p : ℕ) : ‖1 - zetaPrimeFeature (Complex.I * xi) p‖ =
      2 * |Real.sin (xi * Real.log p / 2)| := by
    rw [one_sub_feature_eq_sine]
    rw [show -((xi * Real.log p / 2 : ℝ) : ℂ) =
      ((-(xi * Real.log p / 2) : ℝ) : ℂ) by norm_cast]
    simp only [norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_eq_abs, mul_one]
    norm_num
  rw [primeProduct, norm_prod]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The exact prime-factor integral of the original band retains the
same negative multiplicity source under a hypothetical right-half zero. -/
theorem tendsto_actual_primePair_integral (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ((1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Ioi 0,
        bandPrimePair (zetaPrimeLogBand N)
          (fun n => zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + Complex.I * rho.1.im) n)
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) xi))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [actual_band_eq_primePair_integral] using
    SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho

end
end RiemannGaussian.ZetaRieszPrimeFourier
