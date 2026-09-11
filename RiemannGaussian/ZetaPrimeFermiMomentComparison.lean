/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPrimeComparison
import RiemannGaussian.ZetaSquarefreeEulerPrimeTailSource
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Fermi weighting preserves the original normalized prime-tail source

The literal ordinary-prime correction may be multiplied by the same
Fermi factor used in the Gaussian budget. Its difference has an additional
half power of Dirichlet damping when the Fermi parameter is at least
`1/2`. A full exponential-moment bound then gives decay at every original
right-half-zero normalization, uniformly over the cutoff and prime sieve.

The polynomial, factorial moments, original prime phase and ordinary-prime
support are retained. This controls only the change of weight. It neither
bounds the surviving Fermi-weighted moment itself nor transfers Gaussian
phase positivity through a sign-changing moment filter.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open scoped Classical
open EtaGammaSmoothing

/-- The logistic complement is exact on the whole real axis. -/
theorem one_sub_fermi_neg (x : ℝ) : 1 - fermi (-x) = fermi x := by
  have he : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hp : 1 + Real.exp x ≠ 0 := by positivity
  unfold fermi
  rw [Real.exp_neg]
  field_simp
  ring

/-- The original prime tail with a Fermi factor; all cutoffs, prime
exclusions, complex polynomial coefficients and factorial orders remain. -/
def fermiPrimeLogResponse (a : ℝ) (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
    (fermi (-a * Real.log n) : ℂ)

/-- Bounded Fermi weighting preserves the genuine absolute convergence
of the original prime-tail moment. -/
theorem summable_fermiPrimeLogResponse (a : ℝ) (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
      (fermi (-a * Real.log n) : ℂ)) := by
  apply (summable_primeLogResponse p D S hS N hs).norm.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fermi_bounds _).1.le]
  exact mul_le_of_le_one_right (norm_nonneg _) (fermi_bounds _).2.le

/-- The exact signed difference still has ordinary-prime support and the
original kernel; only the positive logistic complement is introduced. -/
theorem primeLogResponse_sub_fermi_eq (a : ℝ) (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    primeLogResponse p D S N s - fermiPrimeLogResponse a p D S N s =
      ∑' n, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (fermi (a * Real.log n) : ℂ) := by
  rw [primeLogResponse, fermiPrimeLogResponse,
    ← (summable_primeLogResponse p D S hS N hs).tsum_sub
      (summable_fermiPrimeLogResponse a p D S hS N hs)]
  apply tsum_congr
  intro n
  rw [← one_sub_fermi_neg (a * Real.log n)]
  push_cast
  rw [neg_mul]
  ring

/-- An arbitrary positive exponential tilt bounds the entire correction
summand by a convergent shifted von Mangoldt weight, without using phase
cancellation or restricting the moving cutoff and sieve sizes. -/
theorem norm_primeFermiCorrectionSummand_le (a : ℝ) (p : Polynomial ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) (s : ℂ) {q : ℝ} (hq : 0 < q) (n : ℕ) :
    ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
      (fermi (a * Real.log n) : ℂ)‖ ≤
      (q⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k) *
        zetaPhasePrimeWeight (s.re + a - q) n := by
  rw [primeCorrectionCoefficient_eq_prime_tail hD S hS]
  by_cases hn : n.Prime ∧ D < n ∧ n ∉ S
  · rw [if_pos hn, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg n), Real.norm_of_nonneg (fermi_bounds _).1.le]
    have hk := norm_zetaPrimeFilterKernel_le_tilt p N s
      (by exact_mod_cast hn.1.one_le : (1 : ℝ) ≤ n) hq
    have hm : 0 ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)
    have he : Real.exp (-(s.re - q) * Real.log (n : ℝ)) * Real.exp (-a * Real.log n) =
        Real.exp (-(s.re + a - q) * Real.log n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.log n *
          (q⁻¹ ^ N * Real.exp (-(s.re - q) * Real.log n) *
            ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k) * Real.exp (-a * Real.log n) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hk (Real.log_natCast_nonneg n)
        · simpa only [neg_mul] using fermi_le_exp_neg (a * Real.log n)
        · exact (fermi_bounds _).1.le
        · positivity
      _ = _ := by
        unfold zetaPhasePrimeWeight
        rw [ArithmeticFunction.vonMangoldt_apply_prime hn.1, ← he]
        ring
  · rw [if_neg hn, zero_mul, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)))
      (zetaPhasePrimeWeight_nonneg _ _)

/-- The complete prime-tail correction has an explicit moment bound.
Its constant is an actual absolutely convergent logarithmic derivative,
independent of the cutoff, sieve and imaginary part of the sample. -/
theorem norm_primeLogResponse_sub_fermi_le (a : ℝ) (p : Polynomial ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) {q : ℝ} (hq : 0 < q)
    (hshift : 1 < s.re + a - q) :
    ‖primeLogResponse p D S N s - fermiPrimeLogResponse a p D S N s‖ ≤
      (q⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k) *
        (-logDeriv riemannZeta ((s.re + a - q : ℝ) : ℂ)).re := by
  let C := q⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k
  have hw := hasSum_zetaPhasePrimeWeight hshift
  have hmajor := hw.summable.mul_left C
  have hi := hmajor.of_norm_bounded (norm_primeFermiCorrectionSummand_le a p hD S hS N s hq)
  rw [primeLogResponse_sub_fermi_eq a p D S hS N hs]
  calc
    _ ≤ ∑' n : ℕ, ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (fermi (a * Real.log n) : ℂ)‖ := norm_tsum_le_tsum_norm hi.norm
    _ ≤ ∑' n : ℕ, C * zetaPhasePrimeWeight (s.re + a - q) n :=
      Summable.tsum_le_tsum (norm_primeFermiCorrectionSummand_le a p hD S hS N s hq)
        hi.norm hmajor
    _ = _ := by rw [tsum_mul_left, hw.tsum_eq]

/-- A convergent real-axis von Mangoldt sum decreases with its abscissa. -/
theorem real_logDeriv_mass_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    (-logDeriv riemannZeta (y : ℂ)).re ≤ (-logDeriv riemannZeta (x : ℂ)).re := by
  rw [← (hasSum_zetaPhasePrimeWeight (hx.trans_le hxy)).tsum_eq,
    ← (hasSum_zetaPhasePrimeWeight hx).tsum_eq]
  apply Summable.tsum_le_tsum _ (hasSum_zetaPhasePrimeWeight (hx.trans_le hxy)).summable
    (hasSum_zetaPhasePrimeWeight hx).summable
  intro n
  unfold zetaPhasePrimeWeight
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_natCast_nonneg n]

/-- One explicit geometric rate controls the original source-normalized
correction for every Fermi parameter at least one half, every cutoff,
every finite prime sieve and the entire fixed complex polynomial. -/
theorem exists_normalized_primeFermi_bound (p : Polynomial ℂ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ∀ (N D : ℕ), 1 ≤ D → ∀ S : Finset ℕ,
      (∀ r ∈ S, r.Prime) → ∀ a : ℝ, 1 / 2 ≤ a →
      ‖(u : ℂ) ^ (N + 1) * (primeLogResponse p D S N (3 / 2 + I * y) -
        fermiPrimeLogResponse a p D S N (3 / 2 + I * y))‖ ≤
        C * (2 * u / (1 + u)) ^ N := by
  let q : ℝ := (1 + u) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  let M : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)
  let V : ℝ := (-logDeriv riemannZeta ((2 - q : ℝ) : ℂ)).re
  have hV : 0 ≤ V := by
    change 0 ≤ (-logDeriv riemannZeta ((2 - q : ℝ) : ℂ)).re
    rw [← (hasSum_zetaPhasePrimeWeight (by linarith : 1 < 2 - q)).tsum_eq]
    exact tsum_nonneg (zetaPhasePrimeWeight_nonneg _)
  refine ⟨u * M * V, by positivity, ?_⟩
  intro y N D hD S hS a ha
  have hre : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have hb := norm_primeLogResponse_sub_fermi_le a p hD S hS N
    (s := 3 / 2 + I * y) (by norm_num) hq (by rw [hre]; linarith)
  rw [hre] at hb
  have hv : (-logDeriv riemannZeta ((3 / 2 + a - q : ℝ) : ℂ)).re ≤ V :=
    real_logDeriv_mass_antitone (by linarith) (by linarith)
  have hbound : ‖primeLogResponse p D S N (3 / 2 + I * y) -
      fermiPrimeLogResponse a p D S N (3 / 2 + I * y)‖ ≤ (q⁻¹ ^ N * M) * V :=
    hb.trans (mul_le_mul_of_nonneg_left hv (mul_nonneg (by positivity) hM))
  have hrate : 2 * u / (1 + u) = u * q⁻¹ := by
    dsimp [q]
    field_simp
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * ((q⁻¹ ^ N * M) * V) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [hrate, mul_pow, pow_succ]; ring

/-- The whole change of weight tends to zero at source normalization,
uniformly for arbitrary moving cutoffs, prime sieves and Fermi parameters
at least one half. Only the polynomial is fixed. -/
theorem tendsto_normalized_prime_sub_fermi (p : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (D : ℕ → ℕ) (S : ℕ → Finset ℕ) (a : ℕ → ℝ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N) (hS : ∀ N, ∀ r ∈ S N, r.Prime)
    (ha : ∀ᶠ N in atTop, 1 / 2 ≤ a N) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      (primeLogResponse p (D N) (S N) N (3 / 2 + I * y) -
        fermiPrimeLogResponse (a N) p (D N) (S N) N (3 / 2 + I * y))) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_normalized_primeFermi_bound p hu hu1
  have hbound : ∀ᶠ N in atTop,
      ‖(u : ℂ) ^ (N + 1) * (primeLogResponse p (D N) (S N) N (3 / 2 + I * y) -
        fermiPrimeLogResponse (a N) p (D N) (S N) N (3 / 2 + I * y))‖ ≤
        C * (2 * u / (1 + u)) ^ N := by
    filter_upwards [hD, ha] with N hDN haN
    exact hC y N (D N) hDN (S N) (hS N) (a N) haN
  apply squeeze_zero_norm' hbound
  have hr : 2 * u / (1 + u) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ 2 * u / (1 + u)) hr).const_mul C

/-- Fermi weighting of the actual normalized prime tail, retaining the
unchanged zero-isolating polynomial, prime sieve and sampling point. -/
def normalizedFermiPrimeLogResponse (a : ℝ) (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    fermiPrimeLogResponse a (zetaRightHalfPoleJetFilter rho hrho) D
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The complete original prime-tail source is stable under any moving
Fermi parameter at least one half. The cutoff has no upper-size condition
in this independently proved error estimate. -/
theorem tendsto_actual_prime_sub_fermi (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ) (a : ℕ → ℝ) (hD : ∀ᶠ N in atTop, 1 ≤ D N)
    (ha : ∀ᶠ N in atTop, 1 / 2 ≤ a N) :
    Tendsto (fun N => normalizedPrimeLogResponse rho hrho N (D N) -
      normalizedFermiPrimeLogResponse (a N) rho hrho N (D N)) atTop (𝓝 0) := by
  have h := tendsto_normalized_prime_sub_fermi (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
    (u := 3 / 2 - rho.1.re) (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)
    D (zetaRightHalfPrimePatternPrimes rho) a hD
    (fun N r hr => (zetaRightHalfPrimePatternPrimes_eligible rho N r hr).1) ha
  simpa only [normalizedPrimeLogResponse, normalizedFermiPrimeLogResponse, mul_sub] using h

/-- The actual Fermi parameter supplied by the proved global zero-free
margin satisfies the uniform comparison at every moving height band.
No condition on the chosen height schedule is needed for this error. -/
theorem tendsto_actual_prime_sub_margin_fermi (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (H : ℕ → ℝ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N) :
    Tendsto (fun N => normalizedPrimeLogResponse rho hrho N (D N) -
      normalizedFermiPrimeLogResponse (1 - 2 * zetaFermiZeroMargin (H N)) rho hrho N (D N))
      atTop (𝓝 0) := by
  apply tendsto_actual_prime_sub_fermi rho hrho D _ hD
  exact Eventually.of_forall fun N => by linarith [(zetaFermiZeroMargin_bounds (H N)).2]

/-- Under the hypothetical right-half zero, the Fermi-weighted moment
has the same negative multiplicity limit as the original ordinary-prime
tail. This identifies the surviving source and does not bound it away. -/
theorem tendsto_normalizedFermiPrimeLogResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (a : ℕ → ℝ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2)
    (ha : ∀ᶠ N in atTop, 1 / 2 ≤ a N) :
    Tendsto (fun N => normalizedFermiPrimeLogResponse (a N) rho hrho N (D N)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hp := tendsto_normalizedPrimeLogResponse rho hrho D hD
  have he := tendsto_actual_prime_sub_fermi rho hrho D a (hD.mono fun _ h => h.1) ha
  simpa only [sub_sub_cancel, sub_zero] using hp.sub he

end
end RiemannGaussian.SquarefreeEulerQuadratic
