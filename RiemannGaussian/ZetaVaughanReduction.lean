/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusMultipleBound
import RiemannGaussian.ZetaDominatedMomentBand
import RiemannGaussian.ZetaFiniteDirichlet

/-!
# Vaughan decomposition at the original factorial-moment source

The classical Vaughan identity retains both strict factor cutoffs in a
signed Möbius convolution. Its cofactor is the nonnegative sum of the
von Mangoldt weights of the divisors above the second cutoff. The exact
complex response, rather than a separate estimate on each raw interval,
connects this identity to the existing factorial-moment carrier.

Reference: R. C. Vaughan, *An elementary method in prime number theory*,
Acta Arithmetica 37 (1980), 111–115, DOI 10.4064/aa-37-1-111-115.
No bound for the surviving bilinear sum is assumed or proved by the identity.
-/

open Complex Filter Metric Set Topology
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation

namespace RiemannGaussian.ZetaVaughanReduction
noncomputable section

/-- Truncation of the actual arithmetic function, including its zero value. -/
def head (D : ℕ) (a : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ D then a n else 0
  map_zero' := by simp

/-- The entire complementary von Mangoldt divisor fibre. -/
def cofactor (V : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.vonMangoldt - head V ArithmeticFunction.vonMangoldt) * ζ

/-- The signed bilinear coefficient, with both large factors retained. -/
def bilinear (U V : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ) - head U μ) * cofactor V

/-- All three small-factor terms with their exact relative signs. -/
def small (U V : ℕ) : ArithmeticFunction ℝ :=
  head V ArithmeticFunction.vonMangoldt + head U μ * ArithmeticFunction.log -
    head U μ * head V ArithmeticFunction.vonMangoldt * ζ

/-- Vaughan's identity for the literal von Mangoldt weights, at every cutoff. -/
theorem vaughan (U V : ℕ) : ArithmeticFunction.vonMangoldt = small U V + bilinear U V := by
  unfold small bilinear cofactor
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  calc
    ArithmeticFunction.vonMangoldt = ArithmeticFunction.vonMangoldt *
        ((μ : ArithmeticFunction ℝ) * ζ) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
    _ = _ := by
      have h : (μ : ArithmeticFunction ℝ) * ζ * head V ArithmeticFunction.vonMangoldt =
          head V ArithmeticFunction.vonMangoldt := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
      linear_combination h

/-- Every retained cofactor is an exact sum over its large prime-power divisors. -/
theorem cofactor_eq (V n : ℕ) :
    cofactor V n = ∑ d ∈ n.divisors,
      if V < d then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [cofactor, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d _
  change ArithmeticFunction.vonMangoldt d - head V ArithmeticFunction.vonMangoldt d = _
  by_cases hd : d ≤ V <;> simp [head, hd, not_lt.mpr, not_le.mp]

/-- Positivity of the whole retained divisor fibre uses the exact prime weights. -/
theorem cofactor_nonneg (V n : ℕ) : 0 ≤ cofactor V n := by
  rw [cofactor_eq]
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

/-- The complete divisor identity pays for this cofactor by one logarithm. -/
theorem cofactor_le_log (V n : ℕ) : cofactor V n ≤ Real.log n := by
  have h := congrArg (fun a : ArithmeticFunction ℝ ↦ a n)
    ArithmeticFunction.vonMangoldt_mul_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.log_apply] at h
  rw [cofactor_eq, ← h]
  apply Finset.sum_le_sum
  intro d _
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Only prime-power divisors contribute, with the size cutoff still inside each fibre. -/
theorem cofactor_eq_primePower_sum (V n : ℕ) :
    cofactor V n = ∑ d ∈ n.divisors.filter IsPrimePow,
      if V < d then ArithmeticFunction.vonMangoldt d else 0 := by
  rw [cofactor_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : IsPrimePow d
  · rw [if_pos hd]
  · simp [hd, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd]

/-- Coprime multiplication preserves the full additive prime structure of
the retained cofactor, even when the divisor cutoff splits prime powers. -/
theorem cofactor_mul_of_coprime (V : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    cofactor V (a * b) = cofactor V a + cofactor V b := by
  rw [cofactor_eq_primePower_sum, Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
    Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hab),
    ← cofactor_eq_primePower_sum, ← cofactor_eq_primePower_sum]

/-- No cofactor at or below the second cutoff survives. -/
theorem cofactor_eq_zero {V n : ℕ} (hn : n ≤ V) : cofactor V n = 0 := by
  rw [cofactor_eq]
  apply Finset.sum_eq_zero
  intro d hd
  exact if_neg (not_lt.mpr ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.dvd_of_mem_divisors hd)).trans hn))

/-- Every product keeps the Möbius sign and the same full cofactor. -/
theorem bilinear_eq (U V n : ℕ) :
    bilinear U V n = ∑ a ∈ n.divisorsAntidiagonal,
      if U < a.1 then (μ a.1 : ℝ) * cofactor V a.2 else 0 := by
  rw [bilinear, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  change ((μ a.1 : ℝ) - head U μ a.1) * cofactor V a.2 = _
  by_cases ha : a.1 ≤ U <;> simp [head, ha, not_lt.mpr, not_le.mp]

/-- The exact coefficient has two strict lower cutoffs, hence this product support. -/
theorem bilinear_eq_zero {U V n : ℕ} (hn : n < (U + 1) * (V + 1)) :
    bilinear U V n = 0 := by
  rw [bilinear_eq]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hU : U < a.1
  · rw [if_pos hU, cofactor_eq_zero, mul_zero]
    have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
    by_contra hV
    exact (not_le.mpr hn) (hprod ▸ Nat.mul_le_mul (by omega : U + 1 ≤ a.1)
      (by omega : V + 1 ≤ a.2))
  · exact if_neg hU

/-- The original divisor-log majorant bounds every cutoff simultaneously. -/
theorem norm_bilinear_le (U V n : ℕ) :
    ‖(bilinear U V n : ℂ)‖ ≤ zetaMoebiusLogMajorant n := by
  rw [bilinear_eq, Complex.ofReal_sum, zetaMoebiusLogMajorant]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · rw [Complex.ofReal_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (cofactor_nonneg _ _)]
    have hm : ‖(μ a.1 : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a.1)
    exact (mul_le_mul_of_nonneg_right hm (cofactor_nonneg _ _)).trans
      (by simpa only [one_mul] using cofactor_le_log V a.2)
  · simpa using Real.log_natCast_nonneg a.2

/-- The finite prime-power Dirichlet polynomial, before any estimate. -/
def primeHead (V : ℕ) : ℂ → ℂ :=
  zetaFiniteDirichletSeries (Finset.Icc 1 V) (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))

/-- The exact meromorphic response of the two-large-factor coefficient. -/
def response (U V : ℕ) (s : ℂ) : ℂ :=
  ((riemannZeta s)⁻¹ - zetaMoebiusDirichletHead U s) *
    (-deriv riemannZeta s - primeHead V s * riemannZeta s)

private theorem real_convolution (a b : ArithmeticFunction ℝ) :
    (fun n ↦ ((a * b) n : ℂ)) =
      (fun n ↦ (a n : ℂ)) ⍟ (fun n ↦ (b n : ℂ)) := by
  funext n
  simp [ArithmeticFunction.mul_apply, LSeries.convolution_def]

/-- The finite prime-power prefix is a genuinely convergent series at every center. -/
theorem hasSum_primeHead (V : ℕ) (s : ℂ) :
    LSeriesHasSum (fun n ↦ (head V ArithmeticFunction.vonMangoldt n : ℂ)) s
      (primeHead V s) := by
  have h := LSeriesHasSum_of_support_Icc
    (fun n ↦ (head V ArithmeticFunction.vonMangoldt n : ℂ)) V (by simp)
    (fun n hn ↦ by simp [head, not_le.mpr hn]) s
  convert h using 1
  unfold primeHead zetaFiniteDirichletSeries
  apply Finset.sum_congr rfl
  intro n hn
  simp [head, (Finset.mem_Icc.mp hn).2]

/-- Absolute convergence and the exact response are discharged for the literal coefficient. -/
theorem hasSum_response (U V : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (bilinear U V n : ℂ)) s (response U V s) := by
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hm : (fun n ↦ (((μ : ArithmeticFunction ℝ) - head U μ) n : ℂ)) =
      zetaMoebiusTailCoefficient U := by
    funext n
    change (((μ n : ℝ) - head U μ n : ℝ) : ℂ) = _
    by_cases hn : n ≤ U <;> simp [head, zetaMoebiusTailCoefficient, hn, not_lt.mpr, not_le.mp]
  have hp := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hp
  have hc := (hp.sub (hasSum_primeHead V s)).convolution (LSeriesHasSum_one hs)
  have he : (fun n ↦ (cofactor V n : ℂ)) =
      ((fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) -
        (fun n ↦ (head V ArithmeticFunction.vonMangoldt n : ℂ))) ⍟ (fun _ ↦ (1 : ℂ)) := by
    rw [cofactor, real_convolution]
    apply LSeries.convolution_congr
    · intro n _
      change ((ArithmeticFunction.vonMangoldt n - head V ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) = _
      simp
    · intro n hn
      simp [hn]
  have hval : (-deriv riemannZeta s / riemannZeta s - primeHead V s) * riemannZeta s =
      -deriv riemannZeta s - primeHead V s * riemannZeta s := by
    rw [sub_mul, div_mul_cancel₀ _ hz]
  rw [hval] at hc
  rw [bilinear, real_convolution, hm, he]
  exact (LSeriesHasSum_zetaMoebiusTailCoefficient U hs).convolution hc

/-- The exact response of all small-factor terms. -/
def smallResponse (U V : ℕ) (s : ℂ) : ℂ :=
  primeHead V s + (zetaMoebiusDirichletHead U s * (-deriv riemannZeta s) +
    (-(zetaMoebiusDirichletHead U s * primeHead V s)) * riemannZeta s)

/-- The analytic Vaughan split preserves the complete logarithmic derivative. -/
theorem response_identity (U V : ℕ) {s : ℂ} (hs : riemannZeta s ≠ 0) :
    -logDeriv riemannZeta s = smallResponse U V s + response U V s := by
  simp only [logDeriv, Pi.div_apply, smallResponse, response]
  field_simp
  ring

/-- The small response also has its literal arithmetic coefficients; the
analytic and coefficientwise versions of Vaughan's identity commute. -/
theorem hasSum_smallResponse (U V : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (small U V n : ℂ)) s (smallResponse U V s) := by
  have hp := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hp
  have he : -deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta s := by
    simp [logDeriv, neg_div]
  rw [he] at hp
  have h := hp.sub (hasSum_response U V hs)
  rw [response_identity U V (riemannZeta_ne_zero_of_one_lt_re hs), add_sub_cancel_right] at h
  convert h using 1
  funext n
  have he := congrArg (fun a : ArithmeticFunction ℝ ↦ a n) (vaughan U V)
  rw [ArithmeticFunction.add_apply] at he
  simp only [Pi.sub_apply, he, Complex.ofReal_add, add_sub_cancel_right]

/-- The fixed polynomial acts on the entire small-factor response. -/
def smallFilter (p : Polynomial ℂ) (U V N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (smallResponse U V) s) N

/-- The same fixed polynomial acts on the genuine bilinear response. -/
def responseFilter (p : Polynomial ℂ) (U V N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (response U V) s) N

/-- The original polynomial filter splits with no coefficient or moment loss. -/
theorem filter_identity (p : Polynomial ℂ) (U V N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPrimeLogFilter p N s = smallFilter p U V N s + responseFilter p U V N s := by
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by
    change s ≠ 1
    intro h
    simp [h] at hs)
  have hm := (differentiable_zetaMoebiusDirichletHead U).analyticAt (z := s)
  have ha := (differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 V)
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))).analyticAt (z := s)
  have hsmall : AnalyticAt ℂ (smallResponse U V) s :=
    ha.add ((hm.mul hz.deriv.neg).add ((hm.mul ha).neg.mul hz))
  have hresponse : AnalyticAt ℂ (response U V) s :=
    ((hz.inv (riemannZeta_ne_zero_of_one_lt_re hs)).sub hm).mul
      (hz.deriv.neg.sub (ha.mul hz))
  have he : (fun z ↦ -logDeriv riemannZeta z) =ᶠ[𝓝 s]
      (fun z ↦ smallResponse U V z + response U V z) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz'
    exact response_identity U V (riemannZeta_ne_zero_of_one_lt_re hz')
  simp only [zetaPrimeLogFilter, smallFilter, responseFilter, zetaMomentSequenceFilter,
    Polynomial.sum, zetaPrimeLogMoment, signedTaylorMoment_congr _ he,
    signedTaylorMoment_add _ hsmall hresponse, mul_add, Finset.sum_add_distrib]

/-- Every filtered bilinear response is the actual absolutely convergent arithmetic sum. -/
theorem hasSum_responseFilter (p : Polynomial ℂ) (U V N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (bilinear U V n : ℂ) * zetaPrimeFilterKernel p N s n)
      (responseFilter p U V N s) := by
  have hc : LSeries.abscissaOfAbsConv (fun n ↦ (bilinear U V n : ℂ)) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (hasSum_response U V (by simpa using hy)).LSeriesSummable
  have he : response U V =ᶠ[𝓝 s] LSeries (fun n ↦ (bilinear U V n : ℂ)) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (hasSum_response U V hz).LSeries_eq.symm
  have hm (k : ℕ) := hasSum_signedTaylorMoment_LSeries
    (fun n ↦ (bilinear U V n : ℂ)) (by simp)
    (lt_of_le_of_lt hc (by exact_mod_cast hs)) k
  simp only [← signedTaylorMoment_congr _ he] at hm
  have h := hasSum_sum (s := p.support) (fun k _ ↦ (hm (N + k)).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The finite Möbius multiplier has a linear cutoff budget on the right half-plane. -/
theorem norm_moebiusHead_le (U : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaMoebiusDirichletHead U s‖ ≤ U := by
  rw [zetaMoebiusDirichletHead]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range U, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      have he : Complex.exp (-s * (Real.log (n + 1 : ℕ) : ℂ)) = zetaPrimeFeature s (n + 1) := by
        unfold zetaPrimeFeature
        simp only [neg_mul]
      rw [he]
      rw [norm_mul]
      have hm : ‖(μ (n + 1) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)
      exact (mul_le_mul hm (norm_zetaPrimeFeature_le_one hs _) (norm_nonneg _) (by norm_num)).trans_eq
        (one_mul 1)
    _ = _ := by simp

/-- Each prime-power term pays for its own logarithm before summing the finite prefix. -/
theorem norm_primeHead_le (V : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖primeHead V s‖ ≤ 2 * V := by
  rw [primeHead, zetaFiniteDirichletSeries]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 V, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        _ ≤ Real.log n * ‖zetaPrimeFeature s n‖ :=
          mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (norm_nonneg _)
        _ ≤ 2 := by simpa only [mul_comm] using norm_zetaPrimeFeature_mul_log_le_two hs n
    _ = _ := by simp; ring

private theorem unit_ball_re (y : ℝ) {s : ℂ}
    (hs : s ∈ closedBall (3 / 2 + I * (y : ℂ)) 1) : 1 / 2 ≤ s.re := by
  have hr := (Complex.abs_re_le_norm (s - (3 / 2 + I * (y : ℂ)))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hr
  linarith [(abs_le.mp hr).1]

/-- Every moment of the entire prime prefix has a cutoff-linear independent bound. -/
theorem norm_primeHead_moment_le (V N : ℕ) (y : ℝ) :
    ‖signedTaylorMoment N (primeHead V) (3 / 2 + I * y)‖ ≤ 2 * V := by
  have ha := differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 V)
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hd : DiffContOnCl ℂ (primeHead V) (ball (3 / 2 + I * (y : ℂ)) 1) :=
    ha.differentiableOn.diffContOnCl
  simpa only [one_pow, div_one] using norm_signedTaylorMoment_le (by norm_num) hd
    (fun s hs ↦ norm_primeHead_le V (unit_ball_re y (sphere_subset_closedBall hs))) N

/-- Both Type I terms and the finite prime prefix have one independent cutoff budget. -/
theorem exists_smallFilter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (U V N : ℕ),
      ‖smallFilter p U V N (3 / 2 + I * y)‖ ≤
        (2 * V + C * (U + 2 * U * V)) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_moment_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p U V N
  have hm := differentiable_zetaMoebiusDirichletHead U
  have ha := differentiable_zetaFiniteDirichletSeries (Finset.Icc 1 V)
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  have hg : Differentiable ℂ (fun s ↦ -(zetaMoebiusDirichletHead U s * primeHead V s)) :=
    (hm.mul ha).neg
  have hbound (k : ℕ) := hb (zetaMoebiusDirichletHead U)
    (fun s ↦ -(zetaMoebiusDirichletHead U s * primeHead V s)) hm hg U (2 * U * V)
    (by positivity) (by positivity) (fun s hs ↦ norm_moebiusHead_le U (by linarith))
    (fun s hs ↦ by
      rw [norm_neg, norm_mul]
      exact (mul_le_mul (norm_moebiusHead_le U (by linarith)) (norm_primeHead_le V hs)
        (norm_nonneg _) (by positivity)).trans_eq (by ring)) k
  have hz : AnalyticAt ℂ riemannZeta (3 / 2 + I * (y : ℂ)) :=
    analyticOn_riemannZeta _ (by intro h; have := congrArg Complex.re h; norm_num at this)
  have hsmall (k : ℕ) :
      ‖signedTaylorMoment k (smallResponse U V) (3 / 2 + I * y)‖ ≤
        2 * V + C * (U + 2 * U * V) := by
    have ha' : AnalyticAt ℂ (primeHead V) (3 / 2 + I * (y : ℂ)) := ha.analyticAt (z := _)
    have hb' : AnalyticAt ℂ (fun s ↦ zetaMoebiusDirichletHead U s * (-deriv riemannZeta s) +
        (-(zetaMoebiusDirichletHead U s * primeHead V s)) * riemannZeta s)
        (3 / 2 + I * (y : ℂ)) :=
      ((hm.analyticAt (z := _)).mul hz.deriv.neg).add ((hg.analyticAt (z := _)).mul hz)
    unfold smallResponse
    rw [signedTaylorMoment_add k ha' hb']
    exact (norm_add_le _ _).trans (add_le_add (norm_primeHead_moment_le V k y) (hbound k))
  rw [smallFilter, zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (2 * V + C * (U + 2 * U * V)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hsmall (N + k)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Both cutoffs can grow exponentially while the full small-factor allowance
decays geometrically at the original source scale. The estimate is uniform
over all choices below the two cutoff ceilings and needs no filter roots. -/
theorem exists_smallFilter_geometric_bound (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N U V : ℕ,
      U ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N →
      V ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N →
      ‖(u : ℂ) ^ (N + 1) * smallFilter p U V N (3 / 2 + I * y)‖ ≤
        C * (Real.sqrt u) ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_smallFilter_bound y hy
  let q := zetaMoebiusHeadGrowth u
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  refine ⟨(2 + 3 * C) * u * S + 1, by positivity, ?_⟩
  intro N U V hU hV
  have hD : (zetaMoebiusGeometricCutoff q N : ℝ) ≤ q ^ N :=
    Nat.floor_le (pow_nonneg (zero_le_one.trans hq) N)
  have hU' : (U : ℝ) ≤ q ^ N := (Nat.cast_le.mpr hU).trans hD
  have hV' : (V : ℝ) ≤ q ^ N := (Nat.cast_le.mpr hV).trans hD
  have hpow : 1 ≤ q ^ N := one_le_pow₀ hq
  have hUV : (U : ℝ) * V ≤ (q ^ N) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hU' hV' (Nat.cast_nonneg V) (by positivity)
  have hcost : 2 * (V : ℝ) + C * (U + 2 * U * V) ≤ (2 + 3 * C) * (q ^ N) ^ 2 := by
    have hsq : q ^ N ≤ (q ^ N) ^ 2 := by nlinarith
    have hsum : (U : ℝ) + 2 * U * V ≤ 3 * (q ^ N) ^ 2 := by nlinarith
    have hCsum := mul_le_mul_of_nonneg_left hsum hC.le
    nlinarith
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * ((2 * V + C * (U + 2 * U * V)) * S) :=
      mul_le_mul_of_nonneg_left (hb p U V N) (by positivity)
    _ ≤ u ^ (N + 1) * ((2 + 3 * C) * (q ^ N) ^ 2 * S) := by gcongr
    _ = ((2 + 3 * C) * u * S) * (u * q ^ 2) ^ N := by
      rw [mul_pow, pow_succ, show (q ^ N) ^ 2 = (q ^ 2) ^ N by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = ((2 + 3 * C) * u * S) * (Real.sqrt u) ^ N := by rw [zetaMoebiusHeadGrowth_rate hu]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Independent decay holds for every pair of moving cutoffs within the budget. -/
theorem tendsto_smallFilter (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (U V : ℕ → ℕ)
    (hU : ∀ N, U N ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N)
    (hV : ∀ N, V N ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * smallFilter p (U N) (V N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_smallFilter_geometric_bound p y hy hu hu1
  have hr : Real.sqrt u < 1 := by nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
  apply squeeze_zero_norm (fun N ↦ hb N (U N) (V N) (hU N) (hV N))
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg u) hr).const_mul C

/-- The complete hypothetical-zero source survives after both small-factor
sectors have been independently removed at exponentially growing cutoffs. -/
theorem tendsto_actual_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    let u := 3 / 2 - rho.1.re
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u)
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) *
      responseFilter (zetaRightHalfPoleJetFilter rho hrho) (D N) (D N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  dsimp only
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hsmall := tendsto_smallFilter (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hu hu1
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)))
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)))
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
  have h := (tendsto_zetaRightHalfPoleJetFilter rho hrho).sub hsmall
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [filter_identity _ _ _ N (by norm_num), mul_add, add_sub_cancel_left]

/-- The same source is carried by a genuinely convergent signed arithmetic series. -/
theorem tendsto_actual_sum (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    let u := 3 / 2 - rho.1.re
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u)
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑' n,
      (bilinear (D N) (D N) n : ℂ) *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply (tendsto_actual_source rho hrho).congr'
  filter_upwards [] with N
  rw [(hasSum_responseFilter _ _ _ N (by norm_num)).tsum_eq]

/-- The old finite band transports the bilinear response with its full
cutoff-independent geometric allowance; no new divisor mass is hidden. -/
theorem responseFilter_sub_band_le (p : Polynomial ℂ) (U V N : ℕ) (y : ℝ) :
    ‖responseFilter p U V N (3 / 2 + I * y) -
      zetaArithmeticBand (fun n ↦ (bilinear U V n : ℂ)) p N y‖ ≤
        (1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant p := by
  have h := norm_zetaDominatedFilter_sub_band_le
    (fun n ↦ (bilinear U V n : ℂ)) (norm_bilinear_le U V) p N y
  simpa only [zetaArithmeticFilter,
    (hasSum_responseFilter p U V N (s := 3 / 2 + I * (y : ℂ)) (by norm_num)).tsum_eq] using h

/-- Every original finite-band product retains both strict factor cutoffs,
the Möbius sign, the complete prime-divisor cofactor and its physical phase. -/
theorem band_eq_product_sum (p : Polynomial ℂ) (U V N : ℕ) (y : ℝ) :
    zetaArithmeticBand (fun n ↦ (bilinear U V n : ℂ)) p N y =
      ∑ n ∈ zetaPrimeLogBand N, ∑ a ∈ n.divisorsAntidiagonal,
        if U < a.1 ∧ V < a.2 then
          (μ a.1 : ℂ) * (cofactor V a.2 : ℂ) *
            zetaPrimeFilterKernel p N (3 / 2 + I * y) (a.1 * a.2 : ℕ) else 0 := by
  unfold zetaArithmeticBand
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  rw [bilinear_eq, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Nat.mem_divisorsAntidiagonal.mp ha).1]
  by_cases hU : U < a.1
  · rw [if_pos hU, Complex.ofReal_mul, Complex.ofReal_intCast]
    by_cases hV : V < a.2
    · rw [if_pos ⟨hU, hV⟩]
    · simp [hV, cofactor_eq_zero (not_lt.mp hV)]
  · simp [hU]

/-- Both factors exceed an exponentially growing cutoff inside the original
finite band, and the complete negative-multiplicity source is preserved.
An independent cofinal lower bound for this signed band remains open. -/
theorem tendsto_actual_band (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    let u := 3 / 2 - rho.1.re
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u)
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) *
      zetaArithmeticBand (fun n ↦ (bilinear (D N) (D N) n : ℂ))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u := 3 / 2 - rho.1.re
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u)
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have herror := tendsto_zetaDominatedFilter_sub_band
    (fun N n ↦ (bilinear (D N) (D N) n : ℂ)) (fun N ↦ norm_bilinear_le (D N) (D N)) p rho.1.im
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_actual_sum rho hrho).sub (hpow.mul herror)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [zetaArithmeticFilter]
  ring

end
end RiemannGaussian.ZetaVaughanReduction
