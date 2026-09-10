/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFactorResponse
import RiemannGaussian.ZetaRoughSquarefreeWindowSource
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Liouville

/-!
# Signed finite Euler factors on the actual rough support

The original coprime Euler multiplier retains an exact prime product and
an explicit phase gain. Distinct primes force a strict joint gain on every
compact complex set. On the actual rough physical support, however, the
whole prime-factor feature mass tends to zero uniformly beyond the
square-root line. Both the value multiplier minus one and its logarithmic
companion therefore have a uniform vanishing allowance on each original
Cauchy circle of radius below one. The full signed arithmetic bound still
requires control of the other response multipliers and their total mass.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.CoprimeEulerPhase
noncomputable section

/-- The original multiplicative feature keeps both real damping and phase. -/
theorem feature_mul (s : ℂ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    zetaPrimeFeature s (a * b) = zetaPrimeFeature s a * zetaPrimeFeature s b := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [zetaPrimeFeature, Nat.cast_mul, Real.log_mul haR hbR, Complex.ofReal_add]
  rw [show -(s * ((Real.log a : ℂ) + Real.log b)) =
    -(s * (Real.log a : ℂ)) + -(s * (Real.log b : ℂ)) by ring, Complex.exp_add]

private def arithmeticFeature (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else zetaPrimeFeature s n, by simp⟩

private theorem arithmeticFeature_multiplicative (s : ℂ) :
    (arithmeticFeature s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [arithmeticFeature, zetaPrimeFeature], ?_⟩
  intro m n hm hn _
  simp only [arithmeticFeature, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
    if_neg (Nat.mul_ne_zero hm hn)]
  exact feature_mul s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

/-- The literal finite divisor sum equals the complete prime-factor
product on every squarefree integer. All intersections precede the norm. -/
theorem coprimeEuler_eq_product {P : ℕ} (hP : Squarefree P) (s : ℂ) :
    zetaCoprimeEulerFactor P s = ∏ p ∈ P.primeFactors, (1 - zetaPrimeFeature s p) := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (arithmeticFeature s) (arithmeticFeature_multiplicative s) hP
  simp only [arithmeticFeature, ArithmeticFunction.coe_mk] at h
  have he1 : (∏ p ∈ P.primeFactors, (1 - if p = 0 then 0 else zetaPrimeFeature s p)) =
      ∏ p ∈ P.primeFactors, (1 - zetaPrimeFeature s p) := by
    exact Finset.prod_congr rfl (fun p hp ↦ by
      rw [if_neg (Nat.prime_of_mem_primeFactors hp).ne_zero])
  rw [he1] at h
  rw [h]
  unfold zetaCoprimeEulerFactor zetaFiniteDirichletSeries
  apply Finset.sum_congr rfl
  intro d hd
  rw [if_neg (Nat.pos_of_mem_divisors hd).ne']

/-- The exact original prime multiplier is its two divisor terms. -/
theorem coprimeEuler_prime {p : ℕ} (hp : p.Prime) (s : ℂ) :
    zetaCoprimeEulerFactor p s = 1 - zetaPrimeFeature s p := by
  rw [coprimeEuler_eq_product hp.squarefree, hp.primeFactors]
  simp

/-- The feature's real part retains the literal prime logarithmic phase. -/
theorem feature_re (s : ℂ) (p : ℕ) :
    (zetaPrimeFeature s p).re = zetaPrimeExpWeight s.re p * Real.cos (s.im * Real.log p) := by
  simp only [zetaPrimeFeature, Complex.exp_re, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, Real.cos_neg, zetaPrimeExpWeight, neg_mul]

/-- The exact square identity exposes the phase lost in the triangle cost. -/
theorem norm_factor_sq (s : ℂ) (p : ℕ) :
    ‖1 - zetaPrimeFeature s p‖ ^ 2 =
      (1 + zetaPrimeExpWeight s.re p) ^ 2 -
        2 * zetaPrimeExpWeight s.re p * (1 + Real.cos (s.im * Real.log p)) := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [one_mul, Complex.conj_re, ← Complex.sq_norm, norm_one,
    norm_zetaPrimeFeature, feature_re]
  ring

/-- The exact nonnegative saving exponent for one original Euler factor. -/
def phaseGain (s : ℂ) (p : ℕ) : ℝ :=
  zetaPrimeExpWeight s.re p * (1 + Real.cos (s.im * Real.log p)) /
    (1 + zetaPrimeExpWeight s.re p) ^ 2

/-- No phase saving is assumed: its sign follows from the exact cosine. -/
theorem phaseGain_nonneg (s : ℂ) (p : ℕ) : 0 ≤ phaseGain s p := by
  apply div_nonneg
  · exact mul_nonneg (Real.exp_pos _).le (by linarith [Real.neg_one_le_cos (s.im * Real.log p)])
  · positivity

/-- A phase-sensitive factor bound retains an explicit gain over its
positive triangle envelope at every complex argument. -/
theorem norm_factor_le_with_phase (s : ℂ) (p : ℕ) :
    ‖1 - zetaPrimeFeature s p‖ ≤
      (1 + zetaPrimeExpWeight s.re p) * Real.exp (-phaseGain s p) := by
  let w := zetaPrimeExpWeight s.re p
  let g := phaseGain s p
  have hw : 0 < w := Real.exp_pos _
  have he : (1 + w) ^ 2 * g = w * (1 + Real.cos (s.im * Real.log p)) := by
    change (1 + w) ^ 2 * (w * (1 + Real.cos (s.im * Real.log p)) / (1 + w) ^ 2) = _
    field_simp [show 1 + w ≠ 0 by positivity]
  have hs := norm_factor_sq s p
  change ‖1 - zetaPrimeFeature s p‖ ^ 2 =
    (1 + w) ^ 2 - 2 * w * (1 + Real.cos (s.im * Real.log p)) at hs
  have hb := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2 * g)) (sq_nonneg (1 + w))
  have hexp : Real.exp (-2 * g) = Real.exp (-g) ^ 2 := by
    rw [show -2 * g = -g + -g by ring, Real.exp_add, pow_two]
  rw [hexp] at hb
  have hpos : 0 ≤ (1 + w) * Real.exp (-g) := by positivity
  change ‖1 - zetaPrimeFeature s p‖ ≤ (1 + w) * Real.exp (-g)
  nlinarith [norm_nonneg (1 - zetaPrimeFeature s p)]

/-- Complete prime products keep the sum of phase gains. This is an
estimate for the real repository multiplier, not a synthetic sequence. -/
theorem norm_coprimeEuler_le_with_phase {P : ℕ} (hP : Squarefree P) (s : ℂ) :
    ‖zetaCoprimeEulerFactor P s‖ ≤
      (∏ p ∈ P.primeFactors, (1 + zetaPrimeExpWeight s.re p)) *
        Real.exp (-(∑ p ∈ P.primeFactors, phaseGain s p)) := by
  rw [coprimeEuler_eq_product hP, norm_prod]
  calc
    _ ≤ ∏ p ∈ P.primeFactors,
        (1 + zetaPrimeExpWeight s.re p) * Real.exp (-phaseGain s p) :=
      Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun p _ ↦ norm_factor_le_with_phase s p)
    _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]

/-- Distinct primes cannot have a positive integral logarithmic relation. -/
theorem prime_log_nat_relation {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 0 < a) :
    (a : ℝ) * Real.log p ≠ (b : ℝ) * Real.log q := by
  intro h
  have he := congrArg Real.exp h
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hp.pos),
    Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hq.pos)] at he
  have hn : p ^ a = q ^ b := by exact_mod_cast he
  have hdiv : p ∣ q ^ b := hn ▸ dvd_pow_self p ha.ne'
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdiv))

/-- Unique prime factorization prevents two distinct prime phases from
both attaining the negative real direction at any one ordinate. -/
theorem not_two_prime_antiphases {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (t : ℝ) :
    ¬(Real.cos (t * Real.log p) = -1 ∧ Real.cos (t * Real.log q) = -1) := by
  rintro ⟨hpc, hqc⟩
  have ht : t ≠ 0 := by intro h; subst t; norm_num at hpc
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hpc
  obtain ⟨l, hl⟩ := Real.cos_eq_neg_one_iff.mp hqc
  let a := (2 * k + 1).natAbs
  let b := (2 * l + 1).natAbs
  have hb : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz := Int.natAbs_eq_zero.mp h
    omega
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have h1 : |t| * Real.log p = (a : ℝ) * Real.pi := by
    have h := congrArg abs hk
    rw [show Real.pi + (k : ℝ) * (2 * Real.pi) =
      (((2 * k + 1 : ℤ) : ℝ)) * Real.pi by push_cast; ring] at h
    simpa only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hlogp,
      a, Nat.cast_natAbs, Int.cast_abs] using h.symm
  have h2 : |t| * Real.log q = (b : ℝ) * Real.pi := by
    have h := congrArg abs hl
    rw [show Real.pi + (l : ℝ) * (2 * Real.pi) =
      (((2 * l + 1 : ℤ) : ℝ)) * Real.pi by push_cast; ring] at h
    simpa only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hlogq,
      b, Nat.cast_natAbs, Int.cast_abs] using h.symm
  apply prime_log_nat_relation hp hq hpq hb
  apply mul_left_cancel₀ (abs_pos.mpr ht).ne'
  calc
    |t| * ((b : ℝ) * Real.log p) = (b : ℝ) * (|t| * Real.log p) := by ring
    _ = (b : ℝ) * ((a : ℝ) * Real.pi) := by rw [h1]
    _ = (a : ℝ) * ((b : ℝ) * Real.pi) := by ring
    _ = (a : ℝ) * (|t| * Real.log q) := by rw [h2]
    _ = |t| * ((a : ℝ) * Real.log q) := by ring

/-- A factor loses its entire phase saving exactly at its negative
real direction. The real damping is strictly positive. -/
theorem phaseGain_eq_zero_iff (s : ℂ) (p : ℕ) :
    phaseGain s p = 0 ↔ Real.cos (s.im * Real.log p) = -1 := by
  have hw : 0 < zetaPrimeExpWeight s.re p := Real.exp_pos _
  rw [phaseGain, div_eq_zero_iff]
  have hd : (1 + zetaPrimeExpWeight s.re p) ^ 2 ≠ 0 := by positivity
  simp only [hd, or_false, mul_eq_zero, hw.ne', false_or]
  constructor <;> intro h <;> linarith

/-- Two distinct prime factors supply a strictly positive joint gain
at every complex argument; no irrationality hypothesis is left open. -/
theorem pair_phaseGain_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (s : ℂ) :
    0 < phaseGain s p + phaseGain s q := by
  have h1 := phaseGain_nonneg s p
  have h2 := phaseGain_nonneg s q
  by_contra! h
  have hz1 : phaseGain s p = 0 := by linarith
  have hz2 : phaseGain s q = 0 := by linarith
  exact not_two_prime_antiphases hp hq hpq s.im
    ⟨(phaseGain_eq_zero_iff s p).mp hz1, (phaseGain_eq_zero_iff s q).mp hz2⟩

/-- The exact phase gain is continuous everywhere, including points
where an individual gain vanishes. -/
theorem continuous_phaseGain (p : ℕ) : Continuous (fun s : ℂ ↦ phaseGain s p) := by
  unfold phaseGain zetaPrimeExpWeight
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro s
    positivity

/-- Distinct primes give a positive gain uniform over an entire compact
analytic contour region. Its size is retained as an explicit obligation
for any attempt to accumulate a source-scale bound. -/
theorem exists_uniform_pair_phaseGain {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (K : Set ℂ) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ K, δ ≤ phaseGain s p + phaseGain s q := by
  exact hK.exists_forall_le' ((continuous_phaseGain p).add (continuous_phaseGain q)).continuousOn
    (fun s _ ↦ pair_phaseGain_pos hp hq hpq s)

/-- The complete squarefree Euler multiplier receives the same strict
uniform improvement whenever its prime factors contain this fixed pair. -/
theorem exists_uniform_coprimeEuler_gain {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (K : Set ℂ) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (P : ℕ), Squarefree P → p ∣ P → q ∣ P → ∀ s ∈ K,
      ‖zetaCoprimeEulerFactor P s‖ ≤
        (∏ a ∈ P.primeFactors, (1 + zetaPrimeExpWeight s.re a)) * Real.exp (-δ) := by
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_pair_phaseGain hp hq hpq K hK
  refine ⟨δ, hδ, fun P hP hpP hqP s hs ↦ (norm_coprimeEuler_le_with_phase hP s).trans ?_⟩
  have hpair : ({p, q} : Finset ℕ) ⊆ P.primeFactors := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨hp, hpP, hP.ne_zero⟩
    · exact Nat.mem_primeFactors.mpr ⟨hq, hqP, hP.ne_zero⟩
  have hsum : phaseGain s p + phaseGain s q ≤ ∑ a ∈ P.primeFactors, phaseGain s a := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hpair (fun a _ _ ↦ phaseGain_nonneg s a)
    simpa [hpq] using h
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp.mpr (neg_le_neg ((hb s hs).trans hsum))
  · exact Finset.prod_nonneg (fun a _ ↦ by have := (Real.exp_pos (-s.re * Real.log a)).le; positivity)

/-- Squarefreeness retains the complete logarithmic prime-factor mass. -/
theorem squarefree_log_eq_prime_sum {P : ℕ} (hP : Squarefree P) :
    Real.log P = ∑ p ∈ P.primeFactors, Real.log p := by
  have hprod : (∏ p ∈ P.primeFactors, (p : ℝ)) = P := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hP]
  rw [← hprod, Real.log_prod (fun p hp ↦
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)]

/-- The logarithmic size bounds the number of distinct factors. -/
theorem card_primeFactors_le_log {P : ℕ} (hP : Squarefree P) :
    (P.primeFactors.card : ℝ) ≤ Real.log P / Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  rw [squarefree_log_eq_prime_sum hP]
  calc
    _ = ∑ _p ∈ P.primeFactors, Real.log (2 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun p hp ↦ Real.log_le_log (by norm_num)
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le))

/-- The complete prime-factor feature mass is small when every prime
exceeds a common cutoff; no independence of phases is used. -/
theorem sum_featureWeight_rough_le {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (hrough : ∀ p ∈ P.primeFactors, R ≤ p) {σ : ℝ} (hσ : 0 ≤ σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    (∑ p ∈ P.primeFactors, zetaPrimeExpWeight s.re p) ≤
      (Real.log P / Real.log 2) * zetaPrimeExpWeight σ R := by
  have hw (p : ℕ) (hp : p ∈ P.primeFactors) :
      zetaPrimeExpWeight s.re p ≤ zetaPrimeExpWeight σ R := by
    apply Real.exp_le_exp.mpr
    have hlog : Real.log R ≤ Real.log p := Real.log_le_log
      (by exact_mod_cast (show 0 < R by omega)) (by exact_mod_cast hrough p hp)
    have hn := Real.log_natCast_nonneg p
    nlinarith
  calc
    _ ≤ ∑ _p ∈ P.primeFactors, zetaPrimeExpWeight σ R := Finset.sum_le_sum hw
    _ = (P.primeFactors.card : ℝ) * zetaPrimeExpWeight σ R := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_primeFactors_le_log hP) (Real.exp_pos _).le

/-- The entire original Euler multiplier differs from one by a bound
on its complete prime-factor mass, with every cross term included. -/
theorem norm_coprimeEuler_sub_one_le {P : ℕ} (hP : Squarefree P) (s : ℂ) :
    ‖zetaCoprimeEulerFactor P s - 1‖ ≤
      Real.exp (∑ p ∈ P.primeFactors, zetaPrimeExpWeight s.re p) - 1 := by
  rw [coprimeEuler_eq_product hP]
  simpa only [sub_eq_add_neg, norm_neg, norm_zetaPrimeFeature] using
    P.primeFactors.norm_prod_one_add_sub_one_le (fun p ↦ -zetaPrimeFeature s p)

/-- The explicit budget at the original quadratic prime cutoff. -/
def roughEulerBudget (rho : NontrivialZetaZero) (σ : ℝ) (N : ℕ) : ℝ :=
  (8 * N / Real.log 2) * zetaPrimeExpWeight σ (zetaRightHalfPrimePatternCutoff rho N)

/-- The budget has no sign hypothesis hidden in its later squeeze. -/
theorem roughEulerBudget_nonneg (rho : NontrivialZetaZero) (σ : ℝ) (N : ℕ) :
    0 ≤ roughEulerBudget rho σ N := by
  unfold roughEulerBudget zetaPrimeExpWeight
  positivity

/-- Every prime-factor family in the actual physical support obeys
the same Euler mass bound throughout a right half-plane. -/
theorem actual_factor_feature_mass_le (rho : NontrivialZetaZero) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re) :
    (∑ p ∈ P.primeFactors, zetaPrimeExpWeight s.re p) ≤ roughEulerBudget rho σ N := by
  obtain ⟨hw, _, hsf, _, hrough⟩ := zetaRightHalfRoughSquarefreeWindowCoefficient_support rho hN hc
  have hP : Squarefree P := hsf.squarefree_of_dvd hPn
  have hlog : Real.log P ≤ 8 * N := by
    have hle : P ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) hPn
    have hlogPn := Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hP.ne_zero))
      (by exact_mod_cast hle : (P : ℝ) ≤ n)
    exact hlogPn.trans hw.2
  apply (sum_featureWeight_rough_le hP hR
    (fun p hp ↦ (hrough p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hPn)).le) hσ hs).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The original Euler multiplier of every actual physical divisor
has one uniform error bound. Neither the divisor nor the complex argument
is fixed in advance inside the stated right half-plane. -/
theorem actual_factor_Euler_error_le (rho : NontrivialZetaZero) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖zetaCoprimeEulerFactor P s - 1‖ ≤ Real.exp (roughEulerBudget rho σ N) - 1 := by
  have hsf := (zetaRightHalfRoughSquarefreeWindowCoefficient_support rho hN hc).2.2.1
  exact (norm_coprimeEuler_sub_one_le (hsf.squarefree_of_dvd hPn) s).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (actual_factor_feature_mass_le rho hN hc hPn hR hσ hs)) 1)

/-- Above the square-root line the actual quadratic-cutoff budget
tends to zero, with the floor and original window length retained. -/
theorem tendsto_roughEulerBudget (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {σ : ℝ} (hσ : 1 / 2 < σ) : Tendsto (roughEulerBudget rho σ) atTop (𝓝 0) := by
  let c := zetaRightHalfPrimePatternSlope rho
  let A := fun N : ℕ ↦ ⌊c * (N : ℝ)⌋₊
  have hc : 0 < c := zetaRightHalfPrimePatternSlope_pos rho hrho
  have hA : Tendsto A atTop atTop := tendsto_nat_floor_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have hAR : Tendsto (fun N ↦ (A N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hA
  have hδ : 0 < 2 * σ - 1 := by linarith
  have hlim := ((tendsto_rpow_neg_atTop hδ).comp hAR).const_mul (16 / (c * Real.log 2))
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (roughEulerBudget_nonneg rho σ)) _ hlim
  filter_upwards [hA.eventually (eventually_ge_atTop 1)] with N hAN
  have hApos : (0 : ℝ) < A N := by exact_mod_cast (show 0 < A N by omega)
  have hAone : (1 : ℝ) ≤ A N := by exact_mod_cast hAN
  have hfloor : c * N < (A N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN : (N : ℝ) ≤ 2 * (A N : ℝ) / c := (le_div_iff₀ hc).mpr (by nlinarith)
  have he : (A N : ℝ) * zetaPrimeExpWeight σ (zetaRightHalfPrimePatternCutoff rho N) =
      (A N : ℝ) ^ (-(2 * σ - 1)) := by
    change (A N : ℝ) * Real.exp (-σ * Real.log ((A N ^ 2 : ℕ) : ℝ)) = _
    rw [Nat.cast_pow, Real.log_pow, Real.rpow_def_of_pos hApos]
    calc
      _ = Real.exp (Real.log (A N)) * Real.exp (-σ * ((2 : ℕ) * Real.log (A N))) := by
        rw [Real.exp_log hApos]
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring
  calc
    roughEulerBudget rho σ N = (8 / Real.log 2) * N *
        zetaPrimeExpWeight σ (zetaRightHalfPrimePatternCutoff rho N) := by
      unfold roughEulerBudget
      ring
    _ ≤ (8 / Real.log 2) * (2 * (A N : ℝ) / c) *
        zetaPrimeExpWeight σ (zetaRightHalfPrimePatternCutoff rho N) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by positivity))
        (Real.exp_pos _).le
    _ = (16 / (c * Real.log 2)) * (A N : ℝ) ^ (-(2 * σ - 1)) := by rw [← he]; ring

/-- The full product allowance vanishes, not merely each separate
prime factor. This is uniform over all actual physical divisors. -/
theorem tendsto_roughEulerAllowance (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun N ↦ Real.exp (roughEulerBudget rho σ N) - 1) atTop (𝓝 0) := by
  have h := (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_roughEulerBudget rho hrho hσ)).sub_const 1
  simpa using h

/-- Every fixed analytic circle of radius below one has uniform
Euler-factor error tending to zero on every actual physical divisor.
No choice of one favourable point on the circle is involved. -/
theorem actual_cauchy_factor_Euler_error_le (rho : NontrivialZetaZero)
    {r : ℝ} (hr : r < 1) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N)
    {s : ℂ} (hs : s ∈ Metric.closedBall (3 / 2 + I * rho.1.im) r) :
    ‖zetaCoprimeEulerFactor P s - 1‖ ≤ Real.exp (roughEulerBudget rho (3 / 2 - r) N) - 1 := by
  apply actual_factor_Euler_error_le rho hN hc hPn hR (by linarith : 0 ≤ 3 / 2 - r)
  have hd : ‖s - (3 / 2 + I * rho.1.im)‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - (3 / 2 + I * rho.1.im))).trans hd
  have hsr : (s - (3 / 2 + I * (rho.1.im : ℂ))).re = s.re - 3 / 2 := by simp
  rw [hsr, abs_le] at hre
  linarith [hre.1]

/-- The error from the preceding whole-circle estimate vanishes at
each actual source. Its rate can be slow as the circle approaches radius one. -/
theorem tendsto_actual_cauchy_factor_Euler_allowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {r : ℝ} (hr : r < 1) :
    Tendsto (fun N ↦ Real.exp (roughEulerBudget rho (3 / 2 - r) N) - 1) atTop (𝓝 0) :=
  tendsto_roughEulerAllowance rho hrho (by linarith)

/-- The original logarithmic Euler channel is the negative derivative
of the same complete finite multiplier, including the unit and zero cases. -/
theorem hasDerivAt_coprimeEuler (P : ℕ) (s : ℂ) :
    HasDerivAt (zetaCoprimeEulerFactor P) (-zetaCoprimeEulerLogFactor P s) s := by
  have ht (d : ℕ) : HasDerivAt (fun z ↦ (μ d : ℂ) * zetaPrimeFeature z d)
      (-((μ d : ℂ) * (Real.log d : ℂ) * zetaPrimeFeature s d)) s := by
    have h := (((hasDerivAt_id s).mul_const (Real.log d : ℂ)).neg.cexp).const_mul (μ d : ℂ)
    dsimp only [Pi.neg_apply, id_eq] at h
    unfold zetaPrimeFeature
    convert! h using 1
    ring
  unfold zetaCoprimeEulerFactor zetaCoprimeEulerLogFactor zetaFiniteDirichletSeries
  convert! HasDerivAt.fun_sum (u := P.divisors) (fun d _ ↦ ht d) using 1
  exact (Finset.sum_neg_distrib _).symm

/-- Cauchy's estimate controls the entire logarithmic companion by
the same arithmetic Euler error on a slightly larger circle. -/
theorem actual_cauchy_factor_EulerLog_error_le (rho : NontrivialZetaZero)
    {r : ℝ} (hr : r < 1) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N)
    {s : ℂ} (hs : s ∈ Metric.closedBall (3 / 2 + I * rho.1.im) r) :
    ‖zetaCoprimeEulerLogFactor P s‖ ≤
      (Real.exp (roughEulerBudget rho (3 / 2 - (1 + r) / 2) N) - 1) / ((1 - r) / 2) := by
  have hd : 0 < (1 - r) / 2 := by linarith
  have hf : Differentiable ℂ (fun z ↦ zetaCoprimeEulerFactor P z - 1) :=
    (differentiable_zetaFiniteDirichletSeries P.divisors (fun d ↦ (μ d : ℂ))).sub_const 1
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s)
    (f := fun z ↦ zetaCoprimeEulerFactor P z - 1) hd hf.diffContOnCl
    (fun z hz ↦ actual_cauchy_factor_Euler_error_le rho (by linarith : (1 + r) / 2 < 1)
      hN hc hPn hR (show z ∈ Metric.closedBall (3 / 2 + I * rho.1.im) ((1 + r) / 2) from
        Metric.closedBall_subset_closedBall' (by
          have hdist : dist s (3 / 2 + I * rho.1.im) ≤ r := hs
          linarith) (Metric.sphere_subset_closedBall hz)))
  rw [((hasDerivAt_coprimeEuler P s).sub_const 1).deriv, norm_neg] at hbound
  exact hbound

/-- One allowance retains both Euler channels over the actual circle. -/
def roughEulerChannelAllowance (rho : NontrivialZetaZero) (r : ℝ) (N : ℕ) : ℝ :=
  (1 + 1 / ((1 - r) / 2)) *
    (Real.exp (roughEulerBudget rho (3 / 2 - (1 + r) / 2) N) - 1)

/-- Both original Euler channels have a uniform bound together for
every divisor of every nonzero actual rough-window coefficient. -/
theorem actual_cauchy_factor_Euler_channels_le (rho : NontrivialZetaZero)
    {r : ℝ} (hr : r < 1) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N)
    {s : ℂ} (hs : s ∈ Metric.closedBall (3 / 2 + I * rho.1.im) r) :
    ‖zetaCoprimeEulerFactor P s - 1‖ + ‖zetaCoprimeEulerLogFactor P s‖ ≤
      roughEulerChannelAllowance rho r N := by
  have he := actual_cauchy_factor_Euler_error_le rho (by linarith : (1 + r) / 2 < 1)
    hN hc hPn hR (Metric.closedBall_subset_closedBall (by linarith : r ≤ (1 + r) / 2) hs)
  have hl := actual_cauchy_factor_EulerLog_error_le rho hr hN hc hPn hR hs
  exact (add_le_add he hl).trans_eq (by unfold roughEulerChannelAllowance; ring)

/-- The complete two-channel allowance vanishes, with no omitted
logarithmic derivative term. Multiplying or summing other growing response
coefficients still requires their own budget. -/
theorem tendsto_roughEulerChannelAllowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {r : ℝ} (hr : r < 1) :
    Tendsto (roughEulerChannelAllowance rho r) atTop (𝓝 0) := by
  unfold roughEulerChannelAllowance
  have h := (tendsto_roughEulerAllowance rho hrho
    (by linarith : 1 / 2 < 3 / 2 - (1 + r) / 2)).const_mul (1 + 1 / ((1 - r) / 2))
  simpa only [mul_zero] using h

/-- The retained phase saving is bounded by twice the feature mass;
strict positivity by itself does not imply a large quantitative reserve. -/
theorem phaseGain_le_twice_weight (s : ℂ) (p : ℕ) :
    phaseGain s p ≤ 2 * zetaPrimeExpWeight s.re p := by
  let w := zetaPrimeExpWeight s.re p
  have hw : 0 < w := Real.exp_pos _
  change w * (1 + Real.cos (s.im * Real.log p)) / (1 + w) ^ 2 ≤ 2 * w
  apply (div_le_iff₀ (by positivity : 0 < (1 + w) ^ 2)).mpr
  calc
    _ ≤ 2 * w := by
      have h := mul_le_mul_of_nonneg_left (Real.cos_le_one (s.im * Real.log p)) hw.le
      nlinarith
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (by nlinarith)

/-- The complete joint gain on every divisor of the actual rough
support has an upper bound tending to zero. The gain is not a missing
fixed source-scale reserve in these finite coprime Euler factors. -/
theorem actual_factor_phaseGain_le (rho : NontrivialZetaZero) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re) :
    (∑ p ∈ P.primeFactors, phaseGain s p) ≤ 2 * roughEulerBudget rho σ N := by
  calc
    _ ≤ ∑ p ∈ P.primeFactors, 2 * zetaPrimeExpWeight s.re p :=
      Finset.sum_le_sum (fun p _ ↦ phaseGain_le_twice_weight s p)
    _ = 2 * ∑ p ∈ P.primeFactors, zetaPrimeExpWeight s.re p := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (actual_factor_feature_mass_le rho hN hc hPn hR hσ hs)
      (by norm_num)

/-- The preceding vanishing upper bound is genuinely uniform over
moving actual integers, all their divisors, and the full right half-plane. -/
theorem eventually_actual_factor_phaseGain_lt (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {σ : ℝ} (hσ : 1 / 2 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ n P : ℕ,
      zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 → P ∣ n →
      ∀ s : ℂ, σ ≤ s.re → (∑ p ∈ P.primeFactors, phaseGain s p) < ε := by
  have hlim := (tendsto_roughEulerBudget rho hrho hσ).const_mul 2
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1,
    (tendsto_zetaRightHalfPrimePatternCutoff rho hrho).eventually (eventually_ge_atTop 1)] with N hb hN hR
  intro n P hc hPn s hs
  exact (actual_factor_phaseGain_le rho hN hc hPn hR (by linarith : 0 ≤ σ) hs).trans_lt hb

/-- The uniform two-channel estimate acts on every finite complex
coefficient family, with its complete mass charged explicitly. Pointwise
smallness is not silently promoted to a bound for an unbounded family. -/
theorem norm_weighted_actual_Euler_channels_le {ι : Type*} (rho : NontrivialZetaZero)
    {r : ℝ} (hr : r < 1) {N : ℕ} (hN : 1 ≤ N)
    (hR : 1 ≤ zetaRightHalfPrimePatternCutoff rho N) (T : Finset ι)
    (P : ι → ℕ) (c s : ι → ℂ)
    (hphysical : ∀ i ∈ T, ∃ n, zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 ∧ P i ∣ n)
    (hs : ∀ i ∈ T, s i ∈ Metric.closedBall (3 / 2 + I * rho.1.im) r) :
    ‖∑ i ∈ T, c i * (zetaCoprimeEulerFactor (P i) (s i) - 1)‖ +
      ‖∑ i ∈ T, c i * zetaCoprimeEulerLogFactor (P i) (s i)‖ ≤
        roughEulerChannelAllowance rho r N * ∑ i ∈ T, ‖c i‖ := by
  calc
    _ ≤ (∑ i ∈ T, ‖c i * (zetaCoprimeEulerFactor (P i) (s i) - 1)‖) +
        ∑ i ∈ T, ‖c i * zetaCoprimeEulerLogFactor (P i) (s i)‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = ∑ i ∈ T, ‖c i‖ *
        (‖zetaCoprimeEulerFactor (P i) (s i) - 1‖ + ‖zetaCoprimeEulerLogFactor (P i) (s i)‖) := by
      simp only [norm_mul, mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ T, ‖c i‖ * roughEulerChannelAllowance rho r N := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨n, hc, hPn⟩ := hphysical i hi
      exact mul_le_mul_of_nonneg_left
        (actual_cauchy_factor_Euler_channels_le rho hr hN hc hPn hR (hs i hi)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end
end RiemannGaussian.CoprimeEulerPhase
