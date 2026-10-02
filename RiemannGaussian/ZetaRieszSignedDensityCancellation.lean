/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLongCutoffError

/-!
# Signed cancellation in the original rough-density prefixes

The elementary weighted Möbius inequality of Tao bounds the complete signed
reciprocal prefix by one for prime weights in `[0,1]`. The proof below uses
the integer divisor convolution and retains every parity before taking an
absolute value. It is a bound on the existing density scalar, not an
estimate for the remaining masked cofactor moments or their variation.

Reference: Terence Tao, *A remark on partial sums involving the Möbius
function*, arXiv:0908.4323, Theorem 1.1 and Remark 2.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedDensityCancellation
open Real

private def weightedMoebius (a : ℕ → ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul
    (ArithmeticFunction.prodPrimeFactors a)

private theorem weighted_apply (a : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    weightedMoebius a n = (μ n : ℝ) * ∏ p ∈ n.primeFactors, a p := by
  simp only [weightedMoebius, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.prodPrimeFactors_apply hn]

private theorem weighted_one (a : ℕ → ℝ) : weightedMoebius a 1 = 1 := by
  rw [weighted_apply a (by norm_num : (1 : ℕ) ≠ 0)]
  norm_num

private theorem divisor_convolution (a : ℕ → ℝ) :
    weightedMoebius a * ArithmeticFunction.zeta =
      ArithmeticFunction.prodPrimeFactors (fun p => 1-a p) := by
  have hf := (ArithmeticFunction.isMultiplicative_moebius.intCast (R := ℝ)).pmul
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors a)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors (fun p => 1-a p))).mpr
  intro p k hp
  change (weightedMoebius a * ArithmeticFunction.zeta) (p^k) =
    (ArithmeticFunction.prodPrimeFactors (fun p => 1-a p)) (p^k)
  cases k with
  | zero =>
    rw [pow_zero, ArithmeticFunction.coe_mul_zeta_apply]
    simp only [Nat.divisors_one, Finset.sum_singleton, weighted_one,
      ArithmeticFunction.prodPrimeFactors_apply (by norm_num : (1 : ℕ) ≠ 0),
      Nat.primeFactors_one, Finset.prod_empty]
  | succ k =>
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
      Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : (∑ j ∈ Finset.range k, weightedMoebius a (p^(j+1+1))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [weightedMoebius, ArithmeticFunction.moebius_apply_prime_pow
        (k := j+1+1) hp (by omega)]
    simp only [Nat.zero_add, pow_one, pow_zero]
    rw [hz, weighted_apply a hp.ne_zero,
      ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
      Nat.primeFactors_pow p (by omega), hp.primeFactors]
    simp only [weighted_one, Finset.prod_singleton,
      ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one]
    ring

private theorem product_bounds (a : ℕ → ℝ)
    (ha : ∀ p, p.Prime → 0 ≤ a p ∧ a p ≤ 1) (n : ℕ) :
    0 ≤ ∏ p ∈ n.primeFactors, a p ∧
      (∏ p ∈ n.primeFactors, a p) ≤ 1 :=
  ⟨Finset.prod_nonneg (fun p hp => (ha p (Nat.prime_of_mem_primeFactors hp)).1),
    Finset.prod_le_one (fun p hp => (ha p (Nat.prime_of_mem_primeFactors hp)).1)
      (fun p hp => (ha p (Nat.prime_of_mem_primeFactors hp)).2)⟩

private theorem complementary_product_bound (a : ℕ → ℝ)
    (ha : ∀ p, p.Prime → 0 ≤ a p ∧ a p ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    |weightedMoebius a n| +
      (∏ p ∈ n.primeFactors, (1-a p)) ≤ 1 + if n = 1 then 1 else 0 := by
  by_cases h1 : n = 1
  · simp [h1, weighted_one]
  have hne : n.primeFactors.Nonempty := by
    exact Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨p,hp⟩ := hne
  have hap := ha p (Nat.prime_of_mem_primeFactors hp)
  have hb : ∀ q, q.Prime → 0 ≤ 1-a q ∧ 1-a q ≤ 1 := by
    intro q hq
    have := ha q hq
    constructor <;> linarith
  have hpa : (∏ q ∈ n.primeFactors, a q) ≤ a p := by
    have ht := Finset.prod_le_one
      (s := n.primeFactors.erase p) (f := a)
      (fun q hq => (ha q (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq))).1)
      (fun q hq => (ha q (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq))).2)
    rw [← Finset.mul_prod_erase _ _ hp]
    exact (mul_le_mul_of_nonneg_left ht hap.1).trans_eq (mul_one _)
  have hpb : (∏ q ∈ n.primeFactors, (1-a q)) ≤ 1-a p := by
    have ht := Finset.prod_le_one
      (s := n.primeFactors.erase p) (f := fun q => 1-a q)
      (fun q hq => (hb q (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq))).1)
      (fun q hq => (hb q (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq))).2)
    rw [← Finset.mul_prod_erase _ _ hp]
    exact (mul_le_mul_of_nonneg_left ht (hb p (Nat.prime_of_mem_primeFactors hp)).1).trans_eq
      (mul_one _)
  have hm : |weightedMoebius a n| ≤ ∏ q ∈ n.primeFactors, a q := by
    rw [weighted_apply a hn, abs_mul, abs_of_nonneg (product_bounds a ha n).1]
    exact mul_le_of_le_one_left (product_bounds a ha n).1
      (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
  simp only [if_neg h1, add_zero]
  linarith

private theorem integer_rounding_bound {M n : ℕ} (hn : 0 < n) :
    0 ≤ (M : ℝ)/n-(M/n : ℕ) ∧
      (M : ℝ)/n-(M/n : ℕ) ≤ 1-(n : ℝ)⁻¹ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo := Nat.cast_div_le (m := M) (n := n) (α := ℝ)
  have hhi : (M : ℝ)+1 ≤ (n : ℝ)*((M/n : ℕ)+1) := by
    exact_mod_cast (Nat.lt_mul_div_succ M hn)
  refine ⟨by linarith, ?_⟩
  have he : (n : ℝ)*((M : ℝ)/n-(M/n : ℕ)) = M-(n : ℝ)*(M/n : ℕ) := by
    field_simp
  have hi : (n : ℝ)*(1-(n : ℝ)⁻¹) = n-1 := by field_simp
  nlinarith

/-- Tao's elementary inequality for every real prime weight in `[0,1]`.
The integer rounding and complete divisor convolution are both retained. -/
theorem weighted_moebius_harmonic_le_one (a : ℕ → ℝ)
    (ha : ∀ p, p.Prime → 0 ≤ a p ∧ a p ≤ 1) (M : ℕ) :
    |∑ n ∈ Finset.Icc 1 M, (μ n : ℝ)/n * ∏ p ∈ n.primeFactors, a p| ≤ 1 := by
  by_cases hM : M = 0
  · simp [hM]
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  let f := weightedMoebius a
  let g := ArithmeticFunction.prodPrimeFactors (fun p => 1-a p)
  let G : ℝ := ∑ n ∈ Finset.Icc 1 M, f n/n
  let H : ℝ := ∑ n ∈ Finset.Icc 1 M, |f n|/n
  have hn0 (n : ℕ) (hn : n ∈ Finset.Icc 1 M) : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hgn (n : ℕ) (hn : n ∈ Finset.Icc 1 M) :
      g n = ∏ p ∈ n.primeFactors, (1-a p) :=
    ArithmeticFunction.prodPrimeFactors_apply (hn0 n hn)
  have hgpos (n : ℕ) (hn : n ∈ Finset.Icc 1 M) : 0 ≤ g n := by
    rw [hgn n hn]
    apply Finset.prod_nonneg
    intro p hp
    have := (ha p (Nat.prime_of_mem_primeFactors hp)).2
    linarith
  have htotal : (∑ n ∈ Finset.Icc 1 M, g n) +
      (∑ n ∈ Finset.Icc 1 M, |f n|) ≤ M+1 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 M, ((1 : ℝ) + if n = 1 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [hgn n hn, add_comm]
        exact complementary_product_bound a ha (hn0 n hn)
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_eq',
        show 1 ≤ M by omega]
  have hconv : (∑ n ∈ Finset.Icc 1 M, f n*(M/n : ℕ)) =
      ∑ n ∈ Finset.Icc 1 M, g n := by
    have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f M
    have hI : Finset.Ioc 0 M = Finset.Icc 1 M := by ext n; simp; omega
    rw [hI, show f * ArithmeticFunction.zeta = g from divisor_convolution a] at h
    exact h.symm
  have hround :
      |∑ n ∈ Finset.Icc 1 M, f n*((M : ℝ)/n-(M/n : ℕ))| ≤
        (∑ n ∈ Finset.Icc 1 M, |f n|)-H := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 M, |f n*((M : ℝ)/n-(M/n : ℕ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 M, |f n| * (1-(n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        have hr := integer_rounding_bound (M := M) (Finset.mem_Icc.mp hn).1
        rw [abs_mul, abs_of_nonneg hr.1]
        exact mul_le_mul_of_nonneg_left hr.2 (abs_nonneg _)
      _ = _ := by
        simp only [H, Finset.sum_sub_distrib, mul_sub, mul_one, div_eq_mul_inv]
  have he : (M : ℝ)*G = (∑ n ∈ Finset.Icc 1 M, g n) +
      ∑ n ∈ Finset.Icc 1 M, f n*((M : ℝ)/n-(M/n : ℕ)) := by
    rw [← hconv]
    dsimp only [G]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hab : (M : ℝ)*|G| ≤ (∑ n ∈ Finset.Icc 1 M, g n) +
      (∑ n ∈ Finset.Icc 1 M, |f n|)-H := by
    calc
      _ = |(M : ℝ)*G| := by rw [abs_mul, abs_of_pos hMr]
      _ = |(∑ n ∈ Finset.Icc 1 M, g n) +
          ∑ n ∈ Finset.Icc 1 M, f n*((M : ℝ)/n-(M/n : ℕ))| := congrArg abs he
      _ ≤ |∑ n ∈ Finset.Icc 1 M, g n| +
          |∑ n ∈ Finset.Icc 1 M, f n*((M : ℝ)/n-(M/n : ℕ))| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (Finset.sum_nonneg hgpos)]
        linarith
  have hG : |G| ≤ 1 := by
    by_cases hH : H ≤ 1
    · apply le_trans _ hH
      have habs (n : ℕ) : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
      simpa only [G, H, abs_div, habs] using
        Finset.abs_sum_le_sum_abs (s := Finset.Icc 1 M) (f := fun n => f n/n)
    · have hH' : 1 < H := lt_of_not_ge hH
      nlinarith
  apply le_trans (le_of_eq ?_) hG
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [show f n = (μ n : ℝ)*(∏ p ∈ n.primeFactors, a p) from
    weighted_apply a (hn0 n hn)]
  ring

private theorem rough_mark_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : Squarefree n)
    (hcop : ¬∃ p ∈ S, p ∣ n) :
    RoughSquarefreeCounting.markedDensity S n =
      ((ZetaRieszUnsignedDivisorError.density S *
        ∏ p ∈ n.primeFactors, ((p : ℝ)+1)⁻¹ : ℝ) : ℂ) := by
  have hr : RoughSquarefreeCounting.markedDensity S n =
      ((∑ W ∈ S.powerset, (-1 : ℝ)^W.card *
        SquarefreeCounting.density (n.primeFactors ∪ W) : ℝ) : ℂ) := by
    rw [RoughSquarefreeCounting.markedDensity, if_pos hn, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun W _ => by push_cast; rfl)
  rw [hr]
  congr 1
  rw [ZetaRieszUnsignedDivisorError.density, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro W hW
  have hWp : ∀ p ∈ W, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hW hp)
  have hdis : Disjoint n.primeFactors W := by
    apply Finset.disjoint_left.mpr
    intro p hp hpW
    exact hcop ⟨p, Finset.mem_powerset.mp hW hpW, Nat.dvd_of_mem_primeFactors hp⟩
  rw [ZetaRieszSignedDensityMain.density_marks _ (fun p hp => by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact hWp p hp), Finset.prod_union hdis,
    ZetaRieszSignedDensityMain.density_marks W hWp]
  ring

/-- The literal rough-density coefficient is a weighted reciprocal
Möbius coefficient; excluded-prime intersections remain exactly zero. -/
theorem rough_coefficient_eq (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : 0 < n) :
    ((μ n : ℂ)*RoughSquarefreeCounting.markedDensity S n).re =
      ZetaRieszUnsignedDivisorError.density S * ((μ n : ℝ)/n *
        ∏ p ∈ n.primeFactors, if p ∈ S then 0 else (p : ℝ)/((p : ℝ)+1)) := by
  by_cases hsf : Squarefree n
  · by_cases hhit : ∃ p ∈ S, p ∣ n
    · obtain ⟨p,hp,hpn⟩ := hhit
      rw [RoughSquarefreeCounting.markedDensity_eq_zero_of_sieve_hit S hS
        ⟨p,hp,hpn⟩]
      have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hS p hp,hpn,hn.ne'⟩
      rw [Finset.prod_eq_zero hpf (by simp [hp])]
      simp
    · rw [rough_mark_product S hS hsf hhit]
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hp : (∏ p ∈ n.primeFactors,
          if p ∈ S then (0 : ℝ) else (p : ℝ)/((p : ℝ)+1)) =
          (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ)+1)⁻¹ := by
        calc
          _ = ∏ p ∈ n.primeFactors, (p : ℝ)*((p : ℝ)+1)⁻¹ := by
            apply Finset.prod_congr rfl
            intro p hp
            have hpS : p ∉ S := fun hh => hhit ⟨p,hh,Nat.dvd_of_mem_primeFactors hp⟩
            simp only [if_neg hpS, div_eq_mul_inv]
          _ = _ := by
            rw [Finset.prod_mul_distrib, ← Nat.cast_prod,
              Nat.prod_primeFactors_of_squarefree hsf]
      rw [hp]
      have hc : (μ n : ℂ) = ((μ n : ℝ) : ℂ) := by norm_cast
      rw [hc, ← Complex.ofReal_mul, Complex.ofReal_re]
      field_simp
  · have hm : (μ n : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    have hmc : (μ n : ℂ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    simp [hm,hmc]

/-- The ORIGINAL signed rough-density prefix is uniformly bounded by its
own density. This replaces the previous `1 + log D` allowance, for every
cutoff and every finite set of actual excluded primes. -/
theorem roughDensityPrefix_signed_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (D : ℕ) :
    |ZetaRieszLongCutoffError.roughDensityPrefix S D| ≤
      ZetaRieszUnsignedDivisorError.density S := by
  have he : ZetaRieszLongCutoffError.roughDensityPrefix S D =
      ZetaRieszUnsignedDivisorError.density S *
        ∑ n ∈ Finset.Icc 1 D, (μ n : ℝ)/n *
          ∏ p ∈ n.primeFactors, if p ∈ S then 0 else (p : ℝ)/((p : ℝ)+1) := by
    rw [ZetaRieszLongCutoffError.roughDensityPrefix, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n hn =>
      rough_coefficient_eq S hS (Finset.mem_Icc.mp hn).1)
  have ha : ∀ p, p.Prime →
      0 ≤ (if p ∈ S then (0 : ℝ) else (p : ℝ)/((p : ℝ)+1)) ∧
      (if p ∈ S then (0 : ℝ) else (p : ℝ)/((p : ℝ)+1)) ≤ 1 := by
    intro p _
    split_ifs
    · norm_num
    · constructor
      · positivity
      · apply (div_le_one (by positivity : (0 : ℝ) < (p : ℝ)+1)).mpr
        linarith
  rw [he, abs_mul, abs_of_pos (ZetaRieszLongCutoffError.rough_density_pos S hS)]
  exact (mul_le_mul_of_nonneg_left
    (weighted_moebius_harmonic_le_one _ ha D)
    (ZetaRieszLongCutoffError.rough_density_pos S hS).le).trans_eq (mul_one _)

/-- The unexcluded signed density prefix has its exact density as a
cutoff-independent allowance, improving its previously proved constant two. -/
theorem densityPrefix_signed_bound (D : ℕ) :
    |ZetaRieszCofactorDiscrepancy.densityPrefix D| ≤ SquarefreeCounting.density ∅ := by
  have he : ZetaRieszLongCutoffError.roughDensityPrefix ∅ D =
      ZetaRieszCofactorDiscrepancy.densityPrefix D := by
    simp only [ZetaRieszLongCutoffError.roughDensityPrefix, Complex.re_sum,
      ZetaRieszCofactorDiscrepancy.densityPrefix]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Squarefree n
    · rw [RoughSquarefreeCounting.markedDensity, if_pos hn]
      simp
    · simp only [RoughSquarefreeCounting.markedDensity, if_neg hn, mul_zero,
        Complex.zero_re]
      have hm : (μ n : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn
      simp [hm]
  have h := roughDensityPrefix_signed_bound ∅ (by simp) D
  simpa only [he, ZetaRieszUnsignedDivisorError.density,
    Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
    one_mul] using h

open ZetaRieszLongCutoffError

/-- A moving cutoff profile is charged only after its complete signed
prefix has been summed across all divisor parities. -/
theorem rough_profile_signed_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (R : ℕ) (f : ℕ → ℝ) :
    |∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*roughDensityPrefix S D| ≤
      ZetaRieszUnsignedDivisorError.density S *
        ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  rw [abs_mul, mul_comm (ZetaRieszUnsignedDivisorError.density S)]
  exact mul_le_mul_of_nonneg_left (roughDensityPrefix_signed_bound S hS D)
    (abs_nonneg _)

/-- Uniform signed bound for the original translated hinge profile.
Its cutoff loss is linear rather than quadratic in the hinge height. -/
theorem rough_hinge_signed_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (c : ℝ) :
    |∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
      (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix S D| ≤
      ZetaRieszUnsignedDivisorError.density S * max 0 c := by
  have h := rough_profile_signed_bound S hS ⌊exp c⌋₊ (fun d => max 0 (c-log d))
  simpa only [hinge_profile_variation] using h

/-- Exact owner conditioning eliminates its density factor before the
bound is applied. The whole signed cofactor sum can remain outside. -/
theorem owner_hinge_signed_bound (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) (c : ℝ) :
    |(((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
        (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*
          roughDensityPrefix (insert p S) D)| ≤
      ZetaRieszUnsignedDivisorError.density S * max 0 c := by
  have hSp : ∀ q ∈ insert p S, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hS q hq
  have hfac : 0 ≤ ((p : ℝ)+1)/(p : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hfac]
  calc
    _ ≤ (((p : ℝ)+1)/(p : ℝ))*
        (ZetaRieszUnsignedDivisorError.density (insert p S)*max 0 c) :=
      mul_le_mul_of_nonneg_left (rough_hinge_signed_bound (insert p S) hSp c) hfac
    _ = _ := by rw [← mul_assoc, rough_owner_normalization S hS hp hpS]

/-- Joint bounds retain the signed zeroth cofactor moment. In particular
the price is `|sum V|`, not `sum |V|` across cofactor counts or periods. -/
theorem owner_main_signed_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℝ) (U V : ℕ → ℝ) :
    let rho := SquarefreeCounting.density ∅
    let M := ∑ p ∈ P, (rho*U p - (((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*
          roughDensityPrefix {p} D)*V p)
    rho*(∑ p ∈ P, (U p-max 0 (L-log p)*|V p|)) ≤ M ∧
      M ≤ rho*(∑ p ∈ P, (U p+max 0 (L-log p)*|V p|)) := by
  dsimp only
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro p hp
  all_goals
    have hb := owner_hinge_signed_bound ∅ (by simp) (hP p hp) (by simp) (L-log p)
    simp only [Finset.insert_empty, ZetaRieszUnsignedDivisorError.density,
      Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
      one_mul] at hb
    have hc := mul_le_mul_of_nonneg_right hb (abs_nonneg (V p))
    rw [← abs_mul] at hc
    have hlo := (abs_le.mp hc).1
    have hhi := (abs_le.mp hc).2
    nlinarith only [hlo, hhi]

/-- An actual whole-core one-sided estimate with every owner, phase,
count, physical, allocation and factorial mask retained. The explicit
literal variation is NOT paid by this theorem. -/
theorem literal_whole_carrier_signed_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ ZetaRieszParityPacket.coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    let J := scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let E := 6*countingConstant*exp (-(N : ℝ)/128)*
      (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|))
    rho*(∑ p ∈ P, ((∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
      max 0 (L-log p)*|∑ a ∈ Finset.Icc 1 X, w a p|))-E ≤ rho*J ∧
    rho*J ≤ rho*(∑ p ∈ P, ((∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)+
      max 0 (L-log p)*|∑ a ∈ Finset.Icc 1 X, w a p|))+E := by
  dsimp only
  have hc := literal_whole_carrier_estimate hu hN B hB A y scale
  have hP : ∀ p ∈ ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree),
      p.Prime := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hn' := Finset.mem_filter.mp hn
    have hcore := ZetaRieszJointPrimeEnergy.core_count (hB hn'.1)
    exact (ZetaRieszJointPrimeEnergy.owner_data hn'.2 hcore).1
  have hm := owner_main_signed_bounds _ hP (SquarefreeVaughanLogSource.length u N)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p *
          VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) a)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p)
  dsimp only at hc hm
  have hclo := (abs_le.mp hc).1
  have hchi := (abs_le.mp hc).2
  constructor
  · linarith [hm.1]
  · linarith [hm.2]

/-- The classical unweighted reciprocal Möbius prefix also improves from
the repository's previous elementary allowance two to one. -/
theorem moebiusHarmonicPrefix_signed_bound (M : ℕ) :
    |moebiusHarmonicPrefix M| ≤ 1 := by
  simpa only [moebiusHarmonicPrefix, Finset.prod_const_one, mul_one] using
    weighted_moebius_harmonic_le_one (fun _ => (1 : ℝ)) (by intro p _; norm_num) M

/-- The real-weight inequality must not be transferred to a phase-twisted
prefix. Already the actual integer labels one and two give exactly `4/3`
at an admissible fixed height. This is not a core-carrier counterexample. -/
theorem phase_twisted_prefix_exact :
    54 < 19*Real.pi/log (2 : ℝ) ∧
      (∑ n ∈ Finset.Icc 1 2, (μ n : ℝ)/n *
        (∏ p ∈ n.primeFactors, (p : ℝ)/((p : ℝ)+1)) *
          cos ((19*Real.pi/log (2 : ℝ))*log n)) = 4/3 := by
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlu : log (2 : ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hc : cos (19*Real.pi) = -1 := by
    have h := cos_nat_mul_pi 19
    norm_num at h
    exact h
  constructor
  · apply (lt_div_iff₀ hl).mpr
    nlinarith [Real.pi_gt_three]
  · have hi : Finset.Icc 1 2 = ({1,2} : Finset ℕ) := by decide
    rw [hi, Finset.sum_insert (by decide)]
    simp only [Finset.sum_singleton, Nat.primeFactors_one, Finset.prod_empty,
      Nat.prime_two.primeFactors, Finset.prod_singleton,
      Int.cast_one, Nat.cast_one, div_one, log_one, mul_zero, cos_zero,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two, Int.cast_neg]
    norm_num
    rw [hc]
    norm_num

/-- There is no universal phase-twisted extension of the constant-one
prefix theorem, even at fixed heights above the low-zero exclusion. -/
theorem phase_twisted_prefix_not_bounded_by_one :
    ∃ y : ℝ, 54 < y ∧
      1 < (∑ n ∈ Finset.Icc 1 2, (μ n : ℝ)/n *
        (∏ p ∈ n.primeFactors, (p : ℝ)/((p : ℝ)+1)) *cos (y*log n)) := by
  refine ⟨19*Real.pi/log (2 : ℝ), phase_twisted_prefix_exact.1, ?_⟩
  rw [phase_twisted_prefix_exact.2]
  norm_num

end RiemannGaussian.ZetaRieszSignedDensityCancellation
