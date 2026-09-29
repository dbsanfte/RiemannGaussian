/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaMoebiusLogHarmonicBound
import RiemannGaussian.ZetaRieszGlobalPrimePeriod
import RiemannGaussian.NatProductCollision
import Mathlib.Data.Nat.Totient

/-!
# Signed logarithmic sums for the Riesz second moment

The logarithmic Möbius sum is bounded before taking its square. Prime
exclusions retain their exact local factors. These estimates are intended
for the existing Riesz response, with all prime counts kept together.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSieveQuadratic

/-- The finite logarithmic Möbius sum, retaining every excluded prime. -/
def logPrefix (S : Finset ℕ) (M : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, if ∀ p ∈ S, ¬p ∣ n then
    (μ n : ℝ)/n * Real.log (x/n) else 0

@[simp] theorem logPrefix_zero (S : Finset ℕ) (x : ℝ) : logPrefix S 0 x = 0 := by
  simp [logPrefix]

/-- The earlier harmonic cancellation controls the integer logarithmic
cutoff by an absolute constant, independent of its prime-count content. -/
theorem logPrefix_empty_integer (M : ℕ) : |logPrefix ∅ M M| ≤ 5 := by
  rcases M with _ | M
  · simp
  rcases M with _ | M
  · norm_num [logPrefix]
  have hM : 1 < M+1+1 := by omega
  have hMR : (0 : ℝ) < (M+1+1 : ℕ) := by positivity
  have hlog : 0 < Real.log (M+1+1 : ℕ) := Real.log_pos (by exact_mod_cast hM)
  have he : logPrefix ∅ (M+1+1) (M+1+1 : ℕ) =
      pairedEtaMoebiusLogHarmonic (M+1+1)*Real.log (M+1+1 : ℕ) := by
    unfold logPrefix pairedEtaMoebiusLogHarmonic
    simp only [Finset.notMem_empty,forall_false,implies_true,if_true,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    simp only [pairedEtaMoebiusTrialLogWeight,if_pos hM,Real.log_div hMR.ne' hnR.ne']
    field_simp
  rw [he,abs_mul,abs_of_pos hlog]
  exact (le_div_iff₀ hlog).mp (abs_pairedEtaMoebiusLogHarmonic_le_five_div_log hM)

/-- Fractional physical endpoints cost at most two additional units.
There is no prime-density approximation in this signed bound. -/
theorem logPrefix_empty_bound (M : ℕ) {x : ℝ} (hlo : (M : ℝ) ≤ x)
    (hhi : x < M+1) : |logPrefix ∅ M x| ≤ 7 := by
  rcases M.eq_zero_or_pos with rfl | hM
  · simp
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hx : 0 < x := hMR.trans_le hlo
  have he : logPrefix ∅ M x = logPrefix ∅ M M+
      Real.log (x/M)*moebiusHarmonicPrefix M := by
    unfold logPrefix moebiusHarmonicPrefix
    simp only [Finset.notMem_empty,forall_false,implies_true,if_true,Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [Real.log_div hx.ne' hnR.ne',Real.log_div hMR.ne' hnR.ne',
      Real.log_div hx.ne' hMR.ne']
    ring
  have hlog0 : 0 ≤ Real.log (x/M) := Real.log_nonneg ((one_le_div hMR).mpr hlo)
  have hratio : x/M < 2 := (div_lt_iff₀ hMR).mpr (by
    have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith)
  have hlog1 : Real.log (x/M) ≤ 1 :=
    (Real.log_le_sub_one_of_pos (div_pos hx hMR)).trans (by linarith)
  rw [he]
  apply (abs_add_le _ _).trans
  have hprod : |Real.log (x/M)*moebiusHarmonicPrefix M| ≤ 2 := by
    rw [abs_mul,abs_of_nonneg hlog0]
    exact (mul_le_mul hlog1 (abs_moebiusHarmonicPrefix_le_two M)
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  linarith [logPrefix_empty_integer M]

/-- Removing one prime retains its exact divided-cutoff recurrence. -/
theorem logPrefix_insert (S : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (hS : ∀ q ∈ S, q.Prime) (M : ℕ) (x : ℝ) :
    logPrefix (insert p S) M x = logPrefix S M x+
      (1/(p : ℝ))*logPrefix (insert p S) (M/p) (x/p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdiv : logPrefix S M x = logPrefix (insert p S) M x+
      ∑ n ∈ Finset.Icc 1 M, if p ∣ n then
        (if ∀ q ∈ S, ¬q ∣ n then (μ n : ℝ)/n*Real.log (x/n) else 0) else 0 := by
    simp only [logPrefix,← Finset.sum_add_distrib,Finset.forall_mem_insert]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hd : p ∣ n <;> by_cases h : ∀ q ∈ S, ¬q ∣ n <;> simp [hd,h]
  rw [sum_Icc_dvd_eq hp.pos] at hdiv
  have he : (∑ n ∈ Finset.Icc 1 (M/p), if ∀ q ∈ S, ¬q ∣ p*n then
      (μ (p*n) : ℝ)/(p*n : ℕ)*Real.log (x/(p*n : ℕ)) else 0) =
      -(1/(p : ℝ))*logPrefix (insert p S) (M/p) (x/p) := by
    simp only [logPrefix,Finset.mul_sum,Finset.forall_mem_insert]
    apply Finset.sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hsame : (∀ q ∈ S, ¬q ∣ p*n) ↔ (∀ q ∈ S, ¬q ∣ n) := by
      apply forall₂_congr
      intro q hq
      have hqp : ¬q ∣ p := by
        intro hd
        have heq : q = p := ((Nat.dvd_prime hp).mp hd).resolve_left (hS q hq).ne_one
        exact hpS (heq ▸ hq)
      simp [(hS q hq).dvd_mul,hqp]
    simp only [hsame,moebius_prime_mul_eq_not_dvd hp]
    by_cases hd : p ∣ n
    · simp [hd]
    rw [if_neg hd,Int.cast_neg]
    by_cases h : ∀ q ∈ S, ¬q ∣ n
    · rw [if_pos h,if_pos ⟨hd,h⟩]
      simp only [Nat.cast_mul,div_mul_eq_div_div]
      ring
    · rw [if_neg h,if_neg (fun hh => h hh.2)]
      simp
  rw [he] at hdiv
  linarith

/-- The finite local sieve factor. It depends on excluded primes, not on
the number of prime factors of the tested integers. -/
def exclusionCost (S : Finset ℕ) : ℝ := ∏ p ∈ S, (p : ℝ)/(p-1)

/-- Uniform signed logarithmic cancellation with arbitrary finite prime
exclusions. The local Euler factors are paid exactly. -/
theorem logPrefix_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (M : ℕ) {x : ℝ} (hlo : (M : ℝ) ≤ x) (hhi : x < M+1) :
    |logPrefix S M x| ≤ 7*exclusionCost S := by
  induction S using Finset.induction_on generalizing M x with
  | empty => simpa [exclusionCost] using logPrefix_empty_bound M hlo hhi
  | @insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self _ _)
    have hSP : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hcost : 0 ≤ exclusionCost S := by
      apply Finset.prod_nonneg
      intro q hq
      have hq : (1 : ℝ) < q := by exact_mod_cast (hSP q hq).one_lt
      positivity
    induction M using Nat.strong_induction_on generalizing x with
    | h M rec =>
      rcases M.eq_zero_or_pos with rfl | hM
      · simp only [logPrefix_zero,abs_zero,exclusionCost,
          Finset.prod_insert hpS]
        change 0 ≤ 7*((p : ℝ)/(p-1)*exclusionCost S)
        positivity
      have hquot : M/p < M := Nat.div_lt_self hM hp.one_lt
      have hlo' : ((M/p : ℕ) : ℝ) ≤ x/p := by
        apply (le_div_iff₀ (by linarith : (0 : ℝ) < p)).mpr
        have hmul : ((M/p : ℕ) : ℝ)*p ≤ M := by exact_mod_cast Nat.div_mul_le_self M p
        exact hmul.trans hlo
      have hhi' : x/p < (M/p : ℕ)+1 := by
        apply (div_lt_iff₀ (by linarith : (0 : ℝ) < p)).mpr
        have he : (M+1 : ℝ) ≤ ((M/p : ℕ)+1 : ℝ)*p := by
          exact_mod_cast (show M+1 ≤ (M/p+1)*p by
            have hh := Nat.lt_mul_div_succ M hp.pos
            simpa only [Nat.mul_comm] using Nat.succ_le_of_lt hh)
        exact hhi.trans_le he
      have hrec := rec (M/p) hquot hlo' hhi'
      rw [logPrefix_insert S hp hpS hSP M x]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(p : ℝ))]
      calc
        _ ≤ 7*exclusionCost S+(1/(p : ℝ))*(7*exclusionCost (insert p S)) :=
          add_le_add (ih hSP M hlo hhi) (mul_le_mul_of_nonneg_left hrec (by positivity))
        _ = 7*exclusionCost (insert p S) := by
          rw [show exclusionCost (insert p S) = (p : ℝ)/(p-1)*exclusionCost S by
            simp only [exclusionCost,Finset.prod_insert hpS]]
          field_simp [(by linarith : (p : ℝ) ≠ 0),(by linarith : (p : ℝ)-1 ≠ 0)]
          ring

/-- Prime exclusions give precisely the inverse Euler totient density. -/
theorem exclusionCost_primeFactors {g : ℕ} (hg : 0 < g) :
    exclusionCost g.primeFactors = (g : ℝ)/g.totient := by
  have ht : (g.totient : ℝ) = (g : ℝ)*∏ p ∈ g.primeFactors, (1-(p : ℝ)⁻¹) := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors g)
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,
      Rat.cast_one,Rat.cast_inv] using hh
  have hp p (hp : p ∈ g.primeFactors) : (1 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have he : exclusionCost g.primeFactors = (∏ p ∈ g.primeFactors, (1-(p : ℝ)⁻¹))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hpm
    field_simp [(by linarith [hp p hpm] : (p : ℝ) ≠ 0),
      (by linarith [hp p hpm] : (p : ℝ)-1 ≠ 0)]
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [he,ht,div_mul_eq_div_div,div_self hgR,one_div]

private theorem coprime_iff_primeFactors {g : ℕ} (hg : g ≠ 0) (n : ℕ) :
    g.Coprime n ↔ ∀ p ∈ g.primeFactors, ¬p ∣ n := by
  constructor
  · intro hc p hp hd
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one
      ((Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hd).trans (by rw [hc.gcd_eq_one]))
  · intro h
    by_contra hc
    obtain ⟨p,hp,hpg,hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact h p (hp.mem_primeFactors hpg hg) hpn

/-- The signed row of the actual logarithmic Selberg quadratic form is
bounded before squaring. Non-squarefree common factors contribute zero. -/
theorem divisor_log_row_bound (R g : ℕ) (hg : 0 < g) {x : ℝ}
    (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) :
    |∑ d ∈ Finset.Icc 1 R, if g ∣ d then
      (μ d : ℝ)*Real.log (x/d)/d else 0| ≤ 7/(g.totient : ℝ) := by
  have ht : (0 : ℝ) < g.totient := by exact_mod_cast Nat.totient_pos.mpr hg
  rw [sum_Icc_dvd_eq hg]
  by_cases hsf : Squarefree g
  swap
  · have he : (∑ n ∈ Finset.Icc 1 (R/g),
        (μ (g*n) : ℝ)*Real.log (x/(g*n : ℕ))/(g*n : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hs => hsf hs.of_mul_left)]
      simp
    rw [he,abs_zero]
    positivity
  have he : (∑ n ∈ Finset.Icc 1 (R/g),
      (μ (g*n) : ℝ)*Real.log (x/(g*n : ℕ))/(g*n : ℕ)) =
      (μ g : ℝ)/g*logPrefix g.primeFactors (R/g) (x/g) := by
    simp only [logPrefix,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hc : g.Coprime n
    · rw [if_pos ((coprime_iff_primeFactors hg.ne' n).mp hc),
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
      simp only [Int.cast_mul,Nat.cast_mul,div_mul_eq_div_div]
      ring
    · rw [if_neg (fun h => hc ((coprime_iff_primeFactors hg.ne' n).mpr h)),
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          (fun hs => hc (Nat.coprime_of_squarefree_mul hs))]
      simp
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hb := logPrefix_bound g.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (R/g)
    (x := x/g) (by
      apply (le_div_iff₀ hgR).mpr
      have hh : ((R/g : ℕ) : ℝ)*g ≤ R := by exact_mod_cast Nat.div_mul_le_self R g
      exact hh.trans hlo) (by
      apply (div_lt_iff₀ hgR).mpr
      have hh : (R+1 : ℝ) ≤ ((R/g : ℕ)+1 : ℝ)*g := by
        exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.succ_le_of_lt (Nat.lt_mul_div_succ R hg))
      exact hhi.trans_le hh)
  rw [he,abs_mul,abs_div,abs_of_pos hgR]
  calc
    _ ≤ (1/(g : ℝ))*(7*exclusionCost g.primeFactors) := mul_le_mul
      (div_le_div_of_nonneg_right (abs_real_moebius_le_one g) hgR.le) hb
      (abs_nonneg _) (by positivity)
    _ = _ := by rw [exclusionCost_primeFactors hg]; field_simp

private theorem exclusionCost_le_divisor_sum {g : ℕ} (hg : g ≠ 0) :
    exclusionCost g.primeFactors ≤ ∑ d ∈ g.divisors, (d.divisors.card : ℝ)/d := by
  have he := Nat.sum_divisors_filter_squarefree hg
    (f := fun d => (d.divisors.card : ℝ)/d)
  rw [Nat.factors_eq] at he
  have hprod : (∏ p ∈ g.primeFactors, (1+2/(p : ℝ))) =
      ∑ d ∈ g.divisors with Squarefree d, (d.divisors.card : ℝ)/d := by
    rw [he,Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T hT
    have hTP : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hT hp)
    have hsf : Squarefree (∏ p ∈ T, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact Nat.coprime_iff_isRelPrime.mp ((hTP p hp).coprime_iff_not_dvd.mpr
          (fun hd => hpq (((hTP q hq).dvd_iff_eq (hTP p hp).ne_one).mp hd).symm))
      · intro p hp
        exact (hTP p hp).squarefree
    rw [show T.val.prod = ∏ p ∈ T, p by
      simp only [Finset.prod_eq_multiset_prod,Multiset.map_id']]
    rw [ZetaRieszSmoothHead.card_divisors_of_squarefree hsf,Nat.primeFactors_prod hTP]
    simp only [Finset.prod_div_distrib,Finset.prod_const,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_prod]
  calc
    _ ≤ ∏ p ∈ g.primeFactors, (1+2/(p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        exact div_nonneg (by linarith) (by linarith)
      · intro p hp
        have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < p-1)).mpr
        have he : (1+2/(p : ℝ))*(p-1) = p+(p-2)/p := by
          field_simp [(by linarith : (p : ℝ) ≠ 0)]
          ring
        rw [he]
        exact le_add_of_nonneg_right (div_nonneg (by linarith) (by linarith))
    _ = _ := hprod
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)

/-- The complete inverse-square divisor mass costs at most four; this
bound includes every factorization and every prime count. -/
theorem divisor_inverse_square_sum_le_four (R : ℕ) :
    (∑ d ∈ Finset.Icc 1 R, (d.divisors.card : ℝ)/(d : ℝ)^2) ≤ 4 := by
  have he (n : ℕ) : (n.divisors.card : ℝ)/(n : ℝ)^2 =
      ∑ ab ∈ n.divisorsAntidiagonal, (1/(ab.1 : ℝ))^2*(1/(ab.2 : ℝ))^2 := by
    rw [Nat.sum_divisorsAntidiagonal (fun a b => (1/(a : ℝ))^2*(1/(b : ℝ))^2)]
    have hh : (∑ d ∈ n.divisors, (1/(d : ℝ))^2*(1/(n/d : ℕ))^2) =
        ∑ _d ∈ n.divisors, (1/(n : ℝ))^2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← mul_pow,div_mul_div_comm,one_mul,← Nat.cast_mul,
        Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [hh]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  simp_rw [he]
  rw [ZetaRieszGlobalCurvature.weighted_hyperbola
    (fun a b => (1/(a : ℝ))^2*(1/(b : ℝ))^2)]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (1/(d : ℝ))^2*2 := by
      apply Finset.sum_le_sum
      intro d _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two _) (sq_nonneg _)
    _ = (∑ d ∈ Finset.Icc 1 R, (1/(d : ℝ))^2)*2 := by rw [Finset.sum_mul]
    _ ≤ _ := by linarith [sum_Icc_inv_sq_le_two R]

/-- Summing all coprimality costs loses only one logarithm, uniformly in
the number and sizes of the prime factors of the common divisor. -/
theorem inverse_totient_sum_bound (R : ℕ) :
    (∑ g ∈ Finset.Icc 1 R, 1/(g.totient : ℝ)) ≤ 4*(1+Real.log R) := by
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 R, ∑ d ∈ g.divisors, ((d.divisors.card : ℝ)/d)/g := by
      apply Finset.sum_le_sum
      intro g hg
      have hgR : (0 : ℝ) < g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
      rw [← Finset.sum_div]
      have h := div_le_div_of_nonneg_right
        (exclusionCost_le_divisor_sum (Nat.ne_of_gt (Finset.mem_Icc.mp hg).1)) hgR.le
      rw [exclusionCost_primeFactors (Finset.mem_Icc.mp hg).1] at h
      convert h using 1
      field_simp
    _ ≤ (1+Real.log R)*(∑ d ∈ Finset.Icc 1 R, ((d.divisors.card : ℝ)/d)/d) :=
      ZetaRieszGlobalCurvature.weighted_divisor_harmonic_le (fun _ => by positivity) R
    _ = (1+Real.log R)*(∑ d ∈ Finset.Icc 1 R, (d.divisors.card : ℝ)/(d : ℝ)^2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (divisor_inverse_square_sum_le_four R)
        (by linarith [Real.log_natCast_nonneg R] : 0 ≤ 1+Real.log R)
      simpa only [mul_comm] using h

/-- Diagonalize the literal least-common-multiple quadratic form before
estimating any signed logarithmic row. -/
theorem quadratic_eq_diagonal (R : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, f d*f e/(Nat.lcm d e : ℝ)) =
      ∑ g ∈ Finset.Icc 1 R, (g.totient : ℝ)*
        (∑ d ∈ Finset.Icc 1 R, if g ∣ d then f d/d else 0)^2 := by
  have hcommon d (hd : d ∈ Finset.Icc 1 R) e :
      (∑ g ∈ Finset.Icc 1 R, if g ∣ Nat.gcd d e then (g.totient : ℝ) else 0) =
        Nat.gcd d e := by
    have hd0 := (Finset.mem_Icc.mp hd).1
    have hg0 : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd0
    have hset : (Finset.Icc 1 R).filter (fun g => g ∣ Nat.gcd d e) =
        (Nat.gcd d e).divisors := by
      ext g
      simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_,_⟩,hgd⟩
        exact ⟨hgd,hg0.ne'⟩
      · rintro ⟨hgd,_⟩
        have hg : 0 < g := Nat.pos_of_dvd_of_pos hgd hg0
        exact ⟨⟨hg,(Nat.le_of_dvd hd0 (hgd.trans (Nat.gcd_dvd_left d e))).trans
          (Finset.mem_Icc.mp hd).2⟩,hgd⟩
    rw [← Finset.sum_filter,hset,← Nat.cast_sum,Nat.sum_totient]
  have hentry d (hd : d ∈ Finset.Icc 1 R) e (he : e ∈ Finset.Icc 1 R) :
      f d*f e/(Nat.lcm d e : ℝ) =
        ∑ g ∈ Finset.Icc 1 R, (g.totient : ℝ)*
          (if g ∣ d then f d/d else 0)*(if g ∣ e then f e/e else 0) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have heR : (0 : ℝ) < e := by exact_mod_cast (Finset.mem_Icc.mp he).1
    have hlR : (0 : ℝ) < Nat.lcm d e := by
      exact_mod_cast Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    have hprod : (Nat.gcd d e : ℝ)*Nat.lcm d e = (d : ℝ)*e := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    calc
      _ = (f d/d)*(f e/e)*(Nat.gcd d e : ℝ) := by
        field_simp
        linear_combination -(f d*f e)*hprod
      _ = (f d/d)*(f e/e)*∑ g ∈ Finset.Icc 1 R,
          if g ∣ Nat.gcd d e then (g.totient : ℝ) else 0 := by rw [hcommon d hd e]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        simp only [Nat.dvd_gcd_iff]
        by_cases hgd : g ∣ d <;> by_cases hge : g ∣ e <;> simp [hgd,hge]
        ring
  calc
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, ∑ g ∈ Finset.Icc 1 R,
        (g.totient : ℝ)*(if g ∣ d then f d/d else 0)*(if g ∣ e then f e/e else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_congr rfl (fun e he => hentry d hd e he)
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ g ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (g.totient : ℝ)*(if g ∣ d then f d/d else 0)*(if g ∣ e then f e/e else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ g ∈ Finset.Icc 1 R, ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (g.totient : ℝ)*(if g ∣ d then f d/d else 0)*(if g ∣ e then f e/e else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring

/-- One logarithmic budget for the original Riesz quadratic form. Every
Möbius cross term is retained until the signed rows have been bounded.
The numerical constant is independent of every prime-count class. -/
theorem logarithmic_quadratic_bound (R : ℕ) {x : ℝ}
    (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) :
    (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      ((μ d : ℝ)*Real.log (x/d))*((μ e : ℝ)*Real.log (x/e))/(Nat.lcm d e : ℝ)) ≤
      196*(1+Real.log R) := by
  rw [quadratic_eq_diagonal]
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 R, 49/(g.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      have ht : (0 : ℝ) < g.totient := by
        exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hg).1
      have hb := divisor_log_row_bound R g (Finset.mem_Icc.mp hg).1 hlo hhi
      have hs := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb) ht.le
      rw [sq_abs] at hs
      apply hs.trans_eq
      field_simp
      ring
    _ = 49*(∑ g ∈ Finset.Icc 1 R, 1/(g.totient : ℝ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ _ := by nlinarith [inverse_totient_sum_bound R]

end RiemannGaussian.ZetaRieszSieveQuadratic
