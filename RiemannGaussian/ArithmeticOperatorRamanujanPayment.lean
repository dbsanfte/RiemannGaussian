/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGcdAudit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Fixed-modulus exceptional prime powers cannot retain a power source

After the common coprime coefficient is killed, a fixed Ramanujan code
is confined to powers of the finitely many primes dividing its moduli.
An exact integer-divisor embedding bounds their total Mangoldt mass by
J*log(q) up to the dyadic cutoff 2^J. Their full fixed-height phase is
retained. The resulting centered fixed-modulus statistic is o(2^(beta J))
for EVERY beta>0; it therefore cannot be a source detector in the campaign.
This theorem does not cover growing moduli or shifted prime correlations.
-/

namespace RiemannGaussian.ArithmeticOperatorRamanujanPayment
noncomputable section
open ArithmeticOperatorRamanujanAudit SuzukiCarryCorrelation
open Filter
open scoped BigOperators Topology

/-- A finite, explicit bound independent of the tested integer. -/
def ramanujanBudget (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, ‖((d : ℤ)*ArithmeticFunction.moebius (q/d) : ℤ)‖

/-- The entire exceptional prime-power correction at one modulus. -/
def correction (q X : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*
    ((ramanujanDivisor q n-ArithmeticFunction.moebius q : ℤ) : ℂ)

/-- A bad prime power below 2^J embeds in the divisor lattice of q^J.
This includes every proper prime power; no density model is used. -/
theorem exceptional_prime_power_dvd {q n J : ℕ} (hn : IsPrimePow n)
    (hbad : ¬Nat.Coprime q n) (hsize : n ≤ 2^J) : n ∣ q^J := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hpq : p ∣ q := by
    apply hp.dvd_iff_not_coprime.mpr
    intro hc
    exact hbad ((Nat.coprime_pow_right_iff hk q p).mpr hc.symm)
  have hkJ : k ≤ J := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
    ((Nat.pow_le_pow_left hp.two_le k).trans hsize)
  exact (pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkJ)

/-- Exceptional Mangoldt mass is only logarithmic in the physical cutoff. -/
theorem exceptional_mass_le {q : ℕ} (hq : 0 < q) (J : ℕ) :
    (∑ n ∈ (Finset.Icc 1 (2^J)).filter (fun n => ¬Nat.Coprime q n),
      ArithmeticFunction.vonMangoldt n) ≤ (J : ℝ)*Real.log q := by
  classical
  let S := ((Finset.Icc 1 (2^J)).filter (fun n => ¬Nat.Coprime q n)).filter IsPrimePow
  have he : (∑ n ∈ (Finset.Icc 1 (2^J)).filter (fun n => ¬Nat.Coprime q n),
      ArithmeticFunction.vonMangoldt n) = ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnS
    have hnp : ¬IsPrimePow n := by
      intro h
      exact hnS (Finset.mem_filter.mpr ⟨hn,h⟩)
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
  have hsub : S ⊆ (q^J).divisors := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hbase,hprime⟩
    rcases Finset.mem_filter.mp hbase with ⟨hsize,hbad⟩
    exact Nat.mem_divisors.mpr ⟨exceptional_prime_power_dvd hprime hbad
      (Finset.mem_Icc.mp hsize).2, pow_ne_zero _ hq.ne'⟩
  rw [he]
  calc
    _ ≤ ∑ n ∈ (q^J).divisors, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = (J : ℝ)*Real.log q := by
      rw [ArithmeticFunction.vonMangoldt_sum,Nat.cast_pow,Real.log_pow]

/-- A uniform finite divisor budget, not an unproved Ramanujan estimate. -/
theorem norm_ramanujanDivisor_le {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ‖ramanujanDivisor q n‖ ≤ ramanujanBudget q := by
  unfold ramanujanDivisor ramanujanBudget
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd hq.ne' (Nat.gcd_dvd_left q n))
    (fun _ _ _ => norm_nonneg _)

/-- The full phase costs nothing in this exceptional finite-base bound;
centering has already removed every coprime prime-power label exactly. -/
theorem norm_correction_le {q : ℕ} (hq : 0 < q) (y : ℝ) (J : ℕ) :
    ‖correction q (2^J) y‖ ≤
      (ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*((J : ℝ)*Real.log q) := by
  classical
  have hbudget : 0 ≤ ramanujanBudget q+‖ArithmeticFunction.moebius q‖ := by
    unfold ramanujanBudget
    positivity
  have he : correction q (2^J) y =
      ∑ n ∈ (Finset.Icc 1 (2^J)).filter (fun n => ¬Nat.Coprime q n),
        (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*
          ((ramanujanDivisor q n-ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    unfold correction
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hc : Nat.Coprime q n := by
      by_contra hh
      exact hnot (Finset.mem_filter.mpr ⟨hn,hh⟩)
    rw [ramanujanDivisor_of_coprime hc,sub_self,Int.cast_zero,mul_zero]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ (Finset.Icc 1 (2^J)).filter (fun n => ¬Nat.Coprime q n),
        ArithmeticFunction.vonMangoldt n*
          (ramanujanBudget q+‖ArithmeticFunction.moebius q‖) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul,norm_mul,norm_primePhase,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      simp only [Complex.norm_intCast,← Real.norm_eq_abs,Int.norm_cast_real]
      exact (norm_sub_le (ramanujanDivisor q n) (ArithmeticFunction.moebius q)).trans
        (add_le_add (norm_ramanujanDivisor_le hq n) le_rfl)
    _ = (ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*
        (∑ n ∈ (Finset.Icc 1 (2^J)).filter (fun n => ¬Nat.Coprime q n),
          ArithmeticFunction.vonMangoldt n) := by rw [← Finset.sum_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (exceptional_mass_le hq J) hbudget

/-- The actual exceptional correction has no persistent power component
at any positive exponent. The ordinate is fixed but otherwise arbitrary. -/
theorem tendsto_scaled_correction {q : ℕ} (hq : 0 < q) (y : ℝ)
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto (fun J : ℕ => (Real.exp (-beta*Real.log 2)^J : ℂ)*correction q (2^J) y)
      atTop (𝓝 0) := by
  let r := Real.exp (-beta*Real.log 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
    have hh : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith)
  have ht : Tendsto (fun J : ℕ =>
      (ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*Real.log q*
        ((J : ℝ)*r^J)) atTop (𝓝 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).const_mul
      ((ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*Real.log q)
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
  calc
    _ ≤ r^J*((ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*
        ((J : ℝ)*Real.log q)) :=
      mul_le_mul_of_nonneg_left (norm_correction_le hq y J) (pow_nonneg hr0 J)
    _ = _ := by ring

/-- A complete fixed-modulus observation, with every Mangoldt phase. -/
def codeObservation (Q : Finset ℕ) (lambda : ℕ → ℂ) (X : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*code Q lambda n

/-- Exact joined identity: only the common principal channel can survive
a fixed-modulus source scale. -/
theorem codeObservation_sub_principal (Q : Finset ℕ) (lambda : ℕ → ℂ)
    (X : ℕ) (y : ℝ) :
    codeObservation Q lambda X y-principalCoefficient Q lambda*
      (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n) =
        ∑ q ∈ Q, lambda q*correction q X y := by
  classical
  unfold codeObservation
  rw [weighted_code_split,add_sub_cancel_left]
  unfold principalCoefficient code correction
  simp_rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- Strict fixed-modulus no-go. Exact principal/pole centering makes the
whole literal arithmetic code o(2^(beta J)), so it loses EVERY matched
zero source as well. This does not assert nonvanishing of zeta. -/
theorem tendsto_centered_code {Q : Finset ℕ} (lambda : ℕ → ℂ)
    (hQ : ∀ q ∈ Q, 0 < q) (hc : principalCoefficient Q lambda = 0)
    (y : ℝ) {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto (fun J : ℕ => (Real.exp (-beta*Real.log 2)^J : ℂ)*
      codeObservation Q lambda (2^J) y) atTop (𝓝 0) := by
  have he (J : ℕ) : codeObservation Q lambda (2^J) y =
      ∑ q ∈ Q, lambda q*correction q (2^J) y := by
    simpa only [hc,zero_mul,sub_zero] using codeObservation_sub_principal Q lambda (2^J) y
  simp_rw [he,Finset.mul_sum]
  have hh (q : ℕ) (hq : q ∈ Q) :
      Tendsto (fun J : ℕ => (Real.exp (-beta*Real.log 2)^J : ℂ)*
        (lambda q*correction q (2^J) y)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_left_comm] using
      (tendsto_scaled_correction (hQ q hq) y hbeta).const_mul (lambda q)
  simpa using tendsto_finsetSum Q hh

end
end RiemannGaussian.ArithmeticOperatorRamanujanPayment
