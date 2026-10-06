/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiIntegerCarryMellinAudit

/-!
# Integer endpoint correlations of carry increments

The incidence of a prime power at two integer-scale increments is governed
by gcds of the literal cutoff endpoints. Every prime-power phase remains
inside the joined correlation. These estimates concern the same-integer
incidence kernel, not the off-diagonal Weil quadratic or a Suzuki floor.
-/

namespace RiemannGaussian.SuzukiCarryCorrelation
noncomputable section
open scoped BigOperators
open SuzukiIntegerCarry

/-- Exact signed increment of a binary carry profile. -/
def incidence (N d : ℕ) : ℝ := (carry (N+1) d : ℝ) - carry N d

/-- The indicator of actual integer divisibility, not a density model. -/
def divisorIndicator (a d : ℕ) : ℝ := if d ∣ a then 1 else 0

/-- All three endpoints, including the doubled factorial subtraction. -/
def endpoint (N : ℕ) (i : Fin 3) : ℕ :=
  if i = 0 then 2*N+1 else if i = 1 then 2*N+2 else N+1

/-- The signed factorial coefficients are retained before summing. -/
def endpointSign (i : Fin 3) : ℝ := if i = 2 then -2 else 1

/-- A phase-preserving observation of the prime-power factors of one integer. -/
def divisorPhase (phase : ℕ → ℂ) (a : ℕ) : ℂ :=
  ∑ d ∈ a.divisors, (ArithmeticFunction.vonMangoldt d : ℂ) * phase d

/-- The complete literal incidence correlation on a common finite support. -/
def correlation (X N M : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X,
    ((incidence N d * incidence M d : ℝ) : ℂ) *
      (ArithmeticFunction.vonMangoldt d : ℂ) * phase d

/-- A literal phased overlap at two integer scales, on the same support. -/
def overlap (X N M : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X,
    ((carry N d * carry M d : ℕ) : ℂ) *
      (ArithmeticFunction.vonMangoldt d : ℂ) * phase d

/-- The incidence bound controls the actual mixed finite difference of
the phase-retaining overlap. Every term uses the identical finite cutoff. -/
theorem correlation_eq_overlap_mixed_difference (X N M : ℕ) (phase : ℕ → ℂ) :
    correlation X N M phase =
      overlap X (N+1) (M+1) phase - overlap X (N+1) M phase -
        overlap X N (M+1) phase + overlap X N M phase := by
  unfold correlation overlap incidence
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

/-- The exact quotient jumps are integer-divisor incidences. -/
theorem incidence_eq_divisorIndicators (N d : ℕ) :
    incidence N d = divisorIndicator (2*N+1) d + divisorIndicator (2*N+2) d -
      2 * divisorIndicator (N+1) d := by
  have hlo (K : ℕ) : 2*(K/d) ≤ (2*K)/d := by
    simpa only [← two_mul] using Nat.div_add_div_le_add_div (x := K) (y := K) (z := d)
  have htwo : (2*(N+1))/d = (2*N)/d +
      (if d ∣ 2*N+1 then 1 else 0) + (if d ∣ 2*N+2 then 1 else 0) := by
    rw [show 2*(N+1) = (2*N+1)+1 by omega, Nat.succ_div, Nat.succ_div]
  have hone := @Nat.succ_div N d
  unfold incidence carry divisorIndicator
  rw [Nat.cast_sub (hlo (N+1)), Nat.cast_sub (hlo N)]
  rw [htwo, hone]
  push_cast
  ring

/-- Endpoint form of the same signed profile, with no discarded incidence. -/
theorem incidence_eq_endpoint_sum (N d : ℕ) :
    incidence N d = ∑ i : Fin 3, endpointSign i * divisorIndicator (endpoint N i) d := by
  rw [incidence_eq_divisorIndicators]
  simp [Fin.sum_univ_three, endpointSign, endpoint, sub_eq_add_neg]

private theorem common_divisor_sum {X a b : ℕ} (ha : 0 < a) (haX : a ≤ X)
    (phase : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 X,
      ((divisorIndicator a d * divisorIndicator b d : ℝ) : ℂ) *
        (ArithmeticFunction.vonMangoldt d : ℂ) * phase d) =
      divisorPhase phase (Nat.gcd a b) := by
  classical
  have hg : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_left b ha).ne'
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ a ∧ d ∣ b) = (Nat.gcd a b).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 ha, (Nat.le_of_dvd ha hd.1).trans haX⟩, hd⟩
  have hterm (d : ℕ) :
      ((divisorIndicator a d * divisorIndicator b d : ℝ) : ℂ) *
          (ArithmeticFunction.vonMangoldt d : ℂ) * phase d =
        if d ∣ a ∧ d ∣ b then (ArithmeticFunction.vonMangoldt d : ℂ) * phase d else 0 := by
    by_cases hda : d ∣ a <;> by_cases hdb : d ∣ b <;>
      simp [divisorIndicator, hda, hdb]
  simp_rw [hterm]
  rw [← Finset.sum_filter, he]
  rfl

/-- Joint signed prime-power correlations reduce exactly to gcds of
integer endpoints. The arbitrary complex phase is unchanged. -/
theorem correlation_eq_gcd_sum {X N M : ℕ} (hN : 2*(N+1) ≤ X)
    (phase : ℕ → ℂ) :
    correlation X N M phase =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ((endpointSign i * endpointSign j : ℝ) : ℂ) *
          divisorPhase phase (Nat.gcd (endpoint N i) (endpoint M j)) := by
  classical
  have hpos (i : Fin 3) : 0 < endpoint N i := by
    unfold endpoint
    split_ifs <;> omega
  have hbound (i : Fin 3) : endpoint N i ≤ X := by
    unfold endpoint
    split_ifs <;> omega
  unfold correlation
  simp_rw [incidence_eq_endpoint_sum, Finset.sum_mul, Finset.mul_sum,
    Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he := common_divisor_sum (a := endpoint N i) (b := endpoint M j) (hpos i) (hbound i) phase
  rw [← he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

/-- The actual prime-power observation is bounded by the factorization
mass of its integer argument, while every unit phase remains literal. -/
theorem norm_divisorPhase_le_log (phase : ℕ → ℂ)
    (hphase : ∀ d, ‖phase d‖ ≤ 1) (a : ℕ) :
    ‖divisorPhase phase a‖ ≤ Real.log a := by
  unfold divisorPhase
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ a.divisors, ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact (mul_le_mul_of_nonneg_left (hphase d) ArithmeticFunction.vonMangoldt_nonneg).trans_eq
        (mul_one _)
    _ = _ := ArithmeticFunction.vonMangoldt_sum

/-- A phase-preserving arithmetic correlation budget depends on shared
integer factors instead of the entire prime mass at the absolute cutoff. -/
theorem norm_correlation_le_gcd_budget {X N M : ℕ}
    (hN : 2*(N+1) ≤ X)
    (phase : ℕ → ℂ) (hphase : ∀ d, ‖phase d‖ ≤ 1) :
    ‖correlation X N M phase‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        |endpointSign i * endpointSign j| *
          Real.log (Nat.gcd (endpoint N i) (endpoint M j)) := by
  rw [correlation_eq_gcd_sum hN]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_divisorPhase_le_log phase hphase _) (abs_nonneg _)

/-- The literal fixed-height prime phase; no cutoff phase is substituted. -/
def primePhase (y : ℝ) (d : ℕ) : ℂ :=
  Complex.exp (-(Complex.I*y)*((Real.log d : ℝ) : ℂ))

/-- The full fixed-height phase has unit norm at each prime power. -/
theorem norm_primePhase (y : ℝ) (d : ℕ) : ‖primePhase y d‖ = 1 := by
  unfold primePhase
  rw [Complex.norm_exp]
  have he : (-(Complex.I*(y : ℂ))*((Real.log d : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.neg_im, Complex.mul_im,
      zero_mul, one_mul, mul_zero, sub_zero, zero_add, neg_zero]
  rw [he, Real.exp_zero]

/-- A nonzero incidence must divide one of the two new integer endpoints. -/
theorem incidence_support {N d : ℕ} (h : incidence N d ≠ 0) :
    d ∣ 2*N+1 ∨ d ∣ 2*N+2 := by
  by_cases ha : d ∣ 2*N+1
  · exact Or.inl ha
  by_cases hb : d ∣ 2*N+2
  · exact Or.inr hb
  have hc : ¬d ∣ N+1 := by
    intro hd
    exact hb (by simpa only [show 2*(N+1) = 2*N+2 by omega] using dvd_mul_of_dvd_right hd 2)
  exact False.elim (h (by simp [incidence_eq_divisorIndicators, divisorIndicator, ha, hb, hc]))

/-- Adjacent incidence rows have no shared denominator above three.
This includes proper prime powers, which are not discarded as an error. -/
theorem incidence_adjacent_product_eq_zero {N d : ℕ} (hd : 3 < d) :
    incidence N d * incidence (N+1) d = 0 := by
  by_cases hn : incidence N d = 0
  · simp [hn]
  by_cases hm : incidence (N+1) d = 0
  · simp [hm]
  rcases incidence_support hn with ha | hb <;> rcases incidence_support hm with hc | he
  · have hh : d ∣ 2 := by
      simpa only [show (2*(N+1)+1)-(2*N+1) = 2 by omega] using Nat.dvd_sub hc ha
    have := Nat.le_of_dvd (by decide : 0 < 2) hh
    omega
  · have hh : d ∣ 3 := by
      simpa only [show (2*(N+1)+2)-(2*N+1) = 3 by omega] using Nat.dvd_sub he ha
    have := Nat.le_of_dvd (by decide : 0 < 3) hh
    omega
  · have hh : d ∣ 1 := by
      simpa only [show (2*(N+1)+1)-(2*N+2) = 1 by omega] using Nat.dvd_sub hc hb
    have := Nat.le_of_dvd (by decide : 0 < 1) hh
    omega
  · have hh : d ∣ 2 := by
      simpa only [show (2*(N+1)+2)-(2*N+2) = 2 by omega] using Nat.dvd_sub he hb
    have := Nat.le_of_dvd (by decide : 0 < 2) hh
    omega

private theorem incidence_two_product (N : ℕ) :
    incidence N 2 * incidence (N+1) 2 = -1 := by
  have hodd (K : ℕ) : ¬2 ∣ 2*K+1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have heven (K : ℕ) : 2 ∣ 2*K+2 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hn : (2 ∣ N+2) ↔ ¬2 ∣ N+1 := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  simp only [incidence_eq_divisorIndicators, divisorIndicator, hodd, heven, if_false, if_true, hn]
  by_cases h : 2 ∣ N+1 <;> norm_num [h]

private theorem incidence_three_product (N : ℕ) :
    incidence N 3 * incidence (N+1) 3 = if N%3 = 1 then -1 else 0 := by
  have ha : (3 ∣ 2*N+1) ↔ N%3 = 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hb : (3 ∣ 2*N+2) ↔ N%3 = 2 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hc : (3 ∣ N+1) ↔ N%3 = 2 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hd : (3 ∣ 2*(N+1)+1) ↔ N%3 = 0 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have he : (3 ∣ 2*(N+1)+2) ↔ N%3 = 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hf : (3 ∣ (N+1)+1) ↔ N%3 = 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  simp only [incidence_eq_divisorIndicators, divisorIndicator, ha, hb, hc, hd, he, hf]
  have hmod := Nat.mod_lt N (by decide : 0 < 3)
  by_cases h1 : N%3 = 1
  · norm_num [h1]
  · have hr : N%3 = 0 ∨ N%3 = 2 := by omega
    rcases hr with h0 | h2
    · norm_num [h0]
    · norm_num [h2]

/-- Exact all-scale anticorrelation of neighboring integer profiles.
Only the literal primes two and three survive, with their original phase. -/
theorem correlation_adjacent_eq {X N : ℕ} (hX : 2*(N+2) ≤ X) (phase : ℕ → ℂ) :
    correlation X N (N+1) phase =
      -(Real.log 2 : ℝ) * phase 2 -
        if N%3 = 1 then (Real.log 3 : ℝ) * phase 3 else 0 := by
  classical
  let f := fun d => ((incidence N d * incidence (N+1) d : ℝ) : ℂ) *
    (ArithmeticFunction.vonMangoldt d : ℂ) * phase d
  have hs : ({2,3} : Finset ℕ) ⊆ Finset.Icc 1 X := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have he : (∑ d ∈ Finset.Icc 1 X, f d) = ∑ d ∈ ({2,3} : Finset ℕ), f d := by
    symm
    apply Finset.sum_subset hs
    intro d hd hnot
    have hne : d ≠ 2 ∧ d ≠ 3 := by simpa using hnot
    by_cases hd3 : 3 < d
    · dsimp [f]
      rw [incidence_adjacent_product_eq_zero hd3]
      simp
    · have hd1 : d = 1 := by have := (Finset.mem_Icc.mp hd).1; omega
      simp [f, hd1]
  unfold correlation
  change (∑ d ∈ Finset.Icc 1 X, f d) = _
  rw [he]
  simp only [Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
  dsimp [f]
  rw [incidence_two_product, incidence_three_product,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime (by decide : Nat.Prime 3)]
  by_cases h : N%3 = 1
  all_goals simp [h]
  all_goals ring

private theorem endpoint_divisor_normalized {d N : ℕ} (i : Fin 3)
    (h : d ∣ endpoint N i) : d ∣ 2*N+1 ∨ d ∣ 2*N+2 := by
  unfold endpoint at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr (by simpa only [show 2*(N+1) = 2*N+2 by omega] using
      dvd_mul_of_dvd_right h 2)

private theorem endpoint_gcd_le_separation {N H : ℕ} (hH : 0 < H) (i j : Fin 3) :
    Nat.gcd (endpoint N i) (endpoint (N+H) j) ≤ 2*H+1 := by
  let g := Nat.gcd (endpoint N i) (endpoint (N+H) j)
  have hi := endpoint_divisor_normalized i (Nat.gcd_dvd_left (endpoint N i) (endpoint (N+H) j))
  have hj := endpoint_divisor_normalized j (Nat.gcd_dvd_right (endpoint N i) (endpoint (N+H) j))
  change g ∣ 2*N+1 ∨ g ∣ 2*N+2 at hi
  change g ∣ 2*(N+H)+1 ∨ g ∣ 2*(N+H)+2 at hj
  rcases hi with ha | hb <;> rcases hj with hc | hd
  · have hg : g ∣ 2*H := by
      simpa only [show (2*(N+H)+1)-(2*N+1) = 2*H by omega] using Nat.dvd_sub hc ha
    exact (Nat.le_of_dvd (by omega : 0 < 2*H) hg).trans (by omega)
  · have hg : g ∣ 2*H+1 := by
      simpa only [show (2*(N+H)+2)-(2*N+1) = 2*H+1 by omega] using Nat.dvd_sub hd ha
    exact Nat.le_of_dvd (by omega : 0 < 2*H+1) hg
  · have hg : g ∣ 2*H-1 := by
      simpa only [show (2*(N+H)+1)-(2*N+2) = 2*H-1 by omega] using Nat.dvd_sub hc hb
    exact (Nat.le_of_dvd (by omega : 0 < 2*H-1) hg).trans (by omega)
  · have hg : g ∣ 2*H := by
      simpa only [show (2*(N+H)+2)-(2*N+2) = 2*H by omega] using Nat.dvd_sub hd hb
    exact (Nat.le_of_dvd (by omega : 0 < 2*H) hg).trans (by omega)

/-- The complete phased correlation has a logarithmic separation budget,
uniform in the absolute integer scale and the fixed phase height.
This is an arithmetic incidence estimate, not a centered-overlap decay rate. -/
theorem norm_correlation_le_log_separation {X N H : ℕ} (hN : 2*(N+1) ≤ X)
    (hH : 0 < H) (phase : ℕ → ℂ) (hphase : ∀ d, ‖phase d‖ ≤ 1) :
    ‖correlation X N (N+H) phase‖ ≤ 16*Real.log (2*H+1 : ℕ) := by
  apply (norm_correlation_le_gcd_budget hN phase hphase).trans
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        |endpointSign i * endpointSign j| * Real.log (2*H+1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hpos : 0 < endpoint N i := by unfold endpoint; split_ifs <;> omega
      have hg : (0 : ℝ) < Nat.gcd (endpoint N i) (endpoint (N+H) j) := by
        exact_mod_cast Nat.gcd_pos_of_pos_left (endpoint (N+H) j) hpos
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log hg (by exact_mod_cast endpoint_gcd_le_separation hH i j)) (abs_nonneg _)
    _ = _ := by
      simp [Fin.sum_univ_three, endpointSign]
      ring

/-- The source's literal phase is an admissible unit test of the same
arithmetic correlation bound at every absolute scale. -/
theorem norm_primePhase_correlation_le_log_separation {X N H : ℕ}
    (hN : 2*(N+1) ≤ X) (hH : 0 < H) (y : ℝ) :
    ‖correlation X N (N+H) (primePhase y)‖ ≤ 16*Real.log (2*H+1 : ℕ) :=
  norm_correlation_le_log_separation hN hH _ (fun d => (norm_primePhase y d).le)

end
end RiemannGaussian.SuzukiCarryCorrelation
