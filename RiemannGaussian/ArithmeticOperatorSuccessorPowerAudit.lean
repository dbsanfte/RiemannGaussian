/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit

/-!
# Direct successor prime powers: a genuine arithmetic but source-blind gate

When both consecutive labels have nonzero Mangoldt weight, the even
endpoint is literally a power of two. All proper powers, endpoints and
both Archimedean phases are retained. The complete direct successor
statistic is polylogarithmic and loses every positive-power zero source.

This does NOT pay the divisor-convolution successor statistic: those
rows include dense composite multiples, to which the sparse support
argument does not apply. Even lags are also outside this audit.
-/

namespace RiemannGaussian.ArithmeticOperatorSuccessorPowerAudit
noncomputable section
open Complex Filter SuzukiCarryCorrelation
open ArithmeticOperatorFloorInverseAudit
open scoped BigOperators Topology ComplexConjugate

/-- Literal raw successor correlation, keeping all Mangoldt powers. -/
def rawSuccessor (X : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    (ArithmeticFunction.vonMangoldt n : ℂ)*(ArithmeticFunction.vonMangoldt (n+1) : ℂ)*
      primePhase y n*conj (primePhase y (n+1))

/-- Both possible locations of the sparse power-of-two endpoint. -/
def exceptionalRows (J : ℕ) : Finset ℕ :=
  ((Finset.range (J+2)).image (fun k => 2^k)) ∪
    ((Finset.range (J+2)).image (fun k => 2^k-1))

private theorem even_prime_power {n : ℕ} (hp : IsPrimePow n) (he : n % 2 = 0) :
    ∃ k : ℕ, 0 < k ∧ n = 2^k := by
  obtain ⟨p,k,hp,hk,hn⟩ := (isPrimePow_nat_iff n).mp hp
  have hp2 : p = 2 := by
    by_contra hh
    have hodd := hp.eq_two_or_odd.resolve_left hh
    have hmod : (p^k)%2 = 1 := by rw [Nat.pow_mod, hodd, one_pow]; norm_num
    rw [hn] at hmod
    omega
  exact ⟨k,hk,by simpa only [hp2] using hn.symm⟩

/-- Exact ordinary addition plus prime-power support, not a smooth or
generalized-prime property. Either endpoint's even label is retained. -/
theorem active_successor_power_two {n : ℕ}
    (hn : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hs : ArithmeticFunction.vonMangoldt (n+1) ≠ 0) :
    (∃ k : ℕ, 0 < k ∧ n = 2^k) ∨ (∃ k : ℕ, 0 < k ∧ n+1 = 2^k) := by
  by_cases he : n % 2 = 0
  · exact Or.inl (even_prime_power (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn) he)
  · have hnext : (n+1)%2 = 0 := by omega
    exact Or.inr (even_prime_power (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hs) hnext)

/-- At every dyadic physical cutoff the active rows are sparse, with
the successor beyond the cutoff kept through exponent J+1. -/
theorem active_row_mem_exceptional {J n : ℕ} (hnX : n ≤ 2^J)
    (hn : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hs : ArithmeticFunction.vonMangoldt (n+1) ≠ 0) : n ∈ exceptionalRows J := by
  have hsize : n+1 ≤ 2^(J+1) := by
    rw [pow_succ]
    have hpow : 1 ≤ 2^J := Nat.one_le_pow J 2 (by omega)
    omega
  rcases active_successor_power_two hn hs with ⟨k,_,he⟩ | ⟨k,_,he⟩
  · have hk : k ≤ J+1 := (Nat.pow_le_pow_iff_right (by omega : 1 < (2 : ℕ))).mp
      (by rw [← he]; omega)
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),he.symm⟩)
  · have hk : k ≤ J+1 := (Nat.pow_le_pow_iff_right (by omega : 1 < (2 : ℕ))).mp
      (by rw [← he]; exact hsize)
    have he' : 2^k-1 = n := by omega
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),he'⟩)

theorem exceptionalRows_card_le (J : ℕ) : (exceptionalRows J).card ≤ 2*(J+2) := by
  unfold exceptionalRows
  exact (Finset.card_union_le _ _).trans (by
    have ha := Finset.card_image_le (s := Finset.range (J+2)) (f := fun k => 2^k)
    have hb := Finset.card_image_le (s := Finset.range (J+2)) (f := fun k => 2^k-1)
    simp only [Finset.card_range] at ha hb
    omega)

/-- The finite join itself is exact before a norm is taken. No active
power, zero row, or either Fourier/Archimedean phase is deleted. -/
theorem rawSuccessor_eq_exceptional (J : ℕ) (y : ℝ) :
    rawSuccessor (2^J) y =
      ∑ n ∈ (Finset.Icc 1 (2^J)).filter (fun n => n ∈ exceptionalRows J),
        (ArithmeticFunction.vonMangoldt n : ℂ)*(ArithmeticFunction.vonMangoldt (n+1) : ℂ)*
          primePhase y n*conj (primePhase y (n+1)) := by
  unfold rawSuccessor
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  by_cases ha : ArithmeticFunction.vonMangoldt n = 0
  · simp [ha]
  by_cases hb : ArithmeticFunction.vonMangoldt (n+1) = 0
  · simp [hb]
  exact False.elim (hnot (Finset.mem_filter.mpr
    ⟨hn,active_row_mem_exceptional (Finset.mem_Icc.mp hn).2 ha hb⟩))

/-- An unconditional actual-prime bound. Since the raw interaction
itself is sparse, this final norm is source-small at every height.
It is NOT a componentwise payment of the dense CRT discrepancy. -/
theorem norm_rawSuccessor_le (J : ℕ) (y : ℝ) :
    ‖rawSuccessor (2^J) y‖ ≤ 16*(Real.log 2)^2*((J+1 : ℕ) : ℝ)^3 := by
  rw [rawSuccessor_eq_exceptional]
  let S := (Finset.Icc 1 (2^J)).filter (fun n => n ∈ exceptionalRows J)
  have hsub : S ⊆ exceptionalRows J := fun _ hn => (Finset.mem_filter.mp hn).2
  have hcard : (S.card : ℝ) ≤ (2*(J+2 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (exceptionalRows_card_le J)
  have hterm {n : ℕ} (hn : n ∈ S) :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)*(ArithmeticFunction.vonMangoldt (n+1) : ℂ)*
        primePhase y n*conj (primePhase y (n+1))‖ ≤
          (((J+1 : ℕ) : ℝ)*Real.log 2)^2 := by
    obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hnp : n+1 ≤ 2^(J+1) := by
      rw [pow_succ]
      have hh := Nat.one_le_pow J 2 (by omega)
      omega
    have hlog : Real.log ((2^(J+1) : ℕ) : ℝ) = ((J+1 : ℕ) : ℝ)*Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    have hnL : ArithmeticFunction.vonMangoldt n ≤ ((J+1 : ℕ) : ℝ)*Real.log 2 :=
      (ArithmeticFunction.vonMangoldt_le_log (n := n)).trans (by
        rw [← hlog]
        exact Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast (by omega : n ≤ 2^(J+1))))
    have hsL : ArithmeticFunction.vonMangoldt (n+1) ≤ ((J+1 : ℕ) : ℝ)*Real.log 2 :=
      (ArithmeticFunction.vonMangoldt_le_log (n := n+1)).trans (by
        rw [← hlog]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hnp))
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_conj,norm_primePhase,norm_primePhase,
      mul_one,mul_one,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simpa only [pow_two] using mul_le_mul hnL hsL
      (ArithmeticFunction.vonMangoldt_nonneg (n := n+1)) (by positivity)
  calc
    _ ≤ ∑ _n ∈ S, (((J+1 : ℕ) : ℝ)*Real.log 2)^2 :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ hn => hterm hn))
    _ = (S.card : ℝ)*(((J+1 : ℕ) : ℝ)*Real.log 2)^2 := by simp
    _ ≤ ((2*(J+2 : ℕ) : ℝ))*(((J+1 : ℕ) : ℝ)*Real.log 2)^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ ≤ _ := by
      have hj : ((2*(J+2 : ℕ) : ℝ)) ≤ 16*((J+1 : ℕ) : ℝ) := by
        push_cast
        have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
        linarith
      calc
        _ ≤ (16*((J+1 : ℕ) : ℝ))*(((J+1 : ℕ) : ℝ)*Real.log 2)^2 :=
          mul_le_mul_of_nonneg_right hj (sq_nonneg _)
        _ = _ := by ring

/-- The direct successor mechanism cannot carry ANY growing power
source. No zero, exposure or simplicity premise enters this no-go. -/
theorem tendsto_scaled_rawSuccessor {beta : ℝ} (hb : 0 < beta) (y : ℝ) :
    Tendsto (fun J : ℕ => ((Real.exp (-beta*Real.log 2))^J : ℂ)*rawSuccessor (2^J) y)
      atTop (𝓝 0) := by
  have hr : Real.exp (-beta*Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith)
  have ht := (tendsto_shifted_polynomial_geometric 3 (Real.exp_pos _) hr).const_mul
    (16*(Real.log 2)^2)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-beta*Real.log 2))^J*(16*(Real.log 2)^2*((J+1 : ℕ) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left (norm_rawSuccessor_le J y) (by positivity)
    _ = _ := by ring

end
end RiemannGaussian.ArithmeticOperatorSuccessorPowerAudit
