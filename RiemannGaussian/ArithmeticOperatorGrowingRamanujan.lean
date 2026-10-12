/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorRamanujanPayment

/-!
# A growing-modulus Ramanujan source-blindness gate

The moduli may grow as the fourth root of the physical cutoff, and all
their number-theoretic exceptional prime powers are retained. A bounded
coefficient code with zero common coprime coefficient is still smaller
than every source exponent above three quarters. This is a rejection of
the coprime-channel centering prototype, not of all growing additive
codes or shifted-prime correlations.
-/

namespace RiemannGaussian.ArithmeticOperatorGrowingRamanujan
noncomputable section
open ArithmeticOperatorRamanujanAudit ArithmeticOperatorRamanujanPayment
open Filter
open scoped BigOperators Topology

/-- A coarse finite divisor budget sufficient for a genuine geometric
growing-modulus audit. No Delange/Ramanujan convergence is assumed. -/
theorem ramanujanBudget_le_square {q : ℕ} (hq : 0 < q) :
    ramanujanBudget q ≤ (q : ℝ)^2 := by
  have hsub : q.divisors ⊆ Finset.Icc 1 q := by
    intro d hd
    have hh := Nat.dvd_of_mem_divisors hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hh hq,Nat.le_of_dvd hq hh⟩
  unfold ramanujanBudget
  calc
    _ ≤ ∑ d ∈ q.divisors, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdq : d ≤ q := (Finset.mem_Icc.mp (hsub hd)).2
      have hm : ‖ArithmeticFunction.moebius (q/d)‖ ≤ (1 : ℝ) := by
        rw [Int.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q/d)
      rw [norm_mul,Int.norm_natCast]
      exact (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg d)).trans
        (by simpa using (show (d : ℝ) ≤ q by exact_mod_cast hdq))
    _ ≤ ∑ d ∈ Finset.Icc 1 q, (q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg q)
    _ = _ := by simp; ring

/-- All growing-modulus exceptions have an explicit geometric-budget
bound while their full height phase and prime-power endpoints remain. -/
theorem norm_growing_centered_code_le {Q : Finset ℕ} {lambda : ℕ → ℂ} {J : ℕ}
    (hQ : Q ⊆ Finset.Icc 1 (2^J))
    (hlambda : ∀ q ∈ Q, ‖lambda q‖ ≤ 1)
    (hc : principalCoefficient Q lambda = 0) (y : ℝ) :
    ‖codeObservation Q lambda (2^(4*J)) y‖ ≤
      8*Real.log 2*(J : ℝ)^2*(8 : ℝ)^J := by
  classical
  have hq (q : ℕ) (hqQ : q ∈ Q) : 0 < q := by
    have := (Finset.mem_Icc.mp (hQ hqQ)).1
    omega
  have he := codeObservation_sub_principal Q lambda (2^(4*J)) y
  rw [hc,zero_mul,sub_zero] at he
  rw [he]
  have hnorm (q : ℕ) (hqQ : q ∈ Q) :
      ‖lambda q*correction q (2^(4*J)) y‖ ≤
        8*Real.log 2*(J : ℝ)^2*((2 : ℝ)^J)^2 := by
    have hqR : (q : ℝ) ≤ (2 : ℝ)^J := by
      exact_mod_cast (Finset.mem_Icc.mp (hQ hqQ)).2
    have hlog : Real.log q ≤ (J : ℝ)*Real.log 2 := by
      have h := Real.log_le_log (by exact_mod_cast hq q hqQ) hqR
      simpa only [Real.log_pow] using h
    have hm : ‖ArithmeticFunction.moebius q‖ ≤ (1 : ℝ) := by
      rw [Int.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have hb : ramanujanBudget q+‖ArithmeticFunction.moebius q‖ ≤
        2*((2 : ℝ)^J)^2 := by
      have hpow : (1 : ℝ) ≤ (2 : ℝ)^J := one_le_pow₀ (by norm_num)
      have hsq : (q : ℝ)^2 ≤ ((2 : ℝ)^J)^2 :=
        (sq_le_sq₀ (Nat.cast_nonneg q) (by positivity)).mpr hqR
      have hsmall := add_le_add (ramanujanBudget_le_square (hq q hqQ)) hm
      nlinarith
    rw [norm_mul]
    calc
      _ ≤ 1*‖correction q (2^(4*J)) y‖ :=
        mul_le_mul_of_nonneg_right (hlambda q hqQ) (norm_nonneg _)
      _ ≤ (ramanujanBudget q+‖ArithmeticFunction.moebius q‖)*
          (((4*J : ℕ) : ℝ)*Real.log q) := by
        simpa only [one_mul] using norm_correction_le (hq q hqQ) y (4*J)
      _ ≤ (2*((2 : ℝ)^J)^2)*(((4*J : ℕ) : ℝ)*((J : ℝ)*Real.log 2)) :=
        mul_le_mul hb (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by
            exact_mod_cast (by have := hq q hqQ; omega : 1 ≤ q)))) (by positivity)
      _ = _ := by push_cast; ring
  have hcard : (Q.card : ℝ) ≤ (2 : ℝ)^J := by
    exact_mod_cast (by simpa using Finset.card_le_card hQ : Q.card ≤ 2^J)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ Q, 8*Real.log 2*(J : ℝ)^2*((2 : ℝ)^J)^2 :=
      Finset.sum_le_sum hnorm
    _ = (Q.card : ℝ)*(8*Real.log 2*(J : ℝ)^2*((2 : ℝ)^J)^2) := by simp
    _ ≤ (2 : ℝ)^J*(8*Real.log 2*(J : ℝ)^2*((2 : ℝ)^J)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [show (8 : ℝ)^J = ((2 : ℝ)^J)^3 by
        rw [← pow_mul,show J*3 = 3*J by omega, pow_mul]; norm_num]
      ring

/-- Even polynomially expanding modular populations of this size lose
every campaign zero source after exact principal centering. No zero
hypothesis or unproved prime-distribution theorem enters the payment. -/
theorem tendsto_growing_centered_code {Q : ℕ → Finset ℕ}
    {lambda : ℕ → ℕ → ℂ}
    (hQ : ∀ J, Q J ⊆ Finset.Icc 1 (2^J))
    (hlambda : ∀ J q, q ∈ Q J → ‖lambda J q‖ ≤ 1)
    (hc : ∀ J, principalCoefficient (Q J) (lambda J) = 0)
    (y : ℝ) {beta : ℝ} (hbeta : 3/4 < beta) :
    Tendsto (fun J : ℕ => (Real.exp (-4*beta*Real.log 2)^J : ℂ)*
      codeObservation (Q J) (lambda J) (2^(4*J)) y) atTop (𝓝 0) := by
  let a := Real.exp (-4*beta*Real.log 2)
  let r := a*8
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have he : r = Real.exp ((3-4*beta)*Real.log 2) := by
      dsimp [r,a]
      calc
        _ = Real.exp (-4*beta*Real.log 2)*Real.exp (3*Real.log 2) := by
          rw [show (3 : ℝ)*Real.log 2 = Real.log ((2 : ℝ)^3) by
            exact (Real.log_pow (2 : ℝ) 3).symm,
            Real.exp_log (by norm_num : (0 : ℝ) < 2^3)]
          norm_num
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    rw [he]
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have ht : Tendsto (fun J : ℕ =>
      (8*Real.log 2)*((J : ℝ)^2*r^J)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1).const_mul
      (8*Real.log 2)
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
  calc
    _ ≤ a^J*(8*Real.log 2*(J : ℝ)^2*(8 : ℝ)^J) :=
      mul_le_mul_of_nonneg_left (norm_growing_centered_code_le
        (hQ J) (hlambda J) (hc J) y) (pow_nonneg ha J)
    _ = _ := by dsimp [r]; rw [mul_pow]; ring

end
end RiemannGaussian.ArithmeticOperatorGrowingRamanujan
