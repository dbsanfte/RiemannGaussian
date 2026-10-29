/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterRate
import Mathlib

/-!
# Exact binomial-tail guard for the actual shared-counter schedule

The elementary finite MGF/Chernoff derivation is adapted from
OpenAI math commit 7ef5c0cc, SqrtLog/SpectralBinomial.lean (Apache-2.0),
rechecked here using Mathlib only. No external module or schedule is imported.
Our exact interval and Q-trial count are those of shared_parameters.py.
-/

namespace RiemannGaussian.SemiprimeCounterTail
open scoped BigOperators
open RiemannGaussian.SemiprimeCounterRate
open Filter
open scoped Topology

/-- Finite expectation against an explicit binomial mass function. -/
def binomialMean (θ : ℝ) (q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w ∈ Finset.range (q + 1),
    (q.choose w : ℝ) * (1 - θ) ^ (q - w) * θ ^ w * f w

theorem binomialMean_succ (θ : ℝ) (q : ℕ) (f : ℕ → ℝ) :
    binomialMean θ (q + 1) f =
      binomialMean θ q (fun w => (1 - θ) * f w + θ * f (w + 1)) := by
  unfold binomialMean
  simp only [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => (1 - θ) ^ j * (θ ^ i * f i)) q]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hwle : w ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
  have he : q + 1 - w = q - w + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

theorem binomialMean_const_mul (θ c : ℝ) (q : ℕ) (f : ℕ → ℝ) :
    binomialMean θ q (fun w => c * f w) = c * binomialMean θ q f := by
  simp [binomialMean, mul_left_comm, ← Finset.mul_sum]

theorem binomialMean_add (θ : ℝ) (q : ℕ) (f g : ℕ → ℝ) :
    binomialMean θ q (fun w => f w + g w) =
      binomialMean θ q f + binomialMean θ q g := by
  simp [binomialMean, mul_add, Finset.sum_add_distrib]

theorem bernoulli_mgf_le (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) ≤
      Real.exp (t ^ 2 / 2) := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hj := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-t))
    (show 0 ≤ 1 - θ by linarith) hθ0 (show 1 - θ + θ = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hj
  have hj' : Real.exp (-t * θ) ≤ 1 - θ + θ * Real.exp (-t) := by
    simpa only [mul_neg, mul_comm] using hj
  have hb : 0 ≤ 1 - θ + θ * Real.exp t := by positivity
  have hm := mul_le_mul_of_nonneg_left hj' hb
  have he : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp : Real.exp (t * (1 - θ)) = Real.exp t * Real.exp (-t * θ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst : (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) ≤
      1 + 2 * θ * (1 - θ) * (Real.cosh t - 1) := by
    rw [hexp]
    calc
      _ = (1 - θ + θ * Real.exp t) * Real.exp (-t * θ) := by ring
      _ ≤ (1 - θ + θ * Real.exp t) * (1 - θ + θ * Real.exp (-t)) := hm
      _ = _ := by
        rw [Real.cosh_eq]
        linear_combination θ ^ 2 * he
  have hc : 0 ≤ Real.cosh t - 1 := sub_nonneg.mpr (Real.one_le_cosh t)
  have hv : 2 * θ * (1 - θ) ≤ 1 := by nlinarith [sq_nonneg (θ - 1 / 2)]
  have hsecond : 1 + 2 * θ * (1 - θ) * (Real.cosh t - 1) ≤ Real.cosh t := by
    nlinarith [mul_le_mul_of_nonneg_right hv hc]
  exact hfirst.trans (hsecond.trans (Real.cosh_le_exp_half_sq t))

theorem binomial_mgf_le (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (q : ℕ) :
    binomialMean θ q (fun w => Real.exp (t * ((w : ℝ) - q * θ))) ≤
      Real.exp ((q : ℝ) * t ^ 2 / 2) := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  induction q with
  | zero => simp [binomialMean]
  | succ q ih =>
    rw [binomialMean_succ]
    have hfun :
        (fun w : ℕ => (1 - θ) * Real.exp (t * ((w : ℝ) - (q + 1 : ℕ) * θ)) +
          θ * Real.exp (t * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ))) =
        (fun w : ℕ => ((1 - θ) * Real.exp (-t * θ) +
          θ * Real.exp (t * (1 - θ))) * Real.exp (t * ((w : ℝ) - q * θ))) := by
      funext w
      have h0 : t * ((w : ℝ) - (q + 1 : ℕ) * θ) =
          -t * θ + t * ((w : ℝ) - q * θ) := by push_cast; ring
      have h1 : t * ((w + 1 : ℕ) - (q + 1 : ℕ) * θ) =
          t * (1 - θ) + t * ((w : ℝ) - q * θ) := by push_cast; ring
      rw [h0, h1, Real.exp_add, Real.exp_add]
      ring
    rw [hfun, binomialMean_const_mul]
    have hfac : 0 ≤ (1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ)) := by
      positivity
    calc
      _ ≤ ((1 - θ) * Real.exp (-t * θ) + θ * Real.exp (t * (1 - θ))) *
          Real.exp ((q : ℝ) * t ^ 2 / 2) := mul_le_mul_of_nonneg_left ih hfac
      _ ≤ Real.exp (t ^ 2 / 2) * Real.exp ((q : ℝ) * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (bernoulli_mgf_le θ t hθ0 hθ1) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem binomialMean_mono (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (q : ℕ) (f g : ℕ → ℝ) (hfg : ∀ w ∈ Finset.range (q + 1), f w ≤ g w) :
    binomialMean θ q f ≤ binomialMean θ q g := by
  have hθc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  apply Finset.sum_le_sum
  intro w hw
  exact mul_le_mul_of_nonneg_left (hfg w hw) (by positivity)

/-- Two-sided finite-binomial concentration with an absolute constant.
The event may be any finite predicate separated from the exact mean. -/
theorem binomial_tail_le (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (q : ℕ) (hq : 0 < q) (b : ℝ) (hb : 0 ≤ b)
    (bad : ℕ → Prop) [DecidablePred bad]
    (hbad : ∀ w ∈ Finset.range (q + 1), bad w → b ≤ |(w : ℝ) - q * θ|) :
    binomialMean θ q (fun w => if bad w then 1 else 0) ≤
      2 * Real.exp (-(b ^ 2) / (2 * q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let t : ℝ := b / q
  have ht : 0 ≤ t := div_nonneg hb hqR.le
  have hpoint : ∀ w ∈ Finset.range (q + 1),
      (if bad w then (1 : ℝ) else 0) ≤
        Real.exp (t * (((w : ℝ) - q * θ) - b)) +
        Real.exp (t * (-((w : ℝ) - q * θ) - b)) := by
    intro w hw
    split_ifs with h
    · rcases le_abs.mp (hbad w hw h) with hp | hn
      · have he : 1 ≤ Real.exp (t * (((w : ℝ) - q * θ) - b)) :=
          Real.one_le_exp_iff.mpr (mul_nonneg ht (sub_nonneg.mpr hp))
        linarith [Real.exp_pos (t * (-((w : ℝ) - q * θ) - b))]
      · have he : 1 ≤ Real.exp (t * (-((w : ℝ) - q * θ) - b)) :=
          Real.one_le_exp_iff.mpr (mul_nonneg ht (sub_nonneg.mpr hn))
        linarith [Real.exp_pos (t * (((w : ℝ) - q * θ) - b))]
    · positivity
  have hbound := binomialMean_mono θ hθ0 hθ1 q _ _ hpoint
  have hfun :
      (fun w : ℕ => Real.exp (t * (((w : ℝ) - q * θ) - b)) +
        Real.exp (t * (-((w : ℝ) - q * θ) - b))) =
      (fun w : ℕ => Real.exp (-t * b) *
        (Real.exp (t * ((w : ℝ) - q * θ)) +
         Real.exp ((-t) * ((w : ℝ) - q * θ)))) := by
    funext w
    have h1 : t * (((w : ℝ) - q * θ) - b) = -t * b + t * ((w : ℝ) - q * θ) := by ring
    have h2 : t * (-((w : ℝ) - q * θ) - b) = -t * b + (-t) * ((w : ℝ) - q * θ) := by ring
    rw [h1, h2, Real.exp_add, Real.exp_add]
    ring
  rw [hfun, binomialMean_const_mul, binomialMean_add] at hbound
  have hp := binomial_mgf_le θ t hθ0 hθ1 q
  have hn := binomial_mgf_le θ (-t) hθ0 hθ1 q
  rw [neg_sq] at hn
  calc
    _ ≤ Real.exp (-t * b) *
        (binomialMean θ q (fun w => Real.exp (t * ((w : ℝ) - q * θ))) +
         binomialMean θ q (fun w => Real.exp ((-t) * ((w : ℝ) - q * θ)))) := hbound
    _ ≤ Real.exp (-t * b) * (2 * Real.exp ((q : ℝ) * t ^ 2 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith
    _ = 2 * Real.exp (-(b ^ 2) / (2 * q)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      dsimp [t]
      field_simp
      ; ring

/-- The actual swap-spectrum Bernoulli parameter, with no Q-1 shift. -/
noncomputable def negativeProbability (r : ℕ) : ℝ := ((r : ℝ) - 1) / (2 * r)

theorem negativeProbability_bounds {r : ℕ} (hr : 2 ≤ r) :
    0 ≤ negativeProbability r ∧ negativeProbability r ≤ 1 := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold negativeProbability
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).mpr
    nlinarith

/-- Exact floor inequalities for the implemented centered interval. -/
theorem interval_mean_bounds {r Q R : ℕ} (hr : 2 ≤ r) (hR : 2 ≤ R)
    (hQR : 6 * R ≤ Q) :
    (intervalStart r Q R : ℝ) ≤ (Q : ℝ) * negativeProbability r - ((R : ℝ) - 1) / 2 ∧
    (Q : ℝ) * negativeProbability r - ((R : ℝ) - 1) / 2 < (intervalStart r Q R : ℝ) + 1 := by
  let num := Q * (r - 1) - r * (R - 1)
  have hnum := interval_numerator_nonnegative hr hQR
  have hrpos : 0 < 2 * r := by omega
  have hrR : (0 : ℝ) < 2 * r := by exact_mod_cast hrpos
  have hlo : intervalStart r Q R * (2 * r) ≤ num := Nat.div_mul_le_self _ _
  have hhi : num < (2 * r) * (intervalStart r Q R + 1) := Nat.lt_mul_div_succ _ hrpos
  have hncast : (num : ℝ) = (Q : ℝ) * ((r : ℝ) - 1) - (r : ℝ) * ((R : ℝ) - 1) := by
    dsimp [num]
    rw [Nat.cast_sub hnum]
    push_cast [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_sub (show 1 ≤ R by omega)]
    ring
  have hcenter : (Q : ℝ) * negativeProbability r - ((R : ℝ) - 1) / 2 =
      (num : ℝ) / (2 * r) := by
    rw [hncast]
    unfold negativeProbability
    field_simp
  rw [hcenter]
  constructor
  · apply (le_div_iff₀ hrR).mpr
    exact_mod_cast hlo
  · apply (div_lt_iff₀ hrR).mpr
    have hhi' : num < (intervalStart r Q R + 1) * (2 * r) := by
      simpa only [Nat.mul_comm] using hhi
    exact_mod_cast hhi'

/-- Every outside index is separated from the exact Q-trial mean. -/
theorem interval_outside_deviation {r Q R : ℕ} (hr : 2 ≤ r) (hR : 2 ≤ R)
    (hQR : 6 * R ≤ Q) (k : ℕ)
    (hk : k ∉ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R)) :
    (R : ℝ) / 4 ≤ |(k : ℝ) - Q * negativeProbability r| := by
  have hbounds := interval_mean_bounds hr hR hQR
  have hRcast : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hcases : k < intervalStart r Q R ∨ intervalStart r Q R + R ≤ k := by
    simp only [Finset.mem_Ico] at hk
    omega
  apply le_abs.mpr
  rcases hcases with hleft | hright
  · right
    have hleftR : (k : ℝ) < intervalStart r Q R := by exact_mod_cast hleft
    nlinarith [hbounds.1]
  · left
    have hrightR : (intervalStart r Q R : ℝ) + R ≤ k := by exact_mod_cast hright
    nlinarith [hbounds.2]

/-- A finite exact-Q tail estimate with the actual interval and an explicit
constant. The weaker constant 32 leaves ample room in the implemented schedule. -/
theorem centered_tail_le_exp {r Q R : ℕ} (hr : 2 ≤ r) (hR : 2 ≤ R)
    (hQR : 6 * R ≤ Q) :
    binomialMean (negativeProbability r) Q
      (fun k => if k ∉ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R) then 1 else 0) ≤
      2 * Real.exp (-((R : ℝ) ^ 2) / (32 * Q)) := by
  have hprob := negativeProbability_bounds hr
  have ht := binomial_tail_le (negativeProbability r) hprob.1 hprob.2 Q
    (by omega) ((R : ℝ) / 4) (by positivity)
    (fun k => k ∉ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R))
    (fun k _ hk => interval_outside_deviation hr hR hQR k hk)
  convert ht using 1
  congr 2
  ring

/-- An elementary exponential budget; no limiting estimate is assumed. -/
theorem four_power_le_exp {ν : ℕ} (hν : 1 ≤ ν) :
    (4 : ℝ) * 4 ^ ν ≤ Real.exp (64 * (ν : ℝ)) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hνR : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  calc
    (4 : ℝ) * 4 ^ ν ≤ Real.exp 4 * (Real.exp 4) ^ ν := by gcongr
    _ = Real.exp (4 + (ν : ℝ) * 4) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The implemented r,lambda budget absorbs the explicit exponential tail. -/
theorem exponential_tail_budget {r lam ν : ℕ} (hr : 2 ≤ r) (hν : 1 ≤ ν)
    (hrlam : r ^ 2 ≤ lam) (hlam : lam ≤ 2 ^ ν) :
    2 * Real.exp (-(64 * (ν : ℝ))) ≤ 1 / (2 * (r : ℝ) ^ 2 * lam) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlampos : (0 : ℝ) < lam := by exact_mod_cast (show 0 < lam by nlinarith)
  have hrLam : (r : ℝ) ^ 2 * lam ≤ (4 : ℝ) ^ ν := by
    have hr2 : (r : ℝ) ^ 2 ≤ lam := by exact_mod_cast hrlam
    have hLam : (lam : ℝ) ≤ (2 : ℝ) ^ ν := by exact_mod_cast hlam
    calc
      (r : ℝ) ^ 2 * lam ≤ (lam : ℝ) * lam := mul_le_mul_of_nonneg_right hr2 (by positivity)
      _ ≤ ((2 : ℝ) ^ ν) * (2 ^ ν) := by gcongr
      _ = _ := by rw [← mul_pow]; norm_num
  have he := four_power_le_exp hν
  have hbudget : 4 * (r : ℝ) ^ 2 * lam ≤ Real.exp (64 * (ν : ℝ)) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hbudget (Real.exp_pos (-(64 * (ν : ℝ)))).le
  have hexp : Real.exp (-(64 * (ν : ℝ))) * Real.exp (64 * (ν : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hexp] at hm
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ) ^ 2 * lam)).mpr
  nlinarith

/-- A sufficient finite integer width condition, specialized to the actual
Q-trial spectrum and the actual centered interval. -/
theorem centered_tail_le_budget {r Q R lam ν : ℕ} (hr : 2 ≤ r) (hR : 2 ≤ R)
    (hQR : 6 * R ≤ Q) (hν : 1 ≤ ν) (hrlam : r ^ 2 ≤ lam)
    (hlam : lam ≤ 2 ^ ν) (hQbudget : 128 * ν * Q ≤ lam)
    (hRbudget : 16 * lam ≤ R ^ 2) :
    binomialMean (negativeProbability r) Q
      (fun k => if k ∉ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R) then 1 else 0) ≤
      1 / (2 * (r : ℝ) ^ 2 * lam) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQB : 128 * (ν : ℝ) * Q ≤ lam := by exact_mod_cast hQbudget
  have hRB : 16 * (lam : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast hRbudget
  have hratio : 64 * (ν : ℝ) ≤ (R : ℝ) ^ 2 / (32 * Q) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * Q)).mpr
    nlinarith
  have he : Real.exp (-((R : ℝ) ^ 2) / (32 * Q)) ≤
      Real.exp (-(64 * (ν : ℝ))) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hratio
  exact (centered_tail_le_exp hr hR hQR).trans
    ((mul_le_mul_of_nonneg_left he (by norm_num)).trans
      (exponential_tail_budget hr hν hrlam hlam))

/-- The exact ceiling square root dominates lambda after squaring. -/
theorem scheduledCeilSqrt_sq_ge (lam : ℕ) : lam ≤ scheduledCeilSqrt lam ^ 2 := by
  unfold scheduledCeilSqrt
  split_ifs with h
  · simpa using le_of_eq h.symm
  · simpa only [Nat.succ_eq_add_one] using le_of_lt (Nat.lt_succ_sqrt' lam)

/-- The actual integer schedule passes the normalized tail bound once its
explicit double-log range holds. No supplied tail hypothesis is used. -/
theorem scheduled_centered_tail_le_budget {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) :
    binomialMean (negativeProbability (scheduledGroupCount lam)) (scheduledPointCount lam)
      (fun k => if k ∉ Finset.Ico
        (intervalStart (scheduledGroupCount lam) (scheduledPointCount lam) (scheduledDegree lam))
        (intervalStart (scheduledGroupCount lam) (scheduledPointCount lam) (scheduledDegree lam) +
          scheduledDegree lam) then 1 else 0) ≤
      1 / (2 * (scheduledGroupCount lam : ℝ) ^ 2 * lam) := by
  have hranges := scheduled_parameter_ranges hν
  apply centered_tail_le_budget (r := scheduledGroupCount lam) (Q := scheduledPointCount lam)
    (R := scheduledDegree lam) (lam := lam) (ν := Nat.clog 2 lam) hranges.1 (by omega) hranges.2.2 (by omega)
  · exact (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans (Nat.sqrt_le' lam)
  · exact Nat.le_pow_clog (by decide) lam
  · simpa [scheduledPointCount, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self lam (128 * Nat.clog 2 lam)
  · have h := scheduledCeilSqrt_sq_ge lam
    unfold scheduledDegree
    nlinarith

/-- The exact integer numerator accumulated by shared_parameters.binomial_tail. -/
def tailNumerator (r Q A R : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (Q + 1), if k ∈ Finset.Ico A (A + R) then 0
    else Q.choose k * (r - 1) ^ k * (r + 1) ^ (Q - k)

private theorem binomial_weight_common_denominator {r Q k : ℕ} (hr : 2 ≤ r) (hk : k ≤ Q) :
    (Q.choose k : ℝ) * (1 - negativeProbability r) ^ (Q - k) * negativeProbability r ^ k =
      (Q.choose k : ℝ) * ((r : ℝ) - 1) ^ k * ((r : ℝ) + 1) ^ (Q - k) /
        (2 * (r : ℝ)) ^ Q := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hm : 1 - negativeProbability r = ((r : ℝ) + 1) / (2 * r) := by
    unfold negativeProbability
    field_simp
    ring
  rw [hm, negativeProbability, div_pow, div_pow]
  rw [mul_assoc, div_mul_div_comm, ← pow_add, Nat.sub_add_cancel hk]
  ring

/-- Exact agreement of the finite real mass function with the integer loop.
The cast identity uses Q trials, not the external spectral proof's Q-1. -/
theorem tailNumerator_normalized {r Q A R : ℕ} (hr : 2 ≤ r) :
    (tailNumerator r Q A R : ℝ) / ((2 * r : ℕ) ^ Q : ℕ) =
      binomialMean (negativeProbability r) Q
        (fun k => if k ∉ Finset.Ico A (A + R) then 1 else 0) := by
  rw [tailNumerator, Nat.cast_sum, Finset.sum_div]
  unfold binomialMean
  apply Finset.sum_congr rfl
  intro k hk
  have hkQ : k ≤ Q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  by_cases hin : k ∈ Finset.Ico A (A + R)
  · simp [hin]
  · simp only [hin, ↓reduceIte, not_false_eq_true, mul_one]
    rw [binomial_weight_common_denominator hr hkQ]
    push_cast [Nat.cast_sub (show 1 ≤ r by omega)]
    ring

/-- Literal cross-multiplied binomial guard for occurrence b=2 and
`tau_denominator=r*lambda`, exactly as in shared_parameters.check_guard. -/
def tailGuard (lam : ℕ) : Prop :=
  let r := scheduledGroupCount lam
  let Q := scheduledPointCount lam
  let R := scheduledDegree lam
  tailNumerator r Q (intervalStart r Q R) R * (2 * r ^ 2 * lam) ≤ (2 * r) ^ Q

/-- The actual finite integer loop's tail test passes under the proved range. -/
theorem scheduled_tail_guard {lam : ℕ} (hν : 64 ≤ Nat.clog 2 lam) : tailGuard lam := by
  let r := scheduledGroupCount lam
  let Q := scheduledPointCount lam
  let R := scheduledDegree lam
  have hranges := scheduled_parameter_ranges hν
  have hr : 2 ≤ r := hranges.1
  have hrLam : r ^ 2 ≤ lam :=
    (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans (Nat.sqrt_le' lam)
  have hlampos : 0 < lam := by nlinarith
  have hden : (0 : ℝ) < (((2 * r) ^ Q : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (show 0 < 2 * r by omega) Q)
  have hbudget : (0 : ℝ) < 2 * (r : ℝ) ^ 2 * lam := by positivity
  have hs := scheduled_centered_tail_le_budget hν
  rw [← tailNumerator_normalized hr] at hs
  have hc := (div_le_div_iff₀ hden hbudget).mp hs
  have hcast : (tailNumerator r Q (intervalStart r Q R) R : ℝ) *
      (2 * (r : ℝ) ^ 2 * lam) ≤ (((2 * r) ^ Q : ℕ) : ℝ) := by simpa using hc
  exact_mod_cast hcast

/-- No supplied tail hypothesis: every sufficiently large actual input length
passes the exact finite binomial guard. -/
theorem eventually_scheduled_tail_guard :
    ∀ᶠ n : ℕ in atTop, tailGuard (Nat.clog 2 n) := by
  have ht := tendsto_clog_two_atTop.comp tendsto_clog_two_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop 64)] with n hn
  exact scheduled_tail_guard hn

/-- All mathematical checks of the actual schedule and Lemma 4.7 guard, for
M=2n and occurrence b=2. Scopes and local predicates still require their own
correctness/complexity connection; this is not an execution theorem. -/
def exactScheduleGuard (n w : ℕ) : Prop :=
  let lam := Nat.clog 2 n
  let r := scheduledGroupCount lam
  let Q := scheduledPointCount lam
  let R := scheduledDegree lam
  0 < n ∧ 0 < w ∧ 2 ≤ r ∧ 1 ≤ R ∧ R < Q ∧ 2 ≤ r * lam ∧
    intervalStart r Q R + R ≤ Q + 1 ∧
    2 * (2 + w) * scheduledDimension n ^ 2 ≤ 2 * n ∧
    2 * Q * r ^ 2 ≤ n ∧ tailGuard lam ∧ 32 ≤ R ∧ 6 * R ≤ Q

/-- Eventual acceptance of the exact implemented schedule for growing arity
w<=C*n^(3/4), proved without assuming any acceptance or binomial-tail premise. -/
theorem eventually_exact_schedule_guard (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ, 0 < w →
      (w : ℝ) ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) → exactScheduleGuard n w := by
  filter_upwards [eventually_non_tail_schedule_checks C hC,
    eventually_scheduled_tail_guard, eventually_gt_atTop (0 : ℕ)] with n hn ht hnpos w hwpos hw
  obtain ⟨hr, hR32, h6R, hRQ, hden, hload, hgroups, hinterval⟩ := hn w hw
  exact ⟨hnpos, hwpos, hr, by omega, hRQ, hden, hinterval,
    hload, hgroups, ht, hR32, h6R⟩

end RiemannGaussian.SemiprimeCounterTail
