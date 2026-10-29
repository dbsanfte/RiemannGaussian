import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity

namespace OAI.Algorithms

/-! Exponential concentration for the exact binomial swap spectrum.
All distribution parameters are explicit; no arity parameter is fixed. -/

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators

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

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
