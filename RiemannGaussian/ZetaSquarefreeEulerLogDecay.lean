/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerQuadraticSieveDecay

/-!
# Logarithmic squarefree decay under the quadratic sieve

The physical logarithm is transported by an exact polynomial identity.
The linear moment cost is paid by the independently proved subexponential
allowance, uniformly over every moving squarefree mark.
-/

namespace RiemannGaussian.SquarefreeEulerLog
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- Coefficient multiplication that raises the factorial order by one
while restoring one physical logarithm. Every complex coefficient is retained. -/
def raisedPolynomial (p : Polynomial ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ p.support, Polynomial.monomial k (((N + k + 1 : ℕ) : ℂ) * p.coeff k)

/-- Raising the polynomial has its exact coefficient at every index. -/
theorem raisedPolynomial_coeff (p : Polynomial ℂ) (N k : ℕ) :
    (raisedPolynomial p N).coeff k = ((N + k + 1 : ℕ) : ℂ) * p.coeff k := by
  simp only [raisedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hk
    simp [Polynomial.notMem_support_iff.mp hk]

/-- The positive moment multipliers preserve the exact polynomial support. -/
theorem raisedPolynomial_support (p : Polynomial ℂ) (N : ℕ) :
    (raisedPolynomial p N).support = p.support := by
  ext k
  simp only [Polynomial.mem_support_iff, raisedPolynomial_coeff, mul_ne_zero_iff]
  exact and_iff_right (by exact_mod_cast (show N + k + 1 ≠ 0 by omega))

/-- The original division and the logarithm-raising operation are exact inverses. -/
theorem divided_raisedPolynomial (p : Polynomial ℂ) (N : ℕ) :
    RoughSquarefreeBare.dividedPolynomial (raisedPolynomial p N) N = p := by
  ext k
  have hn : ((N + k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show N + k + 1 ≠ 0 by omega)
  rw [RoughSquarefreeBare.dividedPolynomial_coeff, raisedPolynomial_coeff]
  field_simp

/-- One physical logarithm is exactly the raised polynomial at the next order. -/
theorem log_mul_kernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ) (x : ℝ) :
    (Real.log x : ℂ) * zetaPrimeFilterKernel p N s x =
      zetaPrimeFilterKernel (raisedPolynomial p N) (N + 1) s x := by
  have h := RoughSquarefreeBare.log_mul_kernel (raisedPolynomial p N) N s x
  rwa [divided_raisedPolynomial] at h

private theorem support_X_mul (p : Polynomial ℂ) :
    (Polynomial.X * p).support = p.support.image (fun k ↦ k + 1) := by
  ext k
  cases k with
  | zero => simp [Polynomial.mem_support_iff]
  | succ k => simp [Polynomial.mem_support_iff, Polynomial.coeff_X_mul]

private theorem envelope_X_mul (p : Polynomial ℂ) :
    (∑ k ∈ (Polynomial.X * p).support, ‖(Polynomial.X * p).coeff k‖) =
      ∑ k ∈ p.support, ‖p.coeff k‖ := by
  rw [support_X_mul, Finset.sum_image (fun a _ b _ hab ↦ Nat.add_right_cancel hab)]
  exact Finset.sum_congr rfl (fun k _ ↦ by rw [Polynomial.coeff_X_mul])

/-- The full raised coefficient envelope costs at most one linear
moment factor, with the fixed polynomial's weighted envelope explicit. -/
theorem raisedPolynomial_envelope_le (p : Polynomial ℂ) (N : ℕ) :
    (∑ k ∈ (Polynomial.X * raisedPolynomial p N).support,
      ‖(Polynomial.X * raisedPolynomial p N).coeff k‖) ≤
        (N + 1 : ℝ) * ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖ := by
  rw [envelope_X_mul, raisedPolynomial_support, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [raisedPolynomial_coeff, norm_mul, Complex.norm_natCast]
  simp only [Nat.cast_add, Nat.cast_one]
  have h : (N + k + 1 : ℝ) ≤ (N + 1 : ℝ) * (k + 1 : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) k]
  exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (by ring)

/-- The genuine complete squarefree series with its physical logarithm. -/
def response (p : Polynomial ℂ) (S : Finset ℕ) (P N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, RoughSquarefreeBare.coefficient S P n * (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n

/-- The logarithmic arithmetic response is an exact original bare
response with its raised and shifted polynomial. -/
theorem response_eq_raised (p : Polynomial ℂ) (S : Finset ℕ) (P N : ℕ) (s : ℂ) :
    response p S P N s = RoughSquarefreeBare.response (Polynomial.X * raisedPolynomial p N) S P N s := by
  apply tsum_congr
  intro n
  rw [mul_assoc, log_mul_kernel]
  simp only [zetaPrimeFilterKernel, zetaFactorialPolynomial_X_mul]

/-- The logarithmic series converges genuinely in the Euler half-plane. -/
theorem summable_response (p : Polynomial ℂ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (P N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ RoughSquarefreeBare.coefficient S P n * (Real.log n : ℂ) *
      zetaPrimeFilterKernel p N s n) := by
  apply (RoughSquarefreeBare.summable_response (raisedPolynomial p N) S hS P N hs).congr
  intro n
  rw [mul_assoc, log_mul_kernel]

/-- The full logarithmic response has an independent bound uniform
over all marks and all prime subsets of the allowed quadratic sieve. -/
theorem exists_quadratic_sieve_bound (y : ℝ) (hy : 1 < |y|)
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop,
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime ∧ a ≤ R N) → ∀ (P : ℕ) (p : Polynomial ℂ),
        ‖response p S P N (3 / 2 + I * y)‖ ≤
          C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
            ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_squarefreeEuler_quadratic_sieve_bound y hy R hR hcut
  refine ⟨C, hC, hb.mono ?_⟩
  intro N hN S hS P p
  rw [response_eq_raised]
  exact (hN S hS P (Polynomial.X * raisedPolynomial p N)).trans
    ((mul_le_mul_of_nonneg_left (raisedPolynomial_envelope_le p N) (by positivity)).trans_eq (by ring))

/-- The quadratic-sieve saving absorbs the full linear cost of a
physical logarithm, without any lower growth condition on the cutoff. -/
theorem tendsto_quadratic_sieve_log_allowance (R : ℕ → ℕ)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) *
      Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ)))) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ ↦ (N : ℝ) + 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hlogsq : Tendsto (fun N : ℕ ↦ Real.log (N + 2 : ℝ) ^ 2 / N) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 (by norm_num)).comp hx using 1
    funext N
    simp
  have hsmall := hlogsq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 80))
  have hbound : ∀ᶠ N : ℕ in atTop,
      (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) ≤
        Real.sqrt (Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ)))) := by
    filter_upwards [hcut, hsmall, eventually_ge_atTop 1] with N hcut hsmall hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL : 0 < Real.log (R N + 2 : ℝ) := Real.log_pos (by
      have := Nat.cast_nonneg (α := ℝ) (R N)
      linarith)
    have hs := Real.sq_sqrt (Nat.cast_nonneg (R N))
    have hR : (R N : ℝ) ≤ (N : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (R N)]
    have hlogR := Real.log_le_log (show (0 : ℝ) < R N + 2 by positivity)
      (show (R N + 2 : ℝ) ≤ (N + 2 : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at hlogR
    norm_num only [Nat.cast_ofNat] at hlogR
    have hlogN : Real.log (N + 1 : ℝ) ≤ Real.log (N + 2 : ℝ) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogN0 : 0 ≤ Real.log (N + 2 : ℝ) := Real.log_nonneg (by linarith)
    have hprod := mul_le_mul hlogN hlogR hL.le hlogN0
    have hsq : 80 * Real.log (N + 2 : ℝ) ^ 2 ≤ N := by
      have h := (div_lt_iff₀ hN0).mp hsmall
      nlinarith
    have hhalf : Real.log (N + 1 : ℝ) ≤ (N : ℝ) / (40 * Real.log (R N + 2 : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have heq : (N : ℝ) / (40 * Real.log (R N + 2 : ℝ)) =
        ((N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) / 2 := by ring
    rw [heq] at hhalf
    calc
      _ = Real.exp (Real.log (N + 1 : ℝ) + -(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ Real.exp ((-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) / 2) := by
        apply Real.exp_le_exp.mpr
        simp only [neg_div] at *
        linarith
      _ = _ := Real.exp_half _
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity)) hbound
  simpa using (tendsto_squarefreeEuler_quadratic_sieve_allowance R hcut).sqrt

/-- The complete logarithmic response tends to zero for every moving
mark and prime subset under the quadratic cutoff. -/
theorem tendsto_quadratic_sieve (y : ℝ) (hy : 1 < |y|)
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40)
    (S : ℕ → Finset ℕ) (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ R N)
    (P : ℕ → ℕ) (p : Polynomial ℂ) :
    Tendsto (fun N ↦ response p (S N) (P N) N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_quadratic_sieve_bound y hy R hR hcut
  apply squeeze_zero_norm' (hb.mono (fun N hN ↦ hN (S N) (hS N) (P N) p))
  simpa only [mul_zero, zero_mul, mul_assoc] using
    ((tendsto_quadratic_sieve_log_allowance R hcut).const_mul C).mul_const
      (∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖)

/-- The original full quadratic sieve has unscaled logarithmic
squarefree decay for every moving mark and fixed complex polynomial. -/
theorem tendsto_actual_quadratic_sieve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ) (p : Polynomial ℂ) :
    Tendsto (fun N ↦ response p (zetaRightHalfPrimePatternPrimes rho N)
      (P N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  exact tendsto_quadratic_sieve rho.1.im (nontrivialZetaZero_one_lt_abs_im rho)
    (zetaRightHalfPrimePatternCutoff rho) (tendsto_zetaRightHalfPrimePatternCutoff rho hrho)
    (Eventually.of_forall (sqrt_zetaRightHalfPrimePatternCutoff_le rho hrho))
    (zetaRightHalfPrimePatternPrimes rho) (zetaRightHalfPrimePatternPrimes_eligible rho) P p

end
end RiemannGaussian.SquarefreeEulerLog
