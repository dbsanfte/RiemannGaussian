/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDivisorPrefix
import RiemannGaussian.ZetaRieszProductCeiling

/-!
# Large smooth factors with arbitrary squarefree rough kernels

The actual product ceiling leaves harmonic smooth-factor mass even when
the second factor has arbitrarily many primes. Its complete divisor cost
adds only one logarithm. The original filtered pair response has a cubic
order allowance against the same strict geometric rate whenever 2*u^2<1.
All original signs, masks, phases and factorial shifts remain upstream.
-/

namespace RiemannGaussian.ZetaRieszSmoothRoughProduct
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszDivisorPrefix

/-- Inserting an arbitrary squarefree factor retains its exact full
divisor-choice cost; no fixed bound on its number of primes is imposed. -/
theorem norm_coefficient_mul_le_count {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    {L : ℝ} (hL : 0 < L) :
    ‖SquarefreeVaughanLogSource.coefficient L (b * a)‖ ≤
      Real.log ((b * a : ℕ) : ℝ) *
        ((2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) := by
  by_cases hn : Squarefree (b * a)
  · have hcard : (b * a).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
      rw [Nat.primeFactors_mul hb.ne_zero ha.ne_zero]
      simpa [add_comm] using Finset.card_union_le b.primeFactors a.primeFactors
    have hpow : (2 : ℝ) ^ (b * a).primeFactors.card ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
      simpa [pow_add] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard
    exact (SquarefreeVaughanLogSource.norm_coefficient_le hL (b * a)).trans
      ((ZetaRieszSmoothHead.logMajorant_le_prime_count hn).trans
        (mul_le_mul_of_nonneg_left hpow (Real.log_natCast_nonneg _)))
  · have hc : SquarefreeVaughanLogSource.coefficient L (b * a) = 0 := by
      simp [SquarefreeVaughanLogSource.coefficient, hn]
    rw [hc, norm_zero]
    positivity

/-- The original full-filter product atom separates two squarefree
factor masses without fixing the number of primes in either factor. -/
theorem norm_squarefree_pair_atom_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) (hband : b * a ∈ zetaPrimeLogBand N)
    {L q : ℝ} (hL : 0 < L) (hq : 1 / 2 < q) :
    ‖SquarefreeVaughanLogSource.coefficient L (b * a) *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (b * a : ℕ)‖ ≤
      (32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-(3 / 2 - q) * Real.log a)) *
      ((2 : ℝ) ^ b.primeFactors.card * (b : ℝ) ^ ((q - 1 / 2) - 1)) := by
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hb0 : 0 < b := Nat.pos_of_ne_zero hb.ne_zero
  have hc := (norm_coefficient_mul_le_count ha hb hL).trans
    (mul_le_mul_of_nonneg_right (ZetaRieszSmoothHead.log_le_of_mem_band hband) (by positivity))
  have hk := ZetaRieszGeneralCofactorTilt.norm_filter_le_rpow P N y hq (Nat.mul_pos hb0 ha0)
  rw [norm_mul]
  apply (mul_le_mul hc hk (norm_nonneg _) (by positivity)).trans_eq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg b) (Nat.cast_nonneg a),
    Real.rpow_def_of_pos haR]
  have he : Real.log (a : ℝ) * ((q - 1 / 2) - 1) = -(3 / 2 - q) * Real.log a := by ring
  rw [he]
  ring

/-- The full squarefree rough factor costs only one extra logarithm
in the product-ceiling bound, independently of how many primes it contains.
The signed pair response and every original subband mask are unchanged. -/
theorem norm_pairResponse_le_harmonic_squarefree (keep : ℕ → Prop) (A Q : Finset ℕ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hQ : ∀ b ∈ Q, Squarefree b)
    {L q : ℝ} (hL : 0 < L) (hq : 1 / 2 < q) :
    ‖ZetaRieszSmoothPrimeProduct.pairResponse keep A Q P N y L‖ ≤
      (32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      (1 + 1 / (q - 1 / 2)) * ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) *
      (1 + Real.log ((2 : ℝ) ^ (32 * N))) *
      ∑ a ∈ A, (2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a) := by
  let B : ℕ := 2 ^ (32 * N)
  let C : ℝ := 32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
    ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  let alpha : ℝ := q - 1 / 2
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have hq0 : 0 < q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : (0 : ℝ) < B := by dsimp [B]; positivity
  have hi (a : ℕ) (ha : a ∈ A) :
      ‖∑ b ∈ Q, if b * a ∈ zetaPrimeLogBand N ∧ keep (b * a) then
        SquarefreeVaughanLogSource.coefficient L (b * a) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (b * a : ℕ) else 0‖ ≤
      C * (1 + 1 / alpha) * (B : ℝ) ^ alpha * (1 + Real.log B) *
        ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a)) := by
    have ha0 : 0 < a := Nat.pos_of_ne_zero (hA a ha).ne_zero
    have haR : (0 : ℝ) < a := by exact_mod_cast ha0
    let T := Q.filter (fun b => b * a ∈ zetaPrimeLogBand N ∧ keep (b * a))
    let w : ℝ := (2 : ℝ) ^ a.primeFactors.card *
      Real.exp (-(3 / 2 - q) * Real.log a)
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have hT : ∀ b ∈ T, Squarefree b ∧ b ≤ B / a := by
      intro b hb
      obtain ⟨hb, hband⟩ := Finset.mem_filter.mp hb
      refine ⟨hQ b hb, (Nat.le_div_iff_mul_le ha0).mpr ?_⟩
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hband.1).1).2
    have hdiv : ((B / a : ℕ) : ℝ) ≤ (B : ℝ) / a := by
      apply (le_div_iff₀ haR).mpr
      exact_mod_cast Nat.div_mul_le_self B a
    have hlog : Real.log ((B / a : ℕ) : ℝ) ≤ Real.log B := by
      by_cases hz : B / a = 0
      · simpa only [hz, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg B
      · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
        exact_mod_cast Nat.div_le_self B a
    calc
      _ = ‖∑ b ∈ T, SquarefreeVaughanLogSource.coefficient L (b * a) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (b * a : ℕ)‖ := by
        simp only [T, Finset.sum_filter]
      _ ≤ ∑ b ∈ T, C * w * ((2 : ℝ) ^ b.primeFactors.card * (b : ℝ) ^ (alpha - 1)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hb, hband⟩ := Finset.mem_filter.mp hb
        exact norm_squarefree_pair_atom_le P N y (hA a ha) (hQ b hb) hband.1 hL hq
      _ = C * w * ∑ b ∈ T, (2 : ℝ) ^ b.primeFactors.card * (b : ℝ) ^ (alpha - 1) := by
        rw [Finset.mul_sum]
      _ ≤ C * w * ((1 + 1 / alpha) * ((B / a : ℕ) : ℝ) ^ alpha *
          (1 + Real.log ((B / a : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (squarefree_rpow_prefix_le T (B / a) hT halpha) (mul_nonneg hC hw)
      _ ≤ C * w * ((1 + 1 / alpha) * ((B : ℝ) / a) ^ alpha * (1 + Real.log B)) := by
        gcongr
      _ = _ := by
        rw [Real.div_rpow hB.le haR.le, Real.rpow_def_of_pos haR, Real.exp_neg]
        dsimp [w]
        have he : Real.exp (-(3 / 2 - q) * Real.log a) /
            Real.exp (Real.log a * alpha) = (Real.exp (Real.log a))⁻¹ := by
          rw [← Real.exp_sub, ← Real.exp_neg]
          congr 1
          dsimp [alpha]
          ring
        calc
          _ = C * (1 + 1 / alpha) * (B : ℝ) ^ alpha * (1 + Real.log B) *
              (2 : ℝ) ^ a.primeFactors.card *
              (Real.exp (-(3 / 2 - q) * Real.log a) / Real.exp (Real.log a * alpha)) := by ring
          _ = _ := by rw [he]; ring
  calc
    _ ≤ ∑ a ∈ A, ‖∑ b ∈ Q, if b * a ∈ zetaPrimeLogBand N ∧ keep (b * a) then
        SquarefreeVaughanLogSource.coefficient L (b * a) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (b * a : ℕ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ A, C * (1 + 1 / alpha) * (B : ℝ) ^ alpha * (1 + Real.log B) *
        ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-Real.log a)) := Finset.sum_le_sum hi
    _ = _ := by simp only [← Finset.mul_sum, B, Nat.cast_pow, Nat.cast_ofNat, C, alpha]

/-- Arbitrarily many rough prime factors cost only a cubic order
allowance against the same strict large-smooth-factor geometric rate. -/
theorem norm_scaled_large_smooth_product_le (keep : ℕ → Prop) (A Q S : Finset ℕ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hS : ∀ a ∈ A, a.primeFactors ⊆ S)
    (hQ : ∀ b ∈ Q, Squarefree b) {u q : ℝ} (hu : 0 < u) (hq : 1 / 2 < q)
    (hlarge : ∀ a ∈ A, (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a) :
    ‖(u : ℂ) ^ (N + 1) * ZetaRieszSmoothPrimeProduct.pairResponse keep A Q P N y
      (SquarefreeVaughanLogSource.length u N)‖ ≤
      (32 * Real.log 2 * u * (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (1 + 1 / (q - 1 / 2))) * (N : ℝ) * ((N : ℝ) + 1) *
      (1 + 32 * (N : ℝ) * Real.log 2) *
      (∏ p ∈ S, (1 + 2 * Real.exp (-(1 / 2 : ℝ) * Real.log p))) *
      ZetaRieszProductCeiling.largeCofactorRate u q ^ N := by
  have hq0 : 0 < q := by linarith
  have hb := norm_pairResponse_le_harmonic_squarefree keep A Q P N y hA hQ
    (SquarefreeVaughanLogSource.length_pos u N) hq
  have hm := ZetaRieszProductCeiling.harmonic_head_tail_le A S hA hS
    (by positivity : (0 : ℝ) < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2)
    (fun a ha => by exact_mod_cast hlarge a ha)
  have hlog : Real.log ((2 : ℝ) ^ (32 * N)) = 32 * (N : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left hb' (pow_nonneg hu.le _)).trans
  calc
    _ ≤ u ^ (N + 1) *
        ((32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
          ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (1 + 1 / (q - 1 / 2)) * ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) *
        (1 + 32 * (N : ℝ) * Real.log 2) *
        ((((N : ℝ) + 1) * u ^ N) *
          ∏ p ∈ S, (1 + 2 * Real.exp (-(1 / 2 : ℝ) * Real.log p)))) := by
      gcongr
      exact ZetaRieszProductCeiling.physical_reciprocal_le hu N
    _ = _ := by
      have he : ((2 : ℝ) ^ (32 * N)) ^ (q - 1 / 2) =
          Real.exp (32 * (q - 1 / 2) * Real.log 2) ^ N := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [he]
      simp only [ZetaRieszProductCeiling.largeCofactorRate, div_pow, mul_pow, inv_pow, pow_succ]
      ring

/-- Every large quadratic smooth factor is independently paid even
against an arbitrary squarefree second-factor family and arbitrary masks. -/
theorem tendsto_large_smooth_pairResponse (keep : ℕ → ℕ → Prop)
    (A Q S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    (hA : ∀ N a, a ∈ A N → Squarefree a)
    (hS : ∀ N a, a ∈ A N → a.primeFactors ⊆ S N)
    (hprime : ∀ N p, p ∈ S N → p.Prime ∧ p ≤ N ^ 2)
    (hQ : ∀ N b, b ∈ Q N → Squarefree b) {u : ℝ} (hu : 0 < u)
    (hu2 : 2 * u ^ 2 < 1)
    (hlarge : ∀ N a, a ∈ A N →
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ZetaRieszSmoothPrimeProduct.pairResponse (keep N) (A N) (Q N) P N y
        (SquarefreeVaughanLogSource.length u N)) atTop (nhds 0) := by
  obtain ⟨q, hq, hrate⟩ := ZetaRieszProductCeiling.exists_large_cofactor_tilt hu2
  let r : ℝ := ZetaRieszProductCeiling.largeCofactorRate u q
  have hr : 0 < r := ZetaRieszProductCeiling.largeCofactorRate_pos hu (by linarith)
  obtain ⟨eps, heps, hsmall⟩ := ZetaRieszEulerPrimeHeadDensity.exists_small_exponential_factor hr hrate
  let C : ℝ := 32 * Real.log 2 * u * (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
    (1 + 1 / (q - 1 / 2))
  have hq0 : 0 < q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (N : ℕ) : (N : ℝ) * ((N : ℝ) + 1) * (1 + 32 * (N : ℝ) * Real.log 2) ≤
      (1 + 32 * Real.log 2) * ((N : ℝ) + 1) ^ 3 := by
    have hN := Nat.cast_nonneg (α := ℝ) N
    have hlog : 0 ≤ Real.log 2 := by positivity
    have hl : 1 + 32 * (N : ℝ) * Real.log 2 ≤ (1 + 32 * Real.log 2) * ((N : ℝ) + 1) := by
      nlinarith
    calc
      _ ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) * ((1 + 32 * Real.log 2) * ((N : ℝ) + 1)) := by gcongr; linarith
      _ = _ := by ring
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * ZetaRieszSmoothPrimeProduct.pairResponse (keep N) (A N) (Q N) P N y
        (SquarefreeVaughanLogSource.length u N)‖ ≤
      (C * (1 + 32 * Real.log 2)) * (((N : ℝ) + 1) ^ 3 * (r * Real.exp eps) ^ N) := by
    filter_upwards [ZetaRieszEulerPrimeHeadDensity.eventually_quadratic_head_product_le heps]
      with N hN
    apply (norm_scaled_large_smooth_product_le (keep N) (A N) (Q N) (S N) P N y
      (hA N) (hS N) (hQ N) hu hq (hlarge N)).trans
    calc
      _ ≤ C * (N : ℝ) * ((N : ℝ) + 1) * (1 + 32 * (N : ℝ) * Real.log 2) *
          Real.exp (eps * N) * r ^ N := by
        gcongr
        exact hN (S N) (hprime N) (1 / 2) le_rfl
      _ = C * ((N : ℝ) * ((N : ℝ) + 1) * (1 + 32 * (N : ℝ) * Real.log 2) *
          (r * Real.exp eps) ^ N) := by
        rw [show eps * (N : ℝ) = (N : ℝ) * eps by ring, Real.exp_nat_mul, mul_pow]
        ring
      _ ≤ C * (((1 + 32 * Real.log 2) * ((N : ℝ) + 1) ^ 3) * (r * Real.exp eps) ^ N) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hp N)
          (pow_nonneg (mul_nonneg hr.le (Real.exp_pos eps).le) N)) hC
      _ = _ := by ring
  apply squeeze_zero_norm' hb
  simpa only [mul_zero] using
    (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
      (mul_pos hr (Real.exp_pos eps)) hsmall).const_mul (C * (1 + 32 * Real.log 2))

end
end RiemannGaussian.ZetaRieszSmoothRoughProduct
