/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothHead
import RiemannGaussian.ZetaRieszGeneralCofactorTilt

/-!
# Prime-prefix bounds with full smooth cofactor mass

The original finite prime/cofactor pair sum has an explicit Euler-product
allowance with arbitrary subband masks and no maximum-cofactor-size cost.
The original physical prime cutoff recovers the exact general-tilt rate.
Quadratic prime heads are paid whenever an admissible scalar saving holds.
-/

namespace RiemannGaussian.ZetaRieszSmoothPrimeProduct
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothHead

/-- A prime insertion adds at most one divisor-choice factor, even
when repeated insertion makes the actual squarefree coefficient vanish. -/
theorem norm_coefficient_prime_mul_le_count {a p : ℕ} (ha : Squarefree a) (hp : p.Prime)
    {L : ℝ} (hL : 0 < L) :
    ‖SquarefreeVaughanLogSource.coefficient L (p * a)‖ ≤
      Real.log ((p * a : ℕ) : ℝ) * (2 * (2 : ℝ) ^ a.primeFactors.card) := by
  by_cases hn : Squarefree (p * a)
  · have hcard : (p * a).primeFactors.card ≤ a.primeFactors.card + 1 := by
      rw [Nat.primeFactors_mul hp.ne_zero ha.ne_zero, hp.primeFactors]
      simpa [add_comm] using (Finset.card_union_le ({p} : Finset ℕ) a.primeFactors)
    have hpow : (2 : ℝ) ^ (p * a).primeFactors.card ≤ 2 * (2 : ℝ) ^ a.primeFactors.card := by
      simpa [pow_succ, mul_comm] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard
    exact (SquarefreeVaughanLogSource.norm_coefficient_le hL (p * a)).trans
      ((logMajorant_le_prime_count hn).trans
        (mul_le_mul_of_nonneg_left hpow (Real.log_natCast_nonneg _)))
  · have hc : SquarefreeVaughanLogSource.coefficient L (p * a) = 0 := by
      simp [SquarefreeVaughanLogSource.coefficient, hn]
    rw [hc, norm_zero]
    positivity

/-- The literal prime/cofactor band atom retains its full factorial
filter and separates the complete cofactor Euler mass from the prime prefix. -/
theorem norm_prime_pair_atom_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {a p : ℕ} (ha : Squarefree a) (hp : p.Prime) (hband : p * a ∈ zetaPrimeLogBand N)
    {L q : ℝ} (hL : 0 < L) (hq : 1 / 2 < q) :
    ‖SquarefreeVaughanLogSource.coefficient L (p * a) *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p * a : ℕ)‖ ≤
      (64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      ((2 : ℝ) ^ a.primeFactors.card * Real.exp (-(3 / 2 - q) * Real.log a)) *
      (p : ℝ) ^ ((q - 1 / 2) - 1) := by
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hn0 : 0 < p * a := Nat.mul_pos hp.pos ha0
  have hc := (norm_coefficient_prime_mul_le_count ha hp hL).trans
    (mul_le_mul_of_nonneg_right (log_le_of_mem_band hband) (by positivity))
  have hk := ZetaRieszGeneralCofactorTilt.norm_filter_le_rpow P N y hq hn0
  rw [norm_mul]
  apply (mul_le_mul hc hk (norm_nonneg _) (by positivity)).trans_eq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg a),
    Real.rpow_def_of_pos haR]
  have he : Real.log (a : ℝ) * ((q - 1 / 2) - 1) = -(3 / 2 - q) * Real.log a := by ring
  rw [he]
  ring

/-- The original signed band contribution on finite prime/cofactor
pairs. A later identification with an integer class must prove uniqueness
of the selected prime insertion rather than silently counting labels twice. -/
def pairResponse (keep : ℕ → Prop) (A Q : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) : ℂ :=
  ∑ a ∈ A, ∑ p ∈ Q, if p * a ∈ zetaPrimeLogBand N ∧ keep (p * a) then
    SquarefreeVaughanLogSource.coefficient L (p * a) *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p * a : ℕ) else 0

/-- The full finite cofactor mass remains an Euler product, with no
maximum-cofactor size in the allowance. An arbitrary subband mask is retained. -/
theorem norm_pairResponse_le_product (keep : ℕ → Prop) (A Q S : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hS : ∀ a ∈ A, a.primeFactors ⊆ S)
    (hQ : ∀ p ∈ Q, p.Prime) {L q : ℝ} (hL : 0 < L) (hq : 1 / 2 < q) :
    ‖pairResponse keep A Q P N y L‖ ≤
      (64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      (∏ p ∈ S, (1 + 2 * Real.exp (-(3 / 2 - q) * Real.log p))) *
      ∑ p ∈ Q, (p : ℝ) ^ ((q - 1 / 2) - 1) := by
  let C : ℝ := 64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
    ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hq0 : 0 < q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w : ℕ → ℝ := fun a => (2 : ℝ) ^ a.primeFactors.card *
    Real.exp (-(3 / 2 - q) * Real.log a)
  calc
    _ ≤ ∑ a ∈ A, ‖∑ p ∈ Q, if p * a ∈ zetaPrimeLogBand N ∧ keep (p * a) then
      SquarefreeVaughanLogSource.coefficient L (p * a) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p * a : ℕ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ A, ∑ p ∈ Q, C * w a * (p : ℝ) ^ ((q - 1 / 2) - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with hb
      · exact norm_prime_pair_atom_le P N y (hA a ha) (hQ p hp) hb.1 hL hq
      · rw [norm_zero]
        dsimp [w]
        positivity
    _ = ∑ a ∈ A, (C * w a) * ∑ p ∈ Q, (p : ℝ) ^ ((q - 1 / 2) - 1) := by
      simp only [Finset.mul_sum]
    _ = (C * ∑ a ∈ A, w a) * ∑ p ∈ Q, (p : ℝ) ^ ((q - 1 / 2) - 1) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (squarefree_head_mass_le A S hA hS (3 / 2 - q)) hC)
      (Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)

/-- The retained prime prefix has the existing complete spatial
power allowance, while every smooth cofactor keeps its full Euler mass. -/
theorem norm_pairResponse_le_prefix (keep : ℕ → Prop) (A Q S : Finset ℕ) (P : Polynomial ℂ) (N X : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hS : ∀ a ∈ A, a.primeFactors ⊆ S)
    (hQ : ∀ p ∈ Q, p.Prime ∧ p ≤ X) {L q : ℝ} (hL : 0 < L) (hq : 1 / 2 < q) :
    ‖pairResponse keep A Q P N y L‖ ≤
      (64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      (∏ p ∈ S, (1 + 2 * Real.exp (-(3 / 2 - q) * Real.log p))) *
      ((1 + 1 / (q - 1 / 2)) * (X : ℝ) ^ (q - 1 / 2)) := by
  have hq0 : 0 < q := by linarith
  apply (norm_pairResponse_le_product keep A Q S P N y hA hS (fun p hp => (hQ p hp).1) hL hq).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ (ZetaRieszGeneralCofactorTilt.sum_rpow_prefix_le (by linarith) X)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_Icc.mpr ⟨(hQ p hp).1.pos, (hQ p hp).2⟩
  · intro p _hp _hp'
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- On the original physical prime prefix, the full smooth cofactor
mass multiplies the exact general-tilt geometric rate. No maximum-cofactor
size appears in the bound. -/
theorem norm_scaled_pairResponse_le_rate (keep : ℕ → Prop) (A Q S : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hS : ∀ a ∈ A, a.primeFactors ⊆ S)
    {u q : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q)
    (hQ : ∀ p ∈ Q, p.Prime ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖(u : ℂ) ^ (N + 1) * pairResponse keep A Q P N y (SquarefreeVaughanLogSource.length u N)‖ ≤
      (64 * Real.log 2 * ZetaRieszGeneralCofactorTilt.tiltCost P u q) * (N : ℝ) *
      (∏ p ∈ S, (1 + 2 * Real.exp (-(3 / 2 - q) * Real.log p))) *
      ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by
  let F : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  let H : ℝ := ∏ p ∈ S, (1 + 2 * Real.exp (-(3 / 2 - q) * Real.log p))
  have hq0 : 0 < q := by linarith
  have ha : 0 < q - 1 / 2 := by linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hb := norm_pairResponse_le_prefix keep A Q S P N
    ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) y hA hS hQ
    (SquarefreeVaughanLogSource.length_pos u N) hq
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hb
  have hp (v : ℝ) (hv : 0 ≤ v) : (v ^ 2) ^ (q - 1 / 2) = v ^ (2 * (q - 1 / 2)) := by
    rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv]
    norm_num
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le _)).trans
  calc
    _ ≤ u ^ (N + 1) * ((64 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N * F) * H *
        ((1 + 1 / (q - 1 / 2)) * ((3 * u⁻¹ ^ N) ^ 2) ^ (q - 1 / 2))) := by
      gcongr
      exact ZetaRieszExponentialCofactor.cutoff_add_two_le hu hu1 N
    _ = (64 * (N : ℝ) * Real.log 2 * F * H *
        (1 + 1 / (q - 1 / 2)) * (3 : ℝ) ^ (2 * (q - 1 / 2))) *
        (u ^ (N + 1) * q⁻¹ ^ N * (u⁻¹ ^ N) ^ (2 * (q - 1 / 2))) := by
      rw [hp _ (by positivity), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity)]
      ring
    _ = _ := by
      rw [ZetaRieszGeneralCofactorTilt.general_scale_identity hu q N]
      dsimp [F, H, ZetaRieszGeneralCofactorTilt.tiltCost]
      ring

/-- A strict general-tilt saving pays every quadratic smooth cofactor
family on the physical prime prefix. This statement is about the literal
finite pair sum; identifying an integer class still requires uniqueness. -/
theorem tendsto_quadratic_pairResponse (keep : ℕ → ℕ → Prop) (A Q S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    (hA : ∀ N a, a ∈ A N → Squarefree a)
    (hS : ∀ N a, a ∈ A N → a.primeFactors ⊆ S N)
    (hprime : ∀ N p, p ∈ S N → p.Prime ∧ p ≤ N ^ 2)
    {u q : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q) (hq1 : q ≤ 1)
    (hQ : ∀ N p, p ∈ Q N → p.Prime ∧
      p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hrate : ZetaRieszCofactorTiltRate.tiltRate u q < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      pairResponse (keep N) (A N) (Q N) P N y (SquarefreeVaughanLogSource.length u N)) atTop (nhds 0) := by
  let r := ZetaRieszCofactorTiltRate.tiltRate u q
  have hr : 0 < r := ZetaRieszGeneralCofactorTilt.tiltRate_pos u (by linarith)
  obtain ⟨eps, heps, hsmall⟩ := ZetaRieszEulerPrimeHeadDensity.exists_small_exponential_factor hr hrate
  let C := 64 * Real.log 2 * ZetaRieszGeneralCofactorTilt.tiltCost P u q
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (ZetaRieszGeneralCofactorTilt.tiltCost_nonneg P hu hq)
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * pairResponse (keep N) (A N) (Q N) P N y
        (SquarefreeVaughanLogSource.length u N)‖ ≤
      C * (((N : ℝ) + 1) * (r * Real.exp eps) ^ N) := by
    filter_upwards [ZetaRieszEulerPrimeHeadDensity.eventually_quadratic_head_product_le heps]
      with N hN
    apply (norm_scaled_pairResponse_le_rate (keep N) (A N) (Q N) (S N) P N y
      (hA N) (hS N) hu hu1 hq (hQ N)).trans
    calc
      _ ≤ C * (N : ℝ) * Real.exp (eps * N) * r ^ N := by
        gcongr
        exact hN (S N) (hprime N) _ (by linarith)
      _ = C * ((N : ℝ) * (r * Real.exp eps) ^ N) := by
        rw [show eps * (N : ℝ) = (N : ℝ) * eps by ring, Real.exp_nat_mul, mul_pow]
        ring
      _ ≤ _ := by gcongr; linarith
  apply squeeze_zero_norm' hb
  simpa only [pow_one, mul_zero] using
    (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
      (mul_pos hr (Real.exp_pos eps)) hsmall).const_mul C

end
end RiemannGaussian.ZetaRieszSmoothPrimeProduct
