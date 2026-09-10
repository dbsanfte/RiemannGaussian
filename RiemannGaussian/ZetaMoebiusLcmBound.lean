/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.NatLcmSqrtMass
import RiemannGaussian.ZetaMoebiusScaleBound

/-!
# Factor-sensitive bounds for the genuine signed arithmetic response

The exact intersection phase retains the gcd of the head divisor and
the selected factor. Summing its reciprocal-square-root weight gives a
factor-sensitive bound on both entire response multipliers. It applies
to every finite complex family of genuine mixed-prime arithmetic sectors,
with all overlaps still present in the original signed sum.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

private theorem log_lcm_add_log_gcd {d P : ℕ} (hd : 0 < d) (hP : 0 < P) :
    Real.log (Nat.lcm d P) + Real.log (Nat.gcd d P) = Real.log d + Real.log P := by
  have hL : (Nat.lcm d P : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hd hP).ne'
  have hG : (Nat.gcd d P : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left P hd).ne'
  rw [← Real.log_mul hL hG, ← Nat.cast_mul, mul_comm (Nat.lcm d P), Nat.gcd_mul_lcm,
    Nat.cast_mul, Real.log_mul (by exact_mod_cast hd.ne') (by exact_mod_cast hP.ne')]

/-- The complete complex intersection phase factors through both
physical factors and their gcd. No imaginary component is discarded. -/
theorem zetaPrimeFeature_lcm_mul_gcd {d P : ℕ} (hd : 0 < d) (hP : 0 < P) (s : ℂ) :
    zetaPrimeFeature s (Nat.lcm d P) * zetaPrimeFeature s (Nat.gcd d P) =
      zetaPrimeFeature s d * zetaPrimeFeature s P := by
  have he : (Real.log (Nat.lcm d P) : ℂ) + (Real.log (Nat.gcd d P) : ℂ) =
      (Real.log d : ℂ) + (Real.log P : ℂ) := by exact_mod_cast log_lcm_add_log_gcd hd hP
  unfold zetaPrimeFeature
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  calc
    _ = -s * ((Real.log (Nat.lcm d P) : ℂ) + (Real.log (Nat.gcd d P) : ℂ)) := by ring
    _ = -s * ((Real.log d : ℂ) + (Real.log P : ℂ)) := by rw [he]
    _ = _ := by ring

/-- The logarithmic displacement is exactly the selected factor's
logarithm minus its common-divisor logarithm. -/
theorem zetaMultipleLogOffset_eq_log_factor_sub_gcd {d P : ℕ}
    (hd : 0 < d) (hP : 0 < P) :
    zetaMultipleLogOffset d P = Real.log P - Real.log (Nat.gcd d P) := by
  unfold zetaMultipleLogOffset
  linarith [log_lcm_add_log_gcd hd hP]

/-- The logarithmic companion costs at most the logarithm of the
selected factor, independently of the head divisor. -/
theorem zetaMultipleLogOffset_le_log_factor {d P : ℕ} (hd : 0 < d) (hP : 0 < P) :
    zetaMultipleLogOffset d P ≤ Real.log P := by
  rw [zetaMultipleLogOffset_eq_log_factor_sub_gcd hd hP]
  linarith [Real.log_natCast_nonneg (Nat.gcd d P)]

/-- Both actual signed multipliers retain the selected factor's
inverse-square-root weight and its full common-divisor correction. -/
theorem norm_zetaMoebiusMultipleMultipliers_le_lcm (D : ℕ) {P : ℕ} (hP : 0 < P)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖zetaMoebiusMultipleDerivativeMultiplier D P s‖ ≤ 2 * Real.sqrt D * lcmSqrtFactorMass P ∧
      ‖zetaMoebiusMultipleValueMultiplier D P s‖ ≤
        2 * Real.sqrt D * lcmSqrtFactorMass P * Real.log P := by
  have hm (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hpoint (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      ‖(μ d : ℂ) * zetaPrimeFeature s (Nat.lcm d P)‖ ≤ 1 / Real.sqrt (Nat.lcm d P) := by
    rw [norm_mul]
    exact (mul_le_mul (hm d)
      (norm_zetaPrimeFeature_le_inv_sqrt hs (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 hP))
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  constructor
  · rw [zetaMoebiusMultipleDerivativeMultiplier, norm_neg]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hpoint).trans (sum_Icc_inv_sqrt_lcm_le D hP))
  · rw [zetaMoebiusMultipleValueMultiplier, norm_neg]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 D, (1 / Real.sqrt (Nat.lcm d P)) * Real.log P := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 := (Finset.mem_Icc.mp hd).1
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (zetaMultipleLogOffset_bounds hd0 hP).1]
        exact mul_le_mul (hpoint d hd) (zetaMultipleLogOffset_le_log_factor hd0 hP)
          (zetaMultipleLogOffset_bounds hd0 hP).1 (by positivity)
      _ = (∑ d ∈ Finset.Icc 1 D, 1 / Real.sqrt (Nat.lcm d P)) * Real.log P := by
        rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_Icc_inv_sqrt_lcm_le D hP)
        (Real.log_natCast_nonneg P)

/-- The better of the established uniform cost and the joint
divisor-factor cost; the full signed response itself is unchanged. -/
def zetaMoebiusLcmCost (P : ℕ) : ℝ :=
  min 3 ((1 + Real.log P) * lcmSqrtFactorMass P)

/-- Both independently proved branches of the factor cost are nonnegative. -/
theorem zetaMoebiusLcmCost_nonneg (P : ℕ) : 0 ≤ zetaMoebiusLcmCost P := by
  unfold zetaMoebiusLcmCost
  exact le_min (by norm_num) (mul_nonneg (by linarith [Real.log_natCast_nonneg P])
    (lcmSqrtFactorMass_nonneg P))

/-- Keeping the selected factor can never worsen the uniform cost. -/
theorem zetaMoebiusLcmCost_le_three (P : ℕ) : zetaMoebiusLcmCost P ≤ 3 := min_le_left _ _

/-- All distinct-prime factors have a decaying explicit size weight;
the logarithmic companion and all divisor corrections are included. -/
theorem zetaMoebiusLcmCost_two_primes_le {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    zetaMoebiusLcmCost (p * q) ≤
      4 * (1 + Real.log (p * q : ℕ)) / Real.sqrt (p * q : ℕ) := by
  apply (min_le_right _ _).trans
  exact (mul_le_mul_of_nonneg_left (lcmSqrtFactorMass_two_primes_le hp hq hpq)
    (by linarith [Real.log_natCast_nonneg (p * q)])).trans_eq (by ring)

/-- The genuine filtered response has the factor-sensitive bound at
every moment order, with no loss from differentiation of a large factor. -/
theorem exists_zetaMoebiusMultipleFilter_lcm_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D P N : ℕ), 0 < P →
      ‖zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)‖ ≤
        C * Real.sqrt D * zetaMoebiusLcmCost P * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_filter_bound y hy
  refine ⟨2 * C, by positivity, ?_⟩
  intro p D P N hP
  obtain ⟨hf, hg⟩ := differentiable_zetaMoebiusMultipleMultipliers D P
  have hA : 0 ≤ 2 * Real.sqrt D * lcmSqrtFactorMass P :=
    mul_nonneg (by positivity) (lcmSqrtFactorMass_nonneg P)
  have hnew := hb _ _ hf hg (2 * Real.sqrt D * lcmSqrtFactorMass P)
    (2 * Real.sqrt D * lcmSqrtFactorMass P * Real.log P)
    hA (mul_nonneg hA (Real.log_natCast_nonneg P))
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_lcm D hP hs).1)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_lcm D hP hs).2) p N
  have hold := hb _ _ hf hg (2 * Real.sqrt D) (4 * Real.sqrt D) (by positivity) (by positivity)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_sqrt D hP hs).1)
    (fun s hs ↦ (norm_zetaMoebiusMultipleMultipliers_le_sqrt D hP hs).2) p N
  unfold zetaMoebiusLcmCost
  rw [min_def]
  split_ifs
  · exact hold.trans_eq (by ring)
  · exact hnew.trans_eq (by ring)

/-- Every actual finite complex factor family is controlled by its
weighted factor mass, with arbitrary overlaps, sizes and valuations.
This is an independent bound on the genuine convergent arithmetic sum. -/
theorem exists_zetaMoebiusMultipleFamily_lcm_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      ‖∑ P ∈ S, w P * ∑' n, zetaMoebiusMultipleCoefficient D P n *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
        C * Real.sqrt D * (∑ k ∈ p.support, ‖p.coeff k‖) *
          ∑ P ∈ S, ‖w P‖ * zetaMoebiusLcmCost P := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_lcm_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p D N S w hS
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ S, ‖w P‖ *
        (C * Real.sqrt D * zetaMoebiusLcmCost P * ∑ k ∈ p.support, ‖p.coeff k‖) := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hP0, hP1, hmix⟩ := hS P hP
      rw [(hasSum_zetaMoebiusMultipleFilter p D N hP0 hP1 hmix (by norm_num)).tsum_eq, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb p D P N hP0) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      ring

/-- Every selected factor beyond the squared divisor cutoff removes
the former square-root cutoff growth from the complete filtered response.
Only the selected factor's logarithmic companion remains. -/
theorem exists_zetaMoebiusMultipleFilter_large_factor_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D P N : ℕ), 0 < P → D ^ 2 ≤ P →
      ‖zetaMoebiusMultipleFilter p D P N (3 / 2 + I * y)‖ ≤
        C * (1 + Real.log P) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_lcm_bound y hy
  refine ⟨4 * C, by positivity, ?_⟩
  intro p D P N hP hlarge
  apply (hb p D P N hP).trans
  calc
    _ ≤ C * Real.sqrt D * ((1 + Real.log P) * lcmSqrtFactorMass P) *
        ∑ k ∈ p.support, ‖p.coeff k‖ := by
      gcongr
      exact min_le_right _ _
    _ = C * (Real.sqrt D * lcmSqrtFactorMass P) * (1 + Real.log P) *
        ∑ k ∈ p.support, ‖p.coeff k‖ := by ring
    _ ≤ C * 4 * (1 + Real.log P) * ∑ k ∈ p.support, ‖p.coeff k‖ := by
      gcongr
      exact sqrt_mul_lcmSqrtFactorMass_le_four hP hlarge
    _ = _ := by ring

end
end RiemannGaussian
