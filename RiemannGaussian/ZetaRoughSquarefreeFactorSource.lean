/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArithmeticSmallProduct
import RiemannGaussian.ZetaRoughSquarefreeFactorGeometry
import RiemannGaussian.ZetaRoughSquarefreeLocalCorrelation

/-!
# The actual source after small-product removal and factor separation

All products through the cube of the original divisor cutoff have an
independent geometric bound. The remaining original signed sum splits
exactly into integers admitting two factors beyond that cutoff and an
unbalanced sector supported on semiprimes. The full complex filter,
physical window, selected-prime exclusions and normalization are retained.
Only their coupled sum is known to carry the multiplicity source: no
independent strict bound for that sum is asserted here.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The normalized actual physical contribution through the cubic
product cutoff, including the original window mask. -/
def zetaRightHalfRoughSquarefreeSmallProduct (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ∑ n ∈ (zetaPrimeLogBand N).filter (fun n ↦ n ≤
    zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3),
      zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n

/-- The large products admitting two factors strictly beyond the
divisor cutoff. The factors need not be comparable in size. -/
def zetaRightHalfRoughSquarefreeBalancedProduct (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ∑ n ∈ (zetaPrimeLogBand N).filter (fun n ↦
    zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3 < n ∧
      zetaBalancedFactorization
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n),
      zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n

/-- The complementary large-product sector. Its nonzero original
coefficients are proved below to be exactly small-prime logarithms on
unbalanced semiprimes, without altering the complex kernel. -/
def zetaRightHalfRoughSquarefreeUnbalancedProduct (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ∑ n ∈ (zetaPrimeLogBand N).filter (fun n ↦
    zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3 < n ∧
      ¬zetaBalancedFactorization
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n),
      zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n

/-- The entire original normalized sum is the exact sum of the three
product sectors. This identity retains both complex orientations. -/
theorem zetaRightHalfRoughSquarefreeProduct_partition (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    zetaRightHalfRoughSquarefreeSmallProduct rho hrho N +
      (zetaRightHalfRoughSquarefreeBalancedProduct rho hrho N +
        zetaRightHalfRoughSquarefreeUnbalancedProduct rho hrho N) =
      ∑ n ∈ zetaPrimeLogBand N, zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n := by
  simp only [zetaRightHalfRoughSquarefreeSmallProduct, zetaRightHalfRoughSquarefreeBalancedProduct,
    zetaRightHalfRoughSquarefreeUnbalancedProduct, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n ≤ zetaMoebiusGeometricCutoff
    (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3
  · simp [hn, Nat.not_lt.mpr hn]
  · simp only [hn, not_le.mp hn, true_and, ↓reduceIte]
    split_ifs <;> simp

/-- At every hypothetical right-half zero the whole smaller-product
sector has an independent bound with the uniform rational rate `3/4`. -/
theorem norm_zetaRightHalfRoughSquarefreeSmallProduct_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    ‖zetaRightHalfRoughSquarefreeSmallProduct rho hrho N‖ ≤
      zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) * (3 / 4 : ℝ) ^ N := by
  unfold zetaRightHalfRoughSquarefreeSmallProduct
  simp only [zetaRightHalfRoughSquarefreeNormalizedSample, ← Finset.mul_sum]
  apply norm_normalized_sum_zetaArithmetic_cubic_product_le _
    (norm_zetaLogWindowCoefficient_le _ (norm_zetaRoughSquarefreeCoefficient_le _ _) N)
    _ N rho.1.im (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)
  exact fun _ hn ↦ (Finset.mem_filter.mp hn).2

/-- Smaller products vanish at the original source normalization,
without invoking any prime distribution or zero-source identity. -/
theorem tendsto_zetaRightHalfRoughSquarefreeSmallProduct (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (zetaRightHalfRoughSquarefreeSmallProduct rho hrho) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_zetaRightHalfRoughSquarefreeSmallProduct_le rho hrho)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).const_mul
        (zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho))

/-- Every nonzero coefficient in the actual unbalanced large-product
sector is an unbalanced semiprime. Both primes avoid the entire quadratic
sieve, and the surviving coefficient is the smaller prime logarithm. -/
theorem zetaRightHalfRoughSquarefreeUnbalancedProduct_support (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {N n : ℕ} (hN : 1 ≤ N)
    (hn : zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3 < n)
    (hbal : ¬zetaBalancedFactorization
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n)
    (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      q ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ∧
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N < p ∧
      zetaRightHalfPrimePatternCutoff rho N < p ∧ zetaRightHalfPrimePatternCutoff rho N < q ∧
      n = p * q ∧ n ∈ zetaLogWindow N ∧
      zetaRightHalfRoughSquarefreeWindowCoefficient rho N n = -(Real.log q : ℂ) := by
  obtain ⟨hw, _, hsf, ⟨a, b, ha, hb, hab, han, hbn⟩, hrough⟩ :=
    zetaRightHalfRoughSquarefreeWindowCoefficient_support rho hN hc
  have hcomp : ¬n.Prime := by
    intro hp
    have hea := (hp.eq_one_or_self_of_dvd a han).resolve_left ha.ne_one
    have heb := (hp.eq_one_or_self_of_dvd b hbn).resolve_left hb.ne_one
    exact hab (hea.trans heb.symm)
  have he : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n =
      zetaRoughSquarefreeCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) n := by
    simp [zetaRightHalfRoughSquarefreeWindowCoefficient, zetaLogWindowCoefficient, hw]
  have h := zetaRoughSquarefreeCoefficient_balanced_or_semiprime _
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun p hp ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N p hp).1)
    hn hsf hcomp (by rwa [he] at hc)
  obtain ⟨p, q, hp, hq, hqD, hDp, heq, hcq⟩ := h.resolve_left hbal
  refine ⟨p, q, hp, hq, hqD, hDp, ?_, ?_, heq, hw, he.trans hcq⟩
  · exact hrough p hp (heq ▸ dvd_mul_right p q)
  · exact hrough q hq (heq ▸ dvd_mul_left q p)

/-- The full multiplicity source survives on the coupled two-factor
and semiprime sectors. No cancellation between these sectors is lost. -/
theorem tendsto_zetaRightHalfRoughSquarefreeFactorSource (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ zetaRightHalfRoughSquarefreeBalancedProduct rho hrho N +
      zetaRightHalfRoughSquarefreeUnbalancedProduct rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_sum_zetaRightHalfRoughSquarefreeNormalizedSample rho hrho).sub
    (tendsto_zetaRightHalfRoughSquarefreeSmallProduct rho hrho)
  simp only [sub_zero] at h
  convert h using 1
  funext N
  rw [← zetaRightHalfRoughSquarefreeProduct_partition rho hrho N]
  ring

/-- The large-product sum is compared to the original Fourier carrier
with the complete old window errors and the new explicit geometric cost. -/
theorem norm_zetaRightHalfRoughSquarefreeFactorSource_sub_fourier_le
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) (hN : 2 ≤ N) :
    ‖(zetaRightHalfRoughSquarefreeBalancedProduct rho hrho N +
      zetaRightHalfRoughSquarefreeUnbalancedProduct rho hrho N) -
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N‖ ≤
      zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) * (3 / 4 : ℝ) ^ N +
        (zetaLogWindowError (zetaRightHalfPoleJetFilter rho hrho) N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) := by
  have he := zetaRightHalfRoughSquarefreeProduct_partition rho hrho N
  have hb := norm_sum_zetaRightHalfRoughSquarefreeNormalizedSample_sub_fourier_le rho hrho N hN
  have hs := norm_zetaRightHalfRoughSquarefreeSmallProduct_le rho hrho N
  calc
    _ = ‖-zetaRightHalfRoughSquarefreeSmallProduct rho hrho N +
        ((∑ n ∈ zetaPrimeLogBand N,
          zetaRightHalfRoughSquarefreeNormalizedSample rho hrho N n) -
            ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
              zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ := by
      rw [← he]
      congr 1
      ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hs) hb)

/-- The factor-separated sum controls the original signed reflection
with a complete explicit allowance. The real part is taken only here,
after the richer complex partition and its comparison have been proved. -/
theorem abs_zetaRightHalfRoughSquarefreeFactorSource_sub_reflection_le
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) (hN : 2 ≤ N) :
    |-(zetaRightHalfRoughSquarefreeBalancedProduct rho hrho N +
        zetaRightHalfRoughSquarefreeUnbalancedProduct rho hrho N).re / 2 -
      (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
        zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤
      (zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) * (3 / 4 : ℝ) ^ N +
        (zetaLogWindowError (zetaRightHalfPoleJetFilter rho hrho) N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)) / 2 := by
  let V := zetaRightHalfRoughSquarefreeBalancedProduct rho hrho N +
    zetaRightHalfRoughSquarefreeUnbalancedProduct rho hrho N
  let z := V - ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N
  have hz : z.re = V.re + 2 * (3 / 2 - rho.1.re) ^ (N + 1) *
      zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N := by
    dsimp [z]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul,
      zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection]
    ring
  change |-V.re / 2 - (3 / 2 - rho.1.re) ^ (N + 1) *
    zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤ _
  rw [show -V.re / 2 - (3 / 2 - rho.1.re) ^ (N + 1) *
    zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N = -z.re / 2 by rw [hz]; ring,
    abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans
    (norm_zetaRightHalfRoughSquarefreeFactorSource_sub_fourier_le rho hrho N hN)) (by norm_num)

/-- A fixed one-sided margin on a cofinal subsequence suffices for the
contradiction. This is a conditional interface: the independent arithmetic
inequality in its last hypothesis is not supplied by the source limit. -/
theorem false_of_cofinal_zetaRightHalfRoughSquarefreeFactor_bound
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∃ᶠ N in atTop, -1 + ε ≤
      (zetaRightHalfRoughSquarefreeBalancedProduct rho hrho N +
        zetaRightHalfRoughSquarefreeUnbalancedProduct rho hrho N).re) : False := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfRoughSquarefreeFactorSource rho hrho)
  have hb := ge_of_tendsto_of_frequently h hbound
  simp only [Complex.neg_re, Complex.natCast_re] at hb
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

end
end RiemannGaussian
