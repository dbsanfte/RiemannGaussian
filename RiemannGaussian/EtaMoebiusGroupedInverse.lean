import RiemannGaussian.EtaOddPowerMellin

/-!
# Actual cross-cutoff cancellation after grouping inverse divisor weights

The entire top-half divisor block has divided cutoff one, so its completed
aggregate is exactly the original completion factor times the grouped odd
power sum. Its norm grows even after grouping. The complementary block
retains the opposite complex main term: together they reconstruct the
actual order-zero completed moment with a decaying error.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Every index in the top half of cutoff `4*K` has divided cutoff one. -/
theorem four_mul_div_eq_one_of_mem_top_half {K d : ℕ} (hd : d ∈ Finset.Ioc (2 * K) (4 * K)) :
    (4 * K) / d = 1 := by
  obtain ⟨hdlo, hdhi⟩ := Finset.mem_Ioc.mp hd
  have hdp : 0 < d := by omega
  have hlo : 1 ≤ (4 * K) / d := (Nat.le_div_iff_mul_le hdp).2 (by simpa using hdhi)
  have hhi : (4 * K) / d < 2 := (Nat.div_lt_iff_lt_mul hdp).2 (by omega)
  omega

/-- All top-half odd indices are exactly the arithmetic midpoints in
the grouped power sum. Their complex phases are preserved by the bijection. -/
theorem sum_odd_top_half_cpow_eq (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ d ∈ (Finset.Ioc (2 * K) (4 * K)).filter Odd, (d : ℂ) ^ (-rho.1)) =
      pairedEtaOddTopPowerSum rho K := by
  unfold pairedEtaOddTopPowerSum
  apply Finset.sum_bij (fun d _ ↦ d / 2 - K)
  · intro d hd
    obtain ⟨hdK, hdo⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdlo, hdhi⟩ := Finset.mem_Ioc.mp hdK
    have hmod := Nat.odd_iff.mp hdo
    apply Finset.mem_range.mpr
    omega
  · intro a ha b hb hab
    obtain ⟨haK, hao⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbK, hbo⟩ := Finset.mem_filter.mp hb
    obtain ⟨halo, hahi⟩ := Finset.mem_Ioc.mp haK
    obtain ⟨hblo, hbhi⟩ := Finset.mem_Ioc.mp hbK
    have hma := Nat.odd_iff.mp hao
    have hmb := Nat.odd_iff.mp hbo
    omega
  · intro k hk
    have hkK := Finset.mem_range.mp hk
    refine ⟨2 * K + 2 * k + 1, Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, Nat.odd_iff.mpr (by omega)⟩, by omega⟩
  · intro d hd
    obtain ⟨hdK, hdo⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdlo, hdhi⟩ := Finset.mem_Ioc.mp hdK
    have hmod := Nat.odd_iff.mp hdo
    congr 2
    omega

/-- The whole top-half contribution in the original completed inverse,
with all actual divisor weights retained. -/
def pairedEtaCompletedOddInverseTop (rho : NontrivialZetaZero) (K : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Ioc (2 * K) (4 * K)).filter Odd, pairedEtaCompletedOddInverseTerm rho (4 * K) d

/-- All complementary original inverse terms, including every divided
cutoff greater than one and its complex phase. -/
def pairedEtaCompletedOddInverseBottom (rho : NontrivialZetaZero) (K : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 (2 * K)).filter Odd, pairedEtaCompletedOddInverseTerm rho (4 * K) d

/-- The complete divided-cutoff-one block is the original completion
factor times its grouped complex power sum, before taking a norm. -/
theorem pairedEtaCompletedOddInverseTop_eq_powerSum (rho : NontrivialZetaZero) (K : ℕ) :
    pairedEtaCompletedOddInverseTop rho K =
      pairedEtaXiCompletionFactor rho.1 * pairedEtaOddTopPowerSum rho K := by
  rw [pairedEtaCompletedOddInverseTop, ← sum_odd_top_half_cpow_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [pairedEtaCompletedOddInverseTerm,
    four_mul_div_eq_one_of_mem_top_half (Finset.mem_filter.mp hd).1,
    pairedEtaCompletedMoebiusOddAggregate_one]
  ring

/-- The two retained inverse blocks sum exactly to the unchanged finite
completed moment at the physical paired cutoff `2*K`. -/
theorem pairedEtaCompletedOddInverseBottom_add_top (rho : NontrivialZetaZero) (K : ℕ) :
    pairedEtaCompletedOddInverseBottom rho K + pairedEtaCompletedOddInverseTop rho K =
      pairedEtaFiniteCompletedMoment rho (2 * K) 0 := by
  have hbot : ((Finset.Icc 1 (4 * K)).filter Odd).filter (fun d ↦ d ≤ 2 * K) =
      (Finset.Icc 1 (2 * K)).filter Odd := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hd1, _⟩, ho⟩, hd2⟩
      exact ⟨⟨hd1, hd2⟩, ho⟩
    · rintro ⟨⟨hd1, hd2⟩, ho⟩
      exact ⟨⟨⟨hd1, by omega⟩, ho⟩, hd2⟩
  have htop : ((Finset.Icc 1 (4 * K)).filter Odd).filter (fun d ↦ ¬ d ≤ 2 * K) =
      (Finset.Ioc (2 * K) (4 * K)).filter Odd := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_, hd4⟩, ho⟩, hd2⟩
      exact ⟨⟨by omega, hd4⟩, ho⟩
    · rintro ⟨⟨hd2, hd4⟩, ho⟩
      exact ⟨⟨⟨by omega, hd4⟩, ho⟩, by omega⟩
  have h := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 (4 * K)).filter Odd)
    (fun d ↦ d ≤ 2 * K) (pairedEtaCompletedOddInverseTerm rho (4 * K))
  rw [hbot, htop] at h
  rw [pairedEtaFiniteCompletedMoment_zero_eq_oddInverse, show 2 * (2 * K) = 4 * K by omega]
  exact h

/-- The entire actual top block has the evaluated complex Mellin main
term with an explicit decaying completion-weighted error. -/
theorem norm_pairedEtaCompletedOddInverseTop_sub_main_le (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖pairedEtaCompletedOddInverseTop rho K -
      pairedEtaXiCompletionFactor rho.1 *
        (((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho)‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ * ((‖rho.1‖ / 2) * (2 * K : ℝ) ^ (-rho.1.re)) := by
  rw [pairedEtaCompletedOddInverseTop_eq_powerSum, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_pairedEtaOddTopPowerSum_sub_main_le rho hK) (norm_nonneg _)

/-- The combined actual inverse blocks have the original zero-prefix
decay, despite the growing magnitude of the separate top block. -/
theorem norm_pairedEtaCompletedOddInverseBottom_add_top_le (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖pairedEtaCompletedOddInverseBottom rho K + pairedEtaCompletedOddInverseTop rho K‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ *
        ((‖rho.1‖ / rho.1.re + 1) * (4 * K : ℝ) ^ (-rho.1.re)) := by
  rw [pairedEtaCompletedOddInverseBottom_add_top, pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix,
    ← pairedEtaUnpairedDirichletPrefix_even, show 2 * (2 * K) = 4 * K by omega, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    norm_pairedEtaUnpairedDirichletPrefix_le rho (show 1 ≤ 4 * K by omega)

/-- The complementary divided cutoffs retain the opposite large
complex Mellin main term with a fully quantitative decaying error. -/
theorem norm_pairedEtaCompletedOddInverseBottom_add_main_le (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖pairedEtaCompletedOddInverseBottom rho K +
      pairedEtaXiCompletionFactor rho.1 *
        (((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho)‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ *
        (((‖rho.1‖ / rho.1.re + 1) * (4 * K : ℝ) ^ (-rho.1.re)) +
          (‖rho.1‖ / 2) * (2 * K : ℝ) ^ (-rho.1.re)) := by
  have htri := norm_sub_le
    (pairedEtaCompletedOddInverseBottom rho K + pairedEtaCompletedOddInverseTop rho K)
    (pairedEtaCompletedOddInverseTop rho K - pairedEtaXiCompletionFactor rho.1 *
      (((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho))
  have he : pairedEtaCompletedOddInverseBottom rho K + pairedEtaCompletedOddInverseTop rho K -
      (pairedEtaCompletedOddInverseTop rho K - pairedEtaXiCompletionFactor rho.1 *
        (((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho)) =
      pairedEtaCompletedOddInverseBottom rho K + pairedEtaXiCompletionFactor rho.1 *
        (((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho) := by ring
  rw [he] at htri
  exact (htri.trans (add_le_add (norm_pairedEtaCompletedOddInverseBottom_add_top_le rho hK)
    (norm_pairedEtaCompletedOddInverseTop_sub_main_le rho hK))).trans_eq (by ring)

/-- The actual completed top block is unbounded even after summing all
of its divisor phases. Other divided cutoffs cannot be discarded when
transferring the aggregate estimates to the original moment or current. -/
theorem pairedEtaCompletedOddInverseTop_norm_tendsto_atTop (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦ ‖pairedEtaCompletedOddInverseTop rho K‖) atTop atTop := by
  have hX : 0 < ‖pairedEtaXiCompletionFactor rho.1‖ := norm_pos_iff.mpr
    (pairedEtaXiCompletionFactor_ne_zero (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho))
  simpa only [pairedEtaCompletedOddInverseTop_eq_powerSum, norm_mul] using
    (pairedEtaOddTopPowerSum_norm_tendsto_atTop rho).const_mul_atTop hX

end

end RiemannGaussian
