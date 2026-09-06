import RiemannGaussian.EtaMomentEndpointVariation

/-!
# The actual moving-center moment and its literal parity main term

Exact center transport splits the original unpaired moment into its own
centered tail, all lower shifted moments, and the odd last endpoint. Their
quantitative bounds keep one power of the center displacement. The result
is an actual-carrier phase estimate below the zero's full multiplicity.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- All lower shifted moments produced by the literal center displacement. -/
def pairedEtaMomentCenterLower (rho : NontrivialZetaZero) (k : ℕ) (δ : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, (k.choose j : ℂ) * (δ : ℂ) ^ (k - j) *
    pairedEtaShiftedLogTailLaplaceMoment j rho.1 N

/-- The explicit lower-moment displacement coefficient on a bounded radius. -/
def pairedEtaMomentCenterLowerBound (rho : NontrivialZetaZero) (k : ℕ) (R : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (k.choose j : ℝ) * R ^ (k - j - 1) *
    pairedEtaShiftedMomentUniformConstant rho j

/-- The lower-moment displacement coefficient is nonnegative. -/
theorem pairedEtaMomentCenterLowerBound_nonneg (rho : NontrivialZetaZero) (k : ℕ)
    {R : ℝ} (hR : 0 ≤ R) : 0 ≤ pairedEtaMomentCenterLowerBound rho k R := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR _))
    (pairedEtaShiftedMomentUniformConstant_nonneg rho j)

/-- Every lower shifted moment keeps one power of the exact center
displacement, with a coefficient uniform in the physical cutoff. -/
theorem norm_pairedEtaMomentCenterLower_le (rho : NontrivialZetaZero) (k N : ℕ)
    {δ R : ℝ} (hδ : |δ| ≤ R) :
    ‖pairedEtaMomentCenterLower rho k δ N‖ ≤ pairedEtaMomentCenterLowerBound rho k R * |δ| := by
  have hR : 0 ≤ R := (abs_nonneg δ).trans hδ
  unfold pairedEtaMomentCenterLower
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        ((k.choose j : ℝ) * R ^ (k - j - 1) * pairedEtaShiftedMomentUniformConstant rho j) * |δ| := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hpow : |δ| ^ (k - j) ≤ R ^ (k - j - 1) * |δ| := by
        rw [show k - j = (k - j - 1) + 1 by omega, pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hδ _) (abs_nonneg _)
      simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      have h := mul_le_mul
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) (k.choose j)))
        (norm_pairedEtaShiftedMoment_le_uniform rho j N) (norm_nonneg _)
        (by positivity : 0 ≤ (k.choose j : ℝ) * (R ^ (k - j - 1) * |δ|))
      convert h using 1
      ring
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- The complete complex moment error keeps its centered Euler error,
every lower shifted moment, and its odd endpoint displacement separately. -/
theorem pairedEtaUnpairedMoment_endpoint_sub_parity_eq
    (rho : NontrivialZetaZero) {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (a : ℝ) (M : ℕ) :
    (pairedEtaUnpairedOddEndpoint M : ℂ) ^ rho.1 *
        pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M -
      (pairedEtaDirichletSign M : ℂ) * pairedEtaMomentEndpointCentralValue k rho.1 / 2 =
      -(pairedEtaShiftedLogTailLaplaceMoment k rho.1 (M / 2) -
          pairedEtaMomentEndpointCentralValue k rho.1 / 2) -
        pairedEtaMomentCenterLower rho k (Real.log (pairedEtaUnpairedOddEndpoint M : ℝ) - a) (M / 2) +
        if Odd M then pairedEtaCenteredMomentEndpointPolynomial k rho.1 a
          (Real.log (pairedEtaUnpairedOddEndpoint M : ℝ)) - pairedEtaMomentEndpointCentralValue k rho.1
        else 0 := by
  rw [pairedEtaUnpairedCenteredMomentPrefix_endpoint_eq_shifted rho hk a M, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero]
  unfold pairedEtaMomentCenterLower
  by_cases ho : Odd M
  · rw [if_pos ho, if_pos ho]
    have hsign : pairedEtaDirichletSign M = 1 := by
      simp only [pairedEtaDirichletSign, if_neg (Nat.not_even_iff_odd.mpr ho)]
    rw [hsign, Int.cast_one]
    ring
  · rw [if_neg ho, if_neg ho]
    have hsign : pairedEtaDirichletSign M = -1 := by
      simp only [pairedEtaDirichletSign, if_pos (Nat.not_odd_iff_even.mp ho)]
    rw [hsign, Int.cast_neg, Int.cast_one]
    ring

/-- The original normalized moment has a literal parity main term
with one inverse-endpoint error and a linear center-displacement error. -/
theorem norm_pairedEtaUnpairedMoment_endpoint_sub_parity_le
    (rho : NontrivialZetaZero) {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (a : ℝ) (M : ℕ) {R : ℝ} (hδ : |Real.log (pairedEtaUnpairedOddEndpoint M : ℝ) - a| ≤ R) :
    ‖(pairedEtaUnpairedOddEndpoint M : ℂ) ^ rho.1 *
        pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M -
      (pairedEtaDirichletSign M : ℂ) * pairedEtaMomentEndpointCentralValue k rho.1 / 2‖ ≤
      pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 / pairedEtaUnpairedOddEndpoint M +
        (pairedEtaMomentCenterLowerBound rho k R + pairedEtaMomentEndpointVariation rho.1 k R) *
          |Real.log (pairedEtaUnpairedOddEndpoint M : ℝ) - a| := by
  let δ := Real.log (pairedEtaUnpairedOddEndpoint M : ℝ) - a
  have ht : ‖pairedEtaShiftedLogTailLaplaceMoment k rho.1 (M / 2) -
      pairedEtaMomentEndpointCentralValue k rho.1 / 2‖ ≤
        pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 / pairedEtaUnpairedOddEndpoint M := by
    have h := norm_pairedEtaShiftedLogTailLaplaceMoment_sub_asymptoticValue_le k
      (NontrivialZetaZero.zero_lt_re rho) (M / 2)
    rw [← pairedEtaCurrentEulerMomentValue_eq_central]
    simpa only [pairedEtaCurrentEulerMomentValue, Real.rpow_neg_one, div_eq_mul_inv,
      pairedEtaUnpairedOddEndpoint] using h
  have he : ‖if Odd M then pairedEtaCenteredMomentEndpointPolynomial k rho.1 a
        (Real.log (pairedEtaUnpairedOddEndpoint M : ℝ)) - pairedEtaMomentEndpointCentralValue k rho.1 else 0‖ ≤
      pairedEtaMomentEndpointVariation rho.1 k R * |δ| := by
    split_ifs
    · exact norm_pairedEtaMomentEndpoint_sub_central_le rho.1 k hδ
    · rw [norm_zero]
      exact mul_nonneg (pairedEtaMomentEndpointVariation_nonneg rho.1 k ((abs_nonneg _).trans hδ))
        (abs_nonneg δ)
  rw [pairedEtaUnpairedMoment_endpoint_sub_parity_eq rho hk a M]
  apply (norm_add_le _ _).trans
  have htn : ‖-(pairedEtaShiftedLogTailLaplaceMoment k rho.1 (M / 2) -
      pairedEtaMomentEndpointCentralValue k rho.1 / 2)‖ ≤
        pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 / pairedEtaUnpairedOddEndpoint M := by
    simpa only [norm_neg] using ht
  have hs := add_le_add ((norm_sub_le
    (-(pairedEtaShiftedLogTailLaplaceMoment k rho.1 (M / 2) -
      pairedEtaMomentEndpointCentralValue k rho.1 / 2)) _).trans
    (add_le_add htn
      (norm_pairedEtaMomentCenterLower_le rho k (M / 2) hδ))) he
  dsimp only [δ] at hs
  convert hs using 1
  ring

end

end RiemannGaussian
