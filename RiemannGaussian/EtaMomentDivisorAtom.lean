import RiemannGaussian.EtaMomentPhysicalReduction

/-!
# The completed moment atom in each actual inverse product

The Möbius sign belongs to the inner divisor, not to the product of
the inner and outer divisors. The atom below therefore retains the
original completed prefix and full product power while its exact
signed coefficient is kept separately. Identities connect it both to
the original forward term and to each original inverse cell.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The unchanged completed prefix at a product divisor, with its
arithmetic coefficient retained separately from its complex power. -/
def pairedEtaMomentDivisorAtom (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M d : ℕ) : ℂ :=
  (d : ℂ) ^ (-rho.1) * (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d)

/-- The original forward moment term is exactly its Möbius sign
times the completed atom, with no division by a possibly zero sign. -/
theorem pairedEtaCompletedMomentMoebiusTerm_eq_atom
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M d : ℕ) :
    pairedEtaCompletedMomentMoebiusTerm rho k a M d =
      (μ d : ℂ) * pairedEtaMomentDivisorAtom rho k a M d := by
  unfold pairedEtaCompletedMomentMoebiusTerm pairedEtaMomentDivisorAtom
  ring

/-- One actual inverse cell has its inner Möbius coefficient at
the exact product divisor; both center translations and complex
powers combine before any norm is taken. -/
theorem pairedEtaMomentInverseCell_eq_atom
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ)
    {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (d : ℂ) ^ (-rho.1) * pairedEtaCompletedMomentMoebiusTerm rho k
      (a - Real.log d) (M / d) e =
        (μ e : ℂ) * pairedEtaMomentDivisorAtom rho k a M (d * e) := by
  unfold pairedEtaCompletedMomentMoebiusTerm pairedEtaMomentDivisorAtom
  rw [Nat.div_div_eq_div_mul, Nat.cast_mul, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow,
    Real.log_mul (by positivity : (d : ℝ) ≠ 0) (by positivity : (e : ℝ) ≠ 0)]
  rw [show a - Real.log d - Real.log e = a - (Real.log d + Real.log e) by ring]
  ring

/-- The complete complex parity amplitude at the actual moment order. -/
def pairedEtaMomentDivisorAmplitude (rho : NontrivialZetaZero) (k : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 * pairedEtaMomentParityCoefficient rho k / 2

/-- The atom retains its own literal divided odd-endpoint power. -/
def pairedEtaMomentDivisorEndpointAtom (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M d : ℕ) : ℂ :=
  ((d * pairedEtaUnpairedOddEndpoint (M / d) : ℕ) : ℂ) ^ rho.1 *
    pairedEtaMomentDivisorAtom rho k a M d

/-- Exact matching complex powers recover the literal normalized
prefix inside the completed atom. -/
theorem pairedEtaMomentDivisorEndpointAtom_eq_prefix
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ)
    {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaMomentDivisorEndpointAtom rho k a M d =
      (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
          pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d)) := by
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hc : (d : ℂ) ^ rho.1 * (d : ℂ) ^ (-rho.1) = 1 := by
    rw [← Complex.cpow_add _ _ hdne, add_neg_cancel, Complex.cpow_zero]
  rw [pairedEtaMomentDivisorEndpointAtom, pairedEtaMomentDivisorAtom,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  linear_combination ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
    ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
      pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d))) * hc

/-- The exact atom error keeps its completed Euler remainder and
the original quotient parity with their full complex amplitude. -/
theorem pairedEtaMomentDivisorEndpointAtom_sub_parity
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ)
    {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaMomentDivisorEndpointAtom rho k a M d -
        pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ) =
      (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        ((pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
            pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d) -
          (pairedEtaDirichletSign (M / d) : ℂ) * pairedEtaMomentEndpointCentralValue k rho.1 / 2) := by
  rw [pairedEtaMomentDivisorEndpointAtom_eq_prefix rho k a M hd]
  unfold pairedEtaMomentDivisorAmplitude pairedEtaMomentParityCoefficient
  ring

/-- Every completed atom below the actual zero multiplicity has
the proved quotient phase with an explicit divisor-over-cutoff error.
Its coefficient need not be the Möbius value of the product divisor. -/
theorem norm_pairedEtaMomentDivisorEndpointAtom_sub_parity_le
    (rho : NontrivialZetaZero) {k M d : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hd : d ∈ Finset.Icc 1 M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖pairedEtaMomentDivisorEndpointAtom rho k a M d -
        pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)‖ ≤
      pairedEtaCompletedMomentPhaseErrorConstant rho k * d / M := by
  have hdp := (Finset.mem_Icc.mp hd).1
  have hM : 1 ≤ M := hdp.trans (Finset.mem_Icc.mp hd).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ := abs_log_divisor_endpoint_sub_center_le hd ha
  have hδ4 : |Real.log (pairedEtaUnpairedOddEndpoint (M / d) : ℝ) - (a - Real.log d)| ≤ 4 := by
    apply hδ.trans
    apply (div_le_iff₀ hMR).mpr
    have hh : (d : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    nlinarith
  have hC := pairedEtaCenteredTailQuantitativeAsymptoticConstant_nonneg rho k
  have hB : 0 ≤ pairedEtaMomentCenterLowerBound rho k 4 + pairedEtaMomentEndpointVariation rho.1 k 4 :=
    add_nonneg (pairedEtaMomentCenterLowerBound_nonneg rho k (by norm_num))
      (pairedEtaMomentEndpointVariation_nonneg rho.1 k (by norm_num))
  have hraw := norm_pairedEtaUnpairedMoment_endpoint_sub_parity_le rho hk
    (a - Real.log d) (M / d) hδ4
  have hfirst := mul_le_mul_of_nonneg_left (inv_pairedEtaUnpairedOddEndpoint_div_le hM hdp) hC
  have hsecond := mul_le_mul_of_nonneg_left hδ hB
  have herr : ‖(pairedEtaUnpairedOddEndpoint (M / d) : ℂ) ^ rho.1 *
        pairedEtaUnpairedCenteredMomentPrefix k rho.1 (a - Real.log d) (M / d) -
      (pairedEtaDirichletSign (M / d) : ℂ) * pairedEtaMomentEndpointCentralValue k rho.1 / 2‖ ≤
      (2 * pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 +
        4 * (pairedEtaMomentCenterLowerBound rho k 4 + pairedEtaMomentEndpointVariation rho.1 k 4)) *
          (d : ℝ) / M := by
    apply hraw.trans
    have h := add_le_add hfirst hsecond
    simp only [mul_one_div] at h
    convert h using 1
    ring
  rw [pairedEtaMomentDivisorEndpointAtom_sub_parity rho k a M hdp, norm_mul]
  have h := mul_le_mul_of_nonneg_left herr (norm_nonneg (pairedEtaXiCompletionFactor rho.1 * rho.1))
  simpa only [pairedEtaCompletedMomentPhaseErrorConstant, mul_div_assoc, mul_assoc] using h

end

end RiemannGaussian
