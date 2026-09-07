import RiemannGaussian.EtaMomentDivisorAtomPhysical
import RiemannGaussian.FiniteInverseSquareWindow

/-!
# Physical control of the weighted original completed atoms

The entire complex weighted family and its signed parity correction are
retained exactly. Cauchy-Schwarz charges the physical error to the same
coefficient energy used by Fourier sampling, rather than a separate
absolute factorization count.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The original completed divisor atoms with a real signed product coefficient. -/
def pairedEtaWeightedMomentDivisorFamily (rho : NontrivialZetaZero) (k : ℕ)
    (w : ℕ → ℝ) (a : ℝ) (M T : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 T, (w d : ℂ) * pairedEtaMomentDivisorAtom rho k a M d

/-- The full weighted complex square retains every ordered divisor pair. -/
theorem pairedEtaWeightedMomentDivisorFamily_norm_sq_eq_pairs
    (rho : NontrivialZetaZero) (k : ℕ) (w : ℕ → ℝ) (a : ℝ) (M T : ℕ) :
    (‖pairedEtaWeightedMomentDivisorFamily rho k w a M T‖ : ℂ) ^ 2 =
      ∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
        ((w d : ℂ) * pairedEtaMomentDivisorAtom rho k a M d) *
          starRingEnd ℂ ((w e : ℂ) * pairedEtaMomentDivisorAtom rho k a M e) := by
  rw [← Complex.mul_conj']
  simp only [pairedEtaWeightedMomentDivisorFamily, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The original physical correction is the entire signed sum of the exact atom errors. -/
theorem pairedEtaWeightedMomentDivisorFamily_physical_sub_parity
    (rho : NontrivialZetaZero) (k : ℕ) (w : ℕ → ℝ) (a : ℝ) (M T : ℕ) :
    (M : ℂ) ^ rho.1 * pairedEtaWeightedMomentDivisorFamily rho k w a M T -
        pairedEtaMomentDivisorAmplitude rho k * pairedEtaWeightedDivisorParityFamily w M T =
      ∑ d ∈ Finset.Icc 1 T, (w d : ℂ) *
        ((M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M d -
          pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)) := by
  unfold pairedEtaWeightedMomentDivisorFamily pairedEtaWeightedDivisorParityFamily
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro d hd <;> ring

/-- The actual weighted normalization error has a complete coefficient-mass bound. -/
theorem norm_pairedEtaWeightedMomentDivisorFamily_physical_sub_parity_le
    (rho : NontrivialZetaZero) {k M T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (w : ℕ → ℝ) (hTM : T ≤ M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaWeightedMomentDivisorFamily rho k w a M T -
        pairedEtaMomentDivisorAmplitude rho k * pairedEtaWeightedDivisorParityFamily w M T‖ ≤
      (pairedEtaMomentDivisorAtomPhysicalConstant rho k * T / M) *
        ∑ d ∈ Finset.Icc 1 T, |w d| := by
  rw [pairedEtaWeightedMomentDivisorFamily_physical_sub_parity]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 T, |w d| *
        ‖(M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M d -
          pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_sum_le (Finset.Icc 1 T) (fun d ↦ (w d : ℂ) *
          ((M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M d -
            pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)))
    _ ≤ ∑ d ∈ Finset.Icc 1 T, |w d| *
        (pairedEtaMomentDivisorAtomPhysicalConstant rho k * T / M) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (norm_pairedEtaMomentDivisorAtom_physical_sub_parity_le rho hk
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hTM⟩) ha).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      apply mul_le_mul_of_nonneg_left _ (pairedEtaMomentDivisorAtomPhysicalConstant_nonneg rho k)
      exact_mod_cast (Finset.mem_Icc.mp hd).2
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Cauchy-Schwarz transfers the full physical error to the signed coefficient energy. -/
theorem pairedEtaWeightedMomentDivisorFamily_physical_error_sq_le
    (rho : NontrivialZetaZero) {k M T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (w : ℕ → ℝ) (hTM : T ≤ M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaWeightedMomentDivisorFamily rho k w a M T -
        pairedEtaMomentDivisorAmplitude rho k * pairedEtaWeightedDivisorParityFamily w M T‖ ^ 2 ≤
      pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * (T : ℝ) ^ 3 /
        (M : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  have hC := pairedEtaMomentDivisorAtomPhysicalConstant_nonneg rho k
  have hb := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (norm_pairedEtaWeightedMomentDivisorFamily_physical_sub_parity_le rho hk w hTM ha)
  have hc : (∑ d ∈ Finset.Icc 1 T, |w d|) ^ 2 ≤
      (∑ d ∈ Finset.Icc 1 T, w d ^ 2) * T := by
    simpa only [mul_one, sq_abs, one_pow, Finset.sum_const, nsmul_eq_mul,
      Nat.card_Icc, Nat.add_sub_cancel] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 T) (fun d ↦ |w d|) (fun _ ↦ (1 : ℝ))
  apply hb.trans
  rw [mul_pow]
  calc
    _ ≤ (pairedEtaMomentDivisorAtomPhysicalConstant rho k * T / M) ^ 2 *
        ((∑ d ∈ Finset.Icc 1 T, w d ^ 2) * T) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by ring

/-- The physical square separates full parity energy from the averaged-error coefficient. -/
theorem pairedEtaWeightedMomentDivisorFamily_physical_sq_le
    (rho : NontrivialZetaZero) {k M T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (w : ℕ → ℝ) (hTM : T ≤ M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaWeightedMomentDivisorFamily rho k w a M T‖ ^ 2 ≤
      2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
        ‖pairedEtaWeightedDivisorParityFamily w M T‖ ^ 2 +
      2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * (T : ℝ) ^ 3 /
        (M : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  let z := (M : ℂ) ^ rho.1 * pairedEtaWeightedMomentDivisorFamily rho k w a M T
  let p := pairedEtaMomentDivisorAmplitude rho k * pairedEtaWeightedDivisorParityFamily w M T
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_le_insert' z p)
  have he := pairedEtaWeightedMomentDivisorFamily_physical_error_sq_le rho hk w hTM ha
  change ‖z - p‖ ^ 2 ≤ _ at he
  have hs := sq_nonneg (‖p‖ - ‖z - p‖)
  have hp : ‖p‖ ^ 2 = ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
      ‖pairedEtaWeightedDivisorParityFamily w M T‖ ^ 2 := by dsimp [p]; rw [norm_mul, mul_pow]
  change ‖z‖ ^ 2 ≤ _
  calc
    _ ≤ 2 * ‖p‖ ^ 2 + 2 * (pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 *
        (T : ℝ) ^ 3 / (M : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2) := by nlinarith
    _ = _ := by rw [hp]; ring

end

end RiemannGaussian
