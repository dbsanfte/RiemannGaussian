import RiemannGaussian.EtaWeightedAtomPhysical

/-!
# A mean-square operator estimate at the full physical starting range

Fourier sampling and the telescoped physical error use the same signed
coefficient energy. The product budget need only be at most the starting
cutoff; the quadratic restriction remains solely on averaging length.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The original weighted atoms averaged with their common physical power. -/
def pairedEtaWeightedMomentDivisorPhysicalMeanSquare
    (rho : NontrivialZetaZero) (k : ℕ) (w : ℕ → ℝ) (A L T : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖((A + n : ℕ) : ℂ) ^ rho.1 *
    pairedEtaWeightedMomentDivisorFamily rho k w (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) T‖ ^ 2) / L

/-- The actual unmodified weighted atom mean square at the moving logarithmic endpoint. -/
def pairedEtaWeightedMomentDivisorMeanSquare
    (rho : NontrivialZetaZero) (k : ℕ) (w : ℕ → ℝ) (A L T : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaWeightedMomentDivisorFamily rho k w
    (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) T‖ ^ 2) / L

/-- Averaging retains the full parity energy and both physical window endpoints. -/
theorem pairedEtaWeightedMomentDivisorPhysicalMeanSquare_le_parity
    (rho : NontrivialZetaZero) {k A L T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (w : ℕ → ℝ) (hA : 1 ≤ A) (hL : 0 < L) (hTA : T ≤ A) :
    pairedEtaWeightedMomentDivisorPhysicalMeanSquare rho k w A L T ≤
      2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
        ((∑ n ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / L) +
      4 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * (T : ℝ) ^ 3 /
        ((A : ℝ) * (A + L)) * ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let E := ∑ d ∈ Finset.Icc 1 T, w d ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun d _ ↦ sq_nonneg _)
  let B := 2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * (T : ℝ) ^ 3 * E
  have hB : 0 ≤ B := by dsimp [B]; positivity
  unfold pairedEtaWeightedMomentDivisorPhysicalMeanSquare
  calc
    _ ≤ (∑ n ∈ Finset.range L,
        (2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
          ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2 +
          B * (1 / ((A + n : ℕ) : ℝ) ^ 2))) / (L : ℝ) := by
      apply div_le_div_of_nonneg_right _ hLR.le
      apply Finset.sum_le_sum
      intro n hn
      have hM : (0 : ℝ) < (A + n : ℕ) := by exact_mod_cast (show 1 ≤ A + n by omega)
      convert pairedEtaWeightedMomentDivisorFamily_physical_sq_le rho hk w
        (show T ≤ A + n by omega) ⟨Real.log_le_log hM (by linarith), le_rfl⟩ using 1
      · rfl
      · dsimp [B, E]
        ring
    _ = 2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
        ((∑ n ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / L) +
      B * ((∑ n ∈ Finset.range L, 1 / ((A + n : ℕ) : ℝ) ^ 2) / L) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ 2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
        ((∑ n ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + n) T‖ ^ 2) / L) +
      B * (2 / ((A : ℝ) * (A + L))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (mean_range_inv_sq_le hA hL) hB)
    _ = _ := by dsimp [B, E]; ring

/-- The explicit operator constant retains completion, moment order, and physical error. -/
def pairedEtaWeightedMomentDivisorConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  10 * finiteCircleSamplingConstant * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 +
    4 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2

/-- The full physical operator constant is nonnegative. -/
theorem pairedEtaWeightedMomentDivisorConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaWeightedMomentDivisorConstant rho k := by
  unfold pairedEtaWeightedMomentDivisorConstant
  have h := finiteCircleSamplingConstant_pos
  positivity

/-- The actual common-power atoms have squared-logarithmic operator cost
throughout the physical product range and on quadratic averaging windows. -/
theorem pairedEtaWeightedMomentDivisorPhysicalMeanSquare_le
    (rho : NontrivialZetaZero) {k A L T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (w : ℕ → ℝ) (hT : 1 ≤ T) (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    pairedEtaWeightedMomentDivisorPhysicalMeanSquare rho k w A L T ≤
      pairedEtaWeightedMomentDivisorConstant rho k * (1 + Real.log T) ^ 2 *
        ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  have hA : 1 ≤ A := hT.trans hTA
  have hL : 0 < L := (pow_pos hT 2).trans_le hTL
  let E := ∑ d ∈ Finset.Icc 1 T, w d ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun d _ ↦ sq_nonneg _)
  have hlog : 1 ≤ (1 + Real.log T) ^ 2 := by
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith [Real.log_nonneg hTR]
  have he : 4 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * (T : ℝ) ^ 3 /
        ((A : ℝ) * (A + L)) * E ≤
      4 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * (1 + Real.log T) ^ 2 * E := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((nat_cube_div_window_le_one hT hTA hTL).trans hlog)
      (by positivity : 0 ≤ 4 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2)) hE
    simpa only [← mul_div_assoc] using h
  have hp := mul_le_mul_of_nonneg_left
    (pairedEtaWeightedDivisorParityFamily_meanSquare_le_quadratic w A hT hTL)
    (by positivity : 0 ≤ 2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2)
  apply (pairedEtaWeightedMomentDivisorPhysicalMeanSquare_le_parity rho hk w hA hL hTA).trans
  apply (add_le_add hp he).trans_eq
  unfold pairedEtaWeightedMomentDivisorConstant
  dsimp [E]
  ring

/-- The common positive physical power has its exact horizontal norm factor. -/
theorem norm_sq_eq_nat_cpow_norm_sq (rho : NontrivialZetaZero) {M : ℕ} (hM : 1 ≤ M) (z : ℂ) :
    ‖z‖ ^ 2 = (M : ℝ) ^ (-2 * rho.1.re) * ‖(M : ℂ) ^ rho.1 * z‖ ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp : ‖(M : ℂ) ^ rho.1‖ = (M : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hMR rho.1
  have hs : ((M : ℝ) ^ rho.1.re) ^ 2 = (M : ℝ) ^ (rho.1.re * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMR.le]
    norm_num
  rw [norm_mul, hp, mul_pow, hs, ← mul_assoc, ← Real.rpow_add hMR,
    show -2 * rho.1.re + rho.1.re * 2 = 0 by ring, Real.rpow_zero, one_mul]

/-- Removing the physical power retains the actual zero's horizontal decay. -/
theorem pairedEtaWeightedMomentDivisorMeanSquare_le_physical
    (rho : NontrivialZetaZero) (k : ℕ) (w : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (L T : ℕ) :
    pairedEtaWeightedMomentDivisorMeanSquare rho k w A L T ≤
      (A : ℝ) ^ (-2 * rho.1.re) * pairedEtaWeightedMomentDivisorPhysicalMeanSquare rho k w A L T := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  unfold pairedEtaWeightedMomentDivisorMeanSquare pairedEtaWeightedMomentDivisorPhysicalMeanSquare
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_sq_eq_nat_cpow_norm_sq rho (show 1 ≤ A + n by omega)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast (Nat.le_add_right A n))
    (by linarith [NontrivialZetaZero.zero_lt_re rho])

/-- The original completed weighted atoms have a mean-square bound with
all moment, physical, Fourier, and normalization hypotheses discharged. -/
theorem pairedEtaWeightedMomentDivisorMeanSquare_le
    (rho : NontrivialZetaZero) {k A L T : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (w : ℕ → ℝ) (hT : 1 ≤ T) (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    pairedEtaWeightedMomentDivisorMeanSquare rho k w A L T ≤
      pairedEtaWeightedMomentDivisorConstant rho k * (1 + Real.log T) ^ 2 *
        (∑ d ∈ Finset.Icc 1 T, w d ^ 2) * (A : ℝ) ^ (-2 * rho.1.re) := by
  apply (pairedEtaWeightedMomentDivisorMeanSquare_le_physical rho k w (hT.trans hTA) L T).trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaWeightedMomentDivisorPhysicalMeanSquare_le rho hk w hT hTA hTL)
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  convert h using 1
  ring

end

end RiemannGaussian
