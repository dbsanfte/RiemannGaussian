import RiemannGaussian.EtaMoebiusQuotientParityRecurrence

/-!
# The complete two-scale parity matrix of quotient shells

The shell-level Möbius recurrence factors the actual shell correlation
matrix through two odd-divisor channels. Both channels retain the quotient
cap selected by the original cutoff. All shell pairs and both mixed
physical-scale correlations are present in the exact complex identities.
The dyadic coefficient is small, but no bound on the full matrix is assumed.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- One odd shell at the original or halved physical scale, always with the quotient cap from the original cutoff. -/
def pairedEtaCompletedMoebiusOddScaleShell (rho : NontrivialZetaZero) (D M j : ℕ) (half : Bool) : ℂ :=
  pairedEtaCompletedMoebiusOddQuotientShell rho (M / (D + 1)) (if half then M / 2 else M) j

/-- Every original shell is exactly the difference of its two odd scale channels with the original complex dyadic multiplier. -/
theorem pairedEtaCompletedMoebiusQuotientShell_eq_scaleChannels
    (rho : NontrivialZetaZero) (D M j : ℕ) :
    pairedEtaCompletedMoebiusQuotientShell rho D M j =
      pairedEtaCompletedMoebiusOddScaleShell rho D M j false -
        (2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddScaleShell rho D M j true :=
  pairedEtaCompletedMoebiusQuotientShell_eq_odd_sub_half rho D M j

/-- The full complex correlation of two odd shell channels, retaining both shell indices and both physical-scale choices. -/
def pairedEtaCompletedMoebiusOddScaleShellCorrelation
    (rho : NontrivialZetaZero) (A L D j l : ℕ) (b c : Bool) : ℂ :=
  (∑ n ∈ Finset.range L, pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j b *
    starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l c)) / L

/-- The actual shell correlation has all four parity-matrix terms, including both complex mixed correlations; the halved channel is not treated as independent. -/
theorem pairedEtaCompletedMoebiusQuotientShellCorrelation_eq_parityMatrix
    (rho : NontrivialZetaZero) (A L D j l : ℕ) :
    pairedEtaCompletedMoebiusQuotientShellCorrelation rho A L D j l =
      pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D j l false false -
        starRingEnd ℂ ((2 : ℂ) ^ (-rho.1)) *
          pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D j l false true -
        (2 : ℂ) ^ (-rho.1) *
          pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D j l true false +
        (‖(2 : ℂ) ^ (-rho.1)‖ : ℂ) ^ 2 *
          pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D j l true true := by
  have hpoint (n : ℕ) :
      pairedEtaCompletedMoebiusQuotientShell rho D (A + n) j *
        starRingEnd ℂ (pairedEtaCompletedMoebiusQuotientShell rho D (A + n) l) =
      pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j false *
        starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l false) -
      starRingEnd ℂ ((2 : ℂ) ^ (-rho.1)) *
        (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j false *
          starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l true)) -
      (2 : ℂ) ^ (-rho.1) *
        (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j true *
          starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l false)) +
      (‖(2 : ℂ) ^ (-rho.1)‖ : ℂ) ^ 2 *
        (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j true *
          starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l true)) := by
    simp only [pairedEtaCompletedMoebiusQuotientShell_eq_scaleChannels, map_sub, map_mul,
      ← Complex.mul_conj']
    ring
  unfold pairedEtaCompletedMoebiusQuotientShellCorrelation pairedEtaCompletedMoebiusOddScaleShellCorrelation
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    add_div, sub_div, mul_div_assoc]

/-- Reversing both shell and physical-scale indices conjugates the exact odd correlation. -/
theorem pairedEtaCompletedMoebiusOddScaleShellCorrelation_conj
    (rho : NontrivialZetaZero) (A L D j l : ℕ) (b c : Bool) :
    starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D j l b c) =
      pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D l j c b := by
  simp only [pairedEtaCompletedMoebiusOddScaleShellCorrelation, map_div₀, map_sum, map_mul,
    map_natCast, starRingEnd_apply, star_star]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact mul_comm _ _

/-- A two-scale matrix entry for the entire shell family, retaining the full double sum of shell correlations. -/
def pairedEtaCompletedMoebiusOddScaleForm
    (rho : NontrivialZetaZero) (A L D J : ℕ) (b c : Bool) : ℂ :=
  ∑ j ∈ Finset.range J, ∑ l ∈ Finset.range J,
    pairedEtaCompletedMoebiusOddScaleShellCorrelation rho A L D j l b c

/-- The whole two-scale entry equals the physical average of the two complete odd-shell sums; all within-channel shell cross terms remain present. -/
theorem pairedEtaCompletedMoebiusOddScaleForm_eq_average
    (rho : NontrivialZetaZero) (A L D J : ℕ) (b c : Bool) :
    pairedEtaCompletedMoebiusOddScaleForm rho A L D J b c =
      (∑ n ∈ Finset.range L,
        (∑ j ∈ Finset.range J, pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j b) *
          starRingEnd ℂ (∑ l ∈ Finset.range J, pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l c)) / L := by
  unfold pairedEtaCompletedMoebiusOddScaleForm pairedEtaCompletedMoebiusOddScaleShellCorrelation
  simp only [← Finset.sum_div, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply congrArg (fun z : ℂ ↦ z / (L : ℂ))
  rw [Finset.sum_comm]
  calc
    _ = ∑ l ∈ Finset.range J, ∑ n ∈ Finset.range L, ∑ j ∈ Finset.range J,
        pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) j b *
          starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleShell rho D (A + n) l c) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The two mixed entries of the full shell form are exact complex conjugates. -/
theorem pairedEtaCompletedMoebiusOddScaleForm_conj
    (rho : NontrivialZetaZero) (A L D J : ℕ) (b c : Bool) :
    starRingEnd ℂ (pairedEtaCompletedMoebiusOddScaleForm rho A L D J b c) =
      pairedEtaCompletedMoebiusOddScaleForm rho A L D J c b := by
  simp only [pairedEtaCompletedMoebiusOddScaleForm, map_sum,
    pairedEtaCompletedMoebiusOddScaleShellCorrelation_conj]
  rw [Finset.sum_comm]

/-- Each diagonal entry is the nonnegative mean square of a whole odd shell channel, rather than a sum of individual shell squares. -/
theorem pairedEtaCompletedMoebiusOddScaleForm_diagonal_nonneg
    (rho : NontrivialZetaZero) (A L D J : ℕ) (b : Bool) :
    0 ≤ (pairedEtaCompletedMoebiusOddScaleForm rho A L D J b b).re := by
  rw [pairedEtaCompletedMoebiusOddScaleForm_eq_average, Complex.div_natCast_re]
  apply div_nonneg _ (Nat.cast_nonneg L)
  change 0 ≤ Complex.reAddGroupHom _
  rw [map_sum]
  apply Finset.sum_nonneg
  intro n _
  rw [Complex.mul_conj']
  simp only [← Complex.ofReal_pow]
  exact sq_nonneg _

/-- The full original complete-block energy factors through the entire two-scale odd parity matrix, with the actual moving quotient cap on both scales. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_parityMatrix
    (rho : NontrivialZetaZero) (k : ℕ) :
    (pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) : ℂ) =
      pairedEtaCompletedMoebiusOddScaleForm rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) (k + 1) false false -
      starRingEnd ℂ ((2 : ℂ) ^ (-rho.1)) *
        pairedEtaCompletedMoebiusOddScaleForm rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) (k + 1) false true -
      (2 : ℂ) ^ (-rho.1) *
        pairedEtaCompletedMoebiusOddScaleForm rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) (k + 1) true false +
      (‖(2 : ℂ) ^ (-rho.1)‖ : ℂ) ^ 2 *
        pairedEtaCompletedMoebiusOddScaleForm rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) (k + 1) true true := by
  rw [pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_shellCorrelations]
  simp only [pairedEtaCompletedMoebiusQuotientShellCorrelation_eq_parityMatrix,
    pairedEtaCompletedMoebiusOddScaleForm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]

/-- The full energy retains a single signed mixed-scale correlation after the exact Hermitian matrix identity is used. Its diagonal coefficient is the genuine dyadic power, with every shell cross term still inside the two channel energies. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_parityEnergy
    (rho : NontrivialZetaZero) (k : ℕ) :
    let G := pairedEtaCompletedMoebiusOddScaleForm rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) (k + 1)
    pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) =
      (G false false).re + (2 : ℝ) ^ (-2 * rho.1.re) * (G true true).re -
        2 * (starRingEnd ℂ ((2 : ℂ) ^ (-rho.1)) * G false true).re := by
  let a : ℂ := (2 : ℂ) ^ (-rho.1)
  let G := pairedEtaCompletedMoebiusOddScaleForm rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) (k + 1)
  change pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) =
    (G false false).re + (2 : ℝ) ^ (-2 * rho.1.re) * (G true true).re - 2 * (starRingEnd ℂ a * G false true).re
  have hconj : starRingEnd ℂ (G false true) = G true false :=
    pairedEtaCompletedMoebiusOddScaleForm_conj rho _ _ _ _ false true
  have hcross : (a * G true false).re = (starRingEnd ℂ a * G false true).re := by
    have he : a * G true false = starRingEnd ℂ (starRingEnd ℂ a * G false true) := by
      simp only [map_mul, starRingEnd_apply, star_star, ← hconj]
    rw [he, Complex.conj_re]
  have hnorm : ‖a‖ ^ 2 = (2 : ℝ) ^ (-2 * rho.1.re) := by
    have hp : ‖a‖ = (2 : ℝ) ^ (-rho.1.re) := by
      change ‖((2 : ℝ) : ℂ) ^ (-rho.1)‖ = _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
      rfl
    rw [hp, ← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h := congrArg Complex.re (pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_parityMatrix rho k)
  change pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) =
    (G false false - starRingEnd ℂ a * G false true - a * G true false + (‖a‖ : ℂ) ^ 2 * G true true).re at h
  have hdiag : (((‖a‖ ^ 2 : ℝ) : ℂ) * G true true).re = ‖a‖ ^ 2 * (G true true).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.add_re, Complex.sub_re, Complex.sub_re, hcross, ← Complex.ofReal_pow,
    hdiag, hnorm] at h
  linarith

end

end RiemannGaussian
