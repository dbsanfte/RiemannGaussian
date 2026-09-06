import RiemannGaussian.EtaMoebiusTermBounds

/-!
# Quadratic estimates with every Möbius cross-cutoff interaction retained

The actual completed eta terms give a complex pair kernel. Its full sum
is fixed by finite inversion, whereas its positive diagonal energy has an
explicit power bound. The off-diagonal sum is retained as a complex object
before identifying its exact diagonal defect and bounding that defect.
The reflected signed pair uses the original completed-pair orientation.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The complex quadratic interaction between two literal divided-cutoff
terms, retaining both Möbius signs and both phases. -/
def pairedEtaCompletedMoebiusPairKernel (rho : NontrivialZetaZero) (M d e : ℕ) : ℂ :=
  pairedEtaCompletedMoebiusTerm rho M d * starRingEnd ℂ (pairedEtaCompletedMoebiusTerm rho M e)

/-- The positive diagonal energy of the actual completed divisor terms. -/
def pairedEtaCompletedMoebiusDiagonal (rho : NontrivialZetaZero) (M : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 M, ‖pairedEtaCompletedMoebiusTerm rho M d‖ ^ 2

/-- All interactions between distinct divisors, with their exact complex
phases. The diagonal alone cannot replace this sum. -/
def pairedEtaCompletedMoebiusOffDiagonal (rho : NontrivialZetaZero) (M : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 M, ∑ e ∈ (Finset.Icc 1 M).erase d,
    pairedEtaCompletedMoebiusPairKernel rho M d e

/-- The diagonal energy is nonnegative. -/
theorem pairedEtaCompletedMoebiusDiagonal_nonneg (rho : NontrivialZetaZero) (M : ℕ) :
    0 ≤ pairedEtaCompletedMoebiusDiagonal rho M :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- Summing every complex pair retains the square of the full signed
arithmetic aggregate before using finite Möbius inversion. -/
theorem sum_pairedEtaCompletedMoebiusPairKernel (rho : NontrivialZetaZero) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 M,
      pairedEtaCompletedMoebiusPairKernel rho M d e) =
        pairedEtaCompletedMoebiusTailAggregate rho M *
          starRingEnd ℂ (pairedEtaCompletedMoebiusTailAggregate rho M) := by
  simp only [pairedEtaCompletedMoebiusPairKernel, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul,
    sum_pairedEtaCompletedMoebiusTerm]

/-- The real diagonal energy is exactly the diagonal of the retained
complex kernel. -/
theorem sum_diagonal_pairedEtaCompletedMoebiusPairKernel (rho : NontrivialZetaZero) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, pairedEtaCompletedMoebiusPairKernel rho M d d) =
      (pairedEtaCompletedMoebiusDiagonal rho M : ℂ) := by
  simp only [pairedEtaCompletedMoebiusPairKernel, Complex.mul_conj', pairedEtaCompletedMoebiusDiagonal,
    Complex.ofReal_sum, Complex.ofReal_pow]

/-- Separating the diagonal is an exact complex finite identity; no
interaction between different cutoffs is omitted. -/
theorem pairedEtaCompletedMoebiusOffDiagonal_add_diagonal (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaCompletedMoebiusOffDiagonal rho M + (pairedEtaCompletedMoebiusDiagonal rho M : ℂ) =
      pairedEtaCompletedMoebiusTailAggregate rho M *
        starRingEnd ℂ (pairedEtaCompletedMoebiusTailAggregate rho M) := by
  rw [pairedEtaCompletedMoebiusOffDiagonal, ← sum_diagonal_pairedEtaCompletedMoebiusPairKernel,
    ← Finset.sum_add_distrib, ← sum_pairedEtaCompletedMoebiusPairKernel]
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.sum_erase_add _ _ hd

/-- The exact off-diagonal aggregate equals the nonzero source square
minus the actual diagonal energy. -/
theorem pairedEtaCompletedMoebiusOffDiagonal_eq_source_sub_diagonal
    (rho : NontrivialZetaZero) {M : ℕ} (hM : 2 ≤ M) :
    pairedEtaCompletedMoebiusOffDiagonal rho M =
      (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 : ℝ) - pairedEtaCompletedMoebiusDiagonal rho M := by
  have h := pairedEtaCompletedMoebiusOffDiagonal_add_diagonal rho M
  rw [pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM, Complex.mul_conj'] at h
  exact eq_sub_iff_add_eq.mpr (by simpa only [Complex.ofReal_pow] using h)

/-- The square-sum of all literal divisor terms has an explicit bound at
the original cutoff. This estimate is unconditional for every actual zero. -/
theorem pairedEtaCompletedMoebiusDiagonal_le (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 1 ≤ M) :
    pairedEtaCompletedMoebiusDiagonal rho M ≤
      pairedEtaCompletedMoebiusTermConstant rho ^ 2 * (M : ℝ) ^ (1 - 2 * rho.1.re) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 M,
        (pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re)) ^ 2 := by
      exact Finset.sum_le_sum (fun d hd ↦
        pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaCompletedMoebiusTerm_le rho hd) 2)
    _ = (M : ℝ) * (pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re)) ^ 2 := by
      simp
    _ = _ := by
      rw [show 1 - 2 * rho.1.re = 1 + (-rho.1.re) * 2 by ring,
        Real.rpow_add hMR, Real.rpow_one, Real.rpow_mul hMR.le, Real.rpow_two]
      ring

/-- The error in replacing the full complex off-diagonal aggregate by
the fixed source square is exactly its positive diagonal energy. -/
theorem norm_pairedEtaCompletedMoebiusOffDiagonal_sub_source (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) :
    ‖pairedEtaCompletedMoebiusOffDiagonal rho M - (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 : ℝ)‖ =
      pairedEtaCompletedMoebiusDiagonal rho M := by
  rw [pairedEtaCompletedMoebiusOffDiagonal_eq_source_sub_diagonal rho hM]
  simp only [sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pairedEtaCompletedMoebiusDiagonal_nonneg rho M)]

/-- A quantitative complex estimate for the entire off-diagonal sum,
derived only after retaining all cross-cutoff terms. -/
theorem norm_pairedEtaCompletedMoebiusOffDiagonal_sub_source_le (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) :
    ‖pairedEtaCompletedMoebiusOffDiagonal rho M - (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 : ℝ)‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho ^ 2 * (M : ℝ) ^ (1 - 2 * rho.1.re) := by
  rw [norm_pairedEtaCompletedMoebiusOffDiagonal_sub_source rho hM]
  exact pairedEtaCompletedMoebiusDiagonal_le rho (by omega)

/-- The full reflected signed pair, using the repository's original
conjugate-original orientation at every pair of divided cutoffs. -/
def pairedEtaSignedCompletedMoebiusPairKernel (rho : NontrivialZetaZero) (M d e : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCompletedMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) M d)
    (pairedEtaCompletedMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) M e)
    (pairedEtaCompletedMoebiusTerm rho M d) (pairedEtaCompletedMoebiusTerm rho M e)

/-- Both original completion channels survive the exact quadratic finite
inversion identity. This fixed aggregate still contains all off-diagonal
terms and does not bound the original current's absolute moment. -/
theorem sum_pairedEtaSignedCompletedMoebiusPairKernel (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 M,
      pairedEtaSignedCompletedMoebiusPairKernel rho M d e) =
        etaSignedCompletedPair
          (pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho))
          (pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho))
          (pairedEtaCompletedMoebiusSource rho) (pairedEtaCompletedMoebiusSource rho) := by
  simp only [pairedEtaSignedCompletedMoebiusPairKernel, etaSignedCompletedPair, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul, sum_pairedEtaCompletedMoebiusTerm,
    pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM,
    pairedEtaCompletedMoebiusTailAggregate_eq_source (NontrivialZetaZero.conjugatePartner rho) hM]

/-- The diagonal of the original signed pair is the difference of the
two actual channel energies, with neither completion channel discarded. -/
theorem sum_diagonal_pairedEtaSignedCompletedMoebiusPairKernel (rho : NontrivialZetaZero) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, pairedEtaSignedCompletedMoebiusPairKernel rho M d d) =
      ((pairedEtaCompletedMoebiusDiagonal (NontrivialZetaZero.conjugatePartner rho) M -
        pairedEtaCompletedMoebiusDiagonal rho M : ℝ) : ℂ) := by
  simp only [pairedEtaSignedCompletedMoebiusPairKernel, etaSignedCompletedPair, Finset.sum_sub_distrib,
    Complex.mul_conj', Complex.conj_mul', pairedEtaCompletedMoebiusDiagonal,
    Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_pow]

/-- The reflected signed quadratic constraint retains the entire
off-diagonal correction to the signed energy, not just the fixed source. -/
theorem sum_offDiagonal_pairedEtaSignedCompletedMoebiusPairKernel
    (rho : NontrivialZetaZero) {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, ∑ e ∈ (Finset.Icc 1 M).erase d,
      pairedEtaSignedCompletedMoebiusPairKernel rho M d e) =
        etaSignedCompletedPair
          (pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho))
          (pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho))
          (pairedEtaCompletedMoebiusSource rho) (pairedEtaCompletedMoebiusSource rho) -
            ((pairedEtaCompletedMoebiusDiagonal (NontrivialZetaZero.conjugatePartner rho) M -
              pairedEtaCompletedMoebiusDiagonal rho M : ℝ) : ℂ) := by
  apply eq_sub_iff_add_eq.mpr
  rw [← sum_diagonal_pairedEtaSignedCompletedMoebiusPairKernel, ← Finset.sum_add_distrib,
    ← sum_pairedEtaSignedCompletedMoebiusPairKernel rho hM]
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.sum_erase_add _ _ hd

/-- At a hypothetical actual zero to the right of the critical line,
the diagonal energy tends to zero with the proved negative power rate. -/
theorem pairedEtaCompletedMoebiusDiagonal_tendsto_zero_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaCompletedMoebiusDiagonal rho) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M : ℕ ↦ (M : ℝ) ^ (1 - 2 * rho.1.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * rho.1.re - 1)).comp tendsto_natCast_atTop_atTop
  have hlim := hpow.const_mul (pairedEtaCompletedMoebiusTermConstant rho ^ 2)
  simp only [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (pairedEtaCompletedMoebiusDiagonal_nonneg rho))
    ((eventually_ge_atTop 1).mono fun _ hM ↦ pairedEtaCompletedMoebiusDiagonal_le rho hM) hlim

/-- The off-diagonal terms do not disappear at a hypothetical actual
right-half-strip zero: their complete complex sum tends to the positive
source square even though the sum of squared individual norms tends to zero. -/
theorem pairedEtaCompletedMoebiusOffDiagonal_tendsto_source_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaCompletedMoebiusOffDiagonal rho) atTop
      (𝓝 ((‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 : ℝ) : ℂ)) := by
  have hdiag : Tendsto (fun M ↦ (pairedEtaCompletedMoebiusDiagonal rho M : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp
      (pairedEtaCompletedMoebiusDiagonal_tendsto_zero_of_half_lt_re rho hrho)
  have hlim := hdiag.const_sub ((‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 : ℝ) : ℂ)
  simp only [sub_zero] at hlim
  exact hlim.congr' ((eventually_ge_atTop 2).mono fun _ hM ↦
    (pairedEtaCompletedMoebiusOffDiagonal_eq_source_sub_diagonal rho hM).symm)

/-- A concrete positive amount of cross-cutoff correlation must survive
eventually at a hypothetical actual right-half-strip zero. Thus dropping
these interactions is incompatible with the actual arithmetic identities. -/
theorem pairedEtaCompletedMoebiusOffDiagonal_re_lower_eventually
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    ∀ᶠ M : ℕ in atTop, ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 / 2 ≤
      (pairedEtaCompletedMoebiusOffDiagonal rho M).re := by
  have hsource : 0 < ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (pairedEtaCompletedMoebiusSource_ne_zero rho)) 2
  have hlim : Tendsto (fun M ↦ (pairedEtaCompletedMoebiusOffDiagonal rho M).re) atTop
      (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.tendsto _).comp
        (pairedEtaCompletedMoebiusOffDiagonal_tendsto_source_of_half_lt_re rho hrho)
  exact ((tendsto_order.1 hlim).1 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 / 2)
    (by linarith)).mono fun _ hM ↦ hM.le

end

end RiemannGaussian
