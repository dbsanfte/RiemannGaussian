import RiemannGaussian.EtaMoebiusGrowingFamily

/-!
# Growing-family bounds with both completed reflection channels

The original signed pair orientation is applied to the actual two completed
divisor families. Exact complex identities retain every cross-column term.
Only downstream is its first absolute average bounded by the two proved
family mean squares. The cubic truncation remains essential; this zeroth-order
estimate does not assert the original inverse-weighted current bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The repository's signed completed pair on the two literal summed
endpoint families, with the reflected zero channel in its original position. -/
def pairedEtaSignedCompletedMoebiusFamilyPair (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCompletedMoebiusEndpointFamily (NontrivialZetaZero.conjugatePartner rho) M D)
    (pairedEtaCompletedMoebiusEndpointFamily (NontrivialZetaZero.conjugatePartner rho) M D)
    (pairedEtaCompletedMoebiusEndpointFamily rho M D)
    (pairedEtaCompletedMoebiusEndpointFamily rho M D)

/-- The signed family retains all four positions in every double divisor
entry; no reflected coefficient or cross-column interaction is omitted. -/
theorem pairedEtaSignedCompletedMoebiusFamilyPair_eq_double_sum
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaSignedCompletedMoebiusFamilyPair rho M D =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, etaSignedCompletedPair
        (pairedEtaCompletedMoebiusEndpointPhase (NontrivialZetaZero.conjugatePartner rho) M d)
        (pairedEtaCompletedMoebiusEndpointPhase (NontrivialZetaZero.conjugatePartner rho) M e)
        (pairedEtaCompletedMoebiusEndpointPhase rho M d)
        (pairedEtaCompletedMoebiusEndpointPhase rho M e) := by
  simp only [pairedEtaSignedCompletedMoebiusFamilyPair, pairedEtaCompletedMoebiusEndpointFamily,
    etaSignedCompletedPair, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.sum_comm]

/-- The signed self-pair is the exact difference of the two completed
family squares, preserving their orientation before any absolute value. -/
theorem pairedEtaSignedCompletedMoebiusFamilyPair_eq_channels
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaSignedCompletedMoebiusFamilyPair rho M D =
      ((‖pairedEtaCompletedMoebiusEndpointFamily (NontrivialZetaZero.conjugatePartner rho) M D‖ ^ 2 -
        ‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ^ 2 : ℝ) : ℂ) := by
  simp only [pairedEtaSignedCompletedMoebiusFamilyPair, etaSignedCompletedPair,
    Complex.mul_conj', Complex.conj_mul', Complex.ofReal_sub, Complex.ofReal_pow]

/-- Averaging preserves the exact signed difference of the two actual
family mean squares with the same physical window and divisor cutoff. -/
theorem pairedEtaSignedCompletedMoebiusFamilyPair_average_eq_channels
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    (∑ r ∈ Finset.range L, pairedEtaSignedCompletedMoebiusFamilyPair rho (A + r) D) / (L : ℂ) =
      ((pairedEtaCompletedMoebiusFamilyMeanSquare (NontrivialZetaZero.conjugatePartner rho) A L D -
        pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D : ℝ) : ℂ) := by
  simp_rw [pairedEtaSignedCompletedMoebiusFamilyPair_eq_channels]
  unfold pairedEtaCompletedMoebiusFamilyMeanSquare
  push_cast
  rw [Finset.sum_sub_distrib, sub_div]

/-- The signed completed family pair has absolute value at most the sum
of its two actual family squares; phase cancellation within each family
has already been retained in those squares. -/
theorem norm_pairedEtaSignedCompletedMoebiusFamilyPair_le
    (rho : NontrivialZetaZero) (M D : ℕ) :
    ‖pairedEtaSignedCompletedMoebiusFamilyPair rho M D‖ ≤
      ‖pairedEtaCompletedMoebiusEndpointFamily (NontrivialZetaZero.conjugatePartner rho) M D‖ ^ 2 +
        ‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ^ 2 := by
  rw [pairedEtaSignedCompletedMoebiusFamilyPair_eq_channels, Complex.norm_real, Real.norm_eq_abs]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]

/-- The finite first absolute average of the actual signed family pair. -/
def pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ r ∈ Finset.range L, ‖pairedEtaSignedCompletedMoebiusFamilyPair rho (A + r) D‖) / L

/-- The signed family's first absolute average is controlled by the two
actual mean squares, with identical divisor cutoffs and physical windows. -/
theorem pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute_le_channels
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute rho A L D ≤
      pairedEtaCompletedMoebiusFamilyMeanSquare (NontrivialZetaZero.conjugatePartner rho) A L D +
        pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D := by
  unfold pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute pairedEtaCompletedMoebiusFamilyMeanSquare
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  apply Finset.sum_le_sum
  intro r hr
  exact norm_pairedEtaSignedCompletedMoebiusFamilyPair_le rho (A + r) D

/-- Both actual completion channels have a growing-family first absolute
bound in the explicit cubic range. No critical-line or simple-zero
hypothesis is assumed, and every physical normalization is retained. -/
theorem pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute_le_growing
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 3 ≤ A) (hDL : D ^ 3 ≤ L) :
    pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute rho A L D ≤
      (pairedEtaCompletedMoebiusFamilyBoundConstant (NontrivialZetaZero.conjugatePartner rho) +
        pairedEtaCompletedMoebiusFamilyBoundConstant rho) * D * (1 + Real.log D) := by
  apply (pairedEtaSignedCompletedMoebiusFamilyMeanAbsolute_le_channels rho A L D).trans
  have h := add_le_add
    (pairedEtaCompletedMoebiusFamilyMeanSquare_le_growing
      (NontrivialZetaZero.conjugatePartner rho) hD hDA hDL)
    (pairedEtaCompletedMoebiusFamilyMeanSquare_le_growing rho hD hDA hDL)
  convert h using 1
  ring

end

end RiemannGaussian
