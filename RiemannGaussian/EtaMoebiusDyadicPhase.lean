import RiemannGaussian.EtaMoebiusEndpointPhase

/-!
# Exact dyadic cancellation of the retained completed parity phases

For an odd divisor and twice an odd divisor, a common half-period leaves
one eta parity unchanged and reverses the other. Their completed complex
pair therefore has zero sum over a full arithmetic period, at every
starting cutoff. All completion and Möbius coefficients remain present.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Adding an even integer preserves the literal eta coefficient. -/
theorem pairedEtaDirichletSign_add_even (n k : ℕ) (hk : Even k) :
    pairedEtaDirichletSign (n + k) = pairedEtaDirichletSign n := by
  have hm := Nat.even_iff.mp hk
  simp [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, hm]

/-- Adding an odd integer reverses the literal eta coefficient. -/
theorem pairedEtaDirichletSign_add_odd (n k : ℕ) (hk : Odd k) :
    pairedEtaDirichletSign (n + k) = -pairedEtaDirichletSign n := by
  have hm := Nat.odd_iff.mp hk
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, hm, hn]

/-- The odd-divisor parity phase is preserved by the common half-period. -/
theorem pairedEtaCompletedMoebiusParityPhase_halfPeriod_left
    (rho : NontrivialZetaZero) (M k : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaCompletedMoebiusParityPhase rho (M + 2 * d * k) d =
      pairedEtaCompletedMoebiusParityPhase rho M d := by
  unfold pairedEtaCompletedMoebiusParityPhase
  rw [show 2 * d * k = d * (2 * k) by ring, Nat.add_mul_div_left _ _ hd,
    pairedEtaDirichletSign_add_even _ _ (even_two_mul k)]

/-- The twice-odd-divisor parity phase reverses under the same half-period. -/
theorem pairedEtaCompletedMoebiusParityPhase_halfPeriod_right
    (rho : NontrivialZetaZero) (M : ℕ) {d k : ℕ} (hd : Odd d) (hk : 1 ≤ k) :
    pairedEtaCompletedMoebiusParityPhase rho (M + 2 * d * k) (2 * k) =
      -pairedEtaCompletedMoebiusParityPhase rho M (2 * k) := by
  unfold pairedEtaCompletedMoebiusParityPhase
  rw [show 2 * d * k = (2 * k) * d by ring, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * k),
    pairedEtaDirichletSign_add_odd _ _ hd]
  push_cast
  ring

/-- The completed leading parity interaction of two actual divisor columns. -/
def pairedEtaCompletedMoebiusParityPair (rho : NontrivialZetaZero) (M d e : ℕ) : ℂ :=
  pairedEtaCompletedMoebiusParityPhase rho M d *
    starRingEnd ℂ (pairedEtaCompletedMoebiusParityPhase rho M e)

/-- One common half-period reverses the whole complex pair, including
its completion factor and both original Möbius coefficients. -/
theorem pairedEtaCompletedMoebiusParityPair_halfPeriod
    (rho : NontrivialZetaZero) (M : ℕ) {d k : ℕ} (hd : Odd d) (hk : 1 ≤ k) :
    pairedEtaCompletedMoebiusParityPair rho (M + 2 * d * k) d (2 * k) =
      -pairedEtaCompletedMoebiusParityPair rho M d (2 * k) := by
  have hdp : 1 ≤ d := by obtain ⟨n, rfl⟩ := hd; omega
  unfold pairedEtaCompletedMoebiusParityPair
  rw [pairedEtaCompletedMoebiusParityPhase_halfPeriod_left rho M k hdp,
    pairedEtaCompletedMoebiusParityPhase_halfPeriod_right rho M hd hk, map_neg, mul_neg]

/-- The entire complex leading pair cancels on every full arithmetic
period. No averaging of its norm or deletion of a phase is used. -/
theorem sum_pairedEtaCompletedMoebiusParityPair_period_eq_zero
    (rho : NontrivialZetaZero) (A : ℕ) {d k : ℕ} (hd : Odd d) (hk : 1 ≤ k) :
    (∑ r ∈ Finset.range (4 * d * k), pairedEtaCompletedMoebiusParityPair rho (A + r) d (2 * k)) = 0 := by
  rw [show 4 * d * k = 2 * d * k + 2 * d * k by ring, Finset.sum_range_add]
  have hsum : (∑ r ∈ Finset.range (2 * d * k),
      pairedEtaCompletedMoebiusParityPair rho (A + (2 * d * k + r)) d (2 * k)) =
      -(∑ r ∈ Finset.range (2 * d * k), pairedEtaCompletedMoebiusParityPair rho (A + r) d (2 * k)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show A + (2 * d * k + r) = (A + r) + 2 * d * k by omega]
    exact pairedEtaCompletedMoebiusParityPair_halfPeriod rho (A + r) hd hk
  rw [hsum, add_neg_cancel]

end

end RiemannGaussian
