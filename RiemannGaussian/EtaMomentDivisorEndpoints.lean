import RiemannGaussian.EtaMoebiusParityInverse
import RiemannGaussian.EtaEnergyFiniteWindowArithmeticCorrelation

/-!
# Center translations and bounds for the actual eta moment endpoints

The existing interval antiderivative retains all lower-order terms. This
module proves its translation under divisor rescaling and an explicit
polynomial norm bound. The unpaired endpoint prefix below extends the
original finite centered moment to every integer cutoff, including the
odd endpoint required by finite divisor inversion.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Divisor rescaling translates the center of the entire endpoint
polynomial, including every integration-by-parts term. -/
theorem pairedEtaCenteredMomentEndpointPolynomial_translate
    (k : ℕ) (s : ℂ) (a t h : ℝ) :
    pairedEtaCenteredMomentEndpointPolynomial k s (a - h) t =
      pairedEtaCenteredMomentEndpointPolynomial k s a (t + h) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pairedEtaCenteredMomentEndpointPolynomial, ih,
      show t - (a - h) = t + h - a by ring]

/-- An explicit polynomial envelope for the existing moment endpoint
antiderivative, with every inverse-frequency coefficient retained. -/
def pairedEtaMomentEndpointBound (s : ℂ) : ℕ → ℝ → ℝ
  | 0, _ => ‖s‖⁻¹
  | k + 1, R => R ^ (k + 1) / ‖s‖ +
      ((k + 1 : ℕ) : ℝ) / ‖s‖ * pairedEtaMomentEndpointBound s k R

/-- The endpoint envelope is nonnegative at every nonnegative radius. -/
theorem pairedEtaMomentEndpointBound_nonneg (s : ℂ) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ pairedEtaMomentEndpointBound s k R := by
  induction k with
  | zero => exact inv_nonneg.mpr (norm_nonneg s)
  | succ k ih =>
    unfold pairedEtaMomentEndpointBound
    positivity

/-- Every centered endpoint polynomial obeys its explicit envelope. -/
theorem norm_pairedEtaCenteredMomentEndpointPolynomial_le (s : ℂ) (k : ℕ)
    {a t R : ℝ} (ht : |t - a| ≤ R) :
    ‖pairedEtaCenteredMomentEndpointPolynomial k s a t‖ ≤ pairedEtaMomentEndpointBound s k R := by
  induction k with
  | zero => simp [pairedEtaCenteredMomentEndpointPolynomial, pairedEtaMomentEndpointBound]
  | succ k ih =>
    rw [pairedEtaCenteredMomentEndpointPolynomial, pairedEtaMomentEndpointBound]
    calc
      _ ≤ ‖(((t - a : ℝ) : ℂ) ^ (k + 1)) / s‖ +
          ‖((k + 1 : ℕ) : ℂ) / s * pairedEtaCenteredMomentEndpointPolynomial k s a t‖ := norm_add_le _ _
      _ = |t - a| ^ (k + 1) / ‖s‖ +
          ((k + 1 : ℕ) : ℝ) / ‖s‖ * ‖pairedEtaCenteredMomentEndpointPolynomial k s a t‖ := by
        simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_div,
          Complex.norm_natCast]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ht _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ih (by positivity))

/-- The centered Laplace endpoint prefix at an arbitrary integer cutoff.
An odd last endpoint is retained with its full complex polynomial. -/
def pairedEtaUnpairedCenteredMomentPrefix (k : ℕ) (s : ℂ) (a : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, (pairedEtaDirichletSign n : ℂ) * (n : ℂ) ^ (-s) *
    pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log n)

/-- Each new endpoint adds its exact signed polynomial Dirichlet term. -/
theorem pairedEtaUnpairedCenteredMomentPrefix_succ (k : ℕ) (s : ℂ) (a : ℝ) (M : ℕ) :
    pairedEtaUnpairedCenteredMomentPrefix k s a (M + 1) =
      pairedEtaUnpairedCenteredMomentPrefix k s a M +
        (pairedEtaDirichletSign (M + 1) : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s) *
          pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log (M + 1 : ℕ)) := by
  unfold pairedEtaUnpairedCenteredMomentPrefix
  exact Finset.sum_Icc_succ_top (by omega) _

/-- At every even physical endpoint the arithmetic prefix equals the
original centered moment of the finite positive eta measure. -/
theorem pairedEtaUnpairedCenteredMomentPrefix_even (k : ℕ) {s : ℂ} (hs : s ≠ 0)
    (a : ℝ) (N : ℕ) :
    pairedEtaUnpairedCenteredMomentPrefix k s a (2 * N) =
      pairedEtaLogLaplaceMomentCenteredPartialSum k s a N := by
  rw [pairedEtaLogLaplaceMomentCenteredPartialSum_eq_sum_intervalAtoms]
  simp_rw [pairedEtaLogLaplaceCenteredMomentIntervalAtom_eq_arithmeticAtom k hs]
  induction N with
  | zero => simp [pairedEtaUnpairedCenteredMomentPrefix]
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
      pairedEtaUnpairedCenteredMomentPrefix_succ,
      pairedEtaUnpairedCenteredMomentPrefix_succ, ih, Finset.sum_range_succ]
    norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, Nat.mul_mod,
      pairedEtaLogLaplaceCenteredMomentArithmeticAtom]
    ring_nf

/-- Odd physical endpoints carry the exact unpaired polynomial term in
addition to the original finite centered moment. -/
theorem pairedEtaUnpairedCenteredMomentPrefix_odd (k : ℕ) {s : ℂ} (hs : s ≠ 0)
    (a : ℝ) (N : ℕ) :
    pairedEtaUnpairedCenteredMomentPrefix k s a (2 * N + 1) =
      pairedEtaLogLaplaceMomentCenteredPartialSum k s a N +
        (2 * N + 1 : ℂ) ^ (-s) *
          pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log (2 * N + 1)) := by
  rw [pairedEtaUnpairedCenteredMomentPrefix_succ, pairedEtaUnpairedCenteredMomentPrefix_even k hs]
  norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, Nat.mul_mod]

/-- Every divided cutoff has the literal finite eta moment and its
necessary odd endpoint correction, at the same translated center. -/
theorem pairedEtaUnpairedCenteredMomentPrefix_eq_paired_add_endpoint
    (k : ℕ) {s : ℂ} (hs : s ≠ 0) (a : ℝ) (M : ℕ) :
    pairedEtaUnpairedCenteredMomentPrefix k s a M =
      pairedEtaLogLaplaceMomentCenteredPartialSum k s a (M / 2) +
        if Odd M then (M : ℂ) ^ (-s) *
          pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log M) else 0 := by
  rcases Nat.mod_two_eq_zero_or_one M with hM | hM
  · have he : M = 2 * (M / 2) := by omega
    rw [he, pairedEtaUnpairedCenteredMomentPrefix_even k hs]
    simp [Nat.odd_iff]
  · have he : M = 2 * (M / 2) + 1 := by omega
    conv_lhs => rw [he]
    rw [pairedEtaUnpairedCenteredMomentPrefix_odd k hs,
      if_pos (Nat.odd_iff.mpr hM)]
    have hc : (2 * ((M / 2 : ℕ) : ℂ) + 1) = (M : ℂ) := by exact_mod_cast he.symm
    have hr : (2 * ((M / 2 : ℕ) : ℝ) + 1) = (M : ℝ) := by exact_mod_cast he.symm
    rw [hc, hr]

/-- Order zero specializes to the original Dirichlet prefix divided
by its nonzero Laplace parameter. -/
theorem pairedEtaUnpairedCenteredMomentPrefix_zero (s : ℂ) (a : ℝ) (M : ℕ) :
    pairedEtaUnpairedCenteredMomentPrefix 0 s a M = pairedEtaUnpairedDirichletPrefix M s / s := by
  simp only [pairedEtaUnpairedCenteredMomentPrefix, pairedEtaCenteredMomentEndpointPolynomial,
    pairedEtaUnpairedDirichletPrefix, div_eq_mul_inv, Finset.sum_mul]

/-- The two logarithmic divisor frequencies recombine into the exact
product endpoint, including the center translation. -/
theorem pairedEtaCenteredMomentEndpointPolynomial_log_mul
    (k : ℕ) (s : ℂ) (a : ℝ) {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    pairedEtaCenteredMomentEndpointPolynomial k s (a - Real.log d) (Real.log n) =
      pairedEtaCenteredMomentEndpointPolynomial k s a (Real.log (d * n : ℕ)) := by
  rw [pairedEtaCenteredMomentEndpointPolynomial_translate, Nat.cast_mul,
    Real.log_mul (by positivity : (d : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  congr 1
  ring

end

end RiemannGaussian
