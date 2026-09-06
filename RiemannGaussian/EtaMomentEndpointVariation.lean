import RiemannGaussian.EtaMomentCenterTransport

/-!
# Quantitative variation of the actual moment endpoint polynomial

The complete integration-by-parts polynomial is kept at the moving center.
Its central value and a uniform displacement bound are evaluated explicitly.
The same normalized tail moments have cutoff-independent upper bounds from
their already checked quantitative Euler remainders.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The exact moment endpoint value at its own center. -/
def pairedEtaMomentEndpointCentralValue (k : ℕ) (s : ℂ) : ℂ :=
  pairedEtaCenteredMomentEndpointPolynomial k s 0 0

/-- The original polynomial depends on the full endpoint-center displacement. -/
theorem pairedEtaCenteredMomentEndpointPolynomial_eq_displacement
    (k : ℕ) (s : ℂ) (a t : ℝ) :
    pairedEtaCenteredMomentEndpointPolynomial k s a t =
      pairedEtaCenteredMomentEndpointPolynomial k s 0 (t - a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pairedEtaCenteredMomentEndpointPolynomial, sub_zero, ih]

/-- The central endpoint value is the exact factorial inverse-frequency coefficient. -/
theorem pairedEtaMomentEndpointCentralValue_eq (k : ℕ) {s : ℂ} (hs : s ≠ 0) :
    pairedEtaMomentEndpointCentralValue k s = (k.factorial : ℂ) * (s ^ (k + 1))⁻¹ := by
  induction k with
  | zero => simp [pairedEtaMomentEndpointCentralValue, pairedEtaCenteredMomentEndpointPolynomial]
  | succ k ih =>
    change pairedEtaCenteredMomentEndpointPolynomial (k + 1) s 0 0 = _
    rw [pairedEtaCenteredMomentEndpointPolynomial]
    simp only [sub_self, Complex.ofReal_zero]
    change (0 : ℂ) ^ (k + 1) / s + ((k + 1 : ℕ) : ℂ) / s *
      pairedEtaMomentEndpointCentralValue k s = _
    rw [zero_pow (by omega), zero_div, zero_add, ih, Nat.factorial_succ, Nat.cast_mul,
      pow_succ s (k + 1)]
    field_simp

/-- An explicit displacement coefficient for the original endpoint polynomial. -/
def pairedEtaMomentEndpointVariation (s : ℂ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, R => R ^ k / ‖s‖ +
      ((k + 1 : ℕ) : ℝ) / ‖s‖ * pairedEtaMomentEndpointVariation s k R

/-- The endpoint displacement coefficient is nonnegative on every nonnegative radius. -/
theorem pairedEtaMomentEndpointVariation_nonneg (s : ℂ) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ pairedEtaMomentEndpointVariation s k R := by
  induction k with
  | zero => rfl
  | succ k ih => unfold pairedEtaMomentEndpointVariation; positivity

/-- The exact moving endpoint polynomial differs from its central value
by at most the explicit variation coefficient times its displacement. -/
theorem norm_pairedEtaMomentEndpoint_sub_central_le (s : ℂ) (k : ℕ)
    {a t R : ℝ} (ht : |t - a| ≤ R) :
    ‖pairedEtaCenteredMomentEndpointPolynomial k s a t - pairedEtaMomentEndpointCentralValue k s‖ ≤
      pairedEtaMomentEndpointVariation s k R * |t - a| := by
  induction k with
  | zero => simp [pairedEtaCenteredMomentEndpointPolynomial, pairedEtaMomentEndpointCentralValue,
      pairedEtaMomentEndpointVariation]
  | succ k ih =>
    have heq : pairedEtaCenteredMomentEndpointPolynomial (k + 1) s a t -
        pairedEtaMomentEndpointCentralValue (k + 1) s =
        ((t - a : ℝ) : ℂ) ^ (k + 1) / s + ((k + 1 : ℕ) : ℂ) / s *
          (pairedEtaCenteredMomentEndpointPolynomial k s a t - pairedEtaMomentEndpointCentralValue k s) := by
      unfold pairedEtaMomentEndpointCentralValue
      rw [pairedEtaCenteredMomentEndpointPolynomial, pairedEtaCenteredMomentEndpointPolynomial]
      simp only [sub_self, Complex.ofReal_zero, zero_pow (by omega : k + 1 ≠ 0), zero_div, zero_add]
      ring
    rw [heq, pairedEtaMomentEndpointVariation]
    apply (norm_add_le _ _).trans
    simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_natCast]
    have hp : |t - a| ^ (k + 1) ≤ R ^ k * |t - a| := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ht k) (abs_nonneg _)
    have h := add_le_add (div_le_div_of_nonneg_right hp (norm_nonneg s))
      (mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ) / ‖s‖))
    convert h using 1
    ring

/-- The shifted-tail constant includes its exact central Euler value and remainder budget. -/
def pairedEtaShiftedMomentUniformConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  ‖pairedEtaCurrentEulerMomentValue rho k‖ + pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1

/-- The quantitative shifted-tail Euler remainder coefficient is nonnegative. -/
theorem pairedEtaCenteredTailQuantitativeAsymptoticConstant_nonneg
    (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 := by
  have h := NontrivialZetaZero.zero_lt_re rho
  unfold pairedEtaCenteredTailQuantitativeAsymptoticConstant
  positivity

/-- The cutoff-independent shifted-moment coefficient is nonnegative. -/
theorem pairedEtaShiftedMomentUniformConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaShiftedMomentUniformConstant rho k := by
  exact add_nonneg (norm_nonneg _) (pairedEtaCenteredTailQuantitativeAsymptoticConstant_nonneg rho k)

/-- The literal shifted tail has a uniform bound with its complete
moment order and actual complex zero parameter retained. -/
theorem norm_pairedEtaShiftedMoment_le_uniform (rho : NontrivialZetaZero) (k N : ℕ) :
    ‖pairedEtaShiftedLogTailLaplaceMoment k rho.1 N‖ ≤ pairedEtaShiftedMomentUniformConstant rho k := by
  have hq : (1 : ℝ) ≤ (2 * N + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * N + 1 by omega)
  have hi : ((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg_one]
    exact inv_le_one_of_one_le₀ hq
  have he := (norm_pairedEtaShiftedLogTailLaplaceMoment_sub_asymptoticValue_le k
    (NontrivialZetaZero.zero_lt_re rho) N).trans
      (mul_le_mul_of_nonneg_left hi (pairedEtaCenteredTailQuantitativeAsymptoticConstant_nonneg rho k))
  apply (norm_le_insert' _ (pairedEtaCurrentEulerMomentValue rho k)).trans
  exact add_le_add le_rfl (by simpa only [pairedEtaCurrentEulerMomentValue, mul_one] using he)

/-- The Euler value is exactly half the original central endpoint polynomial. -/
theorem pairedEtaCurrentEulerMomentValue_eq_central (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaCurrentEulerMomentValue rho k = pairedEtaMomentEndpointCentralValue k rho.1 / 2 := by
  rw [pairedEtaMomentEndpointCentralValue_eq k (NontrivialZetaZero.coe_ne_zero rho)]
  rfl

end

end RiemannGaussian
