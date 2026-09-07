import RiemannGaussian.EtaTranslatedFiniteResidual

/-!
# Exact rational arithmetic for the eta translate search

Positive rational physical scales give real logarithmic translates. Their
complete finite Gram entries are rational interval lengths after the exact
change of endpoints by the negative exponential. This interface permits
coefficient candidates to be checked by kernel reduction of rational
arithmetic while retaining the original continuous residual theorem.
-/

open Complex Set

namespace RiemannGaussian

/-- A rational physical scale determines its original logarithmic translate. -/
noncomputable def pairedEtaRationalTranslate (r : ℚ) : ℝ := -Real.log (r : ℝ)

/-- Physical scales in `(0,1]` give the nonnegative translates required by the full residual bound. -/
theorem pairedEtaRationalTranslate_nonneg {r : ℚ} (hr : 0 < r) (hr1 : r ≤ 1) :
    0 ≤ pairedEtaRationalTranslate r := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos (by exact_mod_cast hr.le) (by exact_mod_cast hr1)

/-- The rational length of the complete pairwise interval intersection at the original odd endpoint. -/
def pairedEtaRationalOverlapMass (N : ℕ) (r s : ℚ) (n m : ℕ) : ℚ :=
  max 0 (min 1 (min (r / (2 * n + 1)) (s / (2 * m + 1))) -
    max (1 / (2 * (N : ℚ) + 1)) (max (r / (2 * n + 2)) (s / (2 * m + 2))))

/-- The entire finite rational Gram, including every original interval pair. -/
def pairedEtaRationalFiniteGram (N : ℕ) (r s : ℚ) : ℚ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, pairedEtaRationalOverlapMass N r s n m

/-- The negative exponential reverses a maximum into the exact minimum of physical endpoints. -/
theorem exp_neg_max_eq_min (l u : ℝ) :
    Real.exp (-max l u) = min (Real.exp (-l)) (Real.exp (-u)) := by
  by_cases h : l ≤ u
  · rw [max_eq_right h, min_eq_right (Real.exp_le_exp.mpr (neg_le_neg h))]
  · rw [max_eq_left (le_of_not_ge h), min_eq_left (Real.exp_le_exp.mpr (neg_le_neg (le_of_not_ge h)))]

/-- The negative exponential reverses a minimum into the exact maximum of physical endpoints. -/
theorem exp_neg_min_eq_max (l u : ℝ) :
    Real.exp (-min l u) = max (Real.exp (-l)) (Real.exp (-u)) := by
  by_cases h : l ≤ u
  · rw [min_eq_left h, max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h))]
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (Real.exp_le_exp.mpr (neg_le_neg (le_of_not_ge h)))]

/-- Each translated logarithmic endpoint has exactly its rational physical value. -/
theorem exp_neg_rationalTranslate_add_log {r : ℚ} (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    Real.exp (-(pairedEtaRationalTranslate r + Real.log x)) = (r : ℝ) / x := by
  rw [pairedEtaRationalTranslate, neg_add, neg_neg, Real.exp_add, Real.exp_neg,
    Real.exp_log (by exact_mod_cast hr), Real.exp_log hx, div_eq_mul_inv]

/-- The original real overlap mass is the cast of its complete rational interval computation. -/
theorem pairedEtaTranslatedOverlapMass_eq_rational {r s : ℚ} (hr : 0 < r) (hs : 0 < s)
    (N n m : ℕ) :
    pairedEtaTranslatedOverlapMass (Real.log (2 * N + 1 : ℝ))
      (pairedEtaRationalTranslate r) (pairedEtaRationalTranslate s) n m =
        (pairedEtaRationalOverlapMass N r s n m : ℝ) := by
  unfold pairedEtaTranslatedOverlapMass etaProjectionIntervalMass
  simp only [exp_neg_max_eq_min, exp_neg_min_eq_max, neg_zero, Real.exp_zero]
  rw [exp_neg_rationalTranslate_add_log hr (by positivity),
    exp_neg_rationalTranslate_add_log hs (by positivity),
    exp_neg_rationalTranslate_add_log hr (by positivity),
    exp_neg_rationalTranslate_add_log hs (by positivity),
    Real.exp_neg, Real.exp_log (by positivity : 0 < (2 * N + 1 : ℝ))]
  unfold pairedEtaRationalOverlapMass
  push_cast
  simp only [one_div]

/-- Every complete finite translate Gram entry is exactly rational for positive rational physical scales. -/
theorem pairedEtaTranslatedFiniteGram_eq_rational {r s : ℚ} (hr : 0 < r) (hs : 0 < s) (N : ℕ) :
    pairedEtaTranslatedFiniteGram N (Real.log (2 * N + 1 : ℝ))
      (pairedEtaRationalTranslate r) (pairedEtaRationalTranslate s) =
        (pairedEtaRationalFiniteGram N r s : ℝ) := by
  unfold pairedEtaTranslatedFiniteGram pairedEtaRationalFiniteGram
  simp_rw [pairedEtaTranslatedOverlapMass_eq_rational hr hs]
  push_cast
  rfl

/-- The rational quadratic part includes the full coefficient norm tail allowance. -/
def pairedEtaRationalQuadraticBudget {d : ℕ} (N : ℕ) (r c : Fin d → ℚ) : ℚ :=
  (∑ j, ∑ k, c j * c k * pairedEtaRationalFiniteGram N (r j) (r k)) +
    (∑ j, |c j|) ^ 2 / (2 * N + 1)

/-- The exact target pairing remains logarithmic after the rational Gram is evaluated. -/
theorem pairedEtaTranslatedHeadPairing_rational {r : ℚ} (hr : 0 < r) :
    pairedEtaTranslatedHeadPairing (pairedEtaRationalTranslate r) = max 0 (Real.log (2 * (r : ℝ))) := by
  rw [pairedEtaTranslatedHeadPairing, pairedEtaRationalTranslate, sub_neg_eq_add,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast ne_of_gt hr)]

/-- Rational scales and real rational coefficients retain the exact full finite budget, with every logarithmic target term and tail cost visible. -/
theorem pairedEtaTranslatedFiniteResidualBudget_eq_rational {d N : ℕ} (r c : Fin d → ℚ)
    (hr : ∀ j, 0 < r j) :
    pairedEtaTranslatedFiniteResidualBudget N (fun j ↦ pairedEtaRationalTranslate (r j))
      (fun j ↦ (c j : ℂ)) = 1 + (pairedEtaRationalQuadraticBudget N r c : ℝ) -
        2 * ∑ j, (c j : ℝ) * max 0 (Real.log (2 * (r j : ℝ))) := by
  unfold pairedEtaTranslatedFiniteResidualBudget pairedEtaTranslatedFiniteResidualForm
  simp_rw [pairedEtaTranslatedFiniteGram_eq_rational (hr _) (hr _),
    pairedEtaTranslatedHeadPairing_rational (hr _)]
  unfold pairedEtaRationalQuadraticBudget
  push_cast
  simp only [map_ratCast, Complex.ratCast_re, Complex.ratCast_im, Complex.mul_re,
    Complex.norm_ratCast, mul_zero, sub_zero]
  ring

end RiemannGaussian
