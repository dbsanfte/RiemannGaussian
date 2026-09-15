import RiemannGaussian.ZetaRieszHeadOrders

/-!
# Fixed polynomial filters from shifted complex response bounds

This algebraic transport retains every factorial shift and coefficient.
Its geometric input is supplied by the independently proved high-order
convolution estimates; the transport alone is not a new arithmetic bound.
-/

namespace RiemannGaussian.ZetaRieszShiftedHeadBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- A general single-coefficient transport from a shifted source bound.
The complete complex response remains the input to its norm estimate. -/
theorem norm_shifted_term_le (c v : ℂ) (j N : ℕ) {u L r C : ℝ}
    (hu0 : 0 < u) (hL : 1 ≤ L) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hconv : ‖(u : ℂ) ^ (N + j + 1 + 1) * v‖ ≤ (N + j + 1 + 1 : ℝ) * r ^ (N + j + 1) * C) :
    ‖(u : ℂ) ^ (N + 1) * (-(c * ((N + j + 1 : ℕ) : ℂ) / (L : ℂ)) * v)‖ ≤
      ((N + 1 : ℝ) ^ 2 * r ^ N) * (C * (‖c‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2)) := by
  let M : ℕ := N + j + 1
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have hNM : N ≤ M := by dsimp [M]; omega
  have hconv : ‖(u : ℂ) ^ (M + 1) * v‖ ≤ (M + 1 : ℝ) * r ^ M * C := by
    simpa only [M, Nat.cast_add, Nat.cast_one] using hconv
  have hpow : (u : ℂ)⁻¹ ^ (j + 1) * (u : ℂ) ^ (M + 1) = (u : ℂ) ^ (N + 1) := by
    rw [show M + 1 = (j + 1) + (N + 1) by dsimp [M]; omega,
      pow_add (u : ℂ) (j + 1) (N + 1),
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ huC, one_pow, one_mul]
  have he (v : ℂ) : (u : ℂ) ^ (N + 1) * (-(c * (M : ℂ) / (L : ℂ)) * v) =
      (-(c * (M : ℂ) / (L : ℂ)) * (u : ℂ)⁻¹ ^ (j + 1)) * ((u : ℂ) ^ (M + 1) * v) := by
    calc
      _ = -(c * (M : ℂ) / (L : ℂ)) * ((u : ℂ) ^ (N + 1) * v) := by ring
      _ = _ := by rw [← hpow]; ring
  have hc : ‖-(c * (M : ℂ) / (L : ℂ)) * (u : ℂ)⁻¹ ^ (j + 1)‖ ≤
      ‖c‖ * M * u⁻¹ ^ (j + 1) := by
    rw [norm_mul, norm_neg, norm_div, norm_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ L),
      norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) hL) (by positivity)
  have hMa : (M : ℝ) ≤ (N + 1 : ℝ) * (j + 2 : ℝ) := by
    dsimp [M]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) j,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (Nat.cast_nonneg (α := ℝ) j)]
  have hMb : (M + 1 : ℝ) ≤ (N + 1 : ℝ) * (j + 2 : ℝ) := by
    dsimp [M]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) j,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (Nat.cast_nonneg (α := ℝ) j)]
  have hMM : (M : ℝ) * (M + 1) ≤ (N + 1 : ℝ) ^ 2 * (j + 2 : ℝ) ^ 2 := by
    calc
      _ ≤ ((N + 1 : ℝ) * (j + 2 : ℝ)) * ((N + 1 : ℝ) * (j + 2 : ℝ)) :=
        mul_le_mul hMa hMb (by positivity) (by positivity)
      _ = _ := by ring
  have hrate : r ^ M ≤ r ^ N := pow_le_pow_of_le_one hr0 hr1 hNM
  change ‖(u : ℂ) ^ (N + 1) * (-(c * (M : ℂ) / (L : ℂ)) * _)‖ ≤
    ((N + 1 : ℝ) ^ 2 * r ^ N) * (C * (‖c‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2))
  rw [he, norm_mul]
  calc
    _ ≤ (‖c‖ * M * u⁻¹ ^ (j + 1)) * ((M + 1 : ℝ) * r ^ M * C) :=
      mul_le_mul hc hconv (norm_nonneg _) (by positivity)
    _ = ((M : ℝ) * (M + 1) * r ^ M) * (C * ‖c‖ * u⁻¹ ^ (j + 1)) := by ring
    _ ≤ ((N + 1 : ℝ) ^ 2 * (j + 2 : ℝ) ^ 2 * r ^ N) *
        (C * ‖c‖ * u⁻¹ ^ (j + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hMM hrate (pow_nonneg hr0 _) (by positivity)
    _ = _ := by ring


/-- A fixed polynomial filter transports the proved bounds for all
its original shifted complex responses with one finite coefficient cost. -/
theorem norm_fixedFilter_of_shiftedBounds (P : Polynomial ℂ) (v : ℕ → ℂ) (N : ℕ)
    {u L r C : ℝ} (hu : 0 < u) (hL : 1 ≤ L) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : ∀ j ∈ P.support,
      ‖(u : ℂ) ^ (N + j + 1 + 1) * v j‖ ≤ (N + j + 1 + 1 : ℝ) * r ^ (N + j + 1) * C) :
    ‖(u : ℂ) ^ (N + 1) * ∑ j ∈ P.support,
      -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) / (L : ℂ)) * v j‖ ≤
      ((N + 1 : ℝ) ^ 2 * r ^ N) *
        (C * ∑ j ∈ P.support, ‖P.coeff j‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2) := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ P.support, ((N + 1 : ℝ) ^ 2 * r ^ N) *
        (C * (‖P.coeff j‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun j hj => norm_shifted_term_le (P.coeff j) (v j) j N hu hL hC hr0 hr1 (hv j hj))
    _ = _ := by simp only [Finset.mul_sum]

/-- The polynomial order cost of any fixed-filter transport vanishes
against every strict nonnegative geometric rate. -/
theorem tendsto_quadratic_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun N : ℕ => (N + 1 : ℝ) ^ 2 * r ^ N) atTop (nhds 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
  have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have h := (h2.add (h1.const_mul 2)).add h0
  simpa only [mul_zero, zero_add] using h.congr (fun N => by ring)

end
end RiemannGaussian.ZetaRieszShiftedHeadBudget
