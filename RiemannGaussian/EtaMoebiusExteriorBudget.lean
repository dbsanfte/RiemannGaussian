import RiemannGaussian.EtaMoebiusExteriorArithmetic
import RiemannGaussian.EtaMoebiusRefinedHeadDecay

/-!
# Full canonical bounds from signed exterior Möbius arithmetic

The entire refined exterior energy equals a growing signed arithmetic
square integral plus a genuine infinite tail. That tail is bounded by
`(k+1)^2/4^k` for every grid refinement and tends to zero. The unchanged
canonical deficit and actual zero displacement retain all head, grid,
coefficient, and tail costs. Decay of the arithmetic square integral
itself remains open.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The entire signed arithmetic square integral on the growing exterior interval, with the original eta cutoff and every refined physical endpoint retained. -/
def pairedEtaDyadicMoebiusExteriorArithmeticEnergy (k q : ℕ) : ℝ :=
  ∫ t : ℝ in Ioc (Real.log 2) (Real.log (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ)),
    Real.exp (-t) * pairedEtaMoebiusTrialArithmeticPrefix (pairedEtaDyadicTranslateCutoff k)
      (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1)
      (pairedEtaMoebiusTrialLogWeight (k + 1)) t ^ 2

/-- The actual full infinite tail of the refined arithmetic combination past the original dyadic eta cutoff. -/
def pairedEtaDyadicMoebiusRefinedArithmeticTail (k q : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi (Real.log (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ)),
    Real.exp (-t) * ‖pairedEtaMoebiusTrialGridCombination
      (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1)
      (pairedEtaMoebiusTrialLogWeight (k + 1)) t‖ ^ 2

/-- A dimension-independent arithmetic allowance for the whole refined infinite tail. -/
def pairedEtaDyadicMoebiusArithmeticTailAllowance (k : ℕ) : ℝ :=
  (k + 1 : ℝ) ^ 2 / (4 : ℝ) ^ k

/-- The actual refined exterior integral is exactly its signed arithmetic window plus the entire genuine infinite tail. -/
theorem pairedEtaDyadicMoebiusRefinedExteriorEnergy_eq_arithmetic_add_tail (k q : ℕ) :
    pairedEtaDyadicMoebiusRefinedExteriorEnergy k q =
      pairedEtaDyadicMoebiusExteriorArithmeticEnergy k q + pairedEtaDyadicMoebiusRefinedArithmeticTail k q :=
  pairedEtaMoebiusTrialExteriorEnergy_eq_arithmetic_add_tail (pairedEtaDyadicTranslateCutoff_one_le k) _ _ _

/-- The complete refined arithmetic tail is nonnegative. -/
theorem pairedEtaDyadicMoebiusRefinedArithmeticTail_nonneg (k q : ℕ) :
    0 ≤ pairedEtaDyadicMoebiusRefinedArithmeticTail k q := integral_nonneg (fun _ ↦ by positivity)

/-- Every refined physical grid has the same polynomial-over-exponential bound on the entire arithmetic tail. -/
theorem pairedEtaDyadicMoebiusRefinedArithmeticTail_le (k q : ℕ) :
    pairedEtaDyadicMoebiusRefinedArithmeticTail k q ≤ pairedEtaDyadicMoebiusArithmeticTailAllowance k := by
  have h := integral_Ioi_pairedEtaMoebiusTrialGridCombination_weighted_sq_le
    (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)
    (Real.log (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ))
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ))] at h
  have hpow : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hN : (pairedEtaDyadicTranslateCutoff k : ℝ) = 4 * (4 : ℝ) ^ k := by
    simp only [pairedEtaDyadicTranslateCutoff, pairedEtaDyadicTranslateDimension,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hpow]
  apply h.trans
  rw [hN]
  unfold pairedEtaDyadicMoebiusArithmeticTailAllowance
  simp only [Nat.cast_add, Nat.cast_one, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [show 0 ≤ (k + 1 : ℝ) ^ 2 * (4 : ℝ) ^ k by positivity, sq_nonneg (k + 1 : ℝ)]

/-- The explicit allowance for the whole infinite refined arithmetic tail tends to zero. -/
theorem pairedEtaDyadicMoebiusArithmeticTailAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusArithmeticTailAllowance atTop (𝓝 0) := by
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 4)).comp
    (tendsto_add_atTop_nat 1)).const_mul (4 : ℝ)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] at h
  convert h using 1
  ext k
  unfold pairedEtaDyadicMoebiusArithmeticTailAllowance
  rw [pow_succ]
  ring

/-- The actual complete infinite arithmetic tail tends to zero for every refinement schedule. -/
theorem pairedEtaDyadicMoebiusRefinedArithmeticTail_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ pairedEtaDyadicMoebiusRefinedArithmeticTail k (q k)) atTop (𝓝 0) :=
  squeeze_zero (fun k ↦ pairedEtaDyadicMoebiusRefinedArithmeticTail_nonneg k (q k))
    (fun k ↦ pairedEtaDyadicMoebiusRefinedArithmeticTail_le k (q k))
    pairedEtaDyadicMoebiusArithmeticTailAllowance_tendsto_zero

/-- The difference between the complete exterior energy and its growing signed arithmetic square integral tends to zero with the entire omitted range controlled. -/
theorem pairedEtaDyadicMoebiusRefinedExterior_sub_arithmetic_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ pairedEtaDyadicMoebiusRefinedExteriorEnergy k (q k) -
      pairedEtaDyadicMoebiusExteriorArithmeticEnergy k (q k)) atTop (𝓝 0) := by
  simp_rw [pairedEtaDyadicMoebiusRefinedExteriorEnergy_eq_arithmetic_add_tail, add_sub_cancel_left]
  exact pairedEtaDyadicMoebiusRefinedArithmeticTail_tendsto_zero q

/-- The complete proved allowance accompanying the full growing signed arithmetic square integral. -/
def pairedEtaDyadicMoebiusExteriorArithmeticAllowance (k : ℕ) : ℝ :=
  pairedEtaDyadicMoebiusArithmeticTailAllowance k + pairedEtaDyadicMoebiusExteriorAllowance k

/-- All costs removed from the full signed exterior arithmetic target vanish together. -/
theorem pairedEtaDyadicMoebiusExteriorArithmeticAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusExteriorArithmeticAllowance atTop (𝓝 0) := by
  change Tendsto (fun k ↦ pairedEtaDyadicMoebiusArithmeticTailAllowance k + pairedEtaDyadicMoebiusExteriorAllowance k)
    atTop (𝓝 0)
  simpa only [add_zero] using
    pairedEtaDyadicMoebiusArithmeticTailAllowance_tendsto_zero.add pairedEtaDyadicMoebiusExteriorAllowance_tendsto_zero

/-- The unchanged canonical deficit is bounded by the full growing signed arithmetic square integral, with every head, grid, coefficient, and infinite-tail cost proved vanishing. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_exterior_arithmetic {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaDyadicTranslateDeficit k ≤ pairedEtaDyadicMoebiusExteriorArithmeticEnergy k q +
      pairedEtaDyadicMoebiusExteriorArithmeticAllowance k := by
  have h := pairedEtaDyadicTranslateDeficit_le_moebius_exterior hk q
  rw [pairedEtaDyadicMoebiusRefinedExteriorEnergy_eq_arithmetic_add_tail] at h
  have ht := pairedEtaDyadicMoebiusRefinedArithmeticTail_le k q
  unfold pairedEtaDyadicMoebiusExteriorArithmeticAllowance
  linarith

/-- Every original actual zero displacement inherits the complete signed exterior arithmetic budget without assuming its decay. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_exterior_arithmetic
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicMoebiusExteriorArithmeticEnergy k q + pairedEtaDyadicMoebiusExteriorArithmeticAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_exterior_arithmetic hk q)

end

end RiemannGaussian
