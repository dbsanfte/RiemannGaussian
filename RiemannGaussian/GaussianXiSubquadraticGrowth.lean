import RiemannGaussian.GaussianXiMellinSubquadratic

/-!
# Global subquadratic growth of the pole-cleared xi function

The `4/3`-power upper-tail Mellin estimate is propagated through the split
completed-zeta formula.  Its two reflected real exponents are both bounded by
`norm(s) + 1`, giving a global `4/3`-power bound for
`completedRiemannZeta₀`.

The quadratic polynomial prefactor in `riemannXi` is then absorbed into a
slightly larger `3/2`-power exponential.  Lean thereby proves an unconditional
global xi-growth exponent strictly below two, the threshold needed for
inverse-square divisor summability.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The positive coefficient multiplying `u^(4/3)` in the sharpened Mellin
cost. -/
def mellinFourThirdsCoefficient (p : ℝ) : ℝ :=
  (4 / (2 * p) ^ (1 / 4 : ℝ)) ^ (4 / 3 : ℝ) / (4 / 3)

/-- For a positive exponential rate and nonnegative exponent, the explicit
Mellin cost is exactly coefficient times `u^(4/3)`. -/
theorem mellinFourThirdsCost_eq_coefficient_mul_rpow
    {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) :
    mellinFourThirdsCost p u =
      mellinFourThirdsCoefficient p * u ^ (4 / 3 : ℝ) := by
  unfold mellinFourThirdsCost mellinFourThirdsCoefficient
  rw [show 4 * u / (2 * p) ^ (1 / 4 : ℝ) =
      (4 / (2 * p) ^ (1 / 4 : ℝ)) * u by ring]
  rw [Real.mul_rpow (by positivity) hu]
  ring

/-- The `4/3` Mellin coefficient is nonnegative. -/
theorem mellinFourThirdsCoefficient_nonneg
    {p : ℝ} (hp : 0 < p) :
    0 ≤ mellinFourThirdsCoefficient p := by
  unfold mellinFourThirdsCoefficient
  positivity

/-- The sharpened Mellin cost is monotone on nonnegative exponents. -/
theorem mellinFourThirdsCost_mono_of_nonneg
    {p u v : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (huv : u ≤ v) :
    mellinFourThirdsCost p u ≤ mellinFourThirdsCost p v := by
  have hv : 0 ≤ v := hu.trans huv
  rw [mellinFourThirdsCost_eq_coefficient_mul_rpow hp hu,
    mellinFourThirdsCost_eq_coefficient_mul_rpow hp hv]
  apply mul_le_mul_of_nonneg_left _
    (mellinFourThirdsCoefficient_nonneg hp)
  exact Real.rpow_le_rpow hu huv (by norm_num)

/-- The split Mellin formula gives a global `4/3`-power bound for the entire
completed-zeta regularization. -/
theorem norm_completedRiemannZeta₀_le_fourThirds
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤
      (2 * C / p) *
        Real.exp
          (mellinFourThirdsCoefficient p *
            (‖s‖ + 1) ^ (4 / 3 : ℝ)) := by
  let R : ℝ := ‖s‖ + 1
  let K : ℝ := 2 * C / p
  let B : ℝ := mellinFourThirdsCoefficient p
  let Q : ℝ := B * R ^ (4 / 3 : ℝ)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hfirstU : max 0 ((s / 2).re - 1) ≤ R := by
    apply max_le
    · exact hR0
    · have hre := Complex.abs_re_le_norm s
      norm_num
      dsimp [R]
      nlinarith [le_abs_self s.re]
  have hsecondU : max 0 (((1 - s) / 2).re - 1) ≤ R := by
    apply max_le
    · exact hR0
    · have hre := Complex.abs_re_le_norm s
      norm_num
      dsimp [R]
      nlinarith [neg_le_abs s.re]
  have hfirstCost :
      mellinFourThirdsCost p (max 0 ((s / 2).re - 1)) ≤ Q := by
    calc
      mellinFourThirdsCost p (max 0 ((s / 2).re - 1)) ≤
          mellinFourThirdsCost p R :=
        mellinFourThirdsCost_mono_of_nonneg hp (le_max_left _ _) hfirstU
      _ = Q := by
        rw [mellinFourThirdsCost_eq_coefficient_mul_rpow hp hR0]
  have hsecondCost :
      mellinFourThirdsCost p (max 0 (((1 - s) / 2).re - 1)) ≤ Q := by
    calc
      mellinFourThirdsCost p (max 0 (((1 - s) / 2).re - 1)) ≤
          mellinFourThirdsCost p R :=
        mellinFourThirdsCost_mono_of_nonneg hp (le_max_left _ _) hsecondU
      _ = Q := by
        rw [mellinFourThirdsCost_eq_coefficient_mul_rpow hp hR0]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hfirst :
      ‖mellin riemannThetaUpper (s / 2)‖ ≤ K * Real.exp Q := by
    calc
      ‖mellin riemannThetaUpper (s / 2)‖ ≤
          K * Real.exp
            (mellinFourThirdsCost p (max 0 ((s / 2).re - 1))) :=
        norm_mellin_riemannThetaUpper_le_fourThirds hC hp hbound (s / 2)
      _ ≤ K * Real.exp Q :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hfirstCost) hK0
  have hsecond :
      ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤ K * Real.exp Q := by
    calc
      ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤
          K * Real.exp
            (mellinFourThirdsCost p
              (max 0 (((1 - s) / 2).re - 1))) :=
        norm_mellin_riemannThetaUpper_le_fourThirds
          hC hp hbound ((1 - s) / 2)
      _ ≤ K * Real.exp Q :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hsecondCost) hK0
  rw [completedRiemannZeta₀_eq_upperMellin, norm_div]
  norm_num
  calc
    ‖mellin riemannThetaUpper (s / 2) +
        mellin riemannThetaUpper ((1 - s) / 2)‖ / 2 ≤
        (‖mellin riemannThetaUpper (s / 2)‖ +
          ‖mellin riemannThetaUpper ((1 - s) / 2)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (K * Real.exp Q + K * Real.exp Q) / 2 := by gcongr
    _ = (2 * C / p) *
        Real.exp
          (mellinFourThirdsCoefficient p *
            (‖s‖ + 1) ^ (4 / 3 : ℝ)) := by
      simp only [K, Q, B, R]
      ring

/-- A global subquadratic growth predicate with explicit exponent `3/2`. -/
def RiemannXiThreeHalvesGrowth : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
    ‖riemannXi z‖ ≤
      Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))

/-- Mathlib's theta-kernel estimates imply unconditional global xi growth of
exponent `3/2`, strictly below the inverse-square threshold `2`. -/
theorem riemannXi_threeHalvesGrowth : RiemannXiThreeHalvesGrowth := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  let K : ℝ := max 1 (2 * C / p)
  let B : ℝ := mellinFourThirdsCoefficient p
  let A : ℝ := K + B + 4
  have hrawK0 : 0 ≤ 2 * C / p := by positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hrawK_le : 2 * C / p ≤ K := le_max_right _ _
  have hB0 : 0 ≤ B := mellinFourThirdsCoefficient_nonneg hp
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA1, ?_⟩
  intro z
  let R : ℝ := ‖z‖ + 1
  let U : ℝ := R ^ (4 / 3 : ℝ)
  let T : ℝ := R ^ (3 / 2 : ℝ)
  let E : ℝ := Real.exp (B * U)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hT1 : 1 ≤ T := by
    dsimp [T]
    calc
      (1 : ℝ) = 1 ^ (3 / 2 : ℝ) := by norm_num
      _ ≤ R ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hR1 (by norm_num)
  have hRleT : R ≤ T := by
    dsimp [T]
    calc
      R = R ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ R ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hUleT : U ≤ T := by
    dsimp [U, T]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hcompleted : ‖completedRiemannZeta₀ z‖ ≤ K * E := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * C / p) *
            Real.exp
              (mellinFourThirdsCoefficient p *
                (‖z‖ + 1) ^ (4 / 3 : ℝ)) :=
        norm_completedRiemannZeta₀_le_fourThirds hC hp htail z
      _ = (2 * C / p) * E := by simp only [B, E, U, R]
      _ ≤ K * E :=
        mul_le_mul_of_nonneg_right hrawK_le (Real.exp_nonneg _)
  have honeSub : ‖1 - z‖ ≤ R := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = R := by simp [R, add_comm]
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    linarith
  have hpoly : ‖z‖ * ‖1 - z‖ ≤ R ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hzR honeSub (norm_nonneg _) hR0
  have hmain :
      ‖z * (1 - z) * completedRiemannZeta₀ z‖ ≤ K * R ^ 2 * E := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖1 - z‖ * ‖completedRiemannZeta₀ z‖ ≤
          R ^ 2 * (K * E) :=
        mul_le_mul hpoly hcompleted (norm_nonneg _) (sq_nonneg R)
      _ = K * R ^ 2 * E := by ring
  have hRexp : R ≤ Real.exp R := by
    linarith [Real.add_one_le_exp R]
  have hRsqExp : R ^ 2 ≤ Real.exp (2 * R) := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ Real.exp R * Real.exp R :=
        mul_le_mul hRexp hRexp hR0 (Real.exp_nonneg _)
      _ = Real.exp (2 * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have hKExp : K ≤ Real.exp K := by
    linarith [Real.add_one_le_exp K]
  have hexponent : 1 + K + 2 * R + B * U ≤ A * T := by
    have hnonneg : 0 ≤ (K + B + 3) * (T - 1) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [A]
    nlinarith
  have habsorb : 2 * (K * R ^ 2 * E) ≤ Real.exp (A * T) := by
    calc
      2 * (K * R ^ 2 * E) = 2 * K * R ^ 2 * E := by ring
      _ ≤ Real.exp 1 * Real.exp K * Real.exp (2 * R) * E := by
        gcongr
      _ = Real.exp (1 + K + 2 * R + B * U) := by
        simp only [E, ← Real.exp_add]
      _ ≤ Real.exp (A * T) := Real.exp_le_exp.mpr hexponent
  unfold riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ K * R ^ 2 * E + 1 := by
      simpa using add_le_add_right hmain 1
    _ ≤ 2 * (K * R ^ 2 * E) := by
      have hKRE1 : 1 ≤ K * R ^ 2 * E := by
        have hRtwo : 1 ≤ R ^ 2 := by nlinarith
        have hE1 : 1 ≤ E := by
          dsimp [E]
          rw [Real.one_le_exp_iff]
          exact mul_nonneg hB0 (Real.rpow_nonneg hR0 _)
        exact one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hK1 hRtwo) hE1
      linarith
    _ ≤ Real.exp (A * T) := habsorb
    _ = Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)) := by rfl

end

end RiemannGaussian
