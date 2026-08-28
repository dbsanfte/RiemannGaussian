import RiemannGaussian.RiemannXiSuzukiPointwiseLocalPositivity

/-!
# Curvature of Suzuki's pointwise Archimedean term

This file differentiates the literal order-two Hurwitz--Lerch gap in
Suzuki's pointwise arithmetic formula.  On positive screw time, two
termwise derivatives turn the gap into a geometric series.  Evaluating that
series proves that the second derivative of the complete Archimedean term is
exactly `suzukiSmoothCurvature`, the curvature used by the transport
modules.

Thus the transport curvature is no longer a separately chosen model input:
it is derived from Suzuki's source-exact arithmetic formula.
-/

namespace RiemannGaussian

noncomputable section

open Filter
open scoped BigOperators Topology

/-! ## Two derivatives of the order-two Lerch gap -/

/-- First time derivative of one order-two Lerch-gap summand. -/
def suzukiPointwiseLerchGapSlopeSummand (t : ℝ) (n : ℕ) : ℝ :=
  2 * Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) /
    ((n : ℝ) + 1 / 4)

/-- Second time derivative of one order-two Lerch-gap summand. -/
def suzukiPointwiseLerchGapCurvatureSummand (t : ℝ) (n : ℕ) : ℝ :=
  -4 * Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)

/-- The first-derivative series of the order-two Lerch gap. -/
def suzukiPointwiseLerchGapSlope (t : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiPointwiseLerchGapSlopeSummand t n

/-- The second-derivative series of the order-two Lerch gap. -/
def suzukiPointwiseLerchGapCurvature (t : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiPointwiseLerchGapCurvatureSummand t n

/-- Direct differentiation of one order-two Lerch-gap summand. -/
theorem hasDerivAt_suzukiPointwiseLerchGapSummand
    (t : ℝ) (n : ℕ) :
    HasDerivAt (fun u : ℝ => suzukiPointwiseLerchGapSummand u n)
      (suzukiPointwiseLerchGapSlopeSummand t n) t := by
  rw [show (fun u : ℝ => suzukiPointwiseLerchGapSummand u n) =
      fun u : ℝ =>
        (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * u)) /
          ((n : ℝ) + 1 / 4) ^ 2 by
    funext u
    exact suzukiPointwiseLerchGapSummand_eq u n]
  unfold suzukiPointwiseLerchGapSlopeSummand
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hinner : HasDerivAt (fun u : ℝ => -2 * a * u) (-2 * a) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (-2 * a)
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-2 * a * u))
      (Real.exp (-2 * a * t) * (-2 * a)) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-2 * a * t)).comp t hinner
  have hquot := ((hasDerivAt_const t 1).sub hexp).div_const (a ^ 2)
  apply hquot.congr_deriv
  dsimp only [a] at ha ⊢
  field_simp [ha.ne']
  ring

/-- The displayed slope summand differentiates to its curvature summand. -/
theorem hasDerivAt_suzukiPointwiseLerchGapSlopeSummand
    (t : ℝ) (n : ℕ) :
    HasDerivAt (fun u : ℝ => suzukiPointwiseLerchGapSlopeSummand u n)
      (suzukiPointwiseLerchGapCurvatureSummand t n) t := by
  unfold suzukiPointwiseLerchGapSlopeSummand
    suzukiPointwiseLerchGapCurvatureSummand
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hinner : HasDerivAt (fun u : ℝ => -2 * a * u) (-2 * a) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (-2 * a)
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-2 * a * u))
      (Real.exp (-2 * a * t) * (-2 * a)) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-2 * a * t)).comp t hinner
  have hquot := (hexp.const_mul 2).div_const a
  apply hquot.congr_deriv
  dsimp only [a] at ha ⊢
  field_simp [ha.ne']
  ring

/-- On a fixed positive-time neighborhood, every exponential mode is
dominated by a single geometric sequence. -/
theorem suzukiPointwiseLerchMode_le_geometric
    {t u : ℝ} (ht : 0 < t) (hu : t / 2 < u) (n : ℕ) :
    Real.exp (-2 * ((n : ℝ) + 1 / 4) * u) ≤
      Real.exp (-t) ^ n := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hu0 : 0 ≤ u := (by linarith : 0 < u).le
  have htime : (n : ℝ) * t ≤ (n : ℝ) * (2 * u) :=
    mul_le_mul_of_nonneg_left (by linarith) hn
  have hshift : (n : ℝ) * u ≤ ((n : ℝ) + 1 / 4) * u :=
    mul_le_mul_of_nonneg_right (by norm_num) hu0
  nlinarith

/-- Uniform geometric bound for the first derivatives of the gap summands
on a positive-time neighborhood. -/
theorem norm_suzukiPointwiseLerchGapSlopeSummand_le
    {t u : ℝ} (ht : 0 < t) (hu : t / 2 < u) (n : ℕ) :
    ‖suzukiPointwiseLerchGapSlopeSummand u n‖ ≤
      8 * Real.exp (-t) ^ n := by
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have haQuarter : (1 / 4 : ℝ) ≤ a := by
    dsimp only [a]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hcoefficient : 2 / a ≤ (8 : ℝ) := by
    rw [div_le_iff₀ ha]
    nlinarith
  have hmode := suzukiPointwiseLerchMode_le_geometric ht hu n
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · change 2 * Real.exp (-2 * a * u) / a ≤
      8 * Real.exp (-t) ^ n
    calc
      2 * Real.exp (-2 * a * u) / a =
          (2 / a) * Real.exp (-2 * a * u) := by ring
      _ ≤ 8 * Real.exp (-2 * a * u) :=
        mul_le_mul_of_nonneg_right hcoefficient (Real.exp_pos _).le
      _ ≤ 8 * Real.exp (-t) ^ n :=
        mul_le_mul_of_nonneg_left hmode (by norm_num)
  · unfold suzukiPointwiseLerchGapSlopeSummand
    positivity

/-- Uniform geometric bound for the second derivatives of the gap summands
on a positive-time neighborhood. -/
theorem norm_suzukiPointwiseLerchGapCurvatureSummand_le
    {t u : ℝ} (ht : 0 < t) (hu : t / 2 < u) (n : ℕ) :
    ‖suzukiPointwiseLerchGapCurvatureSummand u n‖ ≤
      4 * Real.exp (-t) ^ n := by
  have hmode := suzukiPointwiseLerchMode_le_geometric ht hu n
  rw [Real.norm_eq_abs]
  unfold suzukiPointwiseLerchGapCurvatureSummand
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (Real.exp_pos _).le)]
  calc
    -(-4 * Real.exp (-2 * ((n : ℝ) + 1 / 4) * u)) =
        4 * Real.exp (-2 * ((n : ℝ) + 1 / 4) * u) := by ring
    _ ≤ 4 * Real.exp (-t) ^ n :=
      mul_le_mul_of_nonneg_left hmode (by norm_num)

/-- The first-derivative Lerch-gap series converges at every positive time. -/
theorem summable_suzukiPointwiseLerchGapSlopeSummand
    {t : ℝ} (ht : 0 < t) :
    Summable (suzukiPointwiseLerchGapSlopeSummand t) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  apply ((summable_geometric_of_lt_one hq0 hq1).mul_left 8).of_norm_bounded
  intro n
  exact norm_suzukiPointwiseLerchGapSlopeSummand_le ht (by linarith) n

/-- The second-derivative Lerch-gap series converges at every positive time. -/
theorem summable_suzukiPointwiseLerchGapCurvatureSummand
    {t : ℝ} (ht : 0 < t) :
    Summable (suzukiPointwiseLerchGapCurvatureSummand t) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  apply ((summable_geometric_of_lt_one hq0 hq1).mul_left 4).of_norm_bounded
  intro n
  exact norm_suzukiPointwiseLerchGapCurvatureSummand_le ht (by linarith) n

/-- On positive time, differentiation passes through the complete
order-two Lerch-gap series. -/
theorem hasDerivAt_tsum_suzukiPointwiseLerchGapSummand
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => ∑' n : ℕ, suzukiPointwiseLerchGapSummand u n)
      (suzukiPointwiseLerchGapSlope t) t := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hmajor : Summable (fun n : ℕ => 8 * Real.exp (-t) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left 8
  have htmem : t ∈ Set.Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  unfold suzukiPointwiseLerchGapSlope
  refine hasDerivAt_tsum_of_isPreconnected
    (t := Set.Ioo (t / 2) (3 * t / 2))
    (g := fun n u => suzukiPointwiseLerchGapSummand u n)
    (g' := fun n u => suzukiPointwiseLerchGapSlopeSummand u n)
    (y₀ := t) (y := t) hmajor isOpen_Ioo isPreconnected_Ioo
      ?_ ?_ htmem (summable_suzukiPointwiseLerchGapSummand ht.le) htmem
  · intro n u _hu
    exact hasDerivAt_suzukiPointwiseLerchGapSummand u n
  · intro n u hu
    exact norm_suzukiPointwiseLerchGapSlopeSummand_le ht hu.1 n

/-- The first-derivative Lerch series can itself be differentiated termwise
on positive time. -/
theorem hasDerivAt_suzukiPointwiseLerchGapSlope
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiPointwiseLerchGapSlope
      (suzukiPointwiseLerchGapCurvature t) t := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hmajor : Summable (fun n : ℕ => 4 * Real.exp (-t) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left 4
  have htmem : t ∈ Set.Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  unfold suzukiPointwiseLerchGapSlope suzukiPointwiseLerchGapCurvature
  refine hasDerivAt_tsum_of_isPreconnected
    (t := Set.Ioo (t / 2) (3 * t / 2))
    (g := fun n u => suzukiPointwiseLerchGapSlopeSummand u n)
    (g' := fun n u => suzukiPointwiseLerchGapCurvatureSummand u n)
    (y₀ := t) (y := t) hmajor isOpen_Ioo isPreconnected_Ioo
      ?_ ?_ htmem (summable_suzukiPointwiseLerchGapSlopeSummand ht) htmem
  · intro n u _hu
    exact hasDerivAt_suzukiPointwiseLerchGapSlopeSummand u n
  · intro n u hu
    exact norm_suzukiPointwiseLerchGapCurvatureSummand_le ht hu.1 n

/-! ## Evaluation of the second-derivative series -/

/-- Each exponential mode separates into a quarter-shift factor and a
geometric mode. -/
theorem suzukiPointwiseLerchMode_eq_geometric
    (t : ℝ) (n : ℕ) :
    Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) =
      Real.exp (-t / 2) * Real.exp (-2 * t) ^ n := by
  symm
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- The exponential modes produced by two Lerch-gap derivatives sum to an
elementary geometric quotient. -/
theorem tsum_suzukiPointwiseLerchMode
    {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) =
      Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  calc
    (∑' n : ℕ, Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) =
        ∑' n : ℕ, Real.exp (-t / 2) * Real.exp (-2 * t) ^ n := by
      apply tsum_congr
      exact suzukiPointwiseLerchMode_eq_geometric t
    _ = Real.exp (-t / 2) * (1 - Real.exp (-2 * t))⁻¹ :=
      ((hasSum_geometric_of_lt_one hq0 hq1).mul_left
        (Real.exp (-t / 2))).tsum_eq
    _ = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
      rfl

/-- The complete Lerch-gap curvature series is the corresponding negative
geometric quotient. -/
theorem suzukiPointwiseLerchGapCurvature_eq
    {t : ℝ} (ht : 0 < t) :
    suzukiPointwiseLerchGapCurvature t =
      -4 * (Real.exp (-t / 2) / (1 - Real.exp (-2 * t))) := by
  unfold suzukiPointwiseLerchGapCurvature
    suzukiPointwiseLerchGapCurvatureSummand
  rw [tsum_mul_left, tsum_suzukiPointwiseLerchMode ht]

/-! ## The source-exact Archimedean curvature -/

/-- Positive-time series presentation of Suzuki's pointwise Archimedean
term. -/
def suzukiPointwiseArchimedeanSeries (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    t / 2 * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) +
      1 / 4 *
        (∑' n : ℕ, suzukiPointwiseLerchGapSummand t n)

/-- The literal Hurwitz--Lerch expression equals its summandwise gap series
at every nonnegative time. -/
theorem suzukiPointwiseArchimedean_eq_series
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiPointwiseArchimedean t =
      suzukiPointwiseArchimedeanSeries t := by
  unfold suzukiPointwiseArchimedean
    suzukiPointwiseArchimedeanSeries
  rw [suzukiHurwitzLerchTwo_sub_damped_eq_tsum_gap ht]

/-- The first derivative of Suzuki's pointwise Archimedean term on positive
time. -/
def suzukiPointwiseArchimedeanSlope (t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) - 2 * Real.exp (-t / 2) +
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 +
      1 / 4 * suzukiPointwiseLerchGapSlope t

private theorem hasDerivAt_exp_half (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      (Real.exp (t / 2) * (1 / 2)) t := by
  have hinner : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const 2
  simpa only [Function.comp_def] using
    (Real.hasDerivAt_exp (t / 2)).comp t hinner

private theorem hasDerivAt_exp_neg_half (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
      (Real.exp (-t / 2) * (-1 / 2)) t := by
  have hinner : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2) t := by
    simpa only [Pi.neg_apply, id_eq] using
      (hasDerivAt_id t).neg.div_const 2
  simpa only [Function.comp_def] using
    (Real.hasDerivAt_exp (-t / 2)).comp t hinner

/-- The source-exact pointwise Archimedean term has the displayed first
derivative at every positive time. -/
theorem hasDerivAt_suzukiPointwiseArchimedean
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiPointwiseArchimedean
      (suzukiPointwiseArchimedeanSlope t) t := by
  let D : ℝ := (Complex.digamma (1 / 4)).re - Real.log Real.pi
  have helementary :=
    (((hasDerivAt_exp_half t).add (hasDerivAt_exp_neg_half t)).sub_const 2).const_mul 4
  have hlinear := ((hasDerivAt_id t).div_const 2).mul_const D
  have hgap :=
    (hasDerivAt_tsum_suzukiPointwiseLerchGapSummand ht).const_mul (1 / 4)
  have hseries : HasDerivAt suzukiPointwiseArchimedeanSeries
      (suzukiPointwiseArchimedeanSlope t) t := by
    unfold suzukiPointwiseArchimedeanSeries
      suzukiPointwiseArchimedeanSlope
    apply ((helementary.add hlinear).add hgap).congr_deriv
    dsimp only [D]
    ring
  apply hseries.congr_of_eventuallyEq
  exact eventuallyEq_of_mem (Ioi_mem_nhds ht) fun u hu =>
    suzukiPointwiseArchimedean_eq_series hu.le

/-- Differentiating the explicit Archimedean slope leaves the elementary
exponential pair plus one quarter of the Lerch-gap curvature series. -/
theorem hasDerivAt_suzukiPointwiseArchimedeanSlope_series
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiPointwiseArchimedeanSlope
      (Real.exp (t / 2) + Real.exp (-t / 2) +
        1 / 4 * suzukiPointwiseLerchGapCurvature t) t := by
  let D : ℝ := (Complex.digamma (1 / 4)).re - Real.log Real.pi
  have hpositive := (hasDerivAt_exp_half t).const_mul 2
  have hnegative := (hasDerivAt_exp_neg_half t).const_mul 2
  have hconstant := hasDerivAt_const t (D / 2)
  have hgap :=
    (hasDerivAt_suzukiPointwiseLerchGapSlope ht).const_mul (1 / 4)
  unfold suzukiPointwiseArchimedeanSlope
  apply (((hpositive.sub hnegative).add hconstant).add hgap).congr_deriv
  ring_nf

/-- The geometric quotient from the Lerch gap converts the series curvature
exactly into Suzuki's smooth transport curvature. -/
theorem suzukiPointwiseArchimedeanCurvatureSeries_eq_smoothCurvature
    {t : ℝ} (ht : 0 < t) :
    Real.exp (t / 2) + Real.exp (-t / 2) +
        1 / 4 * suzukiPointwiseLerchGapCurvature t =
      suzukiSmoothCurvature t := by
  rw [suzukiPointwiseLerchGapCurvature_eq ht]
  unfold suzukiSmoothCurvature suzukiMissingCurvature
  have hden : 1 - Real.exp (-2 * t) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos ht).ne'
  have hden' : 1 - Real.exp (-(t * 2)) ≠ 0 := by
    have harg : -(t * 2) = -2 * t := by ring
    rw [harg]
    exact hden
  have hexp :
      Real.exp (-t / 2) * Real.exp (-2 * t) =
        Real.exp (-(5 * t) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  have halgebra :
      Real.exp (t / 2) + Real.exp (-t / 2) -
          Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) =
        Real.exp (t / 2) -
          Real.exp (-t / 2) * Real.exp (-2 * t) /
            (1 - Real.exp (-2 * t)) := by
    field_simp [hden']
    ring
  ring_nf at halgebra ⊢
  exact halgebra

/-- The explicit first derivative of the source-exact Archimedean term has
derivative `suzukiSmoothCurvature` throughout positive time. -/
theorem hasDerivAt_suzukiPointwiseArchimedeanSlope
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiPointwiseArchimedeanSlope
      (suzukiSmoothCurvature t) t :=
  (hasDerivAt_suzukiPointwiseArchimedeanSlope_series ht).congr_deriv
    (suzukiPointwiseArchimedeanCurvatureSeries_eq_smoothCurvature ht)

/-- The literal pointwise Archimedean term has second derivative
`suzukiSmoothCurvature` at every positive time. -/
theorem hasDerivAt_deriv_suzukiPointwiseArchimedean
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => deriv suzukiPointwiseArchimedean u)
      (suzukiSmoothCurvature t) t := by
  apply (hasDerivAt_suzukiPointwiseArchimedeanSlope ht).congr_of_eventuallyEq
  exact eventuallyEq_of_mem (Ioi_mem_nhds ht) fun u hu =>
    (hasDerivAt_suzukiPointwiseArchimedean hu).deriv

end

end RiemannGaussian
