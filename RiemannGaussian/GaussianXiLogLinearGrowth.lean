import RiemannGaussian.GaussianXiGrowth

/-!
# Log-linear global growth of the pole-cleared xi function

The earlier global xi bound used a fractional-power Young inequality to
control the Mellin weight against the exponentially decaying theta tail. This
module proves the sharper elementary optimization

`x^u exp(-p x) ≤ exp(|u| log(1 + 2|u|/p)) exp(-(p/2)x)`

for `x ≥ 1`. Propagating it through the split theta--Mellin representation and
absorbing the polynomial prefactor proves unconditional
`exp(O(R log R))` growth for `riemannXi`. Jensen's inequality then gives a
multiplicity-aware `O(R log R)` centered-disk zero count.

This order-one logarithmic scale is a strict improvement over the previous
three-halves bound. It is intended for a sharper canonical lower estimate; by
itself it does not establish the critical-line `o(T)` negative-log frontier.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The Mellin power can be absorbed into half the exponential tail at the
exact logarithmic optimization scale. -/
theorem rpow_mul_exp_neg_le_exp_abs_mul_log_mul_exp_neg_half
    {p x u : ℝ} (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ u * Real.exp (-p * x) ≤
      Real.exp (|u| * Real.log (1 + 2 * |u| / p)) *
        Real.exp (-(p / 2) * x) := by
  let U : ℝ := |u|
  let a : ℝ := 1 + 2 * U / p
  have hU0 : 0 ≤ U := by simp [U]
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have ha1 : 1 ≤ a := by
    dsimp [a]
    have : 0 ≤ 2 * U / p := by positivity
    linarith
  have hapos : 0 < a := zero_lt_one.trans_le ha1
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxpos hapos)
  rw [Real.log_div hxpos.ne' hapos.ne'] at hlog
  have hweighted :
      U * (Real.log x - Real.log a) ≤ U * (x / a - 1) :=
    mul_le_mul_of_nonneg_left hlog hU0
  have hcoef : U / a ≤ p / 2 := by
    rw [div_le_iff₀ hapos]
    have heq : p / 2 * a = p / 2 + U := by
      dsimp [a]
      field_simp [hp.ne']
    rw [heq]
    linarith
  have hright : U * (x / a - 1) ≤ (p / 2) * x := by
    calc
      U * (x / a - 1) ≤ U * (x / a) := by
        nlinarith
      _ = (U / a) * x := by ring
      _ ≤ (p / 2) * x :=
        mul_le_mul_of_nonneg_right hcoef hx0
  have hmain :
      U * Real.log x - (p / 2) * x ≤ U * Real.log a := by
    linarith
  have huLog : u * Real.log x ≤ U * Real.log x :=
    mul_le_mul_of_nonneg_right (by simpa [U] using le_abs_self u) hlogx0
  rw [Real.rpow_def_of_pos hxpos]
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [U, a] at hmain ⊢
  nlinarith

/-- Logarithmic exponent cost for absorbing a Mellin power into an exponential
tail. -/
def mellinLogLinearCost (p u : ℝ) : ℝ :=
  |u| * Real.log (1 + 2 * |u| / p)

/-- The positive order-one logarithmic scale used for global xi growth. -/
def xiLogLinearScale (R : ℝ) : ℝ :=
  R * (1 + Real.log (R + 1))

/-- On a bounded real-exponent window, the Mellin cost is controlled by the
uniform xi log-linear scale. -/
lemma mellinLogLinearCost_le_xiLogLinearScale
    {p u R : ℝ} (hp : 0 < p) (hR : 1 ≤ R) (hu : |u| ≤ R) :
    mellinLogLinearCost p u ≤
      (Real.log (max 1 (2 / p)) + 1) * xiLogLinearScale R := by
  let U : ℝ := |u|
  let q : ℝ := max 1 (2 / p)
  have hU0 : 0 ≤ U := by simp [U]
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hq1 : 1 ≤ q := by exact le_max_left _ _
  have hqpos : 0 < q := zero_lt_one.trans_le hq1
  have htwoP0 : 0 ≤ 2 / p := by positivity
  have htwoPq : 2 / p ≤ q := by exact le_max_right _ _
  have hUR : U ≤ R := by simpa [U] using hu
  have hinner : 1 + 2 * U / p ≤ q * (R + 1) := by
    calc
      1 + 2 * U / p = 1 + (2 / p) * U := by ring
      _ ≤ 1 + q * R := by
        gcongr
      _ ≤ q * (R + 1) := by
        nlinarith
  have hinnerOne : 1 ≤ 1 + 2 * U / p := by
    have : 0 ≤ 2 * U / p := by positivity
    linarith
  have hRplus : 0 < R + 1 := by linarith
  have hlogArg :
      Real.log (1 + 2 * U / p) ≤
        Real.log q + Real.log (R + 1) := by
    calc
      Real.log (1 + 2 * U / p) ≤ Real.log (q * (R + 1)) :=
        Real.log_le_log (zero_lt_one.trans_le hinnerOne) hinner
      _ = Real.log q + Real.log (R + 1) := by
        rw [Real.log_mul hqpos.ne' hRplus.ne']
  have hlogArg0 : 0 ≤ Real.log (1 + 2 * U / p) :=
    Real.log_nonneg hinnerOne
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogR0 : 0 ≤ Real.log (R + 1) :=
    Real.log_nonneg (by linarith)
  have hcost :
      U * Real.log (1 + 2 * U / p) ≤
        R * (Real.log q + Real.log (R + 1)) := by
    exact mul_le_mul hUR hlogArg hlogArg0
      hR0
  have hfactor : Real.log q + Real.log (R + 1) ≤
      (Real.log q + 1) * (1 + Real.log (R + 1)) := by
    nlinarith [mul_nonneg hlogq0 hlogR0]
  calc
    mellinLogLinearCost p u =
        U * Real.log (1 + 2 * U / p) := by rfl
    _ ≤ R * (Real.log q + Real.log (R + 1)) := hcost
    _ ≤ R * ((Real.log q + 1) *
        (1 + Real.log (R + 1))) :=
      mul_le_mul_of_nonneg_left hfactor hR0
    _ = (Real.log (max 1 (2 / p)) + 1) *
        xiLogLinearScale R := by
      simp only [q, xiLogLinearScale]
      ring

/-- The upper theta-tail Mellin transform has a log-linear real-exponent
bound. -/
theorem norm_mellin_riemannThetaUpper_le_logLinear
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖mellin riemannThetaUpper s‖ ≤
      (2 * C / p) * Real.exp (mellinLogLinearCost p (s.re - 1)) := by
  let Q : ℝ := mellinLogLinearCost p (s.re - 1)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hhalf : 0 < p / 2 := by positivity
  have hmajorant : IntegrableOn
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (Ioi 0) := by
    change Integrable
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (volume.restrict (Ioi 0))
    exact (exp_neg_integrableOn_Ioi 0 hhalf).const_mul
      (C * Real.exp Q)
  rw [mellin]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) • riemannThetaUpper x‖ ≤
        ∫ x : ℝ in Ioi 0,
          (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx0
      by_cases hx1 : x ≤ 1
      · rw [riemannThetaUpper_eq_zero hx1, smul_zero, norm_zero]
        positivity
      · have hx1' : 1 < x := lt_of_not_ge hx1
        rw [riemannThetaUpper_eq_tail hx1', norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re,
          Complex.one_re]
        calc
          x ^ (s.re - 1) * ‖riemannThetaTail x‖ ≤
              x ^ (s.re - 1) * (C * Real.exp (-p * x)) :=
            mul_le_mul_of_nonneg_left (hbound x hx1'.le)
              (Real.rpow_nonneg hx0.le _)
          _ = C * (x ^ (s.re - 1) * Real.exp (-p * x)) := by ring
          _ ≤ C *
              (Real.exp (mellinLogLinearCost p (s.re - 1)) *
                Real.exp (-(p / 2) * x)) :=
            mul_le_mul_of_nonneg_left
              (by
                simpa [mellinLogLinearCost] using
                  rpow_mul_exp_neg_le_exp_abs_mul_log_mul_exp_neg_half
                    hp hx1'.le (u := s.re - 1))
              hC0
          _ = (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
            simp only [Q]
            ring
    _ = (C * Real.exp Q) * (2 / p) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(p / 2)) (by linarith) 0]
      simp
    _ = (2 * C / p) *
        Real.exp (mellinLogLinearCost p (s.re - 1)) := by
      simp only [Q]
      field_simp [hp.ne']

/-- The split theta--Mellin formula gives global log-linear growth for the
entire completed-zeta regularization. -/
theorem norm_completedRiemannZeta₀_le_logLinear
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤
      (2 * C / p) *
        Real.exp
          ((Real.log (max 1 (2 / p)) + 1) *
            xiLogLinearScale (‖s‖ + 1)) := by
  let R : ℝ := ‖s‖ + 1
  let K : ℝ := 2 * C / p
  let B : ℝ := Real.log (max 1 (2 / p)) + 1
  let Q : ℝ := B * xiLogLinearScale R
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg s]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hfirstAbs : |(s / 2).re - 1| ≤ R := by
    calc
      |(s / 2).re - 1| = |(s.re - 2) / 2| := by
        congr 1
        norm_num
        ring
      _ = |s.re - 2| / 2 := by norm_num [abs_div]
      _ ≤ (|s.re| + 2) / 2 := by
        gcongr
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
          abs_sub s.re 2
      _ ≤ R := by
        dsimp [R]
        nlinarith [norm_nonneg s]
  have hsecondAbs : |((1 - s) / 2).re - 1| ≤ R := by
    calc
      |((1 - s) / 2).re - 1| = |-(s.re + 1) / 2| := by
        congr 1
        norm_num
        ring
      _ = |-(s.re + 1)| / 2 := by
        rw [abs_div]
        norm_num
      _ = |s.re + 1| / 2 := by rw [abs_neg]
      _ ≤ (|s.re| + 1) / 2 := by
        gcongr
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] using
          abs_add_le s.re 1
      _ ≤ R := by
        dsimp [R]
        nlinarith [norm_nonneg s]
  have hfirstCost :
      mellinLogLinearCost p ((s / 2).re - 1) ≤ Q := by
    simpa [B, Q] using
      mellinLogLinearCost_le_xiLogLinearScale hp hR1 hfirstAbs
  have hsecondCost :
      mellinLogLinearCost p (((1 - s) / 2).re - 1) ≤ Q := by
    simpa [B, Q] using
      mellinLogLinearCost_le_xiLogLinearScale hp hR1 hsecondAbs
  have hfirst :
      ‖mellin riemannThetaUpper (s / 2)‖ ≤ K * Real.exp Q := by
    calc
      ‖mellin riemannThetaUpper (s / 2)‖ ≤
          K * Real.exp (mellinLogLinearCost p ((s / 2).re - 1)) := by
        simpa [K] using
          norm_mellin_riemannThetaUpper_le_logLinear hC hp hbound (s / 2)
      _ ≤ K * Real.exp Q :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hfirstCost) hK0
  have hsecond :
      ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤
        K * Real.exp Q := by
    calc
      ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤
          K * Real.exp
            (mellinLogLinearCost p (((1 - s) / 2).re - 1)) := by
        simpa [K] using
          norm_mellin_riemannThetaUpper_le_logLinear
            hC hp hbound ((1 - s) / 2)
      _ ≤ K * Real.exp Q :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsecondCost) hK0
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
          ((Real.log (max 1 (2 / p)) + 1) *
            xiLogLinearScale (‖s‖ + 1)) := by
      simp only [K, Q, B, R]
      ring

/-- Global xi growth on the order-one logarithmic scale. -/
def RiemannXiLogLinearGrowth : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
    ‖riemannXi z‖ ≤
      Real.exp (A * xiLogLinearScale (‖z‖ + 1))

/-- The theta-kernel estimates imply unconditional `exp(O(R log R))` growth
for the pole-cleared xi function. -/
theorem riemannXi_logLinearGrowth : RiemannXiLogLinearGrowth := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  let K : ℝ := max 1 (2 * C / p)
  let B : ℝ := Real.log (max 1 (2 / p)) + 1
  let A : ℝ := K + B + 4
  have hK1 : 1 ≤ K := le_max_left _ _
  have hrawKle : 2 * C / p ≤ K := le_max_right _ _
  have hq1 : 1 ≤ max 1 (2 / p) := le_max_left _ _
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have := Real.log_nonneg hq1
    linarith
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA1, ?_⟩
  intro z
  let R : ℝ := ‖z‖ + 1
  let S : ℝ := xiLogLinearScale R
  let E : ℝ := Real.exp (B * S)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hlog0 : 0 ≤ Real.log (R + 1) :=
    Real.log_nonneg (by linarith)
  have hRleS : R ≤ S := by
    dsimp [S, xiLogLinearScale]
    nlinarith
  have hS1 : 1 ≤ S := hR1.trans hRleS
  have hcompleted : ‖completedRiemannZeta₀ z‖ ≤ K * E := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * C / p) *
            Real.exp
              ((Real.log (max 1 (2 / p)) + 1) *
                xiLogLinearScale (‖z‖ + 1)) :=
        norm_completedRiemannZeta₀_le_logLinear hC hp htail z
      _ = (2 * C / p) * E := by
        simp only [B, E, S, R]
      _ ≤ K * E :=
        mul_le_mul_of_nonneg_right hrawKle (Real.exp_nonneg _)
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
  have hexponent : 1 + K + 2 * R + B * S ≤ A * S := by
    have hKS : 0 ≤ K * (S - 1) :=
      mul_nonneg (zero_le_one.trans hK1) (by linarith)
    have hrest : 0 ≤ 3 * S - 2 * R - 1 := by linarith
    dsimp [A]
    nlinarith
  have habsorb : 2 * (K * R ^ 2 * E) ≤ Real.exp (A * S) := by
    calc
      2 * (K * R ^ 2 * E) = 2 * K * R ^ 2 * E := by ring
      _ ≤ Real.exp 1 * Real.exp K * Real.exp (2 * R) * E := by
        gcongr
      _ = Real.exp (1 + K + 2 * R + B * S) := by
        simp only [E, ← Real.exp_add]
      _ ≤ Real.exp (A * S) := Real.exp_le_exp.mpr hexponent
  unfold riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ K * R ^ 2 * E + 1 := by
      simpa using add_le_add_right hmain 1
    _ ≤ 2 * (K * R ^ 2 * E) := by
      have hRtwo : 1 ≤ R ^ 2 := by nlinarith
      have hE1 : 1 ≤ E := by
        dsimp [E]
        rw [Real.one_le_exp_iff]
        exact mul_nonneg (zero_le_one.trans hB1)
          (zero_le_one.trans hS1)
      have hKRE1 : 1 ≤ K * R ^ 2 * E :=
        one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hK1 hRtwo) hE1
      linarith
    _ ≤ Real.exp (A * S) := habsorb
    _ = Real.exp (A * xiLogLinearScale (‖z‖ + 1)) := by rfl

/-- Jensen's inequality converts log-linear xi growth into a log-linear
centered-disk divisor count. -/
theorem jensen_riemannXi_divisor_le_logLinear
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1))) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * xiLogLinearScale (2 * r + 1) / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hscale0 : 0 ≤ xiLogLinearScale (2 * r + 1) := by
    unfold xiLogLinearScale
    have hbase : 0 ≤ 2 * r + 1 := by linarith
    have hlog : 0 ≤ Real.log ((2 * r + 1) + 1) :=
      Real.log_nonneg (by linarith)
    positivity
  have hM :
      1 ≤ Real.exp (A * xiLogLinearScale (2 * r + 1)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (zero_le_one.trans hA) hscale0
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * xiLogLinearScale (2 * r + 1)))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

/-- A log-linear xi-growth witness supplies one uniform log-linear divisor
count constant. -/
theorem RiemannXiLogLinearGrowth.exists_divisor_bound
    (hGrowth : RiemannXiLogLinearGrowth) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
        A * xiLogLinearScale (2 * r + 1) / Real.log 2 := by
  rcases hGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA, fun r hr ↦
    jensen_riemannXi_divisor_le_logLinear hA hr hbound⟩

/-- Unconditionally, the xi divisor has a centered-disk count of order at most
`R log R`, including analytic multiplicities. -/
theorem exists_riemannXi_divisor_logLinear_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 0 < r →
      ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
        A * xiLogLinearScale (2 * r + 1) / Real.log 2 :=
  riemannXi_logLinearGrowth.exists_divisor_bound

end

end RiemannGaussian
