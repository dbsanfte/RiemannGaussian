/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiBalancedBlockBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A source-sensitive control for joined Suzuki excursion estimates

This is a continuous tail model, not the ordinary integer prime measure.
Its weighted mass has eventually positive density. Its signal has the exact
mass/moment work law and exact balance at a sequence of growing cutoffs.
Nevertheless the joined work minus entropy has negative power excursions.

Thus positivity, balance, the full joint ledger and grouping by complete
phase periods do not by themselves prove a subpolynomial arithmetic floor.
No statement about actual prime excursion depth or zero exclusion is made.
-/

namespace RiemannGaussian.SuzukiJoinedExcursionAudit
noncomputable section
open Filter
open scoped Topology

/-- Model weighted prime mass. `c` is the unchanged affine slope constant. -/
def modelMass (α γ c t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) + c - (2 / γ) * Real.exp (α * t) * Real.sin (γ * t)

/-- Density relative to the continuous unit von Mangoldt density. -/
def modelDensity (α γ t : ℝ) : ℝ :=
  1 - (2 / γ) * Real.exp ((α - 1 / 2) * t) *
    (α * Real.sin (γ * t) + γ * Real.cos (γ * t))

/-- Signed signal with the exact derivative `smooth mass - modelMass`. -/
def modelSignal (α γ b t : ℝ) : ℝ :=
  b + (2 / γ) / (α ^ 2 + γ ^ 2) * Real.exp (α * t) *
    (α * Real.sin (γ * t) - γ * Real.cos (γ * t))

/-- The corresponding logarithmic moment; its derivative is `t * mass'`. -/
def modelLogMoment (α γ c b t : ℝ) : ℝ :=
  modelSignal α γ b t - 4 * Real.exp (t / 2) - c * t - b +
    t * modelMass α γ c t

/-- Same finite mass potential as in the arithmetic Suzuki ledger. -/
def modelPotential (α γ c b t : ℝ) : ℝ :=
  modelLogMoment α γ c b t -
    2 * (modelMass α γ c t - c) *
      (Real.log ((modelMass α γ c t - c) / 2) - 1) + b

/-- Exact complete phase periods at which the corrected model mass balances. -/
def balancedTime (γ : ℝ) (n : ℕ) : ℝ := (n : ℝ) * (2 * Real.pi) / γ

/-- The common initial mass center is retained across the complete block. -/
def modelCenteredWork (α γ c b start finish : ℝ) : ℝ :=
  modelLogMoment α γ c b finish - modelLogMoment α γ c b start -
    2 * Real.log ((modelMass α γ c start - c) / 2) *
      (modelMass α γ c finish - modelMass α γ c start)

/-- The model satisfies the full signed work/entropy law, including the
whole block mass and its cross interactions. -/
theorem modelPotential_sub_eq_centeredWork_sub_entropy
    {α γ c b start finish : ℝ}
    (hs : 0 < modelMass α γ c start - c)
    (ht : 0 < modelMass α γ c finish - c) :
    modelPotential α γ c b finish - modelPotential α γ c b start =
      modelCenteredWork α γ c b start finish -
        2 * ((modelMass α γ c finish - c) *
          Real.log ((modelMass α γ c finish - c) / (modelMass α γ c start - c)) -
            (modelMass α γ c finish - modelMass α γ c start)) := by
  have he : Real.log ((modelMass α γ c finish - c) / 2) =
      Real.log ((modelMass α γ c start - c) / 2) +
        Real.log ((modelMass α γ c finish - c) / (modelMass α γ c start - c)) := by
    rw [Real.log_div ht.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hs.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_div ht.ne' hs.ne']
    ring
  unfold modelPotential modelCenteredWork
  rw [he]
  ring

private theorem denominator_pos {α γ : ℝ} (hγ : 0 < γ) :
    0 < α ^ 2 + γ ^ 2 := by positivity

theorem hasDerivAt_modelSignal {α γ b t : ℝ} (hγ : 0 < γ) :
    HasDerivAt (modelSignal α γ b)
      ((2 / γ) * Real.exp (α * t) * Real.sin (γ * t)) t := by
  have he := (Real.hasDerivAt_exp (α * t)).comp t ((hasDerivAt_id t).const_mul α)
  have hs := (Real.hasDerivAt_sin (γ * t)).comp t ((hasDerivAt_id t).const_mul γ)
  have hc := (Real.hasDerivAt_cos (γ * t)).comp t ((hasDerivAt_id t).const_mul γ)
  have h := ((he.const_mul ((2 / γ) / (α ^ 2 + γ ^ 2))).mul
    ((hs.const_mul α).sub (hc.const_mul γ))).const_add b
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · dsimp
    field_simp [(denominator_pos hγ).ne']
    ring
  · filter_upwards with x
    dsimp [modelSignal]

theorem hasDerivAt_modelMass (α γ c t : ℝ) :
    HasDerivAt (modelMass α γ c)
      (Real.exp (t / 2) * modelDensity α γ t) t := by
  have he := (Real.hasDerivAt_exp (α * t)).comp t ((hasDerivAt_id t).const_mul α)
  have hs := (Real.hasDerivAt_sin (γ * t)).comp t ((hasDerivAt_id t).const_mul γ)
  have hh := (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  have h := ((hh.const_mul 2).add_const c).sub ((he.mul hs).const_mul (2 / γ))
  have heq : Real.exp (t / 2) * Real.exp ((α - 1 / 2) * t) =
      Real.exp (α * t) := by rw [← Real.exp_add]; congr 1; ring
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · dsimp [modelDensity]
    rw [show Real.exp (t / 2) *
      (1 - 2 / γ * Real.exp ((α - 1 / 2) * t) *
        (α * Real.sin (γ * t) + γ * Real.cos (γ * t))) =
        Real.exp (t / 2) - 2 / γ *
          (Real.exp (t / 2) * Real.exp ((α - 1 / 2) * t)) *
            (α * Real.sin (γ * t) + γ * Real.cos (γ * t)) by ring, heq]
    ring
  · filter_upwards with x
    dsimp [modelMass]
    ring

/-- The two model moment channels have the required common derivative.
They are not arbitrary independent mass and work assignments. -/
theorem hasDerivAt_modelLogMoment {α γ c b t : ℝ} (hγ : 0 < γ) :
    HasDerivAt (modelLogMoment α γ c b)
      (t * (Real.exp (t / 2) * modelDensity α γ t)) t := by
  have hh := (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  have hf := (((hasDerivAt_modelSignal (α := α) (b := b) (t := t) hγ).sub
    (hh.const_mul 4)).sub ((hasDerivAt_id t).const_mul c)).sub_const b
  have h := hf.add ((hasDerivAt_id t).mul (hasDerivAt_modelMass α γ c t))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · dsimp [modelMass]
    ring
  · filter_upwards with x
    dsimp [modelLogMoment]

/-- For every positive sub-square-root growth exponent, the control has
uniformly positive density on a sufficiently late tail. -/
theorem eventually_modelDensity_ge_half {α γ : ℝ}
    (hα : 0 < α) (hαhalf : α < 1 / 2) (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, 1 / 2 ≤ modelDensity α γ t := by
  have he : Tendsto (fun t : ℝ => Real.exp ((α - 1 / 2) * t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < 1 / 2 - α))
    convert! h using 1
    ext t
    dsimp
    congr 1
    ring
  have hbound := he.eventually (gt_mem_nhds
    (by positivity : (0 : ℝ) < γ / (4 * (α + γ))))
  filter_upwards [hbound] with t ht
  have htrig : α * Real.sin (γ * t) + γ * Real.cos (γ * t) ≤ α + γ :=
    add_le_add (mul_le_of_le_one_right hα.le (Real.sin_le_one _))
      (mul_le_of_le_one_right hγ.le (Real.cos_le_one _))
  have hcoef : 0 ≤ (2 / γ) * Real.exp ((α - 1 / 2) * t) := by positivity
  have hp := mul_le_mul_of_nonneg_left htrig hcoef
  have hexp := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (α + γ))).mp ht
  have hcost : (2 / γ) * Real.exp ((α - 1 / 2) * t) * (α + γ) ≤ 1 / 2 := by
    apply (mul_le_mul_iff_left₀ hγ).mp
    have heq : (2 / γ * Real.exp ((α - 1 / 2) * t) * (α + γ)) * γ =
        2 * Real.exp ((α - 1 / 2) * t) * (α + γ) := by field_simp
    rw [heq]
    nlinarith
  dsimp [modelDensity]
  linarith

private theorem phase_at_balancedTime {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    γ * balancedTime γ n = (n : ℝ) * (2 * Real.pi) := by
  unfold balancedTime
  field_simp

theorem modelMass_at_balancedTime {γ : ℝ} (hγ : 0 < γ) (α c : ℝ) (n : ℕ) :
    modelMass α γ c (balancedTime γ n) - c =
      2 * Real.exp (balancedTime γ n / 2) := by
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_nat_mul_two_pi 0 n
  simp [modelMass, phase_at_balancedTime hγ, hs]

theorem modelSignal_at_balancedTime {γ : ℝ} (hγ : 0 < γ) (α b : ℝ) (n : ℕ) :
    modelSignal α γ b (balancedTime γ n) =
      b - (2 / (α ^ 2 + γ ^ 2)) * Real.exp (α * balancedTime γ n) := by
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_nat_mul_two_pi 0 n
  simp only [modelSignal, phase_at_balancedTime hγ, hs, Real.cos_nat_mul_two_pi,
    mul_zero, mul_one, zero_sub]
  field_simp
  ring

theorem modelPotential_at_balancedTime {γ : ℝ} (hγ : 0 < γ) (α c b : ℝ) (n : ℕ) :
    modelPotential α γ c b (balancedTime γ n) =
      modelSignal α γ b (balancedTime γ n) := by
  have hm := modelMass_at_balancedTime hγ α c n
  unfold modelPotential modelLogMoment
  rw [hm]
  have hlog : Real.log (2 * Real.exp (balancedTime γ n / 2) / 2) =
      balancedTime γ n / 2 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp]
  rw [hlog]
  have hm' : modelMass α γ c (balancedTime γ n) =
      c + 2 * Real.exp (balancedTime γ n / 2) := by linarith
  rw [hm']
  ring

theorem tendsto_balancedTime {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (balancedTime γ) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact (hn.atTop_mul_const (mul_pos (by norm_num) Real.pi_pos)).atTop_div_const hγ

/-- The source survives after exact balance and joined work accounting. -/
theorem tendsto_normalized_modelPotential {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (c b : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-α * balancedTime γ n) *
      modelPotential α γ c b (balancedTime γ n)) atTop
        (𝓝 (-(2 / (α ^ 2 + γ ^ 2)))) := by
  have he : Tendsto (fun n : ℕ => Real.exp (-α * balancedTime γ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_balancedTime hγ).const_mul_atTop hα)
  have h := (he.mul_const b).sub_const (2 / (α ^ 2 + γ ^ 2))
  convert h using 1
  · ext n
    rw [modelPotential_at_balancedTime hγ, modelSignal_at_balancedTime hγ]
    rw [mul_sub, ← mul_assoc, mul_comm (Real.exp _) (2 / _), mul_assoc,
      ← Real.exp_add]
    simp
  · simp

/-- Every allowance of smaller power fails even at the exactly balanced
phase points, despite eventually positive density and the joined ledger. -/
theorem eventually_modelPotential_lt_smaller_power {α γ δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hδ : δ < α) (c b C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      modelPotential α γ c b (balancedTime γ n) <
        -(C * Real.exp (δ * balancedTime γ n)) := by
  let d := 2 / (α ^ 2 + γ ^ 2)
  have hd : 0 < d := by dsimp [d]; exact div_pos (by norm_num) (denominator_pos hγ)
  have hsource := (tendsto_normalized_modelPotential hα hγ c b).eventually
    (gt_mem_nhds (show -d < -d / 2 by linarith))
  have he : Tendsto (fun n : ℕ => Real.exp ((δ - α) * balancedTime γ n))
      atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_balancedTime hγ).const_mul_atTop (by linarith : 0 < α - δ))
    convert! ht using 1
    ext n
    dsimp
    congr 1
    ring
  have hallow := (he.const_mul (-C)).eventually
    (lt_mem_nhds (show -d / 2 < -C * 0 by linarith))
  filter_upwards [hsource, hallow] with n hs ha
  have hr : Real.exp (-α * balancedTime γ n) *
      (-(C * Real.exp (δ * balancedTime γ n))) =
        -C * Real.exp ((δ - α) * balancedTime γ n) := by
    calc
      _ = -C * (Real.exp (-α * balancedTime γ n) *
        Real.exp (δ * balancedTime γ n)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  apply (mul_lt_mul_iff_right₀ (Real.exp_pos (-α * balancedTime γ n))).mp
  rw [hr]
  linarith

theorem not_eventual_modelPotential_smaller_power_floor {α γ δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hδ : δ < α) (c b : ℝ) :
    ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      -(C * Real.exp (δ * balancedTime γ n)) ≤
        modelPotential α γ c b (balancedTime γ n) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn, hl⟩ := (hC.and
    (eventually_modelPotential_lt_smaller_power hα hγ hδ c b C)).exists
  exact (not_lt_of_ge hn) hl

/-- Arithmetic time-kernel coordinates, distinct from an automatically
positive Gram matrix of pre-existing Hilbert vectors. -/
def timeKernel (f : ℝ → ℝ) (s t : ℝ) : ℝ := f s + f t - f (s - t)

/-- The full quadratic along the equal-weight direction at nodes `t,-t`. -/
def twoNodeJoined (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  timeKernel f t t + timeKernel f t (-t) +
    timeKernel f (-t) t + timeKernel f (-t) (-t)

/-- The two-node even test retains a cross-scale constraint which scalar
nonnegativity alone does not imply for a generic function. -/
theorem twoNodeJoined_eq_dilation {f : ℝ → ℝ} (h0 : f 0 = 0)
    (heven : ∀ t, f (-t) = f t) (t : ℝ) :
    twoNodeJoined f t = 2 * (4 * f t - f (2 * t)) := by
  have hpos : t - -t = 2 * t := by ring
  have hneg : -t - t = -(2 * t) := by ring
  simp only [twoNodeJoined, timeKernel, sub_self, h0, hpos, hneg, heven t, heven (2 * t)]
  ring

theorem dilation_le_of_twoNodeJoined_nonneg {f : ℝ → ℝ}
    (h0 : f 0 = 0) (heven : ∀ t, f (-t) = f t) {t : ℝ}
    (h : 0 ≤ twoNodeJoined f t) : f (2 * t) ≤ 4 * f t := by
  rw [twoNodeJoined_eq_dilation h0 heven] at h
  linarith

/-- Generic scalar positivity is insufficient for time-kernel positivity. -/
theorem nonnegative_even_control_has_negative_twoNodeJoined :
    (∀ t : ℝ, 0 ≤ t ^ 4) ∧ twoNodeJoined (fun t : ℝ => t ^ 4) 1 = -24 := by
  constructor
  · intro t
    positivity
  · norm_num [twoNodeJoined, timeKernel]

/-- A critical-line cosine mode satisfies the dilation constraint exactly. -/
theorem critical_cosine_dilation (x : ℝ) :
    4 * (1 - Real.cos x) - (1 - Real.cos (2 * x)) =
      2 * (1 - Real.cos x) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

theorem critical_cosine_dilation_nonneg (x : ℝ) :
    0 ≤ 4 * (1 - Real.cos x) - (1 - Real.cos (2 * x)) := by
  rw [critical_cosine_dilation]
  positivity

/-- The same dilation test applies to the repository's literal arithmetic
Suzuki function, with its prime powers and full completion unchanged. -/
theorem arithmetic_twoNodeJoined_eq_dilation (t : ℝ) :
    twoNodeJoined riemannXiSuzukiPsi t =
      2 * (4 * riemannXiSuzukiPsi t - riemannXiSuzukiPsi (2 * t)) :=
  twoNodeJoined_eq_dilation riemannXiSuzukiPsi_zero riemannXiSuzukiPsi_neg t

/-- A three-coordinate diagnostic: every two-coordinate restriction is
nonnegative, whereas the joined three-coordinate direction can be negative. -/
def threeCoordinateControl (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 - (3 / 2) * (x * y + x * z + y * z)

theorem threeCoordinateControl_pairwise_nonnegative (x y : ℝ) :
    0 ≤ threeCoordinateControl x y 0 ∧
      0 ≤ threeCoordinateControl x 0 y ∧ 0 ≤ threeCoordinateControl 0 x y := by
  have h : 0 ≤ x ^ 2 + y ^ 2 - (3 / 2) * (x * y) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
  dsimp [threeCoordinateControl]
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem threeCoordinateControl_joined_negative :
    threeCoordinateControl 1 1 1 = -(3 / 2) := by
  norm_num [threeCoordinateControl]

end
end RiemannGaussian.SuzukiJoinedExcursionAudit
