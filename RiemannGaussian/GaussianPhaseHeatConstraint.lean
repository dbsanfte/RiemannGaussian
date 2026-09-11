/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiCosineAverage
import RiemannGaussian.ZetaPhaseArithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Heat constraints for all summable nonnegative cosine spectra

The positive Fermi Gaussian probability density tests the entire phase
kernel before any spectral mass is discarded. The exact integral of its
product with `1-cos(xi*t)` gives a nonnegative heat deficit at every scale,
for arbitrary real frequencies and countably infinite support. Absolute
summability justifies the full interchange, including accumulating
frequencies. Sending the heat parameter to infinity extracts the actual
frequency masses rather than treating nearby frequencies as identical.
-/

namespace RiemannGaussian.GaussianPhaseHeatConstraint
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiSpectralWeight GaussianFermiCosineAverage

/-- The exact characteristic weight of the positive Fermi Gaussian
probability measure, with its Fermi factor retained. -/
def heatWeight (c x : ℝ) : ℝ := 2 * signal 1 c x

/-- A cosine against the positive averaging density is integrable at
every real frequency. -/
theorem integrable_density_cos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Integrable (fun y : ℝ => density 1 c y * Real.cos (x * y)) := by
  have he (y : ℝ) : Real.cos ((0 - y) * x) = Real.cos (x * y) := by
    rw [zero_sub, neg_mul, Real.cos_neg, mul_comm y x]
  simpa only [he] using integrable_density_cosine (by norm_num : (0 : ℝ) ≤ 1) hc 0 x

/-- The actual probability average evaluates the full characteristic
weight at every real frequency. -/
theorem integral_density_cos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (∫ y : ℝ, density 1 c y * Real.cos (x * y)) = heatWeight c x := by
  have he (y : ℝ) : Real.cos ((0 - y) * x) = Real.cos (x * y) := by
    rw [zero_sub, neg_mul, Real.cos_neg, mul_comm y x]
  simpa only [heatWeight, he, zero_mul, Real.cos_zero, mul_one] using
    integral_density_cosine (by norm_num : (0 : ℝ) ≤ 1) hc 0 x

/-- The characteristic weight stays between zero and one. Its upper
bound follows from positivity and exact unit mass of the actual density. -/
theorem heatWeight_bounds {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 ≤ heatWeight c x ∧ heatWeight c x ≤ 1 := by
  constructor
  · exact mul_nonneg (by norm_num) (signal_pos 1 c x).le
  · calc
      _ = ∫ y : ℝ, density 1 c y * Real.cos (x * y) := (integral_density_cos hc x).symm
      _ ≤ ∫ y : ℝ, density 1 c y := by
        apply integral_mono (integrable_density_cos hc x)
          (integrable_density (by norm_num : (0 : ℝ) ≤ 1) hc)
        intro y
        exact mul_le_of_le_one_right (density_nonneg (by norm_num) hc y) (Real.cos_le_one _)
      _ = 1 := integral_density (by norm_num : (0 : ℝ) ≤ 1) hc

/-- The signed spectral test whose full sum is nonnegative for a
nonnegative phase kernel. -/
def probe (c x ξ y : ℝ) : ℝ :=
  density 1 c y * Real.cos (x * y) * (1 - Real.cos (ξ * y))

/-- The exact product-to-sum identity retains the central frequency and
both translated frequencies before an estimate is applied. -/
theorem probe_eq (c x ξ y : ℝ) :
    probe c x ξ y = density 1 c y * Real.cos (x * y) -
      (density 1 c y * Real.cos ((x + ξ) * y) +
        density 1 c y * Real.cos ((x - ξ) * y)) / 2 := by
  unfold probe
  rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
  ring

/-- Every individual signed test has genuine absolute integrability. -/
theorem integrable_probe {c : ℝ} (hc : 0 < c) (x ξ : ℝ) : Integrable (probe c x ξ) := by
  have he : probe c x ξ = fun y => density 1 c y * Real.cos (x * y) -
      (density 1 c y * Real.cos ((x + ξ) * y) +
        density 1 c y * Real.cos ((x - ξ) * y)) / 2 := funext (probe_eq c x ξ)
  rw [he]
  exact (integrable_density_cos hc x).sub
    (((integrable_density_cos hc (x + ξ)).add (integrable_density_cos hc (x - ξ))).div_const 2)

/-- The exact test integral is a central heat weight minus the mean of
the two translated weights. -/
theorem integral_probe {c : ℝ} (hc : 0 < c) (x ξ : ℝ) :
    (∫ y : ℝ, probe c x ξ y) =
      heatWeight c x - (heatWeight c (x + ξ) + heatWeight c (x - ξ)) / 2 := by
  have he : probe c x ξ = fun y => density 1 c y * Real.cos (x * y) -
      (density 1 c y * Real.cos ((x + ξ) * y) +
        density 1 c y * Real.cos ((x - ξ) * y)) / 2 := funext (probe_eq c x ξ)
  have hi : Integrable (fun y : ℝ => (density 1 c y * Real.cos ((x + ξ) * y) +
      density 1 c y * Real.cos ((x - ξ) * y)) / 2) :=
    ((integrable_density_cos hc (x + ξ)).add (integrable_density_cos hc (x - ξ))).div_const 2
  rw [he]
  dsimp only
  rw [integral_sub (integrable_density_cos hc x) hi,
    integral_div, integral_add (integrable_density_cos hc (x + ξ)) (integrable_density_cos hc (x - ξ)),
    integral_density_cos hc, integral_density_cos hc, integral_density_cos hc]

/-- One positive integrable envelope controls every frequency, with no
frequency separation assumption. -/
theorem norm_probe_le {c : ℝ} (hc : 0 < c) (x ξ y : ℝ) :
    ‖probe c x ξ y‖ ≤ 2 * density 1 c y := by
  have hd := density_nonneg (by norm_num : (0 : ℝ) < 1) hc y
  have hcos : 0 ≤ 1 - Real.cos (ξ * y) := by linarith [Real.cos_le_one (ξ * y)]
  have hcosu : 1 - Real.cos (ξ * y) ≤ 2 := by linarith [Real.neg_one_le_cos (ξ * y)]
  rw [probe, norm_mul, norm_mul, Real.norm_of_nonneg hd, Real.norm_of_nonneg hcos]
  calc
    _ ≤ (density 1 c y * 1) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x * y)) hd) hcosu hcos (by positivity)
    _ = _ := by ring

/-- The full family of integral norms has an explicit summable envelope.
This pays for the countable spectral/integral interchange. -/
theorem summable_integral_norm_probe {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    Summable (fun n : ℕ => ∫ y : ℝ, ‖a n * probe c (ω n) ξ y‖) := by
  apply (hs.mul_left 2).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
  intro n
  have hpoint (y : ℝ) : ‖a n * probe c (ω n) ξ y‖ ≤ (2 * a n) * density 1 c y := by
    rw [norm_mul, Real.norm_of_nonneg (ha n)]
    exact (mul_le_mul_of_nonneg_left (norm_probe_le hc (ω n) ξ y) (ha n)).trans_eq (by ring)
  have h := integral_mono ((integrable_probe hc (ω n) ξ).const_mul (a n)).norm
    ((integrable_density (by norm_num : (0 : ℝ) ≤ 1) hc).const_mul (2 * a n)) hpoint
  simpa only [integral_const_mul, integral_density (by norm_num : (0 : ℝ) ≤ 1) hc, mul_one] using h

/-- Exact evaluation of the full signed heat test. The complete kernel
and both translated frequency channels are retained before using its sign. -/
theorem heat_deficit_eq_integral {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    (∑' n : ℕ, a n * (heatWeight c (ω n) -
      (heatWeight c (ω n + ξ) + heatWeight c (ω n - ξ)) / 2)) =
      ∫ y : ℝ, density 1 c y * zetaPhaseKernel a ω y * (1 - Real.cos (ξ * y)) := by
  have hsum := integral_tsum_of_summable_integral_norm
    (fun n => (integrable_probe hc (ω n) ξ).const_mul (a n))
    (summable_integral_norm_probe ha hs hc ξ)
  have he (y : ℝ) : (∑' n : ℕ, a n * probe c (ω n) ξ y) =
      density 1 c y * zetaPhaseKernel a ω y * (1 - Real.cos (ξ * y)) := by
    unfold zetaPhaseKernel
    rw [← tsum_mul_left, ← tsum_mul_right]
    apply tsum_congr
    intro n
    unfold probe
    ring
  simpa only [integral_const_mul, integral_probe hc, he] using hsum

/-- Every nonnegative phase kernel obeys this exact heat constraint at
every positive scale, for arbitrary real frequencies and all summable
nonnegative coefficient families, including infinite support. -/
theorem heat_deficit_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ y : ℝ, 0 ≤ zetaPhaseKernel a ω y) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    0 ≤ ∑' n : ℕ, a n * (heatWeight c (ω n) -
      (heatWeight c (ω n + ξ) + heatWeight c (ω n - ξ)) / 2) := by
  rw [heat_deficit_eq_integral ha hs hc ξ]
  apply integral_nonneg
  intro y
  exact mul_nonneg (mul_nonneg (density_nonneg (by norm_num) hc y) (hp y))
    (by linarith [Real.cos_le_one (ξ * y)])

/-- The Gaussian parameter factors exactly from the fixed Fermi weight. -/
theorem heatWeight_factor (c x : ℝ) :
    heatWeight c x = Real.exp (-c * x ^ 2) * heatWeight 0 x := by
  unfold heatWeight signal GaussianFermiDerivativeBounds.damped
  rw [sub_eq_add_neg, Real.exp_add]
  simp only [neg_zero, zero_mul, zero_sub]
  ring

/-- Infinite heat time extracts a frequency exactly. Accumulating
frequencies are handled later by summable domination, not separation. -/
theorem tendsto_heatWeight (x : ℝ) :
    Tendsto (fun c : ℝ => heatWeight c x) atTop (𝓝 (if x = 0 then 1 else 0)) := by
  by_cases hx : x = 0
  · simp only [hx, heatWeight, signal_zero, mul_one_div, div_self (by norm_num : (2 : ℝ) ≠ 0),
      ↓reduceIte]
    exact tendsto_const_nhds
  · have he : Tendsto (fun c : ℝ => Real.exp (-c * x ^ 2)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp
        (tendsto_id.atTop_mul_const_of_neg (neg_neg_of_pos (sq_pos_of_ne_zero hx)))
      simpa only [Function.comp_def, id_eq, mul_neg, neg_mul] using h
    have hf : (fun c : ℝ => heatWeight c x) =
        (fun c : ℝ => Real.exp (-c * x ^ 2) * heatWeight 0 x) := funext fun c => heatWeight_factor c x
    rw [hf, if_neg hx]
    simpa only [zero_mul] using he.mul_const (heatWeight 0 x)

/-- The total coefficient mass at one exact real frequency. Repeated
frequencies are deliberately combined. -/
def frequencyMass (a ω : ℕ → ℝ) (ξ : ℝ) : ℝ :=
  ∑' n : ℕ, if ω n = ξ then a n else 0

/-- Restriction to any exact frequency preserves genuine summability. -/
theorem summable_frequencyMass_terms {a ω : ℕ → ℝ} (hs : Summable a) (ξ : ℝ) :
    Summable (fun n : ℕ => if ω n = ξ then a n else 0) := by
  apply hs.norm.of_norm_bounded
  intro n
  split_ifs <;> simp

/-- Every exact frequency mass is nonnegative. -/
theorem frequencyMass_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ξ : ℝ) :
    0 ≤ frequencyMass a ω ξ := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact ha n
  · exact le_rfl

/-- A heat average of the spectrum centered at an arbitrary real frequency. -/
def heatMass (a ω : ℕ → ℝ) (c ξ : ℝ) : ℝ :=
  ∑' n : ℕ, a n * heatWeight c (ω n - ξ)

/-- The full translated heat spectrum has the original coefficient
sequence as a summable envelope. -/
theorem summable_heatMass_terms {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    Summable (fun n : ℕ => a n * heatWeight c (ω n - ξ)) := by
  apply hs.of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (heatWeight_bounds hc _).1
  · intro n
    exact mul_le_of_le_one_right (ha n) (heatWeight_bounds hc _).2

/-- The entire heat spectrum converges to its exact frequency mass,
including for infinitely many accumulating or repeated frequencies. -/
theorem tendsto_heatMass {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (ξ : ℝ) :
    Tendsto (fun c : ℝ => heatMass a ω c ξ) atTop (𝓝 (frequencyMass a ω ξ)) := by
  have hp (n : ℕ) : Tendsto (fun c : ℝ => a n * heatWeight c (ω n - ξ)) atTop
      (𝓝 (if ω n = ξ then a n else 0)) := by
    simpa only [mul_ite, mul_one, mul_zero, sub_eq_zero] using
      (tendsto_heatWeight (ω n - ξ)).const_mul (a n)
  have hd : ∀ᶠ c : ℝ in atTop, ∀ n : ℕ, ‖a n * heatWeight c (ω n - ξ)‖ ≤ a n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc n
    rw [Real.norm_of_nonneg (mul_nonneg (ha n) (heatWeight_bounds hc _).1)]
    exact mul_le_of_le_one_right (ha n) (heatWeight_bounds hc _).2
  exact tendsto_tsum_of_dominated_convergence hs hp hd

/-- The finite-scale constraint compares the actual translated spectral
masses before taking any limit or forgetting nearby frequencies. -/
theorem heatMass_deficit_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ y : ℝ, 0 ≤ zetaPhaseKernel a ω y) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    0 ≤ heatMass a ω c 0 - (heatMass a ω c (-ξ) + heatMass a ω c ξ) / 2 := by
  have h0 : Summable (fun n : ℕ => a n * heatWeight c (ω n)) := by
    simpa only [sub_zero] using summable_heatMass_terms ha hs hc 0
  have hplus : Summable (fun n : ℕ => a n * heatWeight c (ω n + ξ)) := by
    simpa only [sub_neg_eq_add] using summable_heatMass_terms ha hs hc (-ξ)
  have hminus := summable_heatMass_terms (ω := ω) ha hs hc ξ
  have he : (fun n : ℕ => a n * (heatWeight c (ω n) -
      (heatWeight c (ω n + ξ) + heatWeight c (ω n - ξ)) / 2)) =
      (fun n : ℕ => a n * heatWeight c (ω n) -
        (a n * heatWeight c (ω n + ξ) + a n * heatWeight c (ω n - ξ)) / 2) := by
    funext n
    ring
  have h := heat_deficit_nonneg ha hs hp hc ξ
  rw [he, h0.tsum_sub ((hplus.add hminus).div_const 2), tsum_div_const,
    hplus.tsum_add hminus] at h
  simpa only [heatMass, sub_zero, sub_neg_eq_add] using h

/-- Every nonnegative summable cosine kernel has at most twice its
constant mass at any pair of opposite frequencies. No assumption on the
number, spacing or integrality of its frequencies is used. -/
theorem opposite_frequencyMass_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ y : ℝ, 0 ≤ zetaPhaseKernel a ω y) (ξ : ℝ) :
    frequencyMass a ω ξ + frequencyMass a ω (-ξ) ≤ 2 * frequencyMass a ω 0 := by
  have ht := (tendsto_heatMass (ω := ω) ha hs 0).sub
    (((tendsto_heatMass (ω := ω) ha hs (-ξ)).add
      (tendsto_heatMass (ω := ω) ha hs ξ)).div_const 2)
  have hn : 0 ≤ frequencyMass a ω 0 -
      (frequencyMass a ω (-ξ) + frequencyMass a ω ξ) / 2 := by
    apply ge_of_tendsto ht
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact heatMass_deficit_nonneg ha hs hp hc ξ
  linarith

/-- The coefficient mass at every nonzero frequency, without a frequency
size weight. This is the leading gamma mass in the Gaussian profile. -/
def nonconstantMass (a ω : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, if ω n ≠ 0 then a n else 0

/-- The nonconstant spectrum is still genuinely summable. -/
theorem summable_nonconstantMass_terms {a ω : ℕ → ℝ} (hs : Summable a) :
    Summable (fun n : ℕ => if ω n ≠ 0 then a n else 0) := by
  apply hs.norm.of_norm_bounded
  intro n
  split_ifs <;> simp

/-- An opposite pair of nonzero frequencies cannot exceed the total
nonconstant mass, even when each frequency occurs infinitely often. -/
theorem opposite_frequencyMass_le_nonconstantMass {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {ξ : ℝ} (hξ : ξ ≠ 0) :
    frequencyMass a ω ξ + frequencyMass a ω (-ξ) ≤ nonconstantMass a ω := by
  unfold frequencyMass nonconstantMass
  rw [← (summable_frequencyMass_terms hs ξ).tsum_add (summable_frequencyMass_terms hs (-ξ))]
  apply Summable.tsum_le_tsum _
    ((summable_frequencyMass_terms hs ξ).add (summable_frequencyMass_terms hs (-ξ)))
    (summable_nonconstantMass_terms hs)
  intro n
  by_cases hpos : ω n = ξ
  · have hneg : ω n ≠ -ξ := by intro h; rw [hpos] at h; apply hξ; linarith
    have hz : ω n ≠ 0 := by rwa [hpos]
    rw [if_pos hpos, if_neg hneg, if_pos hz, add_zero]
  · by_cases hneg : ω n = -ξ
    · have hz : ω n ≠ 0 := by rw [hneg]; exact neg_ne_zero.mpr hξ
      rw [if_neg hpos, if_pos hneg, if_pos hz, zero_add]
    · rw [if_neg hpos, if_neg hneg, zero_add]
      split_ifs
      · exact ha n
      · exact le_rfl

end
end RiemannGaussian.GaussianPhaseHeatConstraint
