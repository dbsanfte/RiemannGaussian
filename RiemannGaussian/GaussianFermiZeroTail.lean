/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPairDecay
import RiemannGaussian.GaussianXiInverseSquareSummability
import RiemannGaussian.GaussianXiDivisorContour
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The actual multiplicity-weighted Gaussian Fermi zero tail

Outside a band containing twice the evaluation height, the exact paired
real contribution is dominated by the already summable zeta divisor
weight. The factor `1/2` records that summing reflected pairs over all
zeros counts each partner twice. No unpaired complex zero-sum identity
or smoothed prime explicit formula is assumed.
-/

namespace RiemannGaussian.GaussianFermiZeroTail

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiDerivativeBounds GaussianFermiPairDecay

/-- The real contribution of one reflected pair, with analytic multiplicity
and the factor correcting for the two occurrences of each pair. -/
def contribution (b σ t : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity ρ : ℝ) / 2 *
    (transform (2 * σ - 1) (window b) ((σ : ℂ) + (t : ℂ) * I - ρ.1) +
      transform (2 * σ - 1) (window b)
        ((σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1))).re

/-- The literal portion outside the stated height band. -/
def outside (b σ t H : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  if H < |ρ.1.im| then contribution b σ t ρ else 0

/-- The original paired contribution restricted to the finite height band. -/
def inside (b σ t H : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  if |ρ.1.im| ≤ H then contribution b σ t ρ else 0

/-- The existing summable multiplicity-weighted zeta divisor majorant. -/
def divisorWeight (ρ : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity ρ : ℝ) / (1 + ρ.1.im ^ 2)

/-- The actual tail of that positive divisor weight. -/
def divisorTail (H : ℝ) : ℝ :=
  ∑' ρ : NontrivialZetaZero, if H < |ρ.1.im| then divisorWeight ρ else 0

/-- The canonical inverse-square weight includes analytic multiplicities. -/
theorem summable_divisorWeight : Summable divisorWeight := by
  change Summable (fun ρ : NontrivialZetaZero => (analyticZetaZeroMultiplicity ρ : ℝ) /
    (1 + ρ.1.im ^ 2))
  simpa only [zetaSpectralCoordinate_re] using
    summable_distinct_zetaZeroInverseSquareSpectralRe

/-- Every summand of the divisor tail is nonnegative. -/
theorem divisorWeight_nonneg (ρ : NontrivialZetaZero) : 0 ≤ divisorWeight ρ := by
  unfold divisorWeight
  positivity

/-- Every height-restricted divisor weight is genuinely summable. -/
theorem summable_divisorTail_terms (H : ℝ) :
    Summable (fun ρ : NontrivialZetaZero => if H < |ρ.1.im| then divisorWeight ρ else 0) := by
  apply summable_divisorWeight.of_nonneg_of_le
  · intro ρ
    split_ifs <;> positivity [divisorWeight_nonneg ρ]
  · intro ρ
    split_ifs <;> simp [divisorWeight_nonneg]

/-- Sending the actual height cutoff to infinity kills the divisor tail. -/
theorem tendsto_divisorTail : Tendsto divisorTail atTop (𝓝 0) := by
  have hp (ρ : NontrivialZetaZero) :
      Tendsto (fun H : ℝ => if H < |ρ.1.im| then divisorWeight ρ else 0) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop |ρ.1.im|] with H hH
    simp [not_lt.mpr hH]
  have hd : ∀ᶠ H : ℝ in atTop, ∀ ρ : NontrivialZetaZero,
      ‖if H < |ρ.1.im| then divisorWeight ρ else 0‖ ≤ divisorWeight ρ := by
    exact Eventually.of_forall fun H ρ => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (divisorWeight_nonneg ρ),
        divisorWeight_nonneg]
  change Tendsto (fun H : ℝ => ∑' ρ : NontrivialZetaZero,
    if H < |ρ.1.im| then divisorWeight ρ else 0) atTop (𝓝 0)
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence summable_divisorWeight hp hd

private theorem separated_gap {t γ : ℝ} (ht : 2 * |t| ≤ |γ|) (hγ : 1 ≤ |γ|) :
    t - γ ≠ 0 ∧ 1 + γ ^ 2 ≤ 8 * (t - γ) ^ 2 := by
  have htriangle : |γ| ≤ |t - γ| + |t| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (γ - t) t
  have hgap : |γ| ≤ 2 * |t - γ| := by linarith
  have hsq := (sq_le_sq₀ (abs_nonneg γ) (by positivity : 0 ≤ 2 * |t - γ|)).mpr hgap
  simp only [mul_pow, sq_abs] at hsq
  have hγsq : 1 ≤ γ ^ 2 := by nlinarith [sq_abs γ]
  refine ⟨?_, by nlinarith⟩
  intro he
  rw [he, abs_zero] at hgap
  linarith

/-- The exact real pair attached to a genuine zero satisfies the analytic
decay estimate whenever its ordinate differs from the evaluation ordinate. -/
theorem abs_zero_pair_re_le {b σ : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (t : ℝ)
    (ρ : NontrivialZetaZero) (hgap : t ≠ ρ.1.im) :
    |(transform (2 * σ - 1) (window b) ((σ : ℂ) + (t : ℂ) * I - ρ.1) +
      transform (2 * σ - 1) (window b)
        ((σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1))).re| ≤
      integralCost (2 * σ - 1) b (1 - σ) / (t - ρ.1.im) ^ 2 := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I - ρ.1
  have he : ((2 * σ - 1 : ℝ) : ℂ) - starRingEnd ℂ z =
      (σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1) := by
    dsimp [z]
    push_cast
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hzre : z.re = σ - ρ.1.re := by simp [z]
  have hzim : z.im = t - ρ.1.im := by simp [z]
  have hp := abs_physical_pair_re_le (a := 2 * σ - 1) (δ := 1 - σ)
    (z := z) (by linarith) hb (by linarith) hscale
    (by rw [hzre]; linarith [NontrivialZetaZero.re_lt_one ρ])
    (by rw [hzre]; linarith [NontrivialZetaZero.zero_lt_re ρ])
    (by rw [hzim]; exact sub_ne_zero.mpr hgap)
  simpa only [he, hzim, z] using hp

/-- Every distant actual zero is controlled by the canonical divisor
weight, with multiplicity and the paired normalization explicit. -/
theorem abs_contribution_le_divisorWeight {b σ : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (t : ℝ) (ρ : NontrivialZetaZero)
    (ht : 2 * |t| ≤ |ρ.1.im|) (hγ : 1 ≤ |ρ.1.im|) :
    |contribution b σ t ρ| ≤ 4 * integralCost (2 * σ - 1) b (1 - σ) * divisorWeight ρ := by
  obtain ⟨hgap, hden⟩ := separated_gap ht hγ
  have hp := abs_zero_pair_re_le hb hσ0 hσ1 hscale t ρ (sub_ne_zero.mp hgap)
  have hC := (integralCost_pos hb (2 * σ - 1) (1 - σ)).le
  have hm : 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
  unfold contribution
  rw [abs_mul, abs_of_nonneg (div_nonneg hm (by norm_num))]
  apply (mul_le_mul_of_nonneg_left hp (div_nonneg hm (by norm_num))).trans
  unfold divisorWeight
  have hD : 0 < 1 + ρ.1.im ^ 2 := by positivity
  have hY : 0 < (t - ρ.1.im) ^ 2 := sq_pos_of_ne_zero hgap
  rw [div_mul_div_comm, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hY) hD).mpr
  exact (mul_le_mul_of_nonneg_left hden (mul_nonneg hm hC)).trans_eq (by ring)

/-- One summable majorant controls the complete actual outside-band sum. -/
theorem abs_outside_le {b σ t H : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (ht : 2 * |t| ≤ H) (hH : 1 ≤ H)
    (ρ : NontrivialZetaZero) :
    |outside b σ t H ρ| ≤ 4 * integralCost (2 * σ - 1) b (1 - σ) *
      (if H < |ρ.1.im| then divisorWeight ρ else 0) := by
  unfold outside
  split_ifs with hρ
  · exact abs_contribution_le_divisorWeight hb hσ0 hσ1 hscale t ρ
      (ht.trans hρ.le) (hH.trans hρ.le)
  · simp

/-- The genuine multiplicity-weighted outside contribution is absolutely
summable; no exchange with a prime sum is assumed. -/
theorem summable_outside {b σ t H : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (ht : 2 * |t| ≤ H) (hH : 1 ≤ H) :
    Summable (outside b σ t H) := by
  exact ((summable_divisorTail_terms H).mul_left
    (4 * integralCost (2 * σ - 1) b (1 - σ))).of_norm_bounded
      (fun ρ => abs_outside_le hb hσ0 hσ1 hscale ht hH ρ)

/-- The full signed outside-band contribution has a two-sided bound by
the vanishing actual divisor tail, with all parameters explicit. -/
theorem abs_tsum_outside_le {b σ t H : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (ht : 2 * |t| ≤ H) (hH : 1 ≤ H) :
    |∑' ρ : NontrivialZetaZero, outside b σ t H ρ| ≤
      4 * integralCost (2 * σ - 1) b (1 - σ) * divisorTail H := by
  have hs := summable_outside hb hσ0 hσ1 hscale ht hH
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero, |outside b σ t H ρ| := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ρ : NontrivialZetaZero, 4 * integralCost (2 * σ - 1) b (1 - σ) *
        (if H < |ρ.1.im| then divisorWeight ρ else 0) :=
      hs.norm.tsum_le_tsum (abs_outside_le hb hσ0 hσ1 hscale ht hH)
        ((summable_divisorTail_terms H).mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The bounded-height contribution has finite support in the genuine
analytic zeta divisor. -/
theorem finite_support_inside (b σ t : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (Function.support (inside b σ t H)).Finite := by
  have hf : {ρ : NontrivialZetaZero | |ρ.1.im| ≤ H}.Finite := by
    simpa only [zetaSpectralCoordinate_re] using spectralZetaZeroWindowSet_finite hH
  apply hf.subset
  intro ρ hρ
  by_contra hn
  change ¬|ρ.1.im| ≤ H at hn
  exact hρ (by simp [inside, hn])

/-- The complete paired real zero sum is absolutely summable, with its
finite band and genuine tail proved separately. -/
theorem summable_contribution {b σ : ℝ} (hb : 0 < b) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ b) (t : ℝ) :
    Summable (contribution b σ t) := by
  let H := max (2 * |t|) 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hin : Summable (inside b σ t H) :=
    summable_of_hasFiniteSupport (finite_support_inside b σ t hH)
  have hout := summable_outside (t := t) (H := H) hb hσ0 hσ1 hscale
    (le_max_left _ _) (le_max_right _ _)
  apply (hin.add hout).congr
  intro ρ
  dsimp [inside, outside]
  by_cases hρ : |ρ.1.im| ≤ H
  · simp [hρ, not_lt.mpr hρ]
  · simp [hρ, lt_of_not_ge hρ]

/-- The known zero-free region makes each multiplicity-weighted inside
contribution nonnegative on the common interior evaluation line. -/
theorem inside_nonneg {b : ℝ} (hb : 0 < b) (H t : ℝ) (ρ : NontrivialZetaZero) :
    0 ≤ inside b (1 - zetaPoleReserveZeroMargin H) t H ρ := by
  unfold inside
  split_ifs with hρ
  · unfold contribution
    apply mul_nonneg (by positivity)
    exact nontrivial_zero_pair_re_nonneg_on_band hb H t ρ (hρ.trans (le_abs_self H))
  · exact le_rfl

/-- A global lower bound for the actual paired zero side at the interior
line supplied by the proved zero-free region. Every omitted zero is paid
for by the explicit multiplicity-weighted tail allowance. -/
theorem global_zero_side_lower_bound {b H t : ℝ} (hb : 0 < b)
    (ht : 2 * |t| ≤ H) (hH : 1 ≤ H) (hscale : zetaPoleReserveZeroMargin H ^ 2 ≤ b) :
    let σ := 1 - zetaPoleReserveZeroMargin H;
    -(4 * integralCost (2 * σ - 1) b (1 - σ) * divisorTail H) ≤
      ∑' ρ : NontrivialZetaZero, contribution b σ t ρ := by
  let σ := 1 - zetaPoleReserveZeroMargin H
  change -(4 * integralCost (2 * σ - 1) b (1 - σ) * divisorTail H) ≤ _
  have hm := zetaPoleReserveZeroMargin_bounds H
  have hσ0 : 1 / 2 ≤ σ := by dsimp [σ]; linarith [hm.2]
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith [hm.1]
  have hbσ : (1 - σ) ^ 2 ≤ b := by simpa [σ] using hscale
  have hin : Summable (inside b σ t H) :=
    summable_of_hasFiniteSupport (finite_support_inside b σ t (by linarith))
  have hout := summable_outside hb hσ0 hσ1 hbσ ht hH
  have hsplit : contribution b σ t = fun ρ => inside b σ t H ρ + outside b σ t H ρ := by
    funext ρ
    dsimp [inside, outside]
    by_cases hρ : |ρ.1.im| ≤ H
    · simp [hρ, not_lt.mpr hρ]
    · simp [hρ, lt_of_not_ge hρ]
  rw [hsplit, hin.tsum_add hout]
  have hp : 0 ≤ ∑' ρ : NontrivialZetaZero, inside b σ t H ρ :=
    tsum_nonneg (inside_nonneg hb H t)
  have he := (abs_le.mp (abs_tsum_outside_le hb hσ0 hσ1 hbσ ht hH)).1
  linarith

end
end RiemannGaussian.GaussianFermiZeroTail
