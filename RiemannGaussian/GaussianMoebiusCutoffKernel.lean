import RiemannGaussian.GaussianMoebiusHeatScale

/-!
# Gaussian control of a literal arithmetic cutoff

The Gaussian's exact exponential moments control the displacement of a
finite cutoff under logarithmic heat smoothing. Its normalized absolute
cutoff error can be made arbitrarily small by choosing a positive heat time.
No arithmetic cancellation is assumed in these kernel estimates.
-/

open MeasureTheory Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The unnormalized Gaussian used to smooth a literal logarithmic cutoff. -/
def moebiusCutoffGaussian (tau v : ℝ) : ℝ := Real.exp (-v ^ 2 / (4 * tau))

/-- The exact positive-time Gaussian integral normalization. -/
def moebiusCutoffGaussianMass (tau : ℝ) : ℝ := Real.sqrt (4 * Real.pi * tau)

/-- The cutoff Gaussian is strictly positive. -/
theorem moebiusCutoffGaussian_pos (tau v : ℝ) : 0 < moebiusCutoffGaussian tau v :=
  Real.exp_pos _

/-- Its normalization is strictly positive at every positive heat time. -/
theorem moebiusCutoffGaussianMass_pos {tau : ℝ} (htau : 0 < tau) :
    0 < moebiusCutoffGaussianMass tau := by
  unfold moebiusCutoffGaussianMass
  positivity

/-- Completing the square retains the exact real exponential weight of a cutoff displacement. -/
theorem moebiusCutoffGaussian_mul_exp_eq {tau : ℝ} (htau : 0 < tau) (c v : ℝ) :
    moebiusCutoffGaussian tau v * Real.exp (c * v) =
      Real.exp (-(1 / (4 * tau)) * (v - 2 * tau * c) ^ 2) * Real.exp (tau * c ^ 2) := by
  unfold moebiusCutoffGaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- Every fixed exponential moment of the positive-time cutoff Gaussian is integrable. -/
theorem integrable_moebiusCutoffGaussian_mul_exp {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Integrable (fun v : ℝ ↦ moebiusCutoffGaussian tau v * Real.exp (c * v)) := by
  simp_rw [moebiusCutoffGaussian_mul_exp_eq htau]
  exact ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * tau))).comp_sub_right
    (2 * tau * c)).mul_const _

/-- The exact exponential moment includes the full positive-time normalization. -/
theorem integral_moebiusCutoffGaussian_mul_exp {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    (∫ v : ℝ, moebiusCutoffGaussian tau v * Real.exp (c * v)) =
      moebiusCutoffGaussianMass tau * Real.exp (tau * c ^ 2) := by
  simp_rw [moebiusCutoffGaussian_mul_exp_eq htau]
  rw [integral_mul_const, integral_sub_right_eq_self
    (fun v : ℝ ↦ Real.exp (-(1 / (4 * tau)) * v ^ 2)) (2 * tau * c), integral_gaussian]
  unfold moebiusCutoffGaussianMass
  congr 2
  field_simp

/-- The cutoff Gaussian itself is integrable at every positive heat time. -/
theorem integrable_moebiusCutoffGaussian {tau : ℝ} (htau : 0 < tau) :
    Integrable (moebiusCutoffGaussian tau) := by
  simpa using integrable_moebiusCutoffGaussian_mul_exp htau 0

/-- Its full integral is exactly the stated Gaussian mass. -/
theorem integral_moebiusCutoffGaussian {tau : ℝ} (htau : 0 < tau) :
    (∫ v : ℝ, moebiusCutoffGaussian tau v) = moebiusCutoffGaussianMass tau := by
  simpa using integral_moebiusCutoffGaussian_mul_exp htau 0

/-- The squared multiplicative displacement keeps both signed exponential corrections. -/
theorem moebiusCutoffGaussian_mul_exp_sub_one_sq (tau v : ℝ) :
    moebiusCutoffGaussian tau v * (Real.exp v - 1) ^ 2 =
      moebiusCutoffGaussian tau v * Real.exp (2 * v) -
        2 * (moebiusCutoffGaussian tau v * Real.exp v) + moebiusCutoffGaussian tau v := by
  rw [show 2 * v = v + v by ring, Real.exp_add]
  ring

/-- The squared cutoff displacement has a genuinely integrable Gaussian majorant. -/
theorem integrable_moebiusCutoffGaussian_exp_sub_one_sq {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun v : ℝ ↦ moebiusCutoffGaussian tau v * (Real.exp v - 1) ^ 2) := by
  simp_rw [moebiusCutoffGaussian_mul_exp_sub_one_sq]
  have h1 := integrable_moebiusCutoffGaussian_mul_exp htau 1
  simp only [one_mul] at h1
  exact ((integrable_moebiusCutoffGaussian_mul_exp htau 2).sub (h1.const_mul 2)).add
    (integrable_moebiusCutoffGaussian htau)

/-- The exact squared cutoff error tends to zero after normalization as the heat time shrinks. -/
theorem integral_moebiusCutoffGaussian_exp_sub_one_sq {tau : ℝ} (htau : 0 < tau) :
    (∫ v : ℝ, moebiusCutoffGaussian tau v * (Real.exp v - 1) ^ 2) =
      moebiusCutoffGaussianMass tau * (Real.exp (4 * tau) - 2 * Real.exp tau + 1) := by
  have h1 := integrable_moebiusCutoffGaussian_mul_exp htau 1
  simp only [one_mul] at h1
  have h2 : Integrable (fun v : ℝ ↦ 2 * (moebiusCutoffGaussian tau v * Real.exp v)) := h1.const_mul 2
  have hsub : Integrable (fun v : ℝ ↦ moebiusCutoffGaussian tau v * Real.exp (2 * v) -
      2 * (moebiusCutoffGaussian tau v * Real.exp v)) :=
    (integrable_moebiusCutoffGaussian_mul_exp htau 2).sub h2
  simp_rw [moebiusCutoffGaussian_mul_exp_sub_one_sq]
  rw [integral_add hsub
    (integrable_moebiusCutoffGaussian htau), integral_sub
    (integrable_moebiusCutoffGaussian_mul_exp htau 2) h2,
    integral_const_mul, integral_moebiusCutoffGaussian_mul_exp htau 2,
    ← show (∫ v : ℝ, moebiusCutoffGaussian tau v * Real.exp (1 * v)) =
      ∫ v : ℝ, moebiusCutoffGaussian tau v * Real.exp v by simp,
    integral_moebiusCutoffGaussian_mul_exp htau 1, integral_moebiusCutoffGaussian htau]
  norm_num
  ring_nf

/-- The absolute multiplicative cutoff displacement is integrable against the actual Gaussian. -/
theorem integrable_moebiusCutoffGaussian_abs_exp_sub_one {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun v : ℝ ↦ moebiusCutoffGaussian tau v * |Real.exp v - 1|) := by
  have h1 := integrable_moebiusCutoffGaussian_mul_exp htau 1
  simp only [one_mul] at h1
  apply (h1.add (integrable_moebiusCutoffGaussian htau)).mono' (by unfold moebiusCutoffGaussian; fun_prop)
  exact Eventually.of_forall fun v ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (moebiusCutoffGaussian_pos _ _), abs_abs]
    change moebiusCutoffGaussian tau v * |Real.exp v - 1| ≤
      moebiusCutoffGaussian tau v * Real.exp v + moebiusCutoffGaussian tau v
    calc
      _ ≤ moebiusCutoffGaussian tau v * (Real.exp v + 1) :=
        mul_le_mul_of_nonneg_left (by simpa using abs_sub (Real.exp v) 1) (moebiusCutoffGaussian_pos _ _).le
      _ = _ := by ring

/-- A quantitative normalized error bound retains the full Gaussian second moment. -/
theorem integral_moebiusCutoffGaussian_abs_exp_sub_one_le {tau eps : ℝ}
    (htau : 0 < tau) (heps : 0 < eps) :
    (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) ≤
      moebiusCutoffGaussianMass tau *
        (eps + (Real.exp (4 * tau) - 2 * Real.exp tau + 1) / eps) := by
  have hb : Integrable (fun v : ℝ ↦ eps * moebiusCutoffGaussian tau v +
      (moebiusCutoffGaussian tau v * (Real.exp v - 1) ^ 2) / eps) :=
    ((integrable_moebiusCutoffGaussian htau).const_mul eps).add
      ((integrable_moebiusCutoffGaussian_exp_sub_one_sq htau).div_const eps)
  have h := integral_mono (integrable_moebiusCutoffGaussian_abs_exp_sub_one htau) hb
    (fun v ↦ by
      have hd : |Real.exp v - 1| ≤ eps + (Real.exp v - 1) ^ 2 / eps := by
        have hm : |Real.exp v - 1| * eps ≤ eps ^ 2 + (Real.exp v - 1) ^ 2 := by
          nlinarith [sq_nonneg (|Real.exp v - 1| - eps), sq_abs (Real.exp v - 1)]
        apply ((le_div_iff₀ heps).mpr hm).trans_eq
        field_simp
      have hm := mul_le_mul_of_nonneg_left hd (moebiusCutoffGaussian_pos tau v).le
      exact hm.trans_eq (by ring))
  rw [integral_add ((integrable_moebiusCutoffGaussian htau).const_mul eps)
    ((integrable_moebiusCutoffGaussian_exp_sub_one_sq htau).div_const eps),
    integral_const_mul, integral_div, integral_moebiusCutoffGaussian htau,
    integral_moebiusCutoffGaussian_exp_sub_one_sq htau] at h
  exact h.trans_eq (by ring)

/-- A positive heat time makes the full normalized absolute cutoff error as small as prescribed. -/
theorem exists_moebiusCutoffGaussian_error_le {eps : ℝ} (heps : 0 < eps) :
    ∃ tau : ℝ, 0 < tau ∧
      (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) ≤
        eps * moebiusCutoffGaussianMass tau := by
  have hc : ContinuousAt (fun tau : ℝ ↦ Real.exp (4 * tau) - 2 * Real.exp tau + 1) 0 := by fun_prop
  have hz : Tendsto (fun tau : ℝ ↦ Real.exp (4 * tau) - 2 * Real.exp tau + 1) (𝓝[>] 0) (𝓝 0) := by
    convert hc.tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds) using 1
    norm_num
  obtain ⟨tau, ht, hp⟩ := (hz.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eps ^ 2 / 4))).and
    (self_mem_nhdsWithin : ∀ᶠ tau : ℝ in 𝓝[>] 0, tau ∈ Set.Ioi 0) |>.exists
  have h := integral_moebiusCutoffGaussian_abs_exp_sub_one_le hp (by linarith : 0 < eps / 2)
  refine ⟨tau, hp, h.trans ?_⟩
  have hcpos := (moebiusCutoffGaussianMass_pos hp).le
  have hdiv : (Real.exp (4 * tau) - 2 * Real.exp tau + 1) / (eps / 2) ≤ eps / 2 := by
    rw [div_le_iff₀ (by linarith : 0 < eps / 2)]
    nlinarith
  nlinarith

end

end RiemannGaussian
