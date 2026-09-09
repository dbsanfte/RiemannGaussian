/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeLogMoments
import RiemannGaussian.ZetaAdaptiveSigned
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Higher signed moments of the actual local zeta divisor

At the safe center every canonical zero factor gives two exact geometric
modes. The singular mode and its reflected regular correction stay paired.
The analytic remainder has a Cauchy estimate at every smaller radius, so a
zero strictly inside that radius has a faster geometric mode.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Alternating Taylor moments commute with scalar multiplication. -/
theorem signedTaylorMoment_const_mul (n : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    signedTaylorMoment n (fun w ↦ c * f w) z = c * signedTaylorMoment n f z := by
  simp only [signedTaylorMoment, iteratedDeriv_const_mul_field]
  ring

/-- Addition retains both analytic channels at the evaluation point. -/
theorem signedTaylorMoment_add (n : ℕ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    signedTaylorMoment n (fun w ↦ f w + g w) z =
      signedTaylorMoment n f z + signedTaylorMoment n g z := by
  simp only [signedTaylorMoment, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, mul_add]

/-- Subtraction preserves the sign of each analytic channel. -/
theorem signedTaylorMoment_sub (n : ℕ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    signedTaylorMoment n (fun w ↦ f w - g w) z =
      signedTaylorMoment n f z - signedTaylorMoment n g z := by
  simp only [signedTaylorMoment, iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, mul_sub]

/-- A finite analytic sum commutes with every signed moment. -/
theorem signedTaylorMoment_sum {ι : Type*} (S : Finset ι) (n : ℕ)
    (f : ι → ℂ → ℂ) {z : ℂ} (hf : ∀ i ∈ S, AnalyticAt ℂ (f i) z) :
    signedTaylorMoment n (fun w ↦ ∑ i ∈ S, f i w) z =
      ∑ i ∈ S, signedTaylorMoment n (f i) z := by
  simp only [signedTaylorMoment, iteratedDeriv_fun_sum (fun i hi ↦ (hf i hi).contDiffAt),
    Finset.mul_sum]

/-- Equality near the center transports all higher signed moments. -/
theorem signedTaylorMoment_congr (n : ℕ) {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : signedTaylorMoment n f z = signedTaylorMoment n g z := by
  rw [signedTaylorMoment, signedTaylorMoment, h.iteratedDeriv_eq n]

/-- The exact affine reciprocal formula after factorial normalization. -/
theorem signedTaylorMoment_inv_linear (n : ℕ) (c d : ℂ) :
    signedTaylorMoment n (fun z ↦ (c * z + d)⁻¹) 0 = c ^ n * (d⁻¹) ^ (n + 1) := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [signedTaylorMoment, iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  simp only [mul_zero, zero_add]
  rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, ← inv_pow]
  calc
    _ = ((-1 : ℂ) ^ n * (-1) ^ n) *
        ((n.factorial : ℂ) / n.factorial) * c ^ n * (d⁻¹) ^ (n + 1) := by ring
    _ = _ := by rw [hs, div_self hf]; simp

/-- Each full canonical response gives its singular geometric mode
minus its reflected mode, with no phase loss at any derivative order. -/
theorem signedTaylorMoment_zetaCanonicalZeroResponse (n : ℕ) {R : ℝ}
    (hR : R ≠ 0) {i : ℂ} (hi : i ≠ 0) :
    signedTaylorMoment n (zetaCanonicalZeroResponse R i) 0 =
      (-i⁻¹) ^ (n + 1) - (-conj i / (R : ℂ) ^ 2) ^ (n + 1) := by
  have hRc : (R : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hR)
  have hsing : AnalyticAt ℂ (fun z : ℂ ↦ (z - i)⁻¹) 0 :=
    (analyticAt_id.sub analyticAt_const).inv (by simpa using hi)
  have hreg : AnalyticAt ℂ (fun z : ℂ ↦ conj i * ((R : ℂ) ^ 2 - conj i * z)⁻¹) 0 :=
    analyticAt_const.mul ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv
      (by simpa using hRc))
  unfold zetaCanonicalZeroResponse
  simp only [div_eq_mul_inv, one_mul]
  rw [signedTaylorMoment_add n hsing hreg, signedTaylorMoment_const_mul]
  have hs := signedTaylorMoment_inv_linear n 1 (-i)
  have hr := signedTaylorMoment_inv_linear n (-conj i) ((R : ℂ) ^ 2)
  simp only [one_mul, one_pow, ← sub_eq_add_neg] at hs
  have he : (fun z : ℂ ↦ ((R : ℂ) ^ 2 - conj i * z)⁻¹) =
      (fun z : ℂ ↦ (-conj i * z + (R : ℂ) ^ 2)⁻¹) := by funext z; congr 1; ring
  rw [hs, he, hr, inv_neg, mul_pow, pow_succ (-conj i)]
  ring

variable (r : Set.Ico (3 / 4 : ℝ) 1)

/-- The finite support consists of the actual local zero divisor. -/
def adaptiveZetaZeroSupport (y : ℝ) : Finset ℂ :=
  (adaptiveZetaCanonicalResidual_decomp r y).meromorphicOn.divisor_ball_support_finite.toFinset

/-- Support membership means a nonzero actual analytic multiplicity. -/
theorem mem_adaptiveZetaZeroSupport (y : ℝ) (i : ℂ) :
    i ∈ adaptiveZetaZeroSupport r y ↔
      divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i ≠ 0 := by
  simp [adaptiveZetaZeroSupport, Function.mem_support]

/-- The full canonical response is a finite sum over actual zeros. -/
theorem adaptiveZetaCanonicalResponse_eq_sum (y : ℝ) (z : ℂ) :
    adaptiveZetaCanonicalResponse r y z =
      ∑ i ∈ adaptiveZetaZeroSupport r y,
        (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z := by
  rw [adaptiveZetaCanonicalResponse,
    finsum_eq_sum_of_support_subset (s := adaptiveZetaZeroSupport r y)]
  · simp only [zsmul_eq_mul]
  · intro i hi
    change i ∈ adaptiveZetaZeroSupport r y
    rw [mem_adaptiveZetaZeroSupport]
    intro he
    exact hi (by simp [he])

/-- The actual analytic residual moment, with its sign still present. -/
def adaptiveZetaResidualMoment (y : ℝ) (n : ℕ) : ℂ :=
  signedTaylorMoment n (logDeriv (adaptiveZetaCanonicalResidual r y)) 0

/-- Cauchy's estimate controls every residual moment at any strictly
smaller radius. The exponential rate is that radius's reciprocal. -/
theorem norm_adaptiveZetaResidualMoment_le (y : ℝ) (n : ℕ) {q : ℝ}
    (hq : 0 < q) (hqR : q < adaptiveZetaCanonicalRadius r y) :
    ‖adaptiveZetaResidualMoment r y n‖ ≤
      (n + 1 : ℝ) * (8 * localZetaLogHeight y / (adaptiveZetaCanonicalRadius r y - q)) /
        q ^ n := by
  have hsub : closedBall (0 : ℂ) q ⊆ ball 0 (adaptiveZetaCanonicalRadius r y) :=
    closedBall_subset_ball hqR
  have hd : DiffContOnCl ℂ (adaptiveZetaCanonicalLog r y) (ball 0 q) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hq.ne']
    intro w hw
    exact (adaptiveZetaCanonicalLog_hasDerivAt r y (hsub hw)).differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ sphere (0 : ℂ) q, ‖adaptiveZetaCanonicalLog r y z‖ ≤
      8 * localZetaLogHeight y * q / (adaptiveZetaCanonicalRadius r y - q) := by
    intro z hz
    have hn : ‖z‖ = q := by simpa only [mem_sphere, dist_zero_right] using hz
    simpa only [hn] using norm_adaptiveZetaCanonicalLog_le r y (hsub (sphere_subset_closedBall hz))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n + 1) hq hd hb
  have he : deriv (adaptiveZetaCanonicalLog r y) =ᶠ[𝓝 (0 : ℂ)]
      logDeriv (adaptiveZetaCanonicalResidual r y) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (adaptiveZetaCanonicalRadius_pos r y))] with z hz
    exact (adaptiveZetaCanonicalLog_hasDerivAt r y hz).deriv
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq n] at h
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hn : ‖adaptiveZetaResidualMoment r y n‖ =
      ‖iteratedDeriv n (logDeriv (adaptiveZetaCanonicalResidual r y)) 0‖ / n.factorial := by
    simp [adaptiveZetaResidualMoment, signedTaylorMoment, norm_pow, div_eq_mul_inv, mul_comm]
  rw [hn]
  apply (div_le_div_of_nonneg_right h hf.le).trans_eq
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- Every actual canonical zero response is analytic at the safe center. -/
theorem analyticAt_adaptiveZetaCanonicalZeroResponse (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) :
    AnalyticAt ℂ (zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i) 0 := by
  have hin := adaptiveZetaDivisor_point_ne_zero r y ((mem_adaptiveZetaZeroSupport r y i).mp hi)
  have hR : (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (adaptiveZetaCanonicalRadius_pos r y).ne')
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by simpa using hin)).add
    (analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (by simpa using hR))

/-- The complete local response is analytic at the safe center. -/
theorem analyticAt_adaptiveZetaCanonicalResponse (y : ℝ) :
    AnalyticAt ℂ (adaptiveZetaCanonicalResponse r y) 0 := by
  have he := funext (adaptiveZetaCanonicalResponse_eq_sum r y)
  rw [he]
  apply (adaptiveZetaZeroSupport r y).analyticAt_fun_sum
  intro i hi
  exact analyticAt_const.mul (analyticAt_adaptiveZetaCanonicalZeroResponse r y hi)

/-- The logarithmic derivative of the actual zero-free residual is
analytic at the center. -/
theorem analyticAt_adaptiveZetaResidualLogDeriv (y : ℝ) :
    AnalyticAt ℂ (logDeriv (adaptiveZetaCanonicalResidual r y)) 0 := by
  have hz : (0 : ℂ) ∈ closedBall 0 (adaptiveZetaCanonicalRadius r y) :=
    mem_closedBall_self (adaptiveZetaCanonicalRadius_pos r y).le
  have hg := (adaptiveZetaCanonicalResidual_decomp r y).analyticOnNhd 0 hz
  exact hg.deriv.div hg ((adaptiveZetaCanonicalResidual_decomp r y).ne_zero 0 hz)

/-- All actual divisor modes, with both canonical channels and analytic
multiplicities, survive every higher signed derivative. -/
theorem signedTaylorMoment_adaptiveZetaCanonicalResponse (y : ℝ) (n : ℕ) :
    signedTaylorMoment n (adaptiveZetaCanonicalResponse r y) 0 =
      ∑ i ∈ adaptiveZetaZeroSupport r y,
        (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          ((-i⁻¹) ^ (n + 1) -
            (-conj i / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2) ^ (n + 1)) := by
  rw [funext (adaptiveZetaCanonicalResponse_eq_sum r y)]
  have hf : ∀ i ∈ adaptiveZetaZeroSupport r y, AnalyticAt ℂ
      (fun z ↦ (divisor (localZetaPoleRemoved y)
        (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z) 0 := by
    intro i hi
    exact analyticAt_const.mul (analyticAt_adaptiveZetaCanonicalZeroResponse r y hi)
  rw [signedTaylorMoment_sum _ n _ hf]
  apply Finset.sum_congr rfl
  intro i hi
  rw [signedTaylorMoment_const_mul, signedTaylorMoment_zetaCanonicalZeroResponse n
    (adaptiveZetaCanonicalRadius_pos r y).ne'
    (adaptiveZetaDivisor_point_ne_zero r y ((mem_adaptiveZetaZeroSupport r y i).mp hi))]

private theorem neg_logDeriv_adaptive_eventually (y : ℝ) :
    (fun z : ℂ ↦ -logDeriv riemannZeta (3 / 2 + I * y + z)) =ᶠ[𝓝 0]
      (fun z ↦ (z + (1 / 2 + I * y))⁻¹ -
        logDeriv (adaptiveZetaCanonicalResidual r y) z - adaptiveZetaCanonicalResponse r y z) := by
  have hhalf : ∀ᶠ z : ℂ in 𝓝 0, 1 < (3 / 2 + I * y + z).re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp; norm_num)
  filter_upwards [hhalf,
    isOpen_ball.mem_nhds (mem_ball_self (adaptiveZetaCanonicalRadius_pos r y))] with z hs hz
  have hs1 : 3 / 2 + I * (y : ℂ) + z ≠ 1 := by
    intro he
    rw [he] at hs
    norm_num at hs
  have hf : localZetaPoleRemoved y z ≠ 0 := riemannZeta₁_ne_zero_of_one_le_re hs.le
  rw [neg_logDeriv_riemannZeta_eq_pole_sub hs1 (riemannZeta_ne_zero_of_one_le_re hs.le),
    ← logDeriv_localZetaPoleRemoved_eq,
    logDeriv_adaptiveZetaPoleRemoved_eq_residual_add_response r y hz hf]
  have he : 3 / 2 + I * (y : ℂ) + z - 1 = z + (1 / 2 + I * y) := by ring
  rw [he, one_div]
  ring

/-- The actual prime log moment is exactly the pole moment minus every
local zero mode and the controlled analytic residual. The equation is
complex-valued and preserves the complete phase block. -/
theorem zetaPrimeLogMoment_eq_adaptive_modes (y : ℝ) (n : ℕ) :
    zetaPrimeLogMoment n (3 / 2 + I * y) =
      ((1 / 2 + I * (y : ℂ))⁻¹) ^ (n + 1) - adaptiveZetaResidualMoment r y n -
      ∑ i ∈ adaptiveZetaZeroSupport r y,
        (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          ((-i⁻¹) ^ (n + 1) -
            (-conj i / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2) ^ (n + 1)) := by
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ (z + (1 / 2 + I * (y : ℂ)))⁻¹) 0 := by
    apply (analyticAt_id.add analyticAt_const).inv
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hres := analyticAt_adaptiveZetaResidualLogDeriv r y
  have hresp := analyticAt_adaptiveZetaCanonicalResponse r y
  have hpr : AnalyticAt ℂ (fun z : ℂ ↦ (z + (1 / 2 + I * (y : ℂ)))⁻¹ -
      logDeriv (adaptiveZetaCanonicalResidual r y) z) 0 := hp.sub hres
  have he : zetaPrimeLogMoment n (3 / 2 + I * y) =
      signedTaylorMoment n (fun z ↦ -logDeriv riemannZeta (3 / 2 + I * y + z)) 0 := by
    have ht := congrFun (iteratedDeriv_comp_const_add n
      (fun z ↦ -logDeriv riemannZeta z) (3 / 2 + I * (y : ℂ))) 0
    simp only [add_zero] at ht
    exact congrArg ((-1 : ℂ) ^ n / n.factorial * ·) ht.symm
  rw [he, signedTaylorMoment_congr n (neg_logDeriv_adaptive_eventually r y),
    signedTaylorMoment_sub n hpr hresp, signedTaylorMoment_sub n hp hres,
    signedTaylorMoment_adaptiveZetaCanonicalResponse]
  congr 2
  simpa only [one_mul, one_pow] using signedTaylorMoment_inv_linear n 1 (1 / 2 + I * y)

/-- Normalizing by any mode strictly inside the canonical radius makes
the actual analytic residual tend to zero. The linear derivative loss is
absorbed by the strict geometric gap. -/
theorem tendsto_adaptiveZetaResidualMoment_mul_pow (y : ℝ) {a : ℂ}
    (ha : ‖a‖ < adaptiveZetaCanonicalRadius r y) :
    Tendsto (fun n : ℕ ↦ a ^ (n + 1) * adaptiveZetaResidualMoment r y n) atTop (𝓝 0) := by
  obtain ⟨q, haq, hqR⟩ := exists_between ha
  have hq : 0 < q := lt_of_le_of_lt (norm_nonneg a) haq
  have hratio : ‖a‖ / q < 1 := (div_lt_one hq).mpr haq
  have hratio0 : 0 ≤ ‖a‖ / q := div_nonneg (norm_nonneg _) hq.le
  let C := ‖a‖ * (8 * localZetaLogHeight y / (adaptiveZetaCanonicalRadius r y - q))
  have hlim : Tendsto (fun n : ℕ ↦ C * ((n : ℝ) * (‖a‖ / q) ^ n + (‖a‖ / q) ^ n))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_self_mul_const_pow_of_lt_one hratio0 hratio).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio))
  apply squeeze_zero_norm (fun n ↦ ?_) hlim
  rw [norm_mul, norm_pow]
  apply (mul_le_mul_of_nonneg_left (norm_adaptiveZetaResidualMoment_le r y n hq hqR)
    (pow_nonneg (norm_nonneg a) _)).trans_eq
  dsimp only [C]
  rw [div_pow, pow_succ]
  ring

end

end RiemannGaussian
