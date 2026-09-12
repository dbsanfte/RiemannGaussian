/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiFisherBound
import RiemannGaussian.GaussianFermiMarginBudget

/-!
# A width-independent bound for the whole outside zero divisor

The signed score--curvature balance also holds on the enlarged reflection
strip when its squared extension is no larger than the Gaussian width.
The curvature costs only Gaussian width times Gaussian mass, together with
the exact unit logistic mass. Thus the full outside-zero error is bounded
by a fixed constant times the actual divisor tail, uniformly over every
admissible width and evaluation ordinate.
-/

namespace RiemannGaussian.GaussianFermiFisherTail
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open EtaGammaSmoothing FermiLaplaceReflection GaussianFermiZeroPair
open GaussianFermiDerivativeBounds GaussianFermiPairDecay GaussianFermiFisherBound
open GaussianFermiZeroTail GaussianFermiPhaseBudget GaussianFermiMarginBudget

/-- The retained curvature cost on the enlarged strip. -/
def curvatureCost (a b : ℝ) : ℝ :=
  Real.exp (1 / 2) * (4 * b * Real.sqrt (Real.pi / (b / 2)) + 2 * a)

/-- One constant controls all positive Fermi parameters and widths at most one. -/
def uniformCost : ℝ := Real.exp (1 / 2) * (8 * Real.sqrt Real.pi + 2)

/-- The uniform derivative cost is strictly positive. -/
theorem uniformCost_pos : 0 < uniformCost := by unfold uniformCost; positivity

/-- The enlarged-strip curvature has an integrable Gaussian-plus-logistic
majorant. Its Gaussian coefficient contains the width itself. -/
theorem curvature_density_le_enlarged {a b x δ : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hs : δ ^ 2 ≤ b) (hx : -δ ≤ x) (hxa : x ≤ a + δ) (t : ℝ) :
    curvature a b t * damped a b x t ≤
      (2 * b * Real.exp (1 / 2)) * window (b / 2) t +
        (a * Real.exp (1 / 2)) * logisticSlope a t := by
  have hW := damped_le_gaussian hb hs hx hxa t
  have h1 : damped a b x t ≤ Real.exp (1 / 2) := hW.trans (by
    apply mul_le_of_le_one_right (Real.exp_pos _).le
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  have hfirst := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 2 * b)
  have hsecond := mul_le_mul_of_nonneg_left h1
    (mul_nonneg ha (logisticSlope_nonneg ha t))
  unfold curvature
  rw [add_mul]
  exact add_le_add (by simpa only [window, mul_assoc] using hfirst)
    (hsecond.trans_eq (by ring))

/-- The enlarged-strip curvature density is integrable with no new
analytic assumption on the original signal. -/
theorem integrable_curvature_density_enlarged {a b x δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : δ ^ 2 ≤ b) (hx : -δ ≤ x) (hxa : x ≤ a + δ) :
    Integrable (fun t : ℝ => curvature a b t * damped a b x t) := by
  have hi : Integrable (fun t : ℝ => (2 * b * Real.exp (1 / 2)) * window (b / 2) t +
      (a * Real.exp (1 / 2)) * logisticSlope a t) :=
    ((integrable_exp_neg_mul_sq (by linarith : 0 < b / 2)).const_mul _).add
      ((integrable_logisticSlope ha).const_mul _)
  have hf := continuous_fermi
  apply hi.mono' (by unfold curvature logisticSlope damped; fun_prop)
  filter_upwards with t
  rw [Real.norm_of_nonneg (mul_nonneg (curvature_nonneg ha.le hb.le t) (damped_pos _ _ _ _).le)]
  exact curvature_density_le_enlarged ha.le hb hs hx hxa t

/-- Integrating the enlarged-strip curvature uses the exact logistic mass. -/
theorem integral_curvature_density_le_enlarged {a b x δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : δ ^ 2 ≤ b) (hx : -δ ≤ x) (hxa : x ≤ a + δ) :
    (∫ t : ℝ, curvature a b t * damped a b x t) ≤
      Real.exp (1 / 2) * (2 * b * Real.sqrt (Real.pi / (b / 2)) + a) := by
  have hiW : Integrable (window (b / 2)) := integrable_exp_neg_mul_sq (by linarith)
  have hiL := integrable_logisticSlope ha
  have h := integral_mono (integrable_curvature_density_enlarged ha hb hs hx hxa)
    ((hiW.const_mul (2 * b * Real.exp (1 / 2))).add
      (hiL.const_mul (a * Real.exp (1 / 2))))
    (curvature_density_le_enlarged ha.le hb hs hx hxa)
  simp only [Pi.add_apply] at h
  rw [integral_add (hiW.const_mul _) (hiL.const_mul _), integral_const_mul,
    integral_const_mul, integral_logisticSlope ha, mul_one] at h
  simp only [window, integral_gaussian] at h
  exact h.trans_eq (by ring)

/-- The squared score remains integrable throughout the enlarged strip. -/
theorem integrable_score_density_enlarged {a b x δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hs : δ ^ 2 ≤ b) (hx : -δ ≤ x) (hxa : x ≤ a + δ) :
    Integrable (fun t : ℝ => score a b x t ^ 2 * damped a b x t) := by
  have hd := (integrable_damped_orders ha.le hb hδ hs hx hxa).2.2
  apply (hd.add (integrable_curvature_density_enlarged ha hb hs hx hxa)).congr
  filter_upwards with t
  simp only [Pi.add_apply, dampedTwo_eq_score_curvature]
  ring

/-- The exact signed score--curvature balance survives the strip extension. -/
theorem integral_score_eq_curvature_enlarged {a b x δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hs : δ ^ 2 ≤ b) (hx : -δ ≤ x) (hxa : x ≤ a + δ) :
    (∫ t : ℝ, score a b x t ^ 2 * damped a b x t) =
      ∫ t : ℝ, curvature a b t * damped a b x t := by
  obtain ⟨_, h1, h2⟩ := integrable_damped_orders ha.le hb hδ hs hx hxa
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_dampedOne a b x) h2 h1
  simp_rw [dampedTwo_eq_score_curvature] at hz
  rw [integral_sub (integrable_score_density_enlarged ha hb hδ hs hx hxa)
    (integrable_curvature_density_enlarged ha hb hs hx hxa)] at hz
  exact sub_eq_zero.mp hz

/-- The enlarged-strip second derivative has a bounded curvature cost,
replacing the former inverse-width envelope. -/
theorem integral_abs_dampedTwo_le_enlarged {a b x δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hs : δ ^ 2 ≤ b) (hx : -δ ≤ x) (hxa : x ≤ a + δ) :
    (∫ t : ℝ, |dampedTwo a b x t|) ≤ curvatureCost a b := by
  have h2 := (integrable_damped_orders ha.le hb hδ hs hx hxa).2.2
  have hscore := integrable_score_density_enlarged ha hb hδ hs hx hxa
  have hc := integrable_curvature_density_enlarged ha hb hs hx hxa
  have hp (t : ℝ) : |dampedTwo a b x t| ≤ score a b x t ^ 2 * damped a b x t +
      curvature a b t * damped a b x t := by
    rw [dampedTwo_eq_score_curvature]
    apply (abs_sub _ _).trans_eq
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (damped_pos _ _ _ _).le),
      abs_of_nonneg (mul_nonneg (curvature_nonneg ha.le hb.le t) (damped_pos _ _ _ _).le)]
  have h := integral_mono h2.abs (hscore.add hc) hp
  simp only [Pi.add_apply] at h
  rw [integral_add hscore hc, integral_score_eq_curvature_enlarged ha hb hδ hs hx hxa] at h
  unfold curvatureCost
  linarith [integral_curvature_density_le_enlarged ha hb hs hx hxa]

/-- The exact curvature cost is uniformly bounded on the entire admissible
positive parameter square. -/
theorem curvatureCost_le_uniform {a b : ℝ} (hau : a ≤ 1) (hb : 0 < b) (hbu : b ≤ 1) :
    curvatureCost a b ≤ uniformCost := by
  have hg := gaussian_curvature_cost_le (by linarith : 0 < b / 2) (by linarith : b / 2 ≤ 1)
  unfold curvatureCost uniformCost
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith

/-- Two exact integrations by parts transfer the improved enlarged-strip
curvature estimate to the full complex analytic reflection. -/
theorem im_sq_mul_norm_pair_le_enlarged {a b δ : ℝ} (ha : 0 < a) (hau : a ≤ 1)
    (hb : 0 < b) (hbu : b ≤ 1) (hδ : 0 ≤ δ) (hs : δ ^ 2 ≤ b)
    {z : ℂ} (hx : -δ ≤ z.re) (hxa : z.re ≤ a + δ) :
    z.im ^ 2 * ‖transform a (window b) z + transform a (window b) ((a : ℂ) - z)‖ ≤
      uniformCost := by
  obtain ⟨h0, h1, h2⟩ := integrable_damped_orders ha.le hb hδ hs hx hxa
  have he := oscillatory_second_derivative (hasDerivAt_damped a b z.re)
    (hasDerivAt_dampedOne a b z.re) h0 h1 h2 z.im
  have hn := congrArg norm he
  have hn' : ‖oscillatory (dampedTwo a b z.re) z.im‖ =
      z.im ^ 2 * ‖oscillatory (damped a b z.re) z.im‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, sq_abs] using hn
  rw [pair_eq_oscillatory hb, ← hn']
  exact (norm_oscillatory_le h2 z.im).trans
    ((integral_abs_dampedTwo_le_enlarged ha hb hδ hs hx hxa).trans
      (curvatureCost_le_uniform hau hb hbu))

/-- Only the real part of the physical reflection is identified with the
analytic reflection, preserving the conjugation distinction. -/
theorem abs_physical_pair_re_le_enlarged {a b δ : ℝ} (ha : 0 < a) (hau : a ≤ 1)
    (hb : 0 < b) (hbu : b ≤ 1) (hδ : 0 ≤ δ) (hs : δ ^ 2 ≤ b)
    {z : ℂ} (hx : -δ ≤ z.re) (hxa : z.re ≤ a + δ) (hy : z.im ≠ 0) :
    |(transform a (window b) z +
      transform a (window b) ((a : ℂ) - starRingEnd ℂ z)).re| ≤ uniformCost / z.im ^ 2 := by
  rw [physical_pair_re_eq]
  apply (Complex.abs_re_le_norm _).trans
  apply (le_div_iff₀ (sq_pos_of_ne_zero hy)).mpr
  simpa only [mul_comm] using im_sq_mul_norm_pair_le_enlarged ha hau hb hbu hδ hs hx hxa

/-- Every genuine distant zero has one inverse-square majorant independent
of Gaussian width and of the chosen interior line. -/
theorem abs_contribution_le_uniform {b σ : ℝ} (hb : 0 < b) (hbu : b ≤ 1)
    (hσ : 1 / 2 < σ) (hσu : σ ≤ 1) (hs : (1 - σ) ^ 2 ≤ b)
    (t : ℝ) (ρ : NontrivialZetaZero) (ht : 2 * |t| ≤ |ρ.1.im|) :
    |contribution b σ t ρ| ≤ 4 * uniformCost * divisorWeight ρ := by
  have him := nontrivialZetaZero_im_sq_gt_three ρ
  have htriangle : |ρ.1.im| ≤ |t - ρ.1.im| + |t| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (ρ.1.im - t) t
  have hgap : t - ρ.1.im ≠ 0 := by
    intro he
    rw [he, abs_zero] at htriangle
    have : |ρ.1.im| = 0 := by linarith [abs_nonneg ρ.1.im]
    have hz := abs_eq_zero.mp this
    rw [hz] at him
    norm_num at him
  have hsq := sq_le_sq₀ (abs_nonneg ρ.1.im) (by positivity : 0 ≤ 2 * |t - ρ.1.im|)
  have hden : 1 + ρ.1.im ^ 2 ≤ 8 * (t - ρ.1.im) ^ 2 := by
    have h := hsq.mpr (by linarith : |ρ.1.im| ≤ 2 * |t - ρ.1.im|)
    simp only [mul_pow, sq_abs] at h
    nlinarith
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I - ρ.1
  have he : ((2 * σ - 1 : ℝ) : ℂ) - starRingEnd ℂ z =
      (σ : ℂ) + (t : ℂ) * I - (1 - starRingEnd ℂ ρ.1) := by
    dsimp [z]
    push_cast
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hp := abs_physical_pair_re_le_enlarged (a := 2 * σ - 1) (δ := 1 - σ) (z := z)
    (by linarith) (by linarith) hb hbu (by linarith) hs
    (by simp [z]; linarith [NontrivialZetaZero.re_lt_one ρ])
    (by simp [z]; linarith [NontrivialZetaZero.zero_lt_re ρ]) (by simpa [z] using hgap)
  simp only [he, z, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_I_im, Complex.ofReal_re, zero_add] at hp
  have hm : 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
  have hm2 : 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) / 2 := by positivity
  unfold contribution
  rw [abs_mul, abs_of_nonneg hm2]
  apply (mul_le_mul_of_nonneg_left hp hm2).trans
  unfold divisorWeight
  rw [div_mul_div_comm, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_ne_zero hgap))
    (by positivity)).mpr
  exact (mul_le_mul_of_nonneg_left hden (mul_nonneg hm uniformCost_pos.le)).trans_eq (by ring)

/-- The complete outside divisor is controlled termwise by one summable
weight, uniformly across the admissible parameter family. -/
theorem abs_outside_le_uniform {b σ t H : ℝ} (hb : 0 < b) (hbu : b ≤ 1)
    (hσ : 1 / 2 < σ) (hσu : σ ≤ 1) (hs : (1 - σ) ^ 2 ≤ b) (ht : 2 * |t| ≤ H)
    (ρ : NontrivialZetaZero) :
    |outside b σ t H ρ| ≤ 4 * uniformCost *
      (if H < |ρ.1.im| then divisorWeight ρ else 0) := by
  unfold outside
  split_ifs with hρ
  · exact abs_contribution_le_uniform hb hbu hσ hσu hs t ρ (ht.trans hρ.le)
  · simp

/-- The improved full-divisor allowance depends only on the height cutoff. -/
def tailAllowance (H : ℝ) : ℝ := 4 * uniformCost * divisorTail H

/-- The new allowance is nonnegative at every height. -/
theorem tailAllowance_nonneg (H : ℝ) : 0 ≤ tailAllowance H := by
  unfold tailAllowance divisorTail
  apply mul_nonneg (by positivity [uniformCost_pos])
  apply tsum_nonneg
  intro ρ
  split_ifs <;> simp [divisorWeight_nonneg]

/-- The exact signed outside-zero sum has the width-independent allowance,
with every actual zero and its analytic multiplicity retained. -/
theorem abs_tsum_outside_le_uniform {b σ t H : ℝ} (hb : 0 < b) (hbu : b ≤ 1)
    (hσ : 1 / 2 < σ) (hσu : σ ≤ 1) (hs : (1 - σ) ^ 2 ≤ b)
    (ht : 2 * |t| ≤ H) (hH : 1 ≤ H) :
    |∑' ρ : NontrivialZetaZero, outside b σ t H ρ| ≤ tailAllowance H := by
  have hi := summable_outside hb hσ.le hσu hs ht hH
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero, |outside b σ t H ρ| := norm_tsum_le_tsum_norm hi.norm
    _ ≤ ∑' ρ : NontrivialZetaZero, 4 * uniformCost *
        (if H < |ρ.1.im| then divisorWeight ρ else 0) :=
      hi.norm.tsum_le_tsum (abs_outside_le_uniform hb hbu hσ hσu hs ht)
        ((summable_divisorTail_terms H).mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The uniform outside allowance vanishes using only the actual divisor
summability, without a quantitative rate for the zero-free margin. -/
theorem tendsto_tailAllowance : Tendsto tailAllowance atTop (𝓝 0) := by
  change Tendsto (fun H : ℝ => 4 * uniformCost * divisorTail H) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_divisorTail.const_mul (4 * uniformCost)

/-- The actual divisor growth estimate makes the new allowance at most
`K / sqrt(H)`, removing the former inverse-margin logarithmic loss. -/
theorem exists_tailAllowance_sqrt_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H → tailAllowance H ≤ K / Real.sqrt H := by
  obtain ⟨C, hC, hbound⟩ := GaussianFermiZeroTailRate.exists_divisorTail_sqrt_bound
  refine ⟨4 * uniformCost * C, by positivity [uniformCost_pos], ?_⟩
  intro H hH
  exact (mul_le_mul_of_nonneg_left (hbound H hH)
    (by positivity [uniformCost_pos] : 0 ≤ 4 * uniformCost)).trans_eq (by ring)

/-- One unconditional inverse-square-root height bound controls every
admissible outside-zero sum, with no scale-dependent constant. -/
theorem exists_uniform_outside_sqrt_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ H b σ t : ℝ, 1 ≤ H → 0 < b → b ≤ 1 →
      1 / 2 < σ → σ ≤ 1 → (1 - σ) ^ 2 ≤ b → 2 * |t| ≤ H →
      |∑' ρ : NontrivialZetaZero, outside b σ t H ρ| ≤ K / Real.sqrt H := by
  obtain ⟨K, hK, hbound⟩ := exists_tailAllowance_sqrt_bound
  refine ⟨K, hK, ?_⟩
  intro H b σ t hH hb hbu hσ hσu hs ht
  exact (abs_tsum_outside_le_uniform hb hbu hσ hσu hs ht hH).trans (hbound H hH)

/-- One height threshold bounds the entire admissible family of outside
zero sums, including all evaluation ordinates up to half that height. -/
theorem eventually_all_outside_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ b σ t : ℝ, 0 < b → b ≤ 1 → 1 / 2 < σ → σ ≤ 1 →
      (1 - σ) ^ 2 ≤ b → 2 * |t| ≤ H →
      |∑' ρ : NontrivialZetaZero, outside b σ t H ρ| < ε := by
  filter_upwards [tendsto_tailAllowance.eventually (gt_mem_nhds hε),
    eventually_ge_atTop (1 : ℝ)] with H htail hH
  intro b σ t hb hbu hσ hσu hs ht
  exact (abs_tsum_outside_le_uniform hb hbu hσ hσu hs ht hH).trans_lt htail

/-- At any proved common band margin, selecting finitely many zeros costs
only the new height-dependent allowance. No lower comparison with a previous
margin or quantitative margin rate is needed. -/
theorem selected_zero_sum_le_full_add_uniform {B m H t : ℝ} (hB : 0 < B) (hBu : B ≤ 1)
    (ht : 2 * |t| ≤ H) (hH : 1 ≤ H) (hm : 0 ≤ m) (hmu : m ≤ 1 / 4) (hs : m ^ 2 ≤ B)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ ρ ∈ S, contribution B (1 - m) t ρ) ≤
      (∑' ρ : NontrivialZetaZero, contribution B (1 - m) t ρ) + tailAllowance H := by
  have hσ : 1 / 2 < 1 - m := by linarith
  have hσu : 1 - m ≤ 1 := by linarith
  have hscale : (1 - (1 - m)) ^ 2 ≤ B := by simpa using hs
  have hin : Summable (inside B (1 - m) t H) :=
    summable_of_hasFiniteSupport (finite_support_inside B (1 - m) t (by linarith))
  have hn (ρ : NontrivialZetaZero) : 0 ≤ inside B (1 - m) t H ρ := by
    unfold inside
    split_ifs with hρ
    · exact contribution_nonneg_of_strip hB hmu t ρ (hzeros ρ hρ).1 (hzeros ρ hρ).2
    · exact le_rfl
  have hsel : (∑ ρ ∈ S, contribution B (1 - m) t ρ) ≤
      ∑' ρ : NontrivialZetaZero, inside B (1 - m) t H ρ := by
    calc
      _ = ∑ ρ ∈ S, inside B (1 - m) t H ρ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        simp only [inside, if_pos (hS ρ hρ)]
      _ ≤ _ := hin.sum_le_tsum S (fun ρ _ => hn ρ)
  have htail := (abs_le.mp (abs_tsum_outside_le_uniform hB hBu hσ hσu hscale ht hH)).1
  have hsplit := zero_sum_eq_inside_add_outside hB hσ.le hσu hscale ht hH
  linarith

/-- The improved full phase budget retains the literal signed prime sum,
all selected zeros and every multiplicity. Its outside cost has no width or
inverse-margin factor, for any finite nonnegative coefficient family. -/
theorem selected_zero_phase_budget_with_uniform_tail {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) {m H b c t : ℝ} (hH : 1 ≤ H)
    (hb : 0 < b) (hc : 0 < c) (hu : b + c ≤ 1)
    (hm : 0 ≤ m) (hmu : m ≤ 1 / 4) (hs : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ j ∈ J, w j * ∑ ρ ∈ S, contribution (b + c) (1 - m) (ω j * t) ρ) +
      (∑ j ∈ J, w j * GaussianFermiPrimeFormula.primeSum (1 - 2 * m) (b + c) (ω j * t)) ≤
      (∑ j ∈ J, w j * (GaussianFermiPoleFormula.polePair (b + c) (1 - m) (ω j * t) -
        Real.log Real.pi / 4 + GaussianFermiPoleFormula.digammaAverage (1 - 2 * m) b c (ω j * t))) +
      (∑ j ∈ J, w j) * tailAllowance H := by
  have hbound : (∑ j ∈ J, w j * ∑ ρ ∈ S, contribution (b + c) (1 - m) (ω j * t) ρ) ≤
      ∑ j ∈ J, w j * ((∑' ρ : NontrivialZetaZero, contribution (b + c) (1 - m) (ω j * t) ρ) +
        tailAllowance H) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (selected_zero_sum_le_full_add_uniform (add_pos hb hc) hu (ht j hj) hH hm hmu hs hzeros S hS)
      (hw j hj)
  simp_rw [GaussianFermiPoleFormula.zero_side_eq_poles_digamma_sub_prime hb hc
    (by linarith : 1 / 2 ≤ 1 - m), show 2 * (1 - m) - 1 = 1 - 2 * m by ring,
    mul_add, mul_sub] at hbound
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul] at hbound
  linarith

/-- The actual global Fermi strip discharges every zero-location premise
of the improved signed phase budget, for all admissible finite families. -/
theorem fermi_selected_zero_phase_budget_with_uniform_tail {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) {H b c t : ℝ} (hH : 1 ≤ H)
    (hb : 0 < b) (hc : 0 < c) (hu : b + c ≤ 1)
    (hs : zetaFermiZeroMargin H ^ 2 ≤ b + c) (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    let m := zetaFermiZeroMargin H;
    (∑ j ∈ J, w j * ∑ ρ ∈ S, contribution (b + c) (1 - m) (ω j * t) ρ) +
      (∑ j ∈ J, w j * GaussianFermiPrimeFormula.primeSum (1 - 2 * m) (b + c) (ω j * t)) ≤
      (∑ j ∈ J, w j * (GaussianFermiPoleFormula.polePair (b + c) (1 - m) (ω j * t) -
        Real.log Real.pi / 4 + GaussianFermiPoleFormula.digammaAverage (1 - 2 * m) b c (ω j * t))) +
      (∑ j ∈ J, w j) * tailAllowance H := by
  apply selected_zero_phase_budget_with_uniform_tail J w ω hw hH hb hc hu
    (zetaFermiZeroMargin_bounds H).1.le (zetaFermiZeroMargin_bounds H).2.le hs ?_ ht S hS
  intro ρ hρ
  have hm := zetaFermiZeroMargin_antitone_abs
    (show |ρ.1.im| ≤ |H| by rwa [abs_of_nonneg (by linarith : 0 ≤ H)])
  have hz := nontrivialZetaZero_mem_fermi_strip ρ
  exact ⟨hm.trans hz.1.le, by linarith [hz.2]⟩

end
end RiemannGaussian.GaussianFermiFisherTail
