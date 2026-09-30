/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszExposedModeCoupling
import RiemannGaussian.ZetaRegularCorrectionVariation

/-!
# Joint payment of the full Gamma completion correction

The actual completion retains its complex phase. Its exact digamma
recurrence cancels the reciprocal at zero and bounds its derivative
uniformly on the positive half-plane. Cauchy's estimate pays its marked
moments together with the unchanged ordered cofactor on the whole Fourier
axis. The zeta pole and the selected zero remain outside this payment.
-/

namespace RiemannGaussian.ZetaRieszCompletionPayment
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Metric Set Topology
open ZetaRieszMarkedLogDerivative ZetaRieszMarkedPrimeCompletion
open ZetaRieszOrderedEulerBound ZetaRieszMarkedEuler
open ZetaRieszExposedModeCoupling ZetaRieszShiftedCenter

/-- The exact two-frequency completion difference, before moments. -/
def completionDifference (xi : ℝ) (s : ℂ) : ℂ :=
  zetaGlobalRegularCorrection s-zetaGlobalRegularCorrection (s+Complex.I*xi)

/-- Both translated corrections are analytic on the same half-plane. -/
theorem analyticAt_completionDifference {s : ℂ} (hs : 0 < s.re) (xi : ℝ) :
    AnalyticAt ℂ (completionDifference xi) s := by
  have ht : 0 < (s+Complex.I*xi).re := by simpa using hs
  exact (analyticAt_regularCorrection hs).sub
    ((analyticAt_regularCorrection ht).comp (f := fun z : ℂ => z+Complex.I*xi)
      (analyticAt_id.add analyticAt_const))

/-- The Fourier zero is uniform over the entire positive half-plane. -/
theorem completionDifference_bound {s : ℂ} (hs : 0 < s.re) (xi : ℝ) :
    ‖completionDifference xi s‖ ≤ |xi| := by
  unfold completionDifference
  rw [norm_sub_rev]
  simpa only [add_sub_cancel_left,norm_mul,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs] using
    norm_zetaGlobalRegularCorrection_sub_le hs
      (show 0 < (s+Complex.I*xi).re by simpa using hs)

/-- Cauchy's radius 3/4 is available uniformly in both frequencies. -/
theorem completionDifference_moment_bound (k : ℕ) (y xi : ℝ) :
    ‖signedTaylorMoment k (completionDifference xi) (3/2+Complex.I*y)‖ ≤
      |xi|/(3/4 : ℝ)^k := by
  apply norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 3/4)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/4 : ℝ) ≠ 0)]
    intro z hz
    have hd := ZetaRieszEulerMoments.disc_re_lower_bound hz
    norm_num at hd
    exact (analyticAt_completionDifference (by linarith) xi).differentiableAt.differentiableWithinAt
  · intro z hz
    have hd := ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)
    norm_num at hd
    exact completionDifference_bound (by linarith) xi

/-- The full derivative is already bounded after the exact Gamma
recurrence; no logarithmic height envelope is introduced. -/
theorem completion_derivative_moment_bound (k : ℕ) (y : ℝ) :
    ‖signedTaylorMoment k (deriv zetaGlobalRegularCorrection) (3/2+Complex.I*y)‖ ≤
      (3/4 : ℝ)⁻¹^k := by
  apply (norm_signedTaylorMoment_le (C := 1) (by norm_num : (0 : ℝ) < 3/4) ?_ ?_ k).trans_eq
    (by simp only [one_div,inv_pow])
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/4 : ℝ) ≠ 0)]
    intro z hz
    have hd := ZetaRieszEulerMoments.disc_re_lower_bound hz
    norm_num at hd
    exact ((analyticAt_regularCorrection (by linarith)).deriv).differentiableAt.differentiableWithinAt
  · intro z hz
    have hd := ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)
    norm_num at hd
    exact norm_deriv_zetaGlobalRegularCorrection_le (by linarith)

/-- All nonconstant completion moments have a height-independent bound. -/
theorem completion_moment_bound (k : ℕ) (y : ℝ) :
    ‖signedTaylorMoment (k+1) zetaGlobalRegularCorrection (3/2+Complex.I*y)‖ ≤
      (3/4 : ℝ)⁻¹^k := by
  have h := completion_derivative_moment_bound k y
  rw [signedTaylorMoment_deriv] at h
  simp only [norm_neg,norm_mul,Complex.norm_natCast] at h
  have hk : (1 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  nlinarith [norm_nonneg (signedTaylorMoment (k+1) zetaGlobalRegularCorrection (3/2+Complex.I*y))]

/-- The unused order zero is zero. All original middle and least-prime
orders remain; the marked rectangle itself has positive order. -/
def completionMark : ℕ → ℂ → ℝ → ℂ
  | 0, _, _ => 0
  | k+1, s, xi =>
    (signedTaylorMoment k zetaGlobalRegularCorrection s-
      signedTaylorMoment k zetaGlobalRegularCorrection (s+Complex.I*xi))/(k+1)

/-- Taking the difference before the moment preserves the Fourier zero. -/
theorem completionMark_eq_moment (k : ℕ) {s : ℂ} (hs : 0 < s.re) (xi : ℝ) :
    completionMark (k+1) s xi = signedTaylorMoment k (completionDifference xi) s/(k+1) := by
  have ht : 0 < (s+Complex.I*xi).re := by simpa using hs
  have ha : AnalyticAt ℂ (fun z => zetaGlobalRegularCorrection (z+Complex.I*xi)) s :=
    (analyticAt_regularCorrection ht).comp (f := fun z : ℂ => z+Complex.I*xi)
      (analyticAt_id.add analyticAt_const)
  have he : signedTaylorMoment k (fun z => zetaGlobalRegularCorrection (z+Complex.I*xi)) s =
      signedTaylorMoment k zetaGlobalRegularCorrection (s+Complex.I*xi) := by
    exact congrArg (fun v => (-1 : ℂ)^k/(k.factorial : ℂ)*v)
      (congrFun (iteratedDeriv_comp_add_const k zetaGlobalRegularCorrection (Complex.I*xi)) s)
  unfold completionDifference
  rw [signedTaylorMoment_sub k (analyticAt_regularCorrection hs) ha,he]
  rfl

/-- The marked completion retains a linear Fourier zero. -/
theorem completionMark_small {j : ℕ} (hj : 0 < j) (y xi : ℝ) :
    ‖completionMark j (3/2+Complex.I*y) xi‖ ≤ |xi| *(1001/2000 : ℝ)⁻¹^j := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [completionMark_eq_moment k (by norm_num),norm_div]
  have hk : (1 : ℝ) ≤ ‖(k : ℂ)+1‖ := by norm_cast
  apply (div_le_self (norm_nonneg _) hk).trans
  apply (completionDifference_moment_bound k y xi).trans
  rw [div_eq_mul_inv,← inv_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg xi)
  calc
    _ ≤ (3/4 : ℝ)⁻¹^(k+1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ (3/4)⁻¹) k]
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Positive derivative moments also have a frequency-independent bound. -/
theorem completionMark_large {j : ℕ} (hj : 2 ≤ j) (y xi : ℝ) :
    ‖completionMark j (3/2+Complex.I*y) xi‖ ≤ 2*(1001/2000 : ℝ)⁻¹^j := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
  have he : (3/2+Complex.I*(y : ℂ))+Complex.I*xi = 3/2+Complex.I*(y+xi : ℝ) := by push_cast; ring
  rw [show 2+k=(k+1)+1 by omega,completionMark,he,norm_div]
  have hk : (1 : ℝ) ≤ ‖((k+1 : ℕ) : ℂ)+1‖ := by norm_cast; omega
  apply (div_le_self (norm_nonneg _) hk).trans
  apply (norm_sub_le _ _).trans
  apply (add_le_add (completion_moment_bound k y) (completion_moment_bound k (y+xi))).trans
  have hpow : (3/4 : ℝ)⁻¹^k ≤ (1001/2000 : ℝ)⁻¹^((k+1)+1) := by
    apply (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3/4)⁻¹)
      (by norm_num : (3/4 : ℝ)⁻¹ ≤ (1001/2000 : ℝ)⁻¹) k).trans
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- The actual completion mark inside the unchanged ordered cofactor
and factorial rectangle. -/
def completionSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    completionMark j s xi*cofactor A N j h s xi

private theorem coupled_symbol_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y xi : ℝ) {u B V : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*f r) ≤ V)
    (hmark : ∀ j ∈ Finset.range (N+2), ∀ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
      ‖completionMark j (3/2+Complex.I*y) xi‖ ≤ B*(1001/2000 : ℝ)⁻¹^j) :
    ‖(u : ℂ)^(N+1)*completionSymbol A N (3/2+Complex.I*y) xi‖ ≤
      2*Real.exp (4*mass (3/2-safeRadius))*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*B*V := by
  have hR := safeRadius_pos
  unfold completionSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := 2*Real.exp (4*mass (3/2-safeRadius))*(9999/10000 : ℝ)^N*B*V)
    (by positivity) ?_).trans_eq (by ring)
  intro j hj h hh
  have hm := hmark j hj h hh
  have hc := cofactor_bound A h16 N j h hh
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi f hf hphase
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
  have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,norm_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hm hc (norm_nonneg _) (by positivity))
    (pow_nonneg hu _)).trans
  calc
    _ = (u^(N+1)*(1001/2000 : ℝ)⁻¹^j*safeRadius⁻¹^(N+1-j))*
        (Real.exp (4*mass (3/2-safeRadius))*B*V) := by ring
    _ ≤ (2*(9999/10000 : ℝ)^N)*(Real.exp (4*mass (3/2-safeRadius))*B*V) :=
      mul_le_mul_of_nonneg_right (coupled_order_bound hu hU hj hh) (by positivity)
    _ = _ := by ring

/-- Two retained Fourier zeros cancel the singular Riesz denominator. -/
theorem completionSymbol_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y xi : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*completionSymbol A N (3/2+Complex.I*y) xi‖ ≤
      couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*xi^2 := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hlog := logMass_nonneg hs
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r)) ≤
      |xi| *logMass (3/2-safeRadius) := by
    simp_rw [show ∀ r : ℕ, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r) =
      |xi| *(Real.log r*zetaPrimeExpWeight (3/2-safeRadius) r) from fun r => by ring]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_logMass_le A hs) (abs_nonneg xi)
  have h := coupled_symbol_bound A h16 N y xi hu hU (abs_nonneg xi)
    (mul_nonneg (abs_nonneg xi) hlog) (fun p => |xi| *Real.log p)
    (fun p => mul_nonneg (abs_nonneg xi) (Real.log_natCast_nonneg p))
    (fun p => ZetaRieszMainFrequency.phase_le_log p xi) hsum
    (fun _ _ _ hh => completionMark_small (marked_order_pos hh) y xi)
  apply h.trans
  unfold couplingConstant
  conv_rhs => rw [← sq_abs xi]
  nlinarith [show 0 ≤ Real.exp (4*mass (3/2-safeRadius))*((N : ℝ)+2)^2*
    (9999/10000 : ℝ)^N*logMass (3/2-safeRadius)*|xi|^2 by positivity]

/-- The complementary bound controls arbitrarily large frequencies. -/
theorem completionSymbol_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {N : ℕ} (hN : 2 ≤ N) (y xi : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*completionSymbol A N (3/2+Complex.I*y) xi‖ ≤
      couplingMassConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hm := mass_nonneg (3/2-safeRadius)
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*2) ≤
      mass (3/2-safeRadius)*2 := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num)
  have h := coupled_symbol_bound A h16 N y xi hu hU (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 ≤ mass (3/2-safeRadius)*2)
    (fun _ => 2) (fun _ => by norm_num) (fun p => ZetaRieszMainFrequency.phase_le_two p xi) hsum
    (fun _ _ _ hh => completionMark_large (by
      have hb := (Finset.mem_filter.mp hh).2
      omega) y xi)
  exact h.trans_eq (by unfold couplingMassConstant; ring)

/-- Both moving Fourier phases of the same completion contribution. -/
def completionPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*completionSymbol A N (3/2+Complex.I*y) xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*completionSymbol A N (3/2+Complex.I*y) (-xi)

/-- Combining the two bounds gives one integrable whole-axis profile. -/
theorem completionPair_profile (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {N : ℕ} (hN : 2 ≤ N) (y L xi : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(completionPair A N y L xi/(xi : ℂ)^2)‖ ≤
      (2*(couplingConstant+couplingMassConstant)*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N)*
        (1+xi^2)⁻¹ := by
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*(Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*
      completionSymbol A N (3/2+Complex.I*y) t)‖ =
      ‖(u : ℂ)^(N+1)*completionSymbol A N (3/2+Complex.I*y) t‖ := by
    rw [mul_left_comm,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have hn : ‖(u : ℂ)^(N+1)*completionPair A N y L xi‖ ≤
      (2*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N)*xi^2 := by
    unfold completionPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (completionSymbol_small A h16 N y xi hu hU)
      (completionSymbol_small A h16 N y (-xi) hu hU)).trans_eq (by rw [neg_sq]; ring)
  have hl : ‖(u : ℂ)^(N+1)*completionPair A N y L xi‖ ≤
      2*couplingMassConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
    unfold completionPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (completionSymbol_large A h16 hN y xi hu hU)
      (completionSymbol_large A h16 hN y (-xi) hu hU)).trans_eq (by ring)
  rw [← mul_div_assoc]
  exact (norm_div_square_profile (by positivity [couplingConstant_nonneg])
    (by positivity [couplingMassConstant_nonneg]) hn hl).trans_eq (by ring)

private theorem continuous_completionMoment (k : ℕ) (y : ℝ) :
    Continuous (fun xi : ℝ => signedTaylorMoment k zetaGlobalRegularCorrection
      (3/2+Complex.I*y+Complex.I*xi)) := by
  apply continuous_iff_continuousAt.mpr
  intro xi
  have ha := (analyticAt_regularCorrection
    (show 0 < (3/2+Complex.I*(y : ℂ)+Complex.I*(xi : ℂ)).re by norm_num)).iterated_deriv k
  have hc : ContinuousAt (fun t : ℝ => (3/2 : ℂ)+Complex.I*y+Complex.I*t) xi := by fun_prop
  have hm : ContinuousAt (fun t : ℝ => iteratedDeriv k zetaGlobalRegularCorrection
      (3/2+Complex.I*y+Complex.I*t)) xi := by
    simpa only [iteratedDeriv_eq_iterate,Function.comp_def] using ha.continuousAt.comp
      (f := fun t : ℝ => (3/2 : ℂ)+Complex.I*y+Complex.I*t) hc
  exact hm.const_mul _

private theorem measurable_completionPair (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ => completionPair A N y L xi/(xi : ℂ)^2) := by
  have hm : Measurable (fun xi : ℝ => completionSymbol A N (3/2+Complex.I*y) xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    apply Measurable.mul _ (measurable_cofactor A h16 N j h (by norm_num [safeRadius]))
    cases j with
    | zero => exact measurable_const
    | succ k =>
      unfold completionMark
      exact (measurable_const.sub (continuous_completionMoment k y).measurable).div_const _
  have hn := hm.comp measurable_neg
  unfold completionPair
  fun_prop

/-- The actual paired completion is integrable on the full frequency
axis before any sum or integral is exchanged. -/
theorem integrable_completionPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {N : ℕ} (hN : 2 ≤ N) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(completionPair A N y L xi/(xi : ℂ)^2))
      (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn).const_mul
    (2*(couplingConstant+couplingMassConstant)*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N)).mono'
  · exact ((measurable_completionPair A h16 N y L).const_mul _).aestronglyMeasurable
  · exact Eventually.of_forall (fun xi => completionPair_profile A h16 hN y L xi hu hU)

/-- The full-frequency Gamma correction with the original Riesz
prefactor, factorial rectangle and ordered cofactor. -/
def completionResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, completionPair A N y L xi/(xi : ℂ)^2

/-- A concrete source-normalized geometric saving, uniform in height,
positive moving length and the finite physical prime set. -/
theorem completionResponse_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    {N : ℕ} (hN : 2 ≤ N) (y : ℝ) {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*completionResponse A N y L‖ ≤
      (Real.pi*(couplingConstant+couplingMassConstant))*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have hi := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
      (2*(couplingConstant+couplingMassConstant)*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N))
    (Eventually.of_forall (fun xi => completionPair_profile A h16 hN y L xi hu hU))
  simp only [integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero] at hi
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold completionResponse
  rw [mul_left_comm,norm_mul]
  apply (mul_le_mul hpref hi (norm_nonneg _) (by positivity)).trans
  calc
    _ = ((N : ℝ)+1)*(Real.pi*(couplingConstant+couplingMassConstant)*
        ((N : ℝ)+2)^2*(9999/10000 : ℝ)^N) := by ring
    _ ≤ ((N : ℝ)+2)*(Real.pi*(couplingConstant+couplingMassConstant)*
        ((N : ℝ)+2)^2*(9999/10000 : ℝ)^N) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity [couplingConstant_nonneg,couplingMassConstant_nonneg]
    _ = _ := by ring

private theorem tendsto_cubic_rate :
    Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N) atTop (nhds 0) := by
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
  · ext N; simp only [pow_zero,pow_one]; ring
  · norm_num

/-- No zero hypothesis or fixed-height restriction is needed for this
component's source-scale decay. -/
theorem tendsto_completionResponse (A : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ A N → 16 ≤ p) (y L u : ℕ → ℝ)
    (hL : ∀ N, 1 ≤ L N) (hu : ∀ N, 0 ≤ u N)
    (hU : ∀ N, u N ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u N : ℂ)^(N+1)*completionResponse (A N) N (y N) (L N))
      atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ => (Real.pi*(couplingConstant+couplingMassConstant))*
    (((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    simpa only [mul_assoc] using completionResponse_bound (A N) (h16 N) hN (y N) (hL N) (hu N) (hU N)
  · simpa only [mul_zero] using tendsto_cubic_rate.const_mul (Real.pi*(couplingConstant+couplingMassConstant))

/-- Exact completion budget at every moment. The pole and the complete
xi logarithmic derivative remain with their original opposite signs. -/
theorem moment_completion_split {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    zetaPrimeLogMoment k s = ((s-1)⁻¹)^(k+1)+
      signedTaylorMoment k zetaGlobalRegularCorrection s-
        signedTaylorMoment k (logDeriv riemannXi) s := by
  have hp : AnalyticAt ℂ (fun z : ℂ => (z-1)⁻¹) s := by
    apply (analyticAt_id.sub analyticAt_const).inv
    apply Complex.ne_zero_of_re_pos
    simpa using sub_pos.mpr hs
  have he : (fun z : ℂ => -logDeriv riemannZeta z) =ᶠ[nhds s]
      (fun z => (z-1)⁻¹+zetaGlobalRegularCorrection z-logDeriv riemannXi z) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    have hb := zeta_global_complex_budget hz
    rw [one_div] at hb
    linear_combination hb
  unfold zetaPrimeLogMoment
  have ha : AnalyticAt ℂ (fun z : ℂ => (z-1)⁻¹+zetaGlobalRegularCorrection z) s :=
    hp.add (analyticAt_regularCorrection (by linarith))
  rw [signedTaylorMoment_congr k he,
    signedTaylorMoment_sub k ha (analyticAt_xi_logDeriv hs),
    signedTaylorMoment_add k hp (analyticAt_regularCorrection (by linarith)),
    signedTaylorMoment_inv_sub_one]

/-- Subtracting this paid mark does not remove any zero mode or pole. -/
theorem logDifference_sub_completionMark (k : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    logDifference (k+1) s xi-completionMark (k+1) s xi =
      modeDifference (1-s) (k+1) xi-
        (signedTaylorMoment k (logDeriv riemannXi) s-
          signedTaylorMoment k (logDeriv riemannXi) (s+Complex.I*xi))/(k+1) := by
  rw [logDifference,completionMark,moment_completion_split hs,
    moment_completion_split (show 1 < (s+Complex.I*xi).re by simpa using hs)]
  simp only [modeDifference,show -(1-s) = s-1 by ring,
    show Complex.I*(xi : ℂ)-(1-s) = s+Complex.I*xi-1 by ring,
    Nat.cast_add,Nat.cast_one]
  ring

/-- The exact surviving signed symbol: the original pole minus the
full xi derivative, still coupled to every cofactor and order mask. -/
theorem logSymbol_sub_completionSymbol (A : Finset ℕ) (N : ℕ) {s : ℂ}
    (hs : 1 < s.re) (xi : ℝ) :
    logSymbol A N s xi-completionSymbol A N s xi =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        (modeDifference (1-s) j xi-
          (signedTaylorMoment (j-1) (logDeriv riemannXi) s-
            signedTaylorMoment (j-1) (logDeriv riemannXi) (s+Complex.I*xi))/(j : ℂ))*
              cofactor A N j h s xi := by
  unfold logSymbol completionSymbol
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← sub_mul]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (marked_order_pos hh))
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using
    congrArg (fun v : ℂ => v*cofactor A N (k+1) h s xi)
      (logDifference_sub_completionMark k hs xi)

/-- Genuine integrability permits the Gamma subtraction inside the
full Fourier integral. The two phases and the complete cofactor remain
in the same signed integrand. -/
theorem logResponse_sub_completionResponse (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) (h16 : ∀ p ∈ A, 16 ≤ p)
    {N : ℕ} (hN : 2 ≤ N) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p) (y L : ℝ) :
    logResponse A N (3/2+Complex.I*y) L-completionResponse A N y L =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Ioi 0,
          (logPair A N (3/2+Complex.I*y) L xi-completionPair A N y L xi)/(xi : ℂ)^2 := by
  have hs : 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius := by norm_num [safeRadius]
  have hi : IntegrableOn (fun xi : ℝ => logPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2)
      (Ioi 0) := by
    simp_rw [logPair_split A N (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re),add_div]
    apply Integrable.add _ (integrable_properPair A h16 N y L)
    simp_rw [completedPair_split A hA N (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re),add_div]
    exact (ZetaRieszMarkedSeparation.integrable_separatedPair A hA h16 N hhead safeRadius_pos hs L).add
      (ZetaRieszMarkedPrimeCompletion.integrable_completionPair A h16 N hgap hs L)
  have hc : IntegrableOn (fun xi : ℝ => completionPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
    have hscaled := integrable_completionPair A h16 hN y L (u := 1/2) (by norm_num)
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    exact (integrable_const_mul_iff (μ := volume.restrict (Ioi (0 : ℝ)))
      (isUnit_iff_ne_zero.mpr (pow_ne_zero (N+1) (by norm_num : ((1/2 : ℝ) : ℂ) ≠ 0))) _).mp hscaled
  unfold logResponse completionResponse
  simp_rw [sub_div]
  rw [integral_sub hi hc,mul_sub]

/-- The actual moving prime set discharges every support premise of the
integral subtraction, without changing the physical cutoff. -/
theorem eventually_logMain_sub_completionResponse {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      logMain u y N-completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
        (SquarefreeVaughanLogSource.length u N) =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(SquarefreeVaughanLogSource.length u N : ℂ))*
        ∫ xi : ℝ in Ioi 0,
          (logPair (ZetaRieszRoughEulerTransfer.roughPrimes u N) N (3/2+Complex.I*y)
              (SquarefreeVaughanLogSource.length u N) xi-
            completionPair (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
              (SquarefreeVaughanLogSource.length u N) xi)/(xi : ℂ)^2 := by
  filter_upwards [ZetaRieszMarkedPrimeCompletion.eventually_rough_support hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hgap hN
  exact logResponse_sub_completionResponse _
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_prime hp)
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) hN
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_head hp) hgap y _

/-- Keep all previous mode payments, and subtract only the independently
paid full-frequency completion response. -/
def completionReducedMain (W : Finset NontrivialZetaZero) (u y : ℝ) (N : ℕ) : ℂ :=
  reducedMain W u y N-completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
    (SquarefreeVaughanLogSource.length u N)

/-- The old disjoint genuine-zero payments and the new completion
payment share an explicit geometric bound. -/
theorem logMain_completionReduced_bound (W : Finset NontrivialZetaZero) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-completionReducedMain W u y N)‖ ≤
      (paidConstant W y+Real.pi*(couplingConstant+couplingMassConstant))*
        ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  unfold completionReducedMain
  rw [sub_sub_eq_add_sub,show logMain u y N+
    completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
      (SquarefreeVaughanLogSource.length u N)-reducedMain W u y N =
      (logMain u y N-reducedMain W u y N)+
        completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
          (SquarefreeVaughanLogSource.length u N) by ring,mul_add]
  apply (norm_add_le _ _).trans
  exact (add_le_add (logMain_reduced_bound W hu hU y N)
    (completionResponse_bound _ (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp)
      hN y (ZetaRieszHeadOrders.one_le_length u N) hu hU)).trans_eq (by ring)

/-- The new reduced main retains the exact original literal packet,
including all previously paid errors. This is not a bound for the main. -/
theorem tendsto_completionReduced_sub_current (W : Finset NontrivialZetaZero) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (completionReducedMain W u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have hc := tendsto_completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) (fun _ => y)
    (SquarefreeVaughanLogSource.length u) (fun _ => u)
    (ZetaRieszHeadOrders.one_le_length u) (fun _ => by linarith) (fun _ => hU)
  have h := (tendsto_reduced_sub_current W hu hU y).sub
    (hc.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_zero] at h
  convert h using 1
  ext j
  dsimp only [Function.comp_def,completionReducedMain]
  ring

end
end RiemannGaussian.ZetaRieszCompletionPayment
