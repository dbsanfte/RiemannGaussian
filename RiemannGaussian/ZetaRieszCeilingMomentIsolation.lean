/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingSharpMultiplicity
import RiemannGaussian.ZetaExposedMovingModes
import RiemannGaussian.ZetaZeroFilterCost
import RiemannGaussian.ZetaEulerPoissonBound

/-!
# A finite-order arithmetic test for the unchanged ceiling

The COMPLETE von Mangoldt moment is bounded by its actual real-axis mass.
The selected source is kept exactly. The competing modes are priced by
their actual separation and their full multiplicity-weighted Poisson mass,
and the residual and reflected channels have explicit geometric bounds.

This supplies an independent multiplicity inequality at EVERY finite order.
It does not assert a uniform exposed gap. A numerical test strictly below
two excludes multiple zeros and pays the SAME joinedPhysical ceiling there.
The all-height ceiling throughout the original fixed strip remains open.
No literal mask, order, phase, count or carrier is replaced.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Complex Filter Topology MeromorphicOn Metric Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingMomentIsolation

/-- The complete, multiplicity-weighted local coefficient. -/
def modeCoefficient (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ) (z : ℂ) : ℝ :=
  (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) z : ℝ)

private theorem modeCoefficient_nonneg (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ) (z : ℂ) :
    0 <= modeCoefficient r y z := by
  unfold modeCoefficient
  have h : (0 : ℤ) <= divisor (localZetaPoleRemoved y)
      (ball 0 (adaptiveZetaCanonicalRadius r y)) z :=
    ((analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y).mono
      ball_subset_closedBall).divisor_nonneg z
  exact_mod_cast h

/-- The local divisor coefficient is the actual analytic multiplicity
of the corresponding genuine zero. -/
theorem modeCoefficient_eq_multiplicity (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ)
    {z : ℂ} (hz : z ∈ adaptiveZetaZeroSupport r y) :
    modeCoefficient r y z = analyticZetaZeroMultiplicity
      ⟨3/2+I*y+z, ZetaZeroFilterCost.support_is_zero r y hz⟩ := by
  let tau : NontrivialZetaZero :=
    ⟨3/2+I*y+z, ZetaZeroFilterCost.support_is_zero r y hz⟩
  have hmem := (divisor (localZetaPoleRemoved y)
    (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain
      ((mem_adaptiveZetaZeroSupport r y z).mp hz)
  have hf : localZetaPoleRemoved y = riemannZeta₁ ∘ (· + (3/2+I*(y : ℂ))) := by
    funext w
    simp only [localZetaPoleRemoved, Function.comp_def, add_comm w]
  unfold modeCoefficient
  rw [((analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y).mono
    ball_subset_closedBall).meromorphicOn.divisor_apply hmem, hf,
    meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  have he : z+(3/2+I*(y : ℂ)) = tau.1 := by dsimp [tau]; ring
  rw [he, meromorphicOrderAt_riemannZeta₁_nontrivialZero tau]
  simp [tau]

/-- The COMPLETE local multiplicity mass has a height-only bound. In
particular, the number of nodes is not multiplied by a second multiplicity
bound; the signed spectral family is summed once. -/
theorem local_mode_mass_le (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ) :
    (∑ z ∈ adaptiveZetaZeroSupport r y, modeCoefficient r y z) <=
      2*ZetaGaussianPhaseAllowance.xiAllowance (3/2) y := by
  let S := adaptiveZetaZeroSupport r y
  let f : {z // z ∈ S} → NontrivialZetaZero :=
    fun z => ⟨3/2+I*y+z.1, ZetaZeroFilterCost.support_is_zero r y z.2⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact add_left_cancel (congrArg (fun tau : NontrivialZetaZero => tau.1) he)
  let s : ℂ := 3/2+I*y
  have hs : 1 <= s.re := by norm_num [s]
  have hp (z : {z // z ∈ S}) :
      modeCoefficient r y z.1 <= 2*zetaGlobalPoissonSummand s (f z) := by
    have hm : 0 <= (analyticZetaZeroMultiplicity (f z) : ℝ) := by positivity
    have hd : (1/2 : ℝ) < s.re-(f z).1.re := by
      dsimp only [s]
      norm_num
      linarith [(f z).re_lt_one]
    have he : s-(f z).1 = -z.1 := by dsimp [s, f]; ring
    have hn : Complex.normSq (s-(f z).1) <= 1 := by
      rw [he, <-Complex.sq_norm, norm_neg]
      have h := ZetaZeroFilterCost.support_norm_lt_one r y z.2
      nlinarith [norm_nonneg z.1]
    have hz : 0 < Complex.normSq (s-(f z).1) :=
      Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos (by
        simp only [Complex.sub_re]; linarith))
    rw [modeCoefficient_eq_multiplicity r y z.2]
    change (analyticZetaZeroMultiplicity (f z) : ℝ) <= _
    unfold zetaGlobalPoissonSummand
    rw [<-mul_div_assoc]
    apply (le_div_iff₀ hz).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hn hm,
      mul_le_mul_of_nonneg_left hd.le hm]
  have hc := (Finset.sum_le_sum (fun z (_hz : z ∈ S.attach) => hp z))
  rw [Finset.sum_attach] at hc
  have hsum : (∑ z ∈ S.attach, zetaGlobalPoissonSummand s (f z)) =
      ∑ tau ∈ S.attach.image f, zetaGlobalPoissonSummand s tau :=
    (Finset.sum_image hf.injOn).symm
  simp only [<-Finset.mul_sum] at hc
  rw [hsum] at hc
  have hb := sum_zetaGlobalPoissonSummand_le hs (S.attach.image f)
  have he := ZetaGaussianPhaseAllowance.xi_le_allowance (σ := 3/2) (by norm_num) y
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
  change (logDeriv riemannXi s).re <= _ at he
  linarith only [hc, hb, he]

/-- An explicit real-axis Euler value pays the constant in the preceding
mass bound; no unknown zero-count constant remains. -/
theorem local_mode_mass_height (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ) :
    (∑ z ∈ adaptiveZetaZeroSupport r y, modeCoefficient r y z) <=
      localZetaLogHeight y+11 := by
  have he := neg_logDeriv_riemannZeta_real_le_global (u := 3/2) (by norm_num)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3/2)
  have ht : Real.log (3/2+|y|) <= localZetaLogHeight y := by
    apply Real.log_le_log (by positivity)
    change 3/2+|y| <= |y|+22
    linarith
  have hm := local_mode_mass_le r y
  unfold ZetaGaussianPhaseAllowance.xiAllowance at hm
  norm_num at hm he hl
  linarith only [hm, he, hl, ht]

/-- At height zero the whole canonical divisor is empty, for every
allowed local radius. This uses the proved actual zero-height restriction. -/
theorem real_axis_support_empty (r : Set.Ico (3/4 : ℝ) 1) :
    adaptiveZetaZeroSupport r 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  let tau : NontrivialZetaZero :=
    ⟨3/2+I*(0 : ℝ)+z, ZetaZeroFilterCost.support_is_zero r 0 hz⟩
  have hheight := nontrivialZetaZero_one_lt_abs_im tau
  have hz1 := ZetaZeroFilterCost.support_norm_lt_one r 0 hz
  have him : |tau.1.im| <= ‖z‖ := by
    simpa [tau] using Complex.abs_im_le_norm z
  linarith

private theorem scaled_residual_bound (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ)
    {u : ℝ} (hu : 0 <= u) (n : ℕ) :
    ‖(u : ℂ)^(n+1)*adaptiveZetaResidualMoment r y n‖ <=
      160*u*localZetaLogHeight y*(n+1)*(10*u/7)^n := by
  have hR := (adaptiveZetaCanonicalRadius_spec r y).1
  have hr : (3/4 : ℝ) < adaptiveZetaCanonicalRadius r y :=
    r.property.1.trans_lt hR
  have hs := norm_adaptiveZetaResidualMoment_le r y n
    (q := 7/10) (by norm_num) (by linarith)
  have hheight := two_lt_localZetaLogHeight y
  have hd : 8*localZetaLogHeight y/(adaptiveZetaCanonicalRadius r y-7/10) <=
      160*localZetaLogHeight y := by
    apply (div_le_iff₀ (by linarith : 0 < adaptiveZetaCanonicalRadius r y-7/10)).mpr
    nlinarith only [hr, hheight]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hs (pow_nonneg hu _)).trans
  calc
    _ <= u^(n+1)*((n+1)* (160*localZetaLogHeight y)/(7/10)^n) := by gcongr
    _ = _ := by
      have hp : ((7/10 : ℝ)^n)⁻¹ = (10/7)^n := by rw [<-inv_pow]; norm_num
      rw [div_eq_mul_inv, hp, pow_succ,
        show 10*u/7 = u*(10/7) by ring, mul_pow]
      ring

/-- The arithmetic modulus at any fixed height is bounded by the
COMPLETE real-axis moment with the same logged order and factorial. -/
theorem norm_moment_le_real_axis (y : ℝ) (n : ℕ) :
    ‖zetaPrimeLogMoment n (3/2+I*y)‖ <= (zetaPrimeLogMoment n (3/2 : ℂ)).re := by
  let f : ℕ → ℝ := fun m => ArithmeticFunction.vonMangoldt m *
    (Real.log m)^n/(n.factorial : ℝ)*zetaPrimeExpWeight (3/2) m
  have hzero := hasSum_zetaPrimeLogMoment (s := (3/2 : ℂ)) (by norm_num) n
  have hreal (m : ℕ) :
      (ArithmeticFunction.vonMangoldt m : ℂ)*
        ((Real.log m : ℂ)^n/(n.factorial : ℂ))*zetaPrimeFeature (3/2) m =
      (f m : ℂ) := by
    simp only [f, zetaPrimeFeature, zetaPrimeExpWeight, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_ofNat]
    push_cast
    ring
  have hr := hzero.congr_fun (fun m => (hreal m).symm)
  have hsum := Complex.reCLM.hasSum hr
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hsum
  have hp := hasSum_zetaPrimeLogMoment (s := 3/2+I*y) (by norm_num) n
  have hnorm (m : ℕ) : ‖(ArithmeticFunction.vonMangoldt m : ℂ)*
      ((Real.log m : ℂ)^n/(n.factorial : ℂ))*zetaPrimeFeature (3/2+I*y) m‖ = f m := by
    rw [norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg _), Complex.norm_natCast,
      norm_zetaPrimeFeature]
    norm_num [f]
    left
    ring
  calc
    _ <= ∑' m, ‖(ArithmeticFunction.vonMangoldt m : ℂ)*
        ((Real.log m : ℂ)^n/(n.factorial : ℂ))*zetaPrimeFeature (3/2+I*y) m‖ :=
      by rw [<-hp.tsum_eq]; exact norm_tsum_le_tsum_norm hp.summable.norm
    _ = ∑' m, f m := tsum_congr hnorm
    _ = _ := hsum.tsum_eq

/-- The real-axis pole is the ONLY unsaved channel of the independent
arithmetic moment bound. No selected resonant mode has been norm-paid. -/
theorem scaled_moment_bound (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ)
    {u : ℝ} (hu : 0 <= u) (n : ℕ) :
    ‖(u : ℂ)^(n+1)*zetaPrimeLogMoment n (3/2+I*y)‖ <=
      (2*u)^(n+1)+160*u*localZetaLogHeight 0*(n+1)*(10*u/7)^n := by
  have he := zetaPrimeLogMoment_eq_adaptive_modes r 0 n
  rw [real_axis_support_empty, Finset.sum_empty, sub_zero] at he
  norm_num at he
  have hphase := norm_moment_le_real_axis y n
  have hnorm := Complex.re_le_norm (zetaPrimeLogMoment n (3/2 : ℂ))
  rw [he] at hnorm
  rw [he] at hphase
  have hc := norm_sub_le ((2 : ℂ)^(n+1)) (adaptiveZetaResidualMoment r 0 n)
  have hbound : ‖(u : ℂ)^(n+1)*zetaPrimeLogMoment n (3/2+I*y)‖ <=
      (2*u)^(n+1)+‖(u : ℂ)^(n+1)*adaptiveZetaResidualMoment r 0 n‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
    rw [norm_pow] at hc
    norm_num at hc
    rw [mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left (hphase.trans (hnorm.trans hc))
      (pow_nonneg hu (n+1))]
  exact hbound.trans (add_le_add_right (scaled_residual_bound r 0 hu n) _)

private theorem norm_modes_le (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ)
    (S : Finset ℂ) (hS : S ⊆ adaptiveZetaZeroSupport r y) (f : ℂ → ℂ)
    {b : ℝ} (hb : 0 <= b) (hf : ∀ z ∈ S, ‖f z‖ <= b) (n : ℕ) :
    ‖∑ z ∈ S, (modeCoefficient r y z : ℂ)*(f z)^(n+1)‖ <=
      (localZetaLogHeight y+11)*b^(n+1) := by
  have hm : (∑ z ∈ S, modeCoefficient r y z) <= localZetaLogHeight y+11 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun z _ _ => modeCoefficient_nonneg r y z)).trans (local_mode_mass_height r y)
  calc
    _ <= ∑ z ∈ S, ‖(modeCoefficient r y z : ℂ)*(f z)^(n+1)‖ := norm_sum_le _ _
    _ <= ∑ z ∈ S, modeCoefficient r y z*b^(n+1) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (modeCoefficient_nonneg r y z)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hf z hz) _) (modeCoefficient_nonneg r y z)
    _ = (∑ z ∈ S, modeCoefficient r y z)*b^(n+1) := by rw [Finset.sum_mul]
    _ <= _ := mul_le_mul_of_nonneg_right hm (pow_nonneg hb _)

/-- The reflected channels are paid geometrically by the LOCAL Cauchy
radius. This radius is not claimed to separate competing direct zeros. -/
theorem reflected_bound (r : Set.Ico (3/4 : ℝ) 1) (y : ℝ)
    {u : ℝ} (hu : 0 <= u) (n : ℕ) :
    ‖∑ z ∈ adaptiveZetaZeroSupport r y,
      (modeCoefficient r y z : ℂ)*
        ((u : ℂ)*(-starRingEnd ℂ z/(adaptiveZetaCanonicalRadius r y : ℂ)^2))^(n+1)‖ <=
      (localZetaLogHeight y+11)*(4*u/3)^(n+1) := by
  apply norm_modes_le r y _ (fun _ h => h) _ (by positivity) _ n
  intro z hz
  have hmem := (divisor (localZetaPoleRemoved y)
    (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain
      ((mem_adaptiveZetaZeroSupport r y z).mp hz)
  have hzR : ‖z‖ <= adaptiveZetaCanonicalRadius r y := by
    exact (show ‖z‖ < adaptiveZetaCanonicalRadius r y by simpa using hmem).le
  have hR : (3/4 : ℝ) < adaptiveZetaCanonicalRadius r y :=
    r.property.1.trans_lt (adaptiveZetaCanonicalRadius_spec r y).1
  rw [norm_mul, norm_div, norm_neg, norm_conj, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hu,
    Complex.norm_real, Real.norm_of_nonneg (adaptiveZetaCanonicalRadius_pos r y).le]
  calc
    _ <= u*(adaptiveZetaCanonicalRadius r y/(adaptiveZetaCanonicalRadius r y)^2) := by gcongr
    _ = u/adaptiveZetaCanonicalRadius r y := by field_simp
    _ <= u/(3/4) := div_le_div_of_nonneg_left hu (by norm_num) hR.le
    _ = _ := by ring

/-- The actual competing divisor is bounded using ONE multiplicity sum
and the stated physical separation, with the selected mode erased first. -/
theorem competing_bound (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    {R : ℝ} (hR : 0 < R)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      R < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) (n : ℕ) :
    let r := zetaRightHalfDiscParameter rho hrho
    let u := 3/2-rho.1.re
    ‖∑ z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase (-(u : ℂ)),
      (modeCoefficient r rho.1.im z : ℂ)*((u : ℂ)*(-z⁻¹))^(n+1)‖ <=
      (localZetaLogHeight rho.1.im+11)*(u/R)^(n+1) := by
  dsimp only
  have hu : 0 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  apply norm_modes_le _ _ _ (Finset.erase_subset _ _) _ (by positivity) _ n
  intro z hz
  obtain ⟨hne, hz⟩ := Finset.mem_erase.mp hz
  have hd := ZetaExposedMovingModes.canonical_support_gap hgap
    (zetaRightHalfDiscParameter rho hrho) hz hne
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu,
    <-div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hu hR hd.le

/-- Every paid term in the finite-order multiplicity test is explicit.
The R in this formula is a competing-zero gap, not an analytic radius. -/
def momentTest (u y R : ℝ) (n : ℕ) : ℝ :=
  (2*u)^(n+1)+(localZetaLogHeight y+11)*(u/R)^(n+1)+u^(n+1)+
    160*u*(localZetaLogHeight y+localZetaLogHeight 0)*(n+1)*(10*u/7)^n+
    (localZetaLogHeight y+11)*(4*u/3)^(n+1)

/-- The SAME signed competing-zero sum from the existing selected split.
No mask or mode is completed or altered by naming this term. -/
def competingMoment (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) (n : ℕ) : ℂ :=
  let r := zetaRightHalfDiscParameter rho hrho
  let u := 3/2-rho.1.re
  ∑ z ∈ (adaptiveZetaZeroSupport r rho.1.im).erase (-(u : ℂ)),
    (modeCoefficient r rho.1.im z : ℂ)*((u : ℂ)*(-z⁻¹))^(n+1)

/-- An independent SIGNED inequality for the full selected/competing
aggregate. Unlike the isolation test, this requires NO competing gap.
Only the pole, residual, reflected and complete real-axis arithmetic
terms are bounded; the competing actual zero family stays signed. -/
theorem multiplicity_add_competing_re_le (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (n : ℕ) :
    let u := 3/2-rho.1.re
    (analyticZetaZeroMultiplicity rho : ℝ)+(competingMoment rho hrho n).re <=
      (2*u)^(n+1)+u^(n+1)+
      160*u*(localZetaLogHeight rho.1.im+localZetaLogHeight 0)*(n+1)*(10*u/7)^n+
      (localZetaLogHeight rho.1.im+11)*(4*u/3)^(n+1) := by
  dsimp only
  let r := zetaRightHalfDiscParameter rho hrho
  let u := 3/2-rho.1.re
  let v := (u : ℂ)^(n+1)*zetaPrimeLogMoment n (3/2+I*rho.1.im)
  let P := ((u : ℂ)*(1/2+I*(rho.1.im : ℂ))⁻¹)^(n+1)
  let E := (u : ℂ)^(n+1)*adaptiveZetaResidualMoment r rho.1.im n
  let F := ∑ z ∈ adaptiveZetaZeroSupport r rho.1.im, (modeCoefficient r rho.1.im z : ℂ)*
    ((u : ℂ)*(-starRingEnd ℂ z/(adaptiveZetaCanonicalRadius r rho.1.im : ℂ)^2))^(n+1)
  have hu : 0 <= u := by dsimp [u]; linarith [rho.re_lt_one]
  have hsupport : (1 : Polynomial ℂ).support = {0} := by
    ext k
    by_cases hk : k = 0 <;> simp [Polynomial.mem_support_iff, Polynomial.coeff_one, hk]
  have he := ZetaExposedMovingModes.primeFilter_selected_split rho hrho (1 : Polynomial ℂ) n
  dsimp only at he
  simp only [zetaPrimeLogFilter, adaptiveZetaResidualFilter, hsupport,
    Finset.sum_singleton, Polynomial.coeff_one_zero, one_mul, Nat.add_zero,
    Polynomial.eval_one, mul_one] at he
  have href : (u : ℂ)^(n+1)*adaptiveZetaReflectedFilter r rho.1.im 1 n = F := by
    simp only [adaptiveZetaReflectedFilter, Polynomial.eval_one, mul_one, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro z _
    simp only [modeCoefficient, Complex.ofReal_intCast, mul_pow]
    ring
  have hv : v = -(analyticZetaZeroMultiplicity rho : ℂ)-competingMoment rho hrho n+P-E+F := by
    rw [<-href]
    dsimp only [v, P, E, u, r, competingMoment]
    simp only [modeCoefficient, Complex.ofReal_intCast, mul_add, mul_sub, mul_pow] at he ⊢
    linear_combination he
  have hvre := congrArg Complex.re hv
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.natCast_re] at hvre
  have hre : (analyticZetaZeroMultiplicity rho : ℝ)+(competingMoment rho hrho n).re <=
      ‖v‖+‖P‖+‖E‖+‖F‖ := by
    have h1 := Complex.re_le_norm (-v)
    have h2 := Complex.re_le_norm P
    have h3 := Complex.re_le_norm (-E)
    have h4 := Complex.re_le_norm F
    simp only [Complex.neg_re, norm_neg] at h1 h3
    linarith only [hvre, h1, h2, h3, h4]
  have hb := scaled_moment_bound r rho.1.im hu n
  have hf := reflected_bound r rho.1.im hu n
  have hr := scaled_residual_bound r rho.1.im hu n
  have hp : ‖P‖ <= u^(n+1) := by
    have hc : 1 <= ‖(1/2 : ℂ)+I*(rho.1.im : ℂ)‖ := by
      exact (nontrivialZetaZero_one_lt_abs_im rho).le.trans (by
        simpa using Complex.abs_im_le_norm ((1/2 : ℂ)+I*(rho.1.im : ℂ)))
    dsimp only [P]
    rw [norm_pow, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu,
      <-div_eq_mul_inv]
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_self hu hc
  change ‖v‖ <= _ at hb
  change ‖F‖ <= _ at hf
  change ‖E‖ <= _ at hr
  change (analyticZetaZeroMultiplicity rho : ℝ)+(competingMoment rho hrho n).re <=
    (2*u)^(n+1)+u^(n+1)+
    160*u*(localZetaLogHeight rho.1.im+localZetaLogHeight 0)*(n+1)*(10*u/7)^n+
    (localZetaLogHeight rho.1.im+11)*(4*u/3)^(n+1)
  linarith only [hre, hb, hf, hr, hp]

/-- A genuinely independent arithmetic inequality on the selected
multiplicity, valid at EVERY finite order. No small-error premise is
assumed; all competing, reflected, pole and analytic terms are paid by
the displayed test. Orders zero and one are included. -/
theorem multiplicity_le_momentTest (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) {R : ℝ} (hR : 0 < R)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      R < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) (n : ℕ) :
    (analyticZetaZeroMultiplicity rho : ℝ) <=
      momentTest (3/2-rho.1.re) rho.1.im R n := by
  let r := zetaRightHalfDiscParameter rho hrho
  let u := 3/2-rho.1.re
  let S := adaptiveZetaZeroSupport r rho.1.im
  let v := (u : ℂ)^(n+1)*zetaPrimeLogMoment n (3/2+I*rho.1.im)
  let Q := ∑ z ∈ S.erase (-(u : ℂ)),
    (modeCoefficient r rho.1.im z : ℂ)*((u : ℂ)*(-z⁻¹))^(n+1)
  let P := ((u : ℂ)*(1/2+I*(rho.1.im : ℂ))⁻¹)^(n+1)
  let E := (u : ℂ)^(n+1)*adaptiveZetaResidualMoment r rho.1.im n
  let F := ∑ z ∈ S, (modeCoefficient r rho.1.im z : ℂ)*
    ((u : ℂ)*(-starRingEnd ℂ z/(adaptiveZetaCanonicalRadius r rho.1.im : ℂ)^2))^(n+1)
  have hu : 0 <= u := by dsimp [u]; linarith [rho.re_lt_one]
  have hsupport : (1 : Polynomial ℂ).support = {0} := by
    ext k
    by_cases hk : k = 0 <;> simp [Polynomial.mem_support_iff, Polynomial.coeff_one, hk]
  have he := ZetaExposedMovingModes.primeFilter_selected_split rho hrho (1 : Polynomial ℂ) n
  dsimp only at he
  simp only [zetaPrimeLogFilter, adaptiveZetaResidualFilter, hsupport,
    Finset.sum_singleton, Polynomial.coeff_one_zero, one_mul, Nat.add_zero,
    Polynomial.eval_one, mul_one] at he
  have href : (u : ℂ)^(n+1)*adaptiveZetaReflectedFilter r rho.1.im 1 n = F := by
    simp only [adaptiveZetaReflectedFilter, Polynomial.eval_one, mul_one, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro z _
    simp only [modeCoefficient, Complex.ofReal_intCast, mul_pow]
    ring
  have hv : v = -(analyticZetaZeroMultiplicity rho : ℂ)-Q+P-E+F := by
    rw [<-href]
    dsimp only [v, Q, P, E, u, r, S]
    simp only [modeCoefficient, Complex.ofReal_intCast, mul_add, mul_sub, mul_pow] at he ⊢
    linear_combination he
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) = -v-Q+P-E+F := by
    linear_combination hv
  have hn : (analyticZetaZeroMultiplicity rho : ℝ) <= ‖v‖+‖Q‖+‖P‖+‖E‖+‖F‖ := by
    have ht := norm_add_le (-v-Q+P-E) F
    have ht' := norm_sub_le (-v-Q+P) E
    have ht'' := norm_add_le (-v-Q) P
    have ht''' := norm_sub_le (-v) Q
    rw [<-hm, Complex.norm_natCast] at ht
    rw [norm_neg] at ht'''
    linarith only [ht, ht', ht'', ht''']
  have hb := scaled_moment_bound r rho.1.im hu n
  have hq := competing_bound rho hrho hR hgap n
  have hf := reflected_bound r rho.1.im hu n
  have hr := scaled_residual_bound r rho.1.im hu n
  have hp : ‖P‖ <= u^(n+1) := by
    have hc : 1 <= ‖(1/2 : ℂ)+I*(rho.1.im : ℂ)‖ := by
      exact (nontrivialZetaZero_one_lt_abs_im rho).le.trans (by
        simpa using Complex.abs_im_le_norm ((1/2 : ℂ)+I*(rho.1.im : ℂ)))
    dsimp only [P]
    rw [norm_pow, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu,
      <-div_eq_mul_inv]
    apply pow_le_pow_left₀ (by positivity)
    exact (div_le_self hu hc)
  dsimp only at hq
  change ‖v‖ <= _ at hb
  change ‖Q‖ <= _ at hq
  change ‖F‖ <= _ at hf
  change ‖E‖ <= _ at hr
  change (analyticZetaZeroMultiplicity rho : ℝ) <= momentTest u rho.1.im R n
  unfold momentTest
  linarith only [hn, hb, hq, hp, hr, hf]

/-- The height-independent real-axis Cauchy constant is explicitly paid. -/
theorem zero_height_log_le : localZetaLogHeight 0 <= 4 := by
  change Real.log (|0|+22) <= 4
  norm_num
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 22)).mpr
  have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) <= 5/2)
    (show (5/2 : ℝ) <= Real.exp 1 by linarith [Real.exp_one_gt_d9]) 4
  rw [<-Real.exp_nat_mul] at he
  norm_num at he
  linarith

private theorem block_power {b c : ℝ} (hb : 0 <= b) (_hc : 0 <= c)
    (h : b^64 <= c) : b^4096 <= c^64 := by
  rw [show (4096 : ℕ) = 64*64 by norm_num, pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg hb _) h _

private theorem block_power_succ {b c : ℝ} (hb : 0 <= b) (hb1 : b <= 1)
    (hc : 0 <= c) (h : b^64 <= c) : b^4097 <= c^64 := by
  have hh := block_power hb hc h
  rw [pow_succ]
  exact (mul_le_mul_of_nonneg_left hb1 (pow_nonneg hb _)).trans
    (by simpa using hh)

/-- Exact rational block certificates pay the finite-order test. The
large height exponent is ONLY a finite bound, not an all-height claim. -/
theorem momentTest_lt_nine_fifths {u y : ℝ} (hu : 1/2 <= u)
    (hU : u <= 10001/20000) (hheight : localZetaLogHeight y <= 10^150) :
    momentTest u y (11/20) 4096 < 9/5 := by
  have hpos : 0 <= u := by linarith
  have h1 : (10001/10000 : ℝ)^64 <= 129/128 := by norm_num
  have hg := block_power (by norm_num : (0 : ℝ) <= 10001/10000)
    (by norm_num : (0 : ℝ) <= 129/128) h1
  have hmain : (10001/10000 : ℝ)^4097 < 7/4 := by
    rw [pow_succ]
    have h := mul_le_mul_of_nonneg_right hg (by norm_num : (0 : ℝ) <= 10001/10000)
    have hp : (129/128 : ℝ)^64*(10001/10000) < 7/4 := by norm_num
    exact h.trans_lt hp
  have hc := block_power_succ (by norm_num : (0 : ℝ) <= 10001/11000)
    (by norm_num : (10001/11000 : ℝ) <= 1)
    (by norm_num : (0 : ℝ) <= 1/400)
    (by norm_num : (10001/11000 : ℝ)^64 <= 1/400)
  have hp := block_power_succ (by norm_num : (0 : ℝ) <= 10001/20000)
    (by norm_num : (10001/20000 : ℝ) <= 1)
    (by norm_num : (0 : ℝ) <= 1/10^18)
    (by norm_num : (10001/20000 : ℝ)^64 <= 1/10^18)
  have hr := block_power (by norm_num : (0 : ℝ) <= 10001/14000)
    (by norm_num : (0 : ℝ) <= 1/10^9)
    (by norm_num : (10001/14000 : ℝ)^64 <= 1/10^9)
  have hf := block_power_succ (by norm_num : (0 : ℝ) <= 10001/15000)
    (by norm_num : (10001/15000 : ℝ) <= 1)
    (by norm_num : (0 : ℝ) <= 1/10^10)
    (by norm_num : (10001/15000 : ℝ)^64 <= 1/10^10)
  have hb0 : 2*u <= (10001/10000 : ℝ) := by linarith only [hU]
  have hb1 : u/(11/20) <= (10001/11000 : ℝ) := by linarith only [hU]
  have hb2 : 10*u/7 <= (10001/14000 : ℝ) := by linarith only [hU]
  have hb3 : 4*u/3 <= (10001/15000 : ℝ) := by linarith only [hU]
  have hmU := pow_le_pow_left₀ (by positivity : 0 <= 2*u) hb0 4097
  have hcU := pow_le_pow_left₀ (by positivity : 0 <= u/(11/20)) hb1 4097
  have hpU := pow_le_pow_left₀ hpos hU 4097
  have hrU := pow_le_pow_left₀ (by positivity : 0 <= 10*u/7) hb2 4096
  have hfU := pow_le_pow_left₀ (by positivity : 0 <= 4*u/3) hb3 4097
  have hh : localZetaLogHeight y+11 <= (10^150+11 : ℝ) := by linarith only [hheight]
  have hhr : localZetaLogHeight y+localZetaLogHeight 0 <= (10^150+4 : ℝ) :=
    add_le_add hheight zero_height_log_le
  have hrr : 0 <= localZetaLogHeight y+localZetaLogHeight 0 := by
    linarith [two_lt_localZetaLogHeight y, two_lt_localZetaLogHeight 0]
  have hcoef := mul_le_mul
    (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) <= 160)) hhr hrr
    (by norm_num : (0 : ℝ) <= 160*(10001/20000))
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (by norm_num : (0 : ℝ) <= 4097)
  have hcU' := mul_le_mul hh hcU (pow_nonneg (by positivity) _)
    (by norm_num : (0 : ℝ) <= 10^150+11)
  have hrU' := mul_le_mul hcoef' hrU (pow_nonneg (by positivity) _)
    (by norm_num : (0 : ℝ) <= 160*(10001/20000)*(10^150+4)*4097)
  have hfU' := mul_le_mul hh hfU (pow_nonneg (by positivity) _)
    (by norm_num : (0 : ℝ) <= 10^150+11)
  have he : momentTest u y (11/20) 4096 <=
      (10001/10000 : ℝ)^4097+
      (10^150+11 : ℝ)*(10001/11000 : ℝ)^4097+
      (10001/20000 : ℝ)^4097+
      (160 : ℝ)*(10001/20000)*(10^150+4)*4097*(10001/14000 : ℝ)^4096+
      (10^150+11 : ℝ)*(10001/15000 : ℝ)^4097 := by
    unfold momentTest
    rw [show ((4096 : ℕ) : ℝ)+1 = 4097 by norm_num]
    exact add_le_add (add_le_add (add_le_add (add_le_add hmU hcU') hpU) hrU') hfU'
  have hcs : (10^150+11 : ℝ)*(1/400)^64 < 1/1000 := by norm_num
  have hps : (1/10^18 : ℝ)^64 < 1/1000 := by norm_num
  have hrs : (160 : ℝ)*(10001/20000)*(10^150+4)*4097*(1/10^9)^64 < 1/1000 := by norm_num
  have hfs : (10^150+11 : ℝ)*(1/10^10)^64 < 1/1000 := by norm_num
  have hcb := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) <= 10^150+11)
  have hrb := mul_le_mul_of_nonneg_left hr
    (by norm_num : (0 : ℝ) <= 160*(10001/20000)*(10^150+4)*4097)
  have hfb := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) <= 10^150+11)
  have hcb' := hcb.trans_lt hcs
  have hp' := hp.trans_lt hps
  have hrb' := hrb.trans_lt hrs
  have hfb' := hfb.trans_lt hfs
  have hs := add_lt_add (add_lt_add (add_lt_add (add_lt_add hmain hcb') hp') hrb') hfb'
  exact he.trans_lt (hs.trans (by norm_num))

/-- The original multiplicity-two threshold, with the stronger finite
certificate retained above. -/
theorem momentTest_lt_two {u y : ℝ} (hu : 1/2 <= u)
    (hU : u <= 10001/20000) (hheight : localZetaLogHeight y <= 10^150) :
    momentTest u y (11/20) 4096 < 2 :=
  (momentTest_lt_nine_fifths hu hU hheight).trans (by norm_num)

/-- NO isolation premise: a multiple candidate forces a quantitatively
negative signed competing-zero aggregate. This is a finite-order actual
zero constraint, not a cofinal joinedPhysical ceiling or floor. -/
theorem multiple_forces_signed_counterweight (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    (competingMoment rho (show 1/2 < rho.1.re by linarith) 4096).re < -1/5 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have hu : 0 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have htest := momentTest_lt_nine_fifths
    (show 1/2 <= 3/2-rho.1.re by linarith [rho.re_lt_one])
    (show 3/2-rho.1.re <= 10001/20000 by linarith) hheight
  have hs := multiplicity_add_competing_re_le rho hrho 4096
  dsimp only at hs
  have hc : 0 <= (localZetaLogHeight rho.1.im+11)*
      ((3/2-rho.1.re)/(11/20))^(4096+1) := by
    have hh := two_lt_localZetaLogHeight rho.1.im
    exact mul_nonneg (by linarith only [hh])
      (pow_nonneg (div_nonneg hu (by norm_num)) _)
  have hm' : (2 : ℝ) <= analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  unfold momentTest at htest
  change (competingMoment rho hrho 4096).re < -1/5
  have hab : (2*(3/2-rho.1.re))^(4096+1) <=
      (2*(3/2-rho.1.re))^(4096+1)+(localZetaLogHeight rho.1.im+11)*
        ((3/2-rho.1.re)/(11/20))^(4096+1) := le_add_of_nonneg_right hc
  have hpaid := add_le_add_right (add_le_add_right (add_le_add_right hab
    ((3/2-rho.1.re)^(4096+1)))
    (160*(3/2-rho.1.re)*(localZetaLogHeight rho.1.im+localZetaLogHeight 0)*
      (((4096 : ℕ) : ℝ)+1)*(10*(3/2-rho.1.re)/7)^4096))
    ((localZetaLogHeight rho.1.im+11)*(4*(3/2-rho.1.re)/3)^(4096+1))
  have htotal := hs.trans_lt (lt_of_le_of_lt
    (by simpa only [add_assoc, add_left_comm, add_comm] using hpaid) htest)
  linarith only [htotal, hm']

/-- Actual zeros in the original fixed strip are simple whenever their
competing-zero distance exceeds 11/20, through this explicit finite
log-height bound. This uses COMPLETE arithmetic moments, not a thinned
prime measure, a numerical zero assumption or a new cancellation premise. -/
theorem simple_of_gap_log_height (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      (11/20 : ℝ) < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) :
    analyticZetaZeroMultiplicity rho = 1 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hU : 3/2-rho.1.re <= 10001/20000 := by linarith
  have hm := (multiplicity_le_momentTest rho hrho (by norm_num) hgap 4096).trans_lt
    (momentTest_lt_two hu hU hheight)
  have hnat : analyticZetaZeroMultiplicity rho < 2 := by exact_mod_cast hm
  have hp := analyticZetaZeroMultiplicity_positive rho
  omega

/-- A concrete independent payment of the SAME joinedPhysical ceiling
in the new isolation sector. The original all-height fixed-strip goal is
not replaced by this sector. All native dyadic masks and orders remain. -/
theorem eventually_joinedPhysical_ceiling_of_gap (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hgap : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      (11/20 : ℝ) < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re < 42/25 := by
  have hrho : 1/2 < rho.1.re := by linarith
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling := by
    unfold ZetaRieszWideOwnerAudit.radiusCeiling
    linarith
  have hexposed (tau : NontrivialZetaZero) (hne : tau ≠ rho) :
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ := by
    exact (show 3/2-rho.1.re < (11/20 : ℝ) by linarith).trans (hgap tau hne)
  have hm := simple_of_gap_log_height rho hnear hheight hgap
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hm, Nat.cast_one, one_pow, one_mul, Complex.add_re, Complex.neg_re,
    Complex.one_re, Complex.ofReal_re] at hs
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  exact hs.eventually (gt_mem_nhds (show -1+ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <
    42/25 by linarith only [hc]))

/-- The precise new obstruction: a surviving multiple zero below the
displayed finite log-height ceiling must have a DISTINCT nearby actual
zero. It is not merely a large analytic residual or a synthetic mode. -/
theorem multiple_forces_cluster (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    ∃ tau : NontrivialZetaZero, tau ≠ rho ∧
      ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖ <= 11/20 := by
  by_contra! hn
  have hs := simple_of_gap_log_height rho hnear hheight hn
  omega

/-- The forced cluster is itself in a right-half strip and within a
quarter in ordinate. This quantifies the population still obstructing
the full ceiling without asserting a global rightmost zero. -/
theorem multiple_forces_right_cluster (rho : NontrivialZetaZero)
    (hnear : 1-rho.1.re <= 1/20000)
    (hheight : localZetaLogHeight rho.1.im <= 10^150)
    (hm : 2 <= analyticZetaZeroMultiplicity rho) :
    ∃ tau : NontrivialZetaZero, tau ≠ rho ∧
      (19/20 : ℝ) <= tau.1.re ∧ |tau.1.im-rho.1.im| < 1/4 := by
  obtain ⟨tau, hne, hd⟩ := multiple_forces_cluster rho hnear hheight hm
  let z : ℂ := (3/2+I*(rho.1.im : ℂ))-tau.1
  have hre : z.re = 3/2-tau.1.re := by simp [z]
  have him : z.im = rho.1.im-tau.1.im := by simp [z]
  have hβ : (19/20 : ℝ) <= tau.1.re := by
    have h := (Complex.re_le_norm z).trans hd
    rw [hre] at h
    linarith
  have hsq : z.re^2+z.im^2 <= (11/20 : ℝ)^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg z) hd 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith only [h]
  have hreal : 1/2 < z.re := by rw [hre]; linarith [tau.re_lt_one]
  have hiv : z.im^2 < (1/4 : ℝ)^2 := by nlinarith
  have habs : |z.im| < 1/4 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
  refine ⟨tau, hne, hβ, ?_⟩
  simpa only [him, abs_sub_comm] using habs

end RiemannGaussian.ZetaRieszCeilingMomentIsolation
