/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRetainedDiscrepancy

/-!
# Joined smooth prime tails with the factorial oscillation retained

The factorial prime density has one turning point. Integration by parts
pays its total variation once, independently of the number of prime periods.
The resulting estimate is passed through both Riesz cutoffs and the exact
retained factorial weights; no density replacement at source scale is made.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSmoothPrimeTail
open Real ZetaRieszWeightedPrimeTail ZetaRieszDiscrepancyEnergy
open ZetaRieszRetainedDiscrepancy ZetaRieszJointPrimeError
open ZetaRieszRetainedFactorial ZetaRieszJointAllocation

private theorem single_peak_variation (f g : ℝ → ℝ) {a b p W : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hf : ∀ t ∈ Icc a b, 0 ≤ f t ∧ f t ≤ W)
    (hleft : ∀ t ∈ Icc a b, t ≤ p → 0 ≤ g t)
    (hright : ∀ t ∈ Icc a b, p ≤ t → g t ≤ 0) :
    f a+f b+(∫ t in a..b, |g t|) ≤ 2*W := by
  have hi := hg.intervalIntegrable_of_Icc (μ := volume) hab
  have hd' := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht)) hi
  by_cases hpa : p ≤ a
  · have he : (∫ t in a..b, |g t|) = -(∫ t in a..b, g t) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
      exact abs_of_nonpos (hright t ht' (hpa.trans ht'.1))
    rw [he,hd']
    linarith [(hf a ⟨le_rfl,hab⟩).2]
  by_cases hbp : b ≤ p
  · have he : (∫ t in a..b, |g t|) = ∫ t in a..b, g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
      exact abs_of_nonneg (hleft t ht' (ht'.2.trans hbp))
    rw [he,hd']
    linarith [(hf b ⟨hab,le_rfl⟩).2]
  have hap : a ≤ p := (lt_of_not_ge hpa).le
  have hpb : p ≤ b := (lt_of_not_ge hbp).le
  have hl := hg.mono (show Icc a p ⊆ Icc a b from fun _ ht => ⟨ht.1,ht.2.trans hpb⟩)
  have hr := hg.mono (show Icc p b ⊆ Icc a b from fun _ ht => ⟨hap.trans ht.1,ht.2⟩)
  have hli := hl.intervalIntegrable_of_Icc (μ := volume) hap
  have hri := hr.intervalIntegrable_of_Icc (μ := volume) hpb
  have heL : (∫ t in a..p, |g t|) = f p-f a := by
    rw [show (∫ t in a..p, |g t|) = ∫ t in a..p, g t from by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc a p := by simpa only [uIcc_of_le hap] using ht
      exact abs_of_nonneg (hleft t ⟨ht'.1,ht'.2.trans hpb⟩ ht'.2)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by rw [uIcc_of_le hap] at ht; exact ⟨ht.1,ht.2.trans hpb⟩)) hli
  have heR : (∫ t in p..b, |g t|) = f p-f b := by
    rw [show (∫ t in p..b, |g t|) = -(∫ t in p..b, g t) from by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc p b := by simpa only [uIcc_of_le hpb] using ht
      exact abs_of_nonpos (hright t ⟨hap.trans ht'.1,ht'.2⟩ ht'.1)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by rw [uIcc_of_le hpb] at ht; exact ⟨hap.trans ht.1,ht.2⟩)) hri]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hli.abs hri.abs,heL,heR]
  linarith [(hf p ⟨hap,hpb⟩).2]

private theorem single_peak_cosine (f g : ℝ → ℝ) {a b p W y c : ℝ}
    (hab : a ≤ b) (hy : y ≠ 0) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hf : ∀ t ∈ Icc a b, 0 ≤ f t ∧ f t ≤ W)
    (hleft : ∀ t ∈ Icc a b, t ≤ p → 0 ≤ g t)
    (hright : ∀ t ∈ Icc a b, p ≤ t → g t ≤ 0) :
    |∫ t in a..b, f t*cos (y*(t+c))| ≤ 2*W/|y| := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hsin : Continuous (fun t : ℝ => sin (y*(t+c))) := by fun_prop
  have hcos : Continuous (fun t : ℝ => cos (y*(t+c))) := by fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := fun t => sin (y*(t+c))) (u' := g)
    (v' := fun t => y*cos (y*(t+c)))
    (by simpa only [uIcc_of_le hab] using hfc) hsin.continuousOn
    (fun t ht => hd t (by simpa only [min_eq_left hab,max_eq_right hab] using Ioo_subset_Icc_self ht))
    (fun t _ => by
      apply ((((hasDerivAt_id t).add_const c).const_mul y).sin).congr_deriv
      simp only [id_eq,mul_one]
      ring)
    (hg.intervalIntegrable_of_Icc hab) ((hcos.const_mul y).intervalIntegrable a b)
  have he : (∫ t in a..b, f t*(y*cos (y*(t+c)))) =
      y*(∫ t in a..b, f t*cos (y*(t+c))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he] at hi
  have hterm t (ht : t ∈ Icc a b) : |f t*sin (y*(t+c))| ≤ f t := by
    rw [abs_mul,abs_of_nonneg (hf t ht).1]
    exact (mul_le_mul_of_nonneg_left (abs_sin_le_one _) (hf t ht).1).trans_eq (mul_one _)
  have hrem : |∫ t in a..b, g t*sin (y*(t+c))| ≤ ∫ t in a..b, |g t| := by
    apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
    apply intervalIntegral.integral_mono_on hab
      ((hg.mul hsin.continuousOn).abs.intervalIntegrable_of_Icc hab)
      (hg.abs.intervalIntegrable_of_Icc hab)
    intro t _
    simp only [Pi.mul_apply,abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  have hbnd : |y*(∫ t in a..b, f t*cos (y*(t+c)))| ≤ 2*W := by
    rw [hi]
    apply ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    apply (add_le_add (add_le_add (hterm b ⟨hab,le_rfl⟩)
      (hterm a ⟨le_rfl,hab⟩)) hrem).trans
    have hv := single_peak_variation f g hab hg hd hf hleft hright
    linarith
  rw [abs_mul] at hbnd
  apply (le_div_iff₀ (abs_pos.mpr hy)).mpr
  simpa only [mul_comm] using hbnd

/-- All factorial orders, including zero, have a single-turning-point
prime density. The full oscillatory interval costs only two peak amplitudes,
regardless of the number of complete periods or exterior clipping. -/
theorem factorial_smooth_interval_bound (j : ℕ) {a b W y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hy : y ≠ 0)
    (hW : ∀ t ∈ Icc a b, |factorialAmplitude j t| ≤ W) (c : ℝ) :
    |∫ t in a..b, factorialAmplitude j t*cos (y*(t+c))/t| ≤ 2*W/(a*|y|) := by
  let f := fun t => factorialAmplitude j t/t
  let g := fun t => (factorialAmplitude j t/t)*(((j : ℝ)-1)/t-1/2)
  have hpos t (ht : t ∈ Icc a b) : 0 < t := ha.trans_le ht.1
  have hfc : ContinuousOn f (Icc a b) :=
    (show Continuous (factorialAmplitude j) from
      (by change Continuous (fun t : ℝ => exp (-t/2)*t^j); fun_prop)).continuousOn.div
      continuousOn_id (fun t ht => (hpos t ht).ne')
  have hgc : ContinuousOn g (Icc a b) := hfc.mul
    ((continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')).sub continuousOn_const)
  have hd t (ht : t ∈ Icc a b) : HasDerivAt f (g t) t := by
    apply ((factorialAmplitude_deriv j (hpos t ht)).div (hasDerivAt_id t) (hpos t ht).ne').congr_deriv
    dsimp [g]
    field_simp [(hpos t ht).ne']
    ring
  have hf t (ht : t ∈ Icc a b) : 0 ≤ f t ∧ f t ≤ W/a := by
    have ht0 := (hpos t ht).le
    have hp : 0 ≤ factorialAmplitude j t := by dsimp [factorialAmplitude]; positivity
    have hW0 : 0 ≤ W := hp.trans ((le_abs_self _).trans (hW t ht))
    refine ⟨div_nonneg hp (hpos t ht).le,?_⟩
    exact (div_le_div_of_nonneg_right ((le_abs_self _).trans (hW t ht)) (hpos t ht).le).trans
      (div_le_div_of_nonneg_left hW0 ha ht.1)
  have hl t (ht : t ∈ Icc a b) (hp : t ≤ 2*((j : ℝ)-1)) : 0 ≤ g t := by
    apply mul_nonneg (hf t ht).1
    have hh : 1/2 ≤ ((j : ℝ)-1)/t := (le_div_iff₀ (hpos t ht)).mpr (by linarith)
    linarith
  have hr t (ht : t ∈ Icc a b) (hp : 2*((j : ℝ)-1) ≤ t) : g t ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (hf t ht).1
    have hh : ((j : ℝ)-1)/t ≤ 1/2 := (div_le_iff₀ (hpos t ht)).mpr (by linarith)
    linarith
  have hh := single_peak_cosine f g (p := 2*((j : ℝ)-1)) (W := W/a) (c := c)
    hab hy hgc hd hf hl hr
  have he : (fun t => factorialAmplitude j t*cos (y*(t+c))/t) = fun t => f t*cos (y*(t+c)) := by
    funext t
    dsimp [f]
    ring
  rw [he]
  exact hh.trans_eq (by ring)

private theorem smooth_density_change (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in exp a..exp b, F (log x)/(x*log x)) = ∫ t in a..b, F t/t := by
  let D := exp '' uIcc a b
  have hx x (hx : x ∈ D) : 0 < x := by
    obtain ⟨t,_,rfl⟩ := hx
    exact exp_pos t
  have hl x (hx : x ∈ D) : 0 < log x := by
    obtain ⟨t,ht,rfl⟩ := hx
    rw [log_exp]
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hg : ContinuousOn (fun x => F (log x)/(x*log x)) D :=
    (hF.comp_continuousOn (continuousOn_id.log (fun x hx' => (hx x hx').ne'))).div
      (continuousOn_id.mul (continuousOn_id.log (fun x hx' => (hx x hx').ne')))
      (fun x hx' => mul_ne_zero (hx x hx').ne' (hl x hx').ne')
  have he := intervalIntegral.integral_comp_mul_deriv'
    (f := exp) (f' := exp) (g := fun x => F (log x)/(x*log x))
    (fun t _ => hasDerivAt_exp t) continuous_exp.continuousOn hg
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Function.comp_apply,log_exp]
  field_simp

/-- Explicit smooth-tail cost for the exact factorial amplitude. -/
def smoothCost (a b y : ℝ) (j : ℕ) : ℝ :=
  2*min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j)/(a*|y|)

private theorem smoothCost_nonneg {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
    0 ≤ smoothCost a b y j := by
  have hb : 0 ≤ b := ha.le.trans hab
  dsimp [smoothCost]
  positivity

/-- Every partial smooth tail keeps the full oscillation through both
cutoffs. There is no interval-length or period-count factor in its amplitude. -/
theorem factorial_smooth_tail_bound (j : ℕ) {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hy : y ≠ 0) (c L t : ℝ) :
    |smoothTail (fun x => factorialAmplitude j x*cos (y*(x+c))) a b L t| ≤
      smoothCost a b y j := by
  by_cases ht : t ∈ Ioc (L-b) L
  · rw [smoothTail,indicator_of_mem ht]
    let D := max a (L-t)
    have hDa : a ≤ D := le_max_left _ _
    have hDb : D ≤ b := max_le hab (by linarith [ht.1])
    have hD0 : 0 < D := ha.trans_le hDa
    have hFc : Continuous (fun x => factorialAmplitude j x*cos (y*(x+c))) := by
      unfold factorialAmplitude
      fun_prop
    rw [smooth_density_change _ hFc hD0 hDb]
    let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j)
    have hW : 0 ≤ W := by have hb := ha.le.trans hab; dsimp [W]; positivity
    have hbound x (hx : x ∈ Icc D b) : |factorialAmplitude j x| ≤ W := by
      have hxa : x ∈ Icc a b := ⟨hDa.trans hx.1,hx.2⟩
      have hh := (factorialAmplitude_bounds j ha (sub_nonneg.mpr hab)
        (show x ∈ Icc a (a+(b-a)) by simpa only [add_sub_cancel] using hxa)).1
      simp only [add_sub_cancel] at hh
      exact le_min hh (factorial_amplitude_global_bound j (ha.le.trans hxa.1))
    exact (factorial_smooth_interval_bound j hD0 hDb hy hbound c).trans
      (div_le_div_of_nonneg_left (by positivity) (mul_pos ha (abs_pos.mpr hy))
        (mul_le_mul_of_nonneg_right hDa (abs_nonneg y)))
  · rw [smoothTail,indicator_of_notMem ht,abs_zero]
    exact smoothCost_nonneg ha hab j

/-- Both smooth Riesz cutoffs are paid in one squared energy. The factorial
oscillation is integrated before squaring, with no sum over phase periods. -/
theorem factorial_smooth_profile_energy (j R : ℕ) {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hy : y ≠ 0) (c L : ℝ) :
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*
      (smoothDifference (fun x => factorialAmplitude j x*cos (y*(x+c))) a b L k)^2) ≤
      b*(smoothCost a b y j)^2 := by
  let F := fun x => factorialAmplitude j x*cos (y*(x+c))
  have hFc : Continuous F := by dsimp [F,factorialAmplitude]; fun_prop
  have hi := smoothTail_integrable F hFc ha hab L
  have hi2 := smoothTail_square_integrable F hFc ha hab L
  have hb0 : 0 ≤ b := ha.le.trans hab
  let H := (Ioc (L-b) L).indicator (fun _ : ℝ => (smoothCost a b y j)^2)
  have hH : Integrable H := (integrableOn_const (μ := volume) (s := Ioc (L-b) L)
    (C := (smoothCost a b y j)^2) (hs := by simp)).integrable_indicator measurableSet_Ioc
  have he t : (smoothTail F a b L t)^2 ≤ H t := by
    by_cases ht : t ∈ Ioc (L-b) L
    · dsimp only [H]
      rw [indicator_of_mem ht]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (smoothCost_nonneg ha hab j)).mpr
        (factorial_smooth_tail_bound j ha hab hy c L t)
    · dsimp only [H]
      rw [indicator_of_notMem ht,smoothTail,indicator_of_notMem ht]
      norm_num
  apply (logarithmic_energy _ hi hi2 R).trans
  apply (integral_mono hi2 hH he).trans_eq
  dsimp only [H]
  rw [integral_indicator_const _ measurableSet_Ioc,Real.volume_real_Ioc,
    show L-(L-b)=b by ring,max_eq_left hb0]
  rfl

private theorem smooth_cosine_square (j : ℕ) {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hy : y ≠ 0) (L c : ℝ) (n : ℕ) :
    (smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+c))) a b L n)^2 ≤
      (smoothResponse (fun t => factorialAmplitude j t*cos (y*t)) a b L n)^2+
      (smoothResponse (fun t => factorialAmplitude j t*cos (y*(t-Real.pi/(2*y)))) a b L n)^2 := by
  let F := fun t => factorialAmplitude j t*cos (y*t)
  let G := fun t => factorialAmplitude j t*cos (y*(t-Real.pi/(2*y)))
  have hF : Continuous F := by dsimp [F,factorialAmplitude]; fun_prop
  have hG : Continuous G := by dsimp [G,factorialAmplitude]; fun_prop
  have hsin t : cos (y*(t-Real.pi/(2*y))) = sin (y*t) := by
    rw [show y*(t-Real.pi/(2*y))=y*t-Real.pi/2 by field_simp [hy],cos_sub_pi_div_two]
  have he : (fun t => factorialAmplitude j t*cos (y*(t+c))) =
      fun t => cos (y*c)*F t+(-sin (y*c))*G t := by
    funext t
    dsimp [F,G]
    rw [hsin,mul_add,cos_add]
    ring
  rw [he,smoothResponse_linear F G hF hG ha hab]
  let A := smoothResponse F a b L n
  let B := smoothResponse G a b L n
  have hs := sin_sq_add_cos_sq (y*c)
  have hid : (cos (y*c)*A-sin (y*c)*B)^2+(sin (y*c)*A+cos (y*c)*B)^2=A^2+B^2 := by
    calc
      _ = (sin (y*c)^2+cos (y*c)^2)*(A^2+B^2) := by ring
      _ = _ := by rw [hs,one_mul]
  have hp := sq_nonneg (sin (y*c)*A+cos (y*c)*B)
  dsimp [A,B,F,G] at hid hp
  nlinarith only [hid,hp]

/-- The signed smooth cofactor mean is now paid for every prime count and
every factorial order, with its arbitrary correlated cofactor phase. -/
theorem exists_smooth_response_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (a b y L : ℝ) (j : ℕ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      0 < a → a ≤ b → y ≠ 0 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n)^2) ≤
        E*X*b*(smoothCost a b y j)^2 := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_signed_profile_mean
  refine ⟨2*E,by positivity,fun a b y L j c X S ha hab hy hS hSF => ?_⟩
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hh (v : ℝ) :
      (∑ n ∈ S, (smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+v))) a b L n)^2) ≤
        E*X*b*(smoothCost a b y j)^2 := by
    have h := hmean X ⌊exp L⌋₊ S
      (smoothDifference (fun t => factorialAmplitude j t*cos (y*(t+v))) a b L) hS hSF
    apply h.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (factorial_smooth_profile_energy j ⌊exp L⌋₊ ha hab hy v L) (by positivity : 0 ≤ E*X)
  have hc := hh 0
  have hs := hh (-(Real.pi/(2*y)))
  simp only [add_zero] at hc
  simp only [← sub_eq_add_neg] at hs
  have h := Finset.sum_le_sum (fun n (_ : n ∈ S) => smooth_cosine_square j ha hab hy L (c n) n)
  rw [Finset.sum_add_distrib] at h
  nlinarith only [h,hc,hs]

/-- Combined smooth-oscillation and ACTUAL-prime-discrepancy cost. -/
def joinedCost (a b y : ℝ) (j : ℕ) : ℝ := smoothCost a b y j+factorialError a b y j

private theorem joinedCost_nonneg {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
    0 ≤ joinedCost a b y j := by
  have hb := ha.le.trans hab
  have hh := sub_nonneg.mpr hab
  dsimp [joinedCost,smoothCost,factorialError,factorialScore]
  positivity

/-- The original signed two-cutoff prime response has an unconditional
arithmetic mean bound. Both its smooth part and its prime error are paid;
there is no remaining smooth-response hypothesis. E and T are unevaluated. -/
theorem exists_joined_prime_mean :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (a b y L : ℝ) (j : ℕ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      T ≤ a → a ≤ b → y ≠ 0 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (primeResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n)^2) ≤
        E*X*b*(joinedCost a b y j)^2 := by
  obtain ⟨T,E,hT,hE,herr⟩ := exists_factorial_error_mean
  obtain ⟨D,hD,hsmooth⟩ := exists_smooth_response_mean
  refine ⟨T,2*(E+D),hT,by positivity,fun a b y L j c X S ha hab hy hS hSF => ?_⟩
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := ha0.le.trans hab
  have h1 := herr a b y L j c X S ha hab hS hSF
  have h2 := hsmooth a b y L j c X S ha0 hab hy hS hSF
  have hp n : (primeResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n)^2 ≤
      2*(cosineError (factorialAmplitude j) a b y L (c n) n)^2+
      2*(smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n)^2 := by
    dsimp [cosineError]
    nlinarith only [sq_nonneg (primeResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n-
      2*smoothResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n)]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ S) => hp n)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hsc := smoothCost_nonneg (y := y) ha0 hab j
  have hec : 0 ≤ factorialError a b y j := by
    have hh := sub_nonneg.mpr hab
    dsimp [factorialError,factorialScore]
    positivity
  have hSbound : (smoothCost a b y j)^2 ≤ (joinedCost a b y j)^2 := by
    exact pow_le_pow_left₀ hsc (by dsimp [joinedCost]; linarith) 2
  have hEbound : (factorialError a b y j)^2 ≤ (joinedCost a b y j)^2 := by
    exact pow_le_pow_left₀ hec (by dsimp [joinedCost]; linarith) 2
  have hh1 := mul_le_mul_of_nonneg_left hEbound (by positivity : 0 ≤ E*X*b)
  have hh2 := mul_le_mul_of_nonneg_left hSbound (by positivity : 0 ≤ D*X*b)
  nlinarith only [hsum,h1,h2,hh1,hh2]

/-- Reciprocal cofactor weights pay the entire joined prime response,
with no remaining smooth term, period-count or prime-count restriction. -/
theorem exists_joined_prime_shell :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (a b y L V : ℝ) (j : ℕ) (c w : ℕ → ℝ) (M : ℕ) (S : Finset ℕ),
      T ≤ a → a ≤ b → y ≠ 0 → 0 ≤ V → 1 ≤ M → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, |w n| ≤ V/n) →
      |∑ n ∈ S, w n*primeResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n| ≤
        sqrt E*V*sqrt b*joinedCost a b y j := by
  obtain ⟨T,E,hT,hE,hmean⟩ := exists_joined_prime_mean
  refine ⟨T,2*E,hT,by positivity,fun a b y L V j c w M S ha hab hy hV hM hS hSF hw => ?_⟩
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := ha0.le.trans hab
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hSI : S ⊆ Finset.Ioc 1 (2*M) := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Ioc.mpr ⟨by omega,h.2⟩
  have hcard : (S.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hS
    rw [Nat.card_Ioc,show 2*M-M=M by omega] at h
    exact_mod_cast h
  have hwE : (∑ n ∈ S, (w n)^2) ≤ V^2/M := by
    have hp n (hn : n ∈ S) : (w n)^2 ≤ (V/M)^2 := by
      have hnM : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1.le
      have h := (hw n hn).trans (div_le_div_of_nonneg_left hV hM0 hnM)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    calc
      _ ≤ ∑ _n ∈ S, (V/M)^2 := Finset.sum_le_sum hp
      _ = S.card*(V/M)^2 := by simp
      _ ≤ M*(V/M)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = V^2/M := by field_simp
  have hmean' := hmean a b y L j c (2*M) S ha hab hy hSI hSF
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => primeResponse (fun t => factorialAmplitude j t*cos (y*(t+c n))) a b L n)).trans
      (mul_le_mul hwE hmean' (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have he : V^2/M*(E*(2*M)*b*(joinedCost a b y j)^2) =
      2*E*V^2*b*(joinedCost a b y j)^2 := by field_simp
  push_cast at hs
  rw [he] at hs
  have herr := joinedCost_nonneg (y := y) ha0 hab j
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt hb0]
  nlinarith only [hs]

/-- Total retained-carrier budget on a joined common interval. -/
def retainedJoinedCost (N M : ℕ) (a b y L : ℝ) : ℝ :=
  exp (-log M/2)*sqrt b/(L*N.factorial)*
    (∑ j ∈ Finset.range (N+2), ((N+1).choose j : ℝ)*log (2*M : ℕ)^(N+1-j)*
      joinedCost a b y j)

/-- Both signs of the ORIGINAL retained carrier on a common joined prime
interval are now bounded with the smooth term and arithmetic discrepancy
both paid. Every allocation weight, factorial order and cofactor phase is
retained. The TOTAL source-scaled budget and literal ownership holes remain
open; this is not a whole-carrier floor or ceiling. -/
theorem exists_literal_joined_bounds :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (A : Finset ℕ) (N M : ℕ) (S : Finset ℕ) (a b y L : ℝ),
      1 ≤ M → T ≤ a → a ≤ b → y ≠ 0 → 0 < L → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime;
      P ⊆ A → (∀ n ∈ S, ∀ p ∈ P, ¬p ∣ n) →
      let J := (∑ n ∈ S, ∑ p ∈ P, residualCoefficient A L N (p*n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let K := sqrt E*retainedJoinedCost N M a b y L;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨T,E,hT,hE,hbound⟩ := exists_joined_prime_shell
  refine ⟨T,E,hT,hE,fun A N M S a b y L hM ha hab hy hL hS hSF hPA hcop => ?_⟩
  dsimp only at hPA hcop ⊢
  let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime
  have hex n (hn : n ∈ S) := exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let B' := fun n j => if hn : n ∈ S then B n hn j else 0
  have hcoef' n (hn : n ∈ S) j (hj : j ≤ N+1) :
      0 ≤ B' n j ∧ B' n j ≤ ((N+1).choose j : ℝ)*log n^(N+1-j) := by
    simpa only [B',dif_pos hn] using hcoef n hn j hj
  have hid' n (hn : n ∈ S) p (hp : p ∈ P) :
      (1-boundedShare A N (p*n))*log (p*n : ℕ)^(N+1) =
        ∑ j ∈ Finset.range (N+2), B' n j*log p^j := by
    simpa only [B',dif_pos hn] using
      hid n hn p (Finset.mem_filter.mp hp).2 (hPA hp) (hcop n hn p hp)
  let w := fun j (n : ℕ) => exp (-log n/2)*B' n j/(n : ℝ)
  let V := fun j => exp (-log M/2)*((N+1).choose j : ℝ)*log (2*M : ℕ)^(N+1-j)
  have hw j (hj : j ∈ Finset.range (N+2)) n (hn : n ∈ S) : |w j n| ≤ V j/n := by
    have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
    have hMn := Finset.mem_Ioc.mp (hS hn)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : log M ≤ log n := log_le_log hM0 (by exact_mod_cast hMn.1.le)
    have hlog' : log n ≤ log (2*M : ℕ) := log_le_log hn0 (by exact_mod_cast hMn.2)
    have hb0 := (hcoef' n hn j hjN).1
    have hb := (hcoef' n hn j hjN).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (log_natCast_nonneg n) hlog' _) (Nat.cast_nonneg _))
    dsimp only [w,V]
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ hn0.le
    simpa only [mul_assoc] using
      (mul_le_mul (exp_le_exp.mpr (show -log n/2 ≤ -log M/2 by linarith))
        hb hb0 (exp_pos (-log M/2)).le)
  have hi n (hn : n ∈ S) :
      (∑ p ∈ P, residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
        (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), w j n*
          primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n) := by
    rw [Complex.re_sum]
    have he p (hp : p ∈ P) := atom_expansion A N L y (hSF n hn).1 (hSF n hn).2
      (Finset.mem_filter.mp hp).2 (hcop n hn p hp) (B' n) (hid' n hn p hp)
    rw [Finset.sum_congr rfl he,← Finset.mul_sum,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [primeResponse,w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have htotal :
      (∑ n ∈ S, ∑ p ∈ P, residualCoefficient A L N (p*n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re =
      (-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S, w j n*
        primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n) := by
    rw [Complex.re_sum,Finset.sum_congr rfl hi,← Finset.mul_sum,Finset.sum_comm]
  have hj j (hj : j ∈ Finset.range (N+2)) :
      |∑ n ∈ S, w j n*primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n| ≤
        sqrt E*V j*sqrt b*joinedCost a b y j :=
    hbound a b y L (V j) j (fun n => log n) (w j) M S ha hab hy
      (by dsimp [V]; positivity) hM hS (fun n hn => (hSF n hn).1) (hw j hj)
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun j => ∑ n ∈ S, w j n*primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n)
    (Finset.range (N+2))).trans (Finset.sum_le_sum hj)
  have habs : |(-1/(L*N.factorial))*(∑ j ∈ Finset.range (N+2), ∑ n ∈ S,
        w j n*primeResponse (fun t => factorialAmplitude j t*cos (y*(t+log n))) a b L n)| ≤
      sqrt E*retainedJoinedCost N M a b y L := by
    rw [abs_mul,abs_div,abs_neg,abs_one,abs_of_pos (show 0 < L*(N.factorial : ℝ) by positivity)]
    apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/(L*(N.factorial : ℝ)))).trans_eq
    dsimp only [V,retainedJoinedCost]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← htotal] at habs
  exact abs_le.mp habs

/-- A finite radial/count family of literal blocks obeys BOTH signed bounds
with one common arithmetic constant. Joined prime intervals may contain
arbitrarily many periods. Labels must still be partitioned without repeated
ownership when this is applied to the whole carrier. -/
theorem exists_literal_joined_family_bounds :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧ ∀ (I : Finset ℕ)
      (A S : ℕ → Finset ℕ) (N M : ℕ → ℕ) (a b y L : ℕ → ℝ),
      (∀ i ∈ I, 1 ≤ M i) → (∀ i ∈ I, T ≤ a i) → (∀ i ∈ I, a i ≤ b i) →
      (∀ i ∈ I, y i ≠ 0) → (∀ i ∈ I, 0 < L i) →
      (∀ i ∈ I, S i ⊆ Finset.Ioc (M i) (2*M i)) →
      (∀ i ∈ I, ∀ n ∈ S i, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := fun i => (Finset.Ioc ⌊exp (a i)⌋₊ ⌊exp (b i)⌋₊).filter Nat.Prime;
      (∀ i ∈ I, P i ⊆ A i) → (∀ i ∈ I, ∀ n ∈ S i, ∀ p ∈ P i, ¬p ∣ n) →
      let J := ∑ i ∈ I, (∑ n ∈ S i, ∑ p ∈ P i,
        residualCoefficient (A i) (L i) (N i) (p*n)*
        zetaPrimeLogKernel (N i) (3/2+Complex.I*y i) (p*n)).re;
      let K := sqrt E*(∑ i ∈ I, retainedJoinedCost (N i) (M i) (a i) (b i) (y i) (L i));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨T,E,hT,hE,hbound⟩ := exists_literal_joined_bounds
  refine ⟨T,E,hT,hE,fun I A S N M a b y L hM ha hab hy hL hS hSF hPA hcop => ?_⟩
  dsimp only at hPA hcop ⊢
  have hh i (hi : i ∈ I) := hbound (A i) (N i) (M i) (S i) (a i) (b i) (y i) (L i)
    (hM i hi) (ha i hi) (hab i hi) (hy i hi) (hL i hi) (hS i hi) (hSF i hi)
    (hPA i hi) (hcop i hi)
  constructor
  · have h := Finset.sum_le_sum (fun i hi => (hh i hi).1)
    simpa only [Finset.sum_neg_distrib,← Finset.mul_sum] using h
  · have h := Finset.sum_le_sum (fun i hi => (hh i hi).2)
    simpa only [← Finset.mul_sum] using h

end RiemannGaussian.ZetaRieszSmoothPrimeTail
