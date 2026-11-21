import RiemannGaussian.SuzukiLocalCancellationPrimeBand
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Finite logarithmic scale averages in a signed prime-cofactor sum

A reciprocal phase at prime scale `p` has angle proportional to `exp(t)*X/p`.
Repeated short uniform averages in `t` suppress this phase while preserving
the exponential response of a zero off the critical line. -/

namespace RiemannGaussian.SuzukiScaleAverage
noncomputable section
open MeasureTheory Set

/-- Translation average on a forward interval of logarithmic scales. -/
def box (a : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (∫ u in (0:ℝ)..a, f (t+u)) / (a:ℂ)

/-- Apply the same scale average a specified number of times. -/
def boxes (a : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | n+1, f => box a (boxes a n f)

private theorem box_cont {f : ℝ → ℂ} (hf : Continuous f) (a : ℝ) : Continuous (box a f) := by
  unfold box
  apply Continuous.div_const
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t u : ℝ => f (t+u)) (hf.comp (continuous_fst.add continuous_snd)) 0 a

private theorem boxes_cont {f : ℝ → ℂ} (hf : Continuous f) (a : ℝ) (n : ℕ) :
    Continuous (boxes a n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact box_cont ih a

private theorem boxes_shift (a b : ℝ) (n : ℕ) (f : ℝ → ℂ) (t : ℝ) :
    boxes a n (fun s => f (s+b)) t = boxes a n f (t+b) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [boxes,box,ih]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg (boxes a n f) (add_right_comm t x b)

private theorem boxes_const_mul (a : ℝ) (n : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    boxes a n (fun s => c*f s) = fun s => c*boxes a n f s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext t
    simp only [boxes,box,ih,intervalIntegral.integral_const_mul,mul_div_assoc]

private theorem boxes_add (a : ℝ) (n : ℕ) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    boxes a n (fun s => f s+g s) = fun s => boxes a n f s+boxes a n g s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext t
    simp only [boxes,box,ih]
    rw [intervalIntegral.integral_add, add_div]
    · exact ((boxes_cont hf a n).comp (continuous_const.add continuous_id)).intervalIntegrable ..
    · exact ((boxes_cont hg a n).comp (continuous_const.add continuous_id)).intervalIntegrable ..

private theorem boxes_box (a : ℝ) (n : ℕ) (f : ℝ → ℂ) :
    boxes a n (box a f) = boxes a (n+1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (box a) ih

/-- A normalized interval average preserves a uniform norm bound. -/
theorem box_norm_le {a B t : ℝ} (ha : 0 < a) (f : ℝ → ℂ)
    (hh : ∀ u ∈ Ioc (0:ℝ) a, ‖f (t+u)‖ ≤ B) : ‖box a f t‖ ≤ B := by
  unfold box
  rw [norm_div,Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  apply (div_le_iff₀ ha).mpr
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
    (f := fun u => f (t+u)) (a := 0) (b := a) (by rwa [uIoc_of_le ha.le])
  simpa only [sub_zero,abs_of_pos ha] using he

/-- Dilation contributes the real weight and the phase has real frequency `ξ`. -/
def wave (b ξ t : ℝ) : ℂ :=
  (Real.exp (-b*t) : ℂ)*Complex.exp (Complex.I*(ξ:ℂ)*(Real.exp t:ℂ))

private theorem wave_cont (b ξ : ℝ) : Continuous (wave b ξ) := by unfold wave; fun_prop

private theorem wave_deriv (b ξ t : ℝ) :
    HasDerivAt (wave (b+1) ξ)
      (Complex.I*ξ*wave b ξ t-((b:ℂ)+1)*wave (b+1) ξ t) t := by
  have h1 := (((hasDerivAt_id t).const_mul (-(b+1))).exp).ofReal_comp
  have h2 := (((Real.hasDerivAt_exp t).ofReal_comp).const_mul (Complex.I*(ξ:ℂ))).cexp
  have he : (Real.exp t : ℂ)*Real.exp (-(b+1)*t) = Real.exp (-b*t) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  convert h1.mul h2 using 1
  · rfl
  · simp only [wave, id_eq, mul_one, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add,
      Complex.ofReal_one]
    linear_combination -(Complex.I*ξ*Complex.exp (Complex.I*ξ*Real.exp t))*he

private theorem box_wave_identity {a : ℝ} (ha : 0 < a) (b ξ t : ℝ) :
    Complex.I*ξ*box a (wave b ξ) t =
      (wave (b+1) ξ (t+a)-wave (b+1) ξ t)/(a:ℂ)+
        ((b:ℂ)+1)*box a (wave (b+1) ξ) t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t) (b := t+a) (fun x _ => wave_deriv b ξ x)
    (((continuous_const.mul (wave_cont b ξ)).sub
      (continuous_const.mul (wave_cont (b+1) ξ))).intervalIntegrable ..)
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  · simp only [box, intervalIntegral.integral_comp_add_left, add_zero]
    have ha0 : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
    linear_combination h
  · exact (continuous_const.mul (wave_cont b ξ)).intervalIntegrable ..
  · exact (continuous_const.mul (wave_cont (b+1) ξ)).intervalIntegrable ..

private theorem iter_wave_identity {a : ℝ} (ha : 0 < a) (b ξ : ℝ) (n : ℕ) (t : ℝ) :
    Complex.I*ξ*boxes a (n+1) (wave b ξ) t =
      (boxes a n (wave (b+1) ξ) (t+a)-boxes a n (wave (b+1) ξ) t)/(a:ℂ)+
      ((b:ℂ)+1)*boxes a (n+1) (wave (b+1) ξ) t := by
  let g := wave (b+1) ξ
  have hg := wave_cont (b+1) ξ
  have h : (fun t => Complex.I*ξ*box a (wave b ξ) t) =
      fun t => ((a:ℂ)⁻¹*g (t+a)+(-(a:ℂ)⁻¹)*g t)+((b:ℂ)+1)*box a g t := by
    funext t
    rw [box_wave_identity ha]
    dsimp only [g]
    ring
  have hc : Continuous g := hg
  have hh := congrArg (fun f : ℝ → ℂ => boxes a n f t) h
  rw [boxes_add a n (f := fun s => (a:ℂ)⁻¹*g (s+a)+(-(a:ℂ)⁻¹)*g s)
      (g := fun s => ((b:ℂ)+1)*box a g s) (by fun_prop)
      ((continuous_const.mul (box_cont hc a)) : Continuous (fun s => ((b:ℂ)+1)*box a g s)),
    boxes_add a n (f := fun s => (a:ℂ)⁻¹*g (s+a)) (g := fun s => (-(a:ℂ)⁻¹)*g s)
      (by fun_prop) (by fun_prop)] at hh
  simp only [boxes_const_mul,boxes_box,boxes_shift] at hh
  change _ = (boxes a n g (t+a)-boxes a n g t)/(a:ℂ)+((b:ℂ)+1)*boxes a (n+1) g t
  rw [hh]
  ring

/-- Repeated short scale averages cancel the true exponential-of-log-scale
reciprocal phase, uniformly for every nonnegative initial translation. -/
theorem boxes_wave_bound {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) (n : ℕ)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    ‖boxes a n (wave b ξ) t‖ ≤ ((2/a+b+n)/ξ)^n := by
  induction n generalizing b t with
  | zero =>
    simp only [boxes, wave, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      zero_mul, mul_zero, one_mul, sub_zero, Real.exp_zero, mul_one, pow_zero]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hb ht])
  | succ n ih =>
    let R := ((2/a+(b+1)+n)/ξ)^n
    have hbound (u : ℝ) (hu : 0 ≤ u) : ‖boxes a n (wave (b+1) ξ) u‖ ≤ R :=
      ih (by linarith) hu
    have hnext : ‖boxes a (n+1) (wave (b+1) ξ) t‖ ≤ R :=
      box_norm_le ha _ (fun u hu => hbound _ (by linarith [hu.1]))
    have hh := congrArg norm (iter_wave_identity ha b ξ n t)
    rw [norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hξ] at hh
    have hdiff := (norm_sub_le (boxes a n (wave (b+1) ξ) (t+a))
      (boxes a n (wave (b+1) ξ) t)).trans (add_le_add (hbound _ (by linarith)) (hbound _ ht))
    have hdiv := div_le_div_of_nonneg_right hdiff ha.le
    have hmul := mul_le_mul_of_nonneg_left hnext (show 0 ≤ b+1 by linarith)
    have hnorm : ‖(b:ℂ)+1‖ = b+1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    have hsum := (le_of_eq hh).trans (norm_add_le ..)
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,norm_mul,hnorm] at hsum
    have hR : R = ((2/a+b+(n+1:ℕ))/ξ)^n := by dsimp [R]; push_cast; ring
    rw [pow_succ, ← hR]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hξ).mpr
    push_cast
    have hRn := mul_nonneg (show 0 ≤ R by dsimp [R]; positivity) (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hsum.trans (add_le_add hdiv hmul), hRn, show (R+R)/a = (2/a)*R by ring]

/-- Multiplier of one uniform scale average on an exponential signal. -/
def factor (z : ℂ) (a : ℝ) : ℂ := (Complex.exp (z*a)-1)/(z*a)

theorem box_exp {z : ℂ} (hz : z ≠ 0) {a : ℝ} (t : ℝ) :
    box a (fun v => Complex.exp (z*v)) t = Complex.exp (z*t)*factor z a := by
  simp only [box, Complex.ofReal_add, mul_add, Complex.exp_add,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex hz, Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,factor]
  ring

/-- A summable sequence of positive widths preserves the mode of each
right-half-plane zero, including in the infinite smoothing limit. -/
theorem factors_ne_zero {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hs : Summable a) {z : ℂ}
    (hz : 0 < z.re) : (∏' j, factor z (a j)) ≠ 0 := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl 0) hz
  have hne (j : ℕ) : factor z (a j) ≠ 0 := by
    apply div_ne_zero _ (mul_ne_zero hz0 (by exact_mod_cast (ha j).ne'))
    apply sub_ne_zero.mpr
    intro he
    have h := congrArg norm he
    rw [Complex.norm_exp, norm_one,Real.exp_eq_one_iff,Complex.mul_re] at h
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at h
    exact (mul_pos hz (ha j)).ne' h
  have hab := hs.mul_left ‖z‖
  have hsmall : ∀ᶠ j in Filter.atTop, ‖z‖*a j < 1 :=
    hab.tendsto_atTop_zero.eventually_lt_const (by norm_num)
  have hh : Summable (fun j => ‖factor z (a j)-1‖) := by
    apply Summable.of_norm_bounded_eventually_nat hab
    filter_upwards [hsmall] with j hj
    let w := z*(a j:ℂ)
    have hw0 : w ≠ 0 := mul_ne_zero hz0 (by exact_mod_cast (ha j).ne')
    have hw : ‖w‖ = ‖z‖*a j := by
      dsimp only [w]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha j)]
    have he : factor z (a j)-1 = (Complex.exp w-1-w)/w := by
      change (Complex.exp w-1)/w-1 = _
      field_simp
    rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),he,norm_div,← hw]
    apply (div_le_iff₀ (norm_pos_iff.mpr hw0)).mpr
    simpa only [sq] using Complex.norm_exp_sub_one_sub_id_le (x := w) (hw.trans_lt hj).le
  simpa only [add_sub_cancel] using tprod_one_add_ne_zero_of_summable
    (f := fun j => factor z (a j)-1) (fun j => by simpa only [add_sub_cancel] using hne j) hh

/-- The block with index `j` contains `2^j` independent uniforms of this width.
Its total width is `1/((j+1)*(j+2))`. -/
def blockWidth (j : ℕ) : ℝ := (2^(j:ℕ)*(j+1:ℝ)*(j+2))⁻¹

/-- After the indicated block, the actual reciprocal phase has geometric
decay in the number of averages, including the physical dilation weight. -/
theorem block_wave_bound (j : ℕ) {H ξ t : ℝ} (hH : 0 < H) (ht : 0 ≤ t)
    (hξ : 8*(2:ℝ)^j*((j:ℝ)+2)^2*H ≤ ξ) :
    ‖boxes (blockWidth j) (2^j) (wave (3/2) ξ) t‖ ≤ (1/(2*H))^(2^j) := by
  have ha : 0 < blockWidth j := by unfold blockWidth; positivity
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
  apply (boxes_wave_bound ha hξ0 _ (by norm_num : 0 ≤ (3/2:ℝ)) ht).trans
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_div_iff₀ hξ0 (by positivity : 0 < 2*H)).mpr
  push_cast
  simp only [blockWidth,div_inv_eq_mul]
  have hpow : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hk : 2*((2:ℝ)^j*(j+1)*(j+2))+3/2+2^j ≤ 4*2^j*(j+2)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (2:ℝ)^j by positivity) (Nat.cast_nonneg (α := ℝ) j),
      mul_nonneg (show 0 ≤ (2:ℝ)^j by positivity) (sq_nonneg (j:ℝ))]
  nlinarith [mul_le_mul_of_nonneg_right hk hH.le]

/-- The total width in the first `n` blocks telescopes exactly. -/
theorem block_total_width (n : ℕ) :
    (∑ j ∈ Finset.range n, (2:ℝ)^j*blockWidth j) = 1-1/(n+1:ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [blockWidth,Nat.cast_succ]
    field_simp
    ring

/-- All proper prime-power rows, before a lower prime cutoff or scale average. -/
def properPowerRows (X : ℝ) : ℝ :=
  ∑ d ∈ (Finset.Ioc 0 ⌊8*X⌋₊).filter (fun d => ¬d.Prime),
    ArithmeticFunction.vonMangoldt d *
    ∑ k ∈ Finset.Ioc 1 ⌊8*X/d⌋₊, suzukiLocalPhysicalKernel X ((d:ℝ)*k)

/-- Before deleting small primes, the only surviving correction of order one
is the signed proper-prime-power sum. The lattice error tends to zero. -/
theorem full_row_error {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalArithmeticComparison X + SuzukiReciprocal.centeredPrimeTailFrom X 0 +
        properPowerRows X| ≤ (53*Real.log (8*X)+21)/Real.sqrt X := by
  have he : SuzukiReciprocal.ordinaryPrimeBand X 0 ⌊8*X⌋₊ + properPowerRows X =
      suzukiLocalCofactorTail X 0 := by
    unfold SuzukiReciprocal.ordinaryPrimeBand properPowerRows suzukiLocalCofactorTail
    simp only [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hp : d.Prime <;> simp [hp,ArithmeticFunction.vonMangoldt_apply_prime]
  have hx := zero_lt_one.trans_le hX
  have hs := suzukiLocalPhysicalKernel_log_prefix_sampling_error_le (q := 1) hX le_rfl hX
  rw [suzukiLocalPhysicalKernel_scaled_log_integral hx (by norm_num)] at hs
  simp only [one_mul,div_one] at hs
  rw [suzukiLocal_log_eq_comparison_add_cofactorTail hX (V := 0) (by norm_num; positivity),
    ← he] at hs
  simpa only [SuzukiReciprocal.centeredPrimeTailFrom,suzukiLocalVaughanSmallCross,
    Finset.Ioc_self,Finset.sum_empty, Finset.sum_const_zero,add_zero,zero_add,sub_eq_add_neg,
    add_comm,add_assoc,add_left_comm] using hs

/-- The zero contribution of a critical-line mode after a unit logarithmic
average, with the signed kernel's exact multiplier and analytic multiplicity. -/
def criticalTerm (ρ : NontrivialZetaZero) (t : ℝ) : ℂ :=
  let z := (ρ.1:ℂ)-1/2
  analyticZetaZeroMultiplicity ρ * (suzukiLocalModeMultiplier z / z^2) *
    factor z 1 * Complex.exp (z*t)

/-- Single-mode estimate, usable whenever this particular zero lies on the line. -/
theorem critical_term_bound (ρ : NontrivialZetaZero) (hb : ρ.1.re = 1/2) (t : ℝ) :
    ‖criticalTerm ρ t‖ ≤ (10/7)*(analyticZetaZeroMultiplicity ρ / ρ.1.im^2) := by
  let z := (ρ.1:ℂ)-1/2
  have hz : z.re = 0 := by simp [z, hb]
  have hn : ‖z‖ = |ρ.1.im| := by
    rw [← Complex.re_add_im z, hz, Complex.ofReal_zero, zero_add, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simp [z]
  have hγ := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hγ0 : 0 < |ρ.1.im| := by linarith
  have he (x : ℝ) : ‖Complex.exp (z*x)‖ = 1 := by simp [Complex.norm_exp,Complex.mul_re,hz]
  have hm : ‖suzukiLocalModeMultiplier z‖ ≤ 10 := by
    let e := Complex.exp (z*Real.log 2)
    have h1 : ‖e-1‖ ≤ 2 := (norm_sub_le ..).trans (by rw [he,norm_one]; norm_num)
    have h2 : ‖e-(Real.sqrt 2:ℝ)‖ ≤ 5/2 := by
      apply (norm_sub_le ..).trans
      rw [he,Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    unfold suzukiLocalModeMultiplier
    rw [norm_mul,norm_pow]
    exact (mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _) (by norm_num)).trans
      (by norm_num)
  have hf : ‖factor z 1‖ ≤ 1/7 := by
    unfold factor
    rw [norm_div,Complex.ofReal_one,mul_one,hn]
    apply (div_le_iff₀ hγ0).mpr
    have hh := norm_sub_le (Complex.exp z) 1
    have he1 := he 1
    simp only [Complex.ofReal_one,mul_one] at he1
    rw [he1, norm_one] at hh
    linarith
  change ‖(analyticZetaZeroMultiplicity ρ:ℂ)*(suzukiLocalModeMultiplier z/z^2)*factor z 1*
      Complex.exp (z*t)‖ ≤ _
  simp only [norm_mul,Complex.norm_natCast,norm_div,norm_pow,he,mul_one,hn,sq_abs]
  have hd := div_le_div_of_nonneg_right hm (sq_nonneg ρ.1.im)
  have h := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
  exact (mul_le_mul h hf (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Summing over every genuine zero on RH, the extra unit box keeps the
complete spectral contribution below the positive square-prime bias. -/
theorem critical_sum_bound (h : RiemannHypothesis) (t : ℝ) :
    ‖∑' ρ : NontrivialZetaZero, criticalTerm ρ t‖ < 1/15 := by
  have hs := RosserSchoenfeldZeroMass.ordinate_mass_le.1.mul_left (10/7:ℝ)
  have hp (ρ : NontrivialZetaZero) := critical_term_bound ρ (h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2) t
  have hnorm := Summable.of_nonneg_of_le (fun ρ => norm_nonneg (criticalTerm ρ t)) hp hs
  apply ((norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hp hs)).trans_lt
  rw [tsum_mul_left]
  linarith [RosserSchoenfeldZeroMass.ordinate_mass_lt]

/-- A Gaussian of log-scale mean `t` and variance `t/2915` has exponential
response `exp (t*heatRate z)`. -/
def heatRate (z : ℂ) : ℂ := z + z^2/(2*2915)

/-- The integral over the actual normal distribution, including zero time. -/
theorem gaussian_mode (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ u : ℝ, Complex.exp (z*u) ∂ProbabilityTheory.gaussianReal t ⟨t/2915, by positivity⟩) =
      Complex.exp (heatRate z*t) := by
  change ProbabilityTheory.complexMGF id (ProbabilityTheory.gaussianReal t ⟨t/2915, by positivity⟩) z = _
  refine (ProbabilityTheory.complexMGF_id_gaussianReal (μ := t)
    (v := ⟨t/2915, by positivity⟩) z).trans ?_
  congr 1
  change z*(t:ℂ) + ((t/2915:ℝ):ℂ)*z^2/2 = _
  push_cast
  unfold heatRate
  ring

/-- The rate is uniformly negative over the full nontrivial zero divisor.
The low-height calculation through 54 and the ordinary critical strip suffice. -/
theorem heatRate_re_le (ρ : NontrivialZetaZero) :
    (heatRate (ρ.1-1/2)).re ≤ -(1/10000:ℝ) := by
  have he : (heatRate (ρ.1-1/2)).re = (ρ.1.re-1/2) +
      ((ρ.1.re-1/2)^2-ρ.1.im^2)/(2*2915) := by
    unfold heatRate
    rw [show (2:ℂ)*2915 = 5830 by norm_num]
    rw [Complex.add_re, Complex.div_ofNat_re, pow_two, Complex.mul_re]
    norm_num [Complex.sub_re, Complex.sub_im]
    ring
  rw [he]
  by_cases h : |ρ.1.im| ≤ 54
  · have hb := ZetaElevenZeroCompleteness.critical_line_through_fiftyFour ρ h
    have hg := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
    rw [hb,sub_self]
    have hg2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 14) hg.le 2
    rw [sq_abs] at hg2
    linarith
  · have hb := ρ.re_lt_one
    have hb0 := ρ.zero_lt_re
    have hg2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 54) (lt_of_not_ge h).le 2
    rw [sq_abs] at hg2
    nlinarith [mul_nonneg hb0.le (sub_nonneg.mpr hb.le)]

/-- Exponential cancellation after Gaussian averaging, simultaneously over
all zeros and for any absolutely summable spectral coefficients. -/
theorem gaussian_spectral_bound (a : NontrivialZetaZero → ℂ)
    (ha : Summable (fun ρ => ‖a ρ‖)) {t : ℝ} (ht : 0 ≤ t) :
    ‖∑' ρ : NontrivialZetaZero, a ρ*Complex.exp (heatRate (ρ.1-1/2)*t)‖ ≤
      (∑' ρ, ‖a ρ‖)*Real.exp (-t/10000) := by
  have h (ρ : NontrivialZetaZero) :
      ‖a ρ * Complex.exp (heatRate (ρ.1-1/2)*t)‖ ≤ ‖a ρ‖*Real.exp (-t/10000) := by
    rw [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (norm_nonneg _)
    linarith [mul_le_mul_of_nonneg_right (heatRate_re_le ρ) ht]
  have hs := ha.mul_right (Real.exp (-t/10000))
  have hd := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h hs
  exact ((norm_tsum_le_tsum_norm hd).trans (hd.tsum_le_tsum h hs)).trans_eq (tsum_mul_right)

/-- Uniform Mellin bound, with analytic multiplicity, for each actual zero. -/
theorem modeCoefficient_bound (ρ : NontrivialZetaZero) :
    ‖(analyticZetaZeroMultiplicity ρ : ℂ) *
      (suzukiLocalModeMultiplier (ρ.1-1/2)/(ρ.1-1/2)^2)‖ ≤
      36*(analyticZetaZeroMultiplicity ρ/ρ.1.im^2) := by
  let z := ρ.1-1/2
  have hz : z.re = ρ.1.re-1/2 := by norm_num [z]
  have hzi : z.im = ρ.1.im := by norm_num [z]
  have he : ‖Complex.exp (z*Real.log 2)‖ ≤ 2 := by
    rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,hz]
    apply (Real.exp_le_exp.mpr _).trans_eq (Real.exp_log (by norm_num : (0:ℝ)<2))
    exact (mul_le_mul_of_nonneg_right (by linarith [ρ.re_lt_one] : ρ.1.re-1/2 ≤ 1)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))).trans_eq (one_mul _)
  have h1 : ‖Complex.exp (z*Real.log 2)-1‖ ≤ 3 := (norm_sub_le ..).trans (by
    rw [norm_one]; linarith)
  have h2 : ‖Complex.exp (z*Real.log 2)-(Real.sqrt 2:ℝ)‖ ≤ 4 := (norm_sub_le ..).trans (by
    rw [Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)])
  have hm : ‖suzukiLocalModeMultiplier z‖ ≤ 36 := by
    unfold suzukiLocalModeMultiplier
    rw [norm_mul,norm_pow]
    exact (mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _) (by norm_num)).trans
      (by norm_num)
  have hγ := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hγ2 : 0 < ρ.1.im^2 := sq_pos_of_ne_zero (fun h => by simp [h] at hγ; linarith)
  have hzn : ρ.1.im^2 ≤ ‖z‖^2 := by
    have hh := Complex.abs_im_le_norm z
    rw [hzi] at hh
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  change ‖(analyticZetaZeroMultiplicity ρ : ℂ)*(suzukiLocalModeMultiplier z/z^2)‖ ≤ _
  rw [norm_mul,Complex.norm_natCast,norm_div,norm_pow]
  exact (mul_le_mul_of_nonneg_left (div_le_div₀ (by norm_num) hm hγ2 hzn)
    (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))).trans_eq (by ring)

/-- The coefficients include every analytic multiplicity and the exact Mellin
response of the signed prime packet. Any uniformly bounded scale factor is allowed. -/
theorem mode_coefficients_summable {q : NontrivialZetaZero → ℂ} {C : ℝ}
    (hq : ∀ ρ, ‖q ρ‖ ≤ C) :
    Summable (fun ρ : NontrivialZetaZero => ‖(analyticZetaZeroMultiplicity ρ : ℂ) *
      (suzukiLocalModeMultiplier (ρ.1-1/2)/(ρ.1-1/2)^2)*q ρ‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (RosserSchoenfeldZeroMass.ordinate_mass_le.1.mul_left (36*max 0 C))
  intro ρ
  rw [norm_mul]
  exact (mul_le_mul (modeCoefficient_bound ρ) ((hq ρ).trans (le_max_right ..))
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The bound holds for the Gaussian integral of the entire zero sum.
The interchange is justified with one integrable majorant on the whole real line. -/
theorem gaussian_integral_spectral_bound (a : NontrivialZetaZero → ℂ)
    (ha : Summable (fun ρ => ‖a ρ‖)) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ u : ℝ, ∑' ρ : NontrivialZetaZero, a ρ*Complex.exp ((ρ.1-1/2)*u)
      ∂ProbabilityTheory.gaussianReal t ⟨t/2915, by positivity⟩‖ ≤
      (∑' ρ, ‖a ρ‖)*Real.exp (-t/10000) := by
  let μ := ProbabilityTheory.gaussianReal t ⟨t/2915, by positivity⟩
  let g (u : ℝ) := Real.exp (1*u) + Real.exp ((-1)*u)
  let F (ρ : NontrivialZetaZero) (u : ℝ) := a ρ*Complex.exp ((ρ.1-1/2)*u)
  have hg : Integrable g μ := (ProbabilityTheory.integrable_exp_mul_gaussianReal 1).add
    (ProbabilityTheory.integrable_exp_mul_gaussianReal (-1))
  have hb (ρ : NontrivialZetaZero) (u : ℝ) : ‖F ρ u‖ ≤ ‖a ρ‖*g u := by
    simp only [F,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hβ : (ρ.1-1/2).re = ρ.1.re-1/2 := by norm_num
    rw [hβ]
    dsimp only [g]
    by_cases hu : 0 ≤ u
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [ρ.re_lt_one]) hu)).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith [ρ.zero_lt_re]) (le_of_not_ge hu))).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hi (ρ : NontrivialZetaZero) : Integrable (F ρ) μ :=
    (hg.const_mul ‖a ρ‖).mono' (by dsimp [F]; fun_prop) (Filter.Eventually.of_forall (hb ρ))
  have hs : Summable (fun ρ : NontrivialZetaZero => ∫ u, ‖F ρ u‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ (ha.mul_right (∫ u, g u ∂μ))
    intro ρ
    rw [← integral_const_mul]
    exact integral_mono (hi ρ).norm (hg.const_mul _) (hb ρ)
  change ‖∫ u, ∑' ρ, F ρ u ∂μ‖ ≤ _
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  have hf (ρ : NontrivialZetaZero) : (∫ u, F ρ u ∂μ) =
      a ρ*Complex.exp (heatRate (ρ.1-1/2)*t) := by
    rw [show (∫ u, F ρ u ∂μ) = a ρ*(∫ u : ℝ, Complex.exp ((ρ.1-1/2)*u) ∂μ) by
      exact integral_const_mul ..,gaussian_mode _ t ht]
  simp_rw [hf]
  exact gaussian_spectral_bound a ha ht

private theorem continuous_prime_packet : Continuous suzukiLocalPrimePacket := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := t + 1 + 2*Real.log 2
  have hc : Continuous (fun v : ℝ => ∑ n ∈ suzukiArithmeticPrimeWindow T,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        suzukiLocalTriangle (Real.log 2) (Real.log n - v)) := by
    unfold suzukiLocalTriangle
    fun_prop
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (by linarith : t < t+1)] with v hv
  exact suzukiLocalPrimePacket_eq_sum_of_le (t := v) (T := T) (by dsimp [T]; linarith)

/-- Moving a unit average changes only its two end intervals. The full zero
abscissa controls the modulus for the literal prime comparison. -/
theorem unit_average_displacement {B t h : ℝ} (hB : B ∈ Set.Icc (1/2) 1)
    (hβ : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (ht : 0 ≤ t) (hh : 0 ≤ h) (hh' : h ≤ 1) :
    |(∫ s in (t+h)..(t+h+1), suzukiLocalPrimeComparison s) -
        (∫ s in t..(t+1), suzukiLocalPrimeComparison s)| ≤
      2 * (192 * ((463/5000 : ℝ) + Real.pi^2/24)) *
        Real.exp ((B-1/2)*(t+2)) * h := by
  let g := suzukiLocalPrimeComparison
  let C := 192 * ((463/5000 : ℝ) + Real.pi^2/24)
  have hc : Continuous g := (continuous_const.mul continuous_prime_packet).sub
    (continuous_prime_packet.comp (continuous_id.add continuous_const))
  have bound {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ t+2) : |g s| ≤ C*Real.exp ((B-1/2)*(t+2)) := by
    apply (abs_suzukiLocalPrimeComparison_le_of_re_le ⟨by linarith [hB.1], hB.2⟩ hβ hs).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
    exact mul_le_mul_of_nonneg_left hs' (sub_nonneg.mpr hB.1)
  have part (a : ℝ) (ha : t ≤ a) (ha' : a ≤ t+1) :
      |∫ s in a..(a+h), g s| ≤ C*Real.exp ((B-1/2)*(t+2))*h := by
    have hh0 : a ≤ a+h := by linarith
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C*Real.exp ((B-1/2)*(t+2))) (f := g) (a := a) (b := a+h) (by
        rw [Set.uIoc_of_le hh0]
        intro s hs
        exact bound (ht.trans (ha.trans hs.1.le)) (by linarith [hs.2]))
    simpa only [Real.norm_eq_abs,add_sub_cancel_left,abs_of_nonneg hh] using hb
  change |(∫ s in (t+h)..(t+h+1), g s) - (∫ s in t..(t+1), g s)| ≤ _
  rw [intervalIntegral.integral_interval_sub_interval_comm'
    (hc.intervalIntegrable ..) (hc.intervalIntegrable ..) (hc.intervalIntegrable ..),
    show t+h+1 = (t+1)+h by ring]
  have h1 := part (t+1) (by linarith) le_rfl
  have h2 := part t le_rfl (by linarith)
  exact (abs_sub ..).trans ((add_le_add h1 h2).trans_eq (by dsimp only [C]; ring))

private def boxDifference (a : ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  (a:ℂ)⁻¹*f (s+a)+(-(a:ℂ)⁻¹)*f s

private theorem boxDifference_cont {f : ℝ → ℂ} (hf : Continuous f) (a : ℝ) :
    Continuous (boxDifference a f) := by unfold boxDifference; fun_prop

private theorem box_hasDerivAt {f : ℝ → ℂ} (hf : Continuous f) (a t : ℝ) :
    HasDerivAt (box a f) (boxDifference a f t) t := by
  let P (s : ℝ) := ∫ u in (0:ℝ)..s, f u
  have hd (s : ℝ) : HasDerivAt P (f s) s := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 s) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : box a f = fun s => (P (s+a)-P s)/(a:ℂ) := by
    funext s
    unfold box P
    rw [intervalIntegral.integral_comp_add_left,add_zero,
      intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)]
  rw [he]
  have hshift : HasDerivAt (fun s => P (s+a)) (f (t+a)) t := by
    simpa [Function.comp_def] using (hd (t+a)).scomp t ((hasDerivAt_id t).add_const a)
  convert ((hshift.sub (hd t)).div_const (a:ℂ)) using 1
  unfold boxDifference
  ring

private theorem deriv_boxes {f : ℝ → ℂ} (hf : Continuous f) (a : ℝ) (n : ℕ) :
    deriv (boxes a (n+1) f) = boxes a n (boxDifference a f) := by
  funext s
  rw [boxes,(box_hasDerivAt (boxes_cont hf a n) a s).deriv]
  unfold boxDifference
  rw [boxes_add a n (f := fun u => (a:ℂ)⁻¹*f (u+a)) (g := fun u => (-(a:ℂ)⁻¹)*f u)
    (by fun_prop) (by fun_prop)]
  simp only [boxes_const_mul,boxes_shift]

/-- Each of the `n` fixed-width averages supplies one derivative. The bound
uses only the values of the original input in the actual interval of shifts. -/
theorem iteratedDeriv_boxes_bound {a : ℝ} (ha : 0 < a) (n : ℕ) {f : ℝ → ℂ}
    (hf : Continuous f) (t B : ℝ) (hb : ∀ s ∈ Icc t (t+n*a), ‖f s‖ ≤ B) :
    ‖iteratedDeriv n (boxes a n f) t‖ ≤ (2/a)^n*B := by
  induction n generalizing f B with
  | zero => simpa [boxes] using hb t (by simp)
  | succ n ih =>
    rw [iteratedDeriv_succ',deriv_boxes hf]
    have h := ih (boxDifference_cont hf a) ((2/a)*B) (by
      intro s hs
      have h0 := hb s ⟨hs.1,by rw [Nat.cast_succ]; nlinarith [hs.2]⟩
      have h1 := hb (s+a) ⟨by linarith [hs.1],by rw [Nat.cast_succ]; nlinarith [hs.2]⟩
      have he : boxDifference a f s = (f (s+a)-f s)/(a:ℂ) := by unfold boxDifference; ring
      rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
      exact (div_le_div_of_nonneg_right ((norm_sub_le ..).trans (add_le_add h1 h0)) ha.le).trans_eq (by ring))
    exact h.trans_eq (by rw [pow_succ]; ring)

/-- For a continuous real test whose Lipschitz constant is bounded by `L` times
its largest absolute value, a sufficiently dense set of nonnegative samples
forces its uniform integral to be nonnegative. Polynomial inverse estimates
supply such an `L` on each rescaled Taylor interval. -/
theorem integral_nonneg_of_sample_mesh {f : ℝ → ℝ} (hf : Continuous f)
    {L h M w : ℝ} (hL : 1 ≤ L) (hh : 0 ≤ h) (hmesh : h ≤ 1/(4*L^2))
    (hw : w ∈ Icc (0:ℝ) 1) (hM : |f w| = M)
    (hlip : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x-f y| ≤ L*M*|x-y|)
    (hsample : ∀ x ∈ Icc (0:ℝ) 1, ∃ y ∈ Icc (0:ℝ) 1, |x-y| ≤ h ∧ 0 ≤ f y) :
    0 ≤ ∫ x in (0:ℝ)..1, f x := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 ≤ M := hM ▸ abs_nonneg _
  let b := L*M*h
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hfloor (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ f x+b := by
    obtain ⟨y,hy,hyh,hyf⟩ := hsample x hx
    have hh' := (hlip x hx y hy).trans (mul_le_mul_of_nonneg_left hyh (mul_nonneg hL0.le hM0))
    dsimp [b]
    linarith [(abs_le.mp hh').1]
  rcases hM0.eq_or_lt with hz | hm
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    simpa [b,← hz] using hfloor x hx
  let r := 1/(2*L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrl : r*L = 1/2 := by dsimp [r]; field
  have hr2 : r ≤ 1/2 := by dsimp [r]; rw [div_le_iff₀ (by positivity)]; linarith
  have hbudget : b ≤ r*M/2 := by
    have hc := (mul_le_mul_of_nonneg_left hmesh (mul_nonneg hL0.le hm.le))
    apply hc.trans_eq
    dsimp [r]
    field
  have hfw : f w = M := by
    rcases abs_choice (f w) with h | h
    · exact h.symm.trans hM
    · have hh' := hfloor w hw
      exfalso
      nlinarith [mul_le_mul_of_nonneg_right hr2 hm.le]
  obtain ⟨a,ha,hend,hdist⟩ : ∃ a : ℝ, 0 ≤ a ∧ a+r ≤ 1 ∧
      ∀ x ∈ Icc a (a+r), |x-w| ≤ r := by
    by_cases h : w ≤ 1/2
    · exact ⟨w,hw.1,by linarith,fun x hx => abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
    · refine ⟨w-r,by linarith,by linarith [hw.2],fun x hx => abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith [hx.1,hx.2]
  have hab : a ≤ a+r := by linarith
  have hlocal (x : ℝ) (hx : x ∈ Icc a (a+r)) : M/2 ≤ f x+b := by
    have h := (hlip x ⟨ha.trans hx.1,hx.2.trans hend⟩ w hw).trans
      (mul_le_mul_of_nonneg_left (hdist x hx) (mul_nonneg hL0.le hm.le))
    rw [hfw] at h
    nlinarith [(abs_le.mp h).1,congrArg (· * M) hrl]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const (c := M/2)) ((hf.add continuous_const).intervalIntegrable a (a+r)) hlocal
  rw [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left] at hi
  have htot := intervalIntegral.integral_mono_interval (μ := volume) (f := fun x => f x+b)
    ha hab hend ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => hfloor x ⟨hx.1.le,hx.2⟩))
    ((hf.add continuous_const).intervalIntegrable 0 1)
  have hwhole : r*(M/2) ≤ ∫ x in (0:ℝ)..1, f x+b := hi.trans htot
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul,sub_zero,one_mul] at hwhole
  linarith only [hwhole,hbudget]

/-- One nonnegative sample in each cell controls the loss between the
signed integral and its absolute integral by mesh times total variation. -/
theorem sampled_partition_variation {f g : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {x : ℕ → ℝ} {N : ℕ} {h : ℝ} (hx : Monotone x)
    (hmesh : ∀ k < N, x (k+1)-x k ≤ h)
    (hsamp : ∀ k < N, ∃ w ∈ Icc (x k) (x (k+1)), 0 ≤ f w) :
    (∫ u in x 0..x N, |f u|) - (∫ u in x 0..x N, f u) ≤
      2*h*(∫ u in x 0..x N, |g u|) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun u => (hd u).continuousAt
  have cell (k : ℕ) (hk : k < N) :
      (∫ u in x k..x (k+1), |f u|-f u) ≤ 2*h*(∫ u in x k..x (k+1), |g u|) := by
    obtain ⟨w,hw,hfw⟩ := hsamp k hk
    have hab : x k ≤ x (k+1) := hx (by omega)
    let V := ∫ u in x k..x (k+1), |g u|
    have hV : 0 ≤ V := intervalIntegral.integral_nonneg hab (fun _ _ => abs_nonneg _)
    have diff {a b : ℝ} (ha : x k ≤ a) (hab' : a ≤ b) (hb : b ≤ x (k+1)) :
        |f b-f a| ≤ V := by
      rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hg.intervalIntegrable ..)]
      exact (intervalIntegral.norm_integral_le_integral_norm (f := g) hab').trans
        (intervalIntegral.integral_mono_interval ha hab' hb
          (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hg.abs.intervalIntegrable ..))
    have hp (u : ℝ) (hu : u ∈ Icc (x k) (x (k+1))) : |f u|-f u ≤ 2*V := by
      have hdu : |f u-f w| ≤ V := by
        rcases le_total u w with h | h
        · rw [abs_sub_comm]; exact diff hu.1 h hw.2
        · exact diff hw.1 h hu.2
      rcases abs_choice (f u) with hh | hh <;> linarith [(abs_le.mp hdu).1]
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab
      ((hf.abs.sub hf).intervalIntegrable ..) intervalIntegrable_const hp
    rw [intervalIntegral.integral_const,smul_eq_mul] at hi
    exact hi.trans (by nlinarith only [mul_le_mul_of_nonneg_right (hmesh k hk) hV])
  have he := Finset.sum_le_sum (s := Finset.range N) (fun k hk => cell k (Finset.mem_range.mp hk))
  rw [intervalIntegral.sum_integral_adjacent_intervals (f := fun u => |f u|-f u) (a := x)
      (fun _ _ => (hf.abs.sub hf).intervalIntegrable ..),← Finset.mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals (f := fun u => |g u|) (a := x)
      (fun _ _ => hg.abs.intervalIntegrable ..),
    intervalIntegral.integral_sub (f := fun u => |f u|) (g := f) (hf.abs.intervalIntegrable ..)
      (hf.intervalIntegrable ..)] at he
  exact he

end
end RiemannGaussian.SuzukiScaleAverage
