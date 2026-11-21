import RiemannGaussian.QuasiRHPrimePrimitiveHeat
import RiemannGaussian.RosserSchoenfeldZeroTail
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Arithmetic bounds between prime checkpoints

Freezing the prefix of the von Mangoldt primitive at a checkpoint gives a
convex upper bound throughout the following cell. The loss is controlled by
the actual accumulated prime mass in the cell.
-/

namespace RiemannGaussian.QuasiRHPrimeWindowBounds
noncomputable section
open MeasureTheory ProbabilityTheory
open QuasiRHPrimePrimitiveHeat

/-- The unnormalized discrepancy at the ordinary real cutoff x. -/
def primeError (x : ℝ) : ℝ := x-1-Real.log (2*Real.pi)*Real.log x -
  RosserSchoenfeldPrimePrimitive.value (Real.log x)

/-- The log moment of the von Mangoldt mass through the integer a. -/
def logMoment (a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 a, ArithmeticFunction.vonMangoldt n * Real.log n

/-- The explicit upper bound obtained by retaining only the prefix through a. -/
def prefixUpper (a : ℕ) (x : ℝ) : ℝ :=
  x-1 + logMoment a - (Real.log (2*Real.pi) + Chebyshev.psi a) * Real.log x

private theorem psi_eq (x : ℝ) : Chebyshev.psi x =
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rfl

private theorem prefixUpper_eq (a : ℕ) (x : ℝ) : prefixUpper a x =
    x-1-Real.log (2*Real.pi)*Real.log x -
      ∑ n ∈ Finset.Icc 1 a, ArithmeticFunction.vonMangoldt n * (Real.log x-Real.log n) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [prefixUpper, logMoment, psi_eq, Nat.floor_natCast]
  ring

private theorem sum_cell {a : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx : (a:ℝ) ≤ x) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc a ⌊x⌋₊, w n) + (∑ n ∈ Finset.Icc 1 a, w n) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, w n := by
  have hs : Finset.Icc 1 a ⊆ Finset.Icc 1 ⌊x⌋₊ :=
    Finset.Icc_subset_Icc_right ((Nat.le_floor_iff hx0).mpr hx)
  have hd : Finset.Icc 1 ⌊x⌋₊ \ Finset.Icc 1 a = Finset.Ioc a ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simpa only [hd] using Finset.sum_sdiff (f := w) hs

private theorem cell_terms {a : ℕ} {x : ℝ} (ha : 0 < a) (hx : (a:ℝ) ≤ x) :
    prefixUpper a x - primeError x =
      ∑ n ∈ Finset.Ioc a ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (Real.log x-Real.log n) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast ha) hx
  rw [prefixUpper_eq, primeError, RosserSchoenfeldPrimePrimitive.value_eq_sum, Real.exp_log hx0]
  have he := sum_cell hx0.le hx (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (Real.log x-Real.log n))
  linarith

/-- The loss from retaining the prefix is nonnegative and bounded by the
cell's actual prime mass times its logarithmic length. -/
theorem prefix_loss {a : ℕ} {x : ℝ} (ha : 0 < a) (hx : (a:ℝ) ≤ x) :
    0 ≤ prefixUpper a x - primeError x ∧
    prefixUpper a x - primeError x ≤
      (Real.log x-Real.log a)*(Chebyshev.psi x-Chebyshev.psi a) := by
  rw [cell_terms ha hx]
  have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast ha) hx
  have hmass : (∑ n ∈ Finset.Ioc a ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi x-Chebyshev.psi a := by
    have he := sum_cell hx0.le hx ArithmeticFunction.vonMangoldt
    simp only [psi_eq, Nat.floor_natCast]
    linarith
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    obtain ⟨han,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn : (0:ℝ) < n := by exact_mod_cast ha.trans han
    exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (sub_nonneg.mpr
      (Real.log_le_log hn ((Nat.le_floor_iff hx0.le).mp hnx)))
  · rw [← hmass, mul_comm, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    have han := (Finset.mem_Ioc.mp hn).1.le
    exact sub_le_sub_left (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast han)) _

/-- A pointwise arithmetic estimate for the loss, uniform in the checkpoint
and cell width. -/
theorem prefix_loss_le {a : ℕ} {x : ℝ} (ha : 0 < a) (hx : (a:ℝ) ≤ x) :
    prefixUpper a x - primeError x ≤ (x-a)^2/a * Real.log x := by
  have ha0 : 0 < (a:ℝ) := by exact_mod_cast ha
  have hx0 := ha0.trans_le hx
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hl : 0 ≤ Real.log x := Real.log_nonneg (ha1.trans hx)
  have hlog : Real.log x-Real.log a ≤ (x-a)/a := by
    rw [← Real.log_div hx0.ne' ha0.ne']
    exact (Real.log_le_sub_one_of_pos (div_pos hx0 ha0)).trans_eq (by field_simp)
  have hcap (n : ℕ) (hn : n ∈ Finset.Ioc a ⌊x⌋₊) :
      ArithmeticFunction.vonMangoldt n * (Real.log x-Real.log n) ≤ Real.log x * ((x-a)/a) := by
    obtain ⟨han,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast ha.trans han
    have hnx' := (Nat.le_floor_iff hx0.le).mp hnx
    exact mul_le_mul (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnx'))
      ((sub_le_sub_left (Real.log_le_log ha0 (by exact_mod_cast han.le)) _).trans hlog)
      (sub_nonneg.mpr (Real.log_le_log hn0 hnx')) hl
  rw [cell_terms ha hx]
  apply (Finset.sum_le_sum hcap).trans
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.cast_sub ((Nat.le_floor_iff hx0.le).mpr hx)]
  apply (mul_le_mul_of_nonneg_right (sub_le_sub_right (Nat.floor_le hx0.le) _)
    (mul_nonneg hl (div_nonneg (sub_nonneg.mpr hx) ha0.le))).trans_eq
  ring

/-- Two endpoint evaluations of the frozen prefix certify every real cutoff
in a cell, regardless of the prime powers inside. -/
theorem primeError_le_cell_max {a : ℕ} {b x : ℝ} (ha : 0 < a) (hx : x ∈ Set.Icc (a:ℝ) b) :
    primeError x ≤ max (prefixUpper a a) (prefixUpper a b) := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have hc : 0 ≤ Real.log (2*Real.pi) + Chebyshev.psi a :=
    add_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three])) (Chebyshev.psi_nonneg _)
  have hlog := ConcaveOn.smul hc strictConcaveOn_log_Ioi.concaveOn
  have hlin := ((convexOn_id (convex_Ioi (0:ℝ))).add_const (-1+logMoment a)).sub hlog
  have hf : ConvexOn ℝ (Set.Ioi 0) (prefixUpper a) := by
    convert hlin using 1
    ext t
    simp [prefixUpper]
    ring
  exact (sub_nonneg.mp (prefix_loss ha hx.1).1).trans
    (hf.le_max_of_mem_Icc ha0 (ha0.trans_le (hx.1.trans hx.2)) hx)

/-- Between consecutive fourth powers the full loss from dropping new
prime powers costs at most a logarithm after square-root normalization. -/
theorem quartic_prefix_loss {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : x ∈ Set.Icc ((m:ℝ)^4) (((m:ℝ)+1)^4)) :
    prefixUpper (m^4) x - primeError x ≤ 225*Real.sqrt x*Real.log x := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have ha : ((m^4 : ℕ):ℝ) ≤ x := by simpa only [Nat.cast_pow] using hx.1
  have h := prefix_loss_le (pow_pos hm 4) ha
  simp only [Nat.cast_pow] at h
  have h12 : (m:ℝ) ≤ m^2 := by nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm1)]
  have h23 : (m:ℝ)^2 ≤ m^3 := by nlinarith [mul_nonneg (sq_nonneg (m:ℝ)) (sub_nonneg.mpr hm1)]
  have hgap : x-(m:ℝ)^4 ≤ 15*m^3 := by nlinarith [hx.2]
  have hs := mul_self_le_mul_self (sub_nonneg.mpr hx.1) hgap
  have hb : (x-(m:ℝ)^4)^2/(m:ℝ)^4 ≤ 225*m^2 := by
    apply (div_le_iff₀ (pow_pos hm0 4)).mpr
    nlinarith
  have hsqrt : (m:ℝ)^2 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) (le_trans (by positivity : (0:ℝ) ≤ (m:ℝ)^4) hx.1)]
    nlinarith [hx.1]
  have hx1 : 1 ≤ x := (one_le_pow₀ hm1).trans hx.1
  exact h.trans (mul_le_mul_of_nonneg_right (hb.trans (by linarith)) (Real.log_nonneg hx1))

/-- A pointwise square-root certificate through the upper cutoff bounds the
Gaussian finite-window average at that observation time. -/
theorem window_le_of_primeError_bound {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (Real.exp (T/4)) (Real.exp (4*T)), primeError x ≤ c*Real.sqrt x) :
    windowPositiveAverage T ≤ c := by
  let μ := gaussianReal T (2*T).toNNReal
  let s := Set.Icc (T/4) (4*T)
  have hm : MeasurableSet s := measurableSet_Icc
  change (∫ u in s, max (discrepancy u).re 0 ∂μ) ≤ c
  rw [← integral_indicator hm]
  apply (integral_mono_of_nonneg _ (integrable_const c) _).trans_eq
  · simp
  · exact Filter.Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  · filter_upwards with u
    by_cases hu : u ∈ s
    · rw [Set.indicator_of_mem hu]
      apply max_le _ hc
      have hu0 : 0 ≤ u := (by positivity : 0 ≤ T/4).trans hu.1
      have hb := h (Real.exp u) ⟨Real.exp_le_exp.mpr hu.1,Real.exp_le_exp.mpr hu.2⟩
      have hd : (discrepancy u).re = Real.exp (-(1/2:ℝ)*u)*primeError (Real.exp u) := by
        simp only [discrepancy, hu0, ↓reduceIte, primeError, Real.log_exp,
          RosserSchoenfeldExplicitFormula.mainTerm_eq, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
          Complex.ofReal_re]
      rw [hd]
      apply (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq
      have he : Real.sqrt (Real.exp u) = Real.exp (u/2) := by
        rw [← Real.sqrt_sq (Real.exp_pos (u/2)).le, sq, ← Real.exp_add]
        ring_nf
      rw [he, mul_left_comm, ← Real.exp_add]
      rw [show -(1/2:ℝ)*u+u/2 = 0 by ring, Real.exp_zero, mul_one]
    · simpa [Set.indicator_of_notMem hu] using hc

/-- A real exponential with a cosine of given frequency and phase. -/
def dampedCosine (d g a u : ℝ) := Real.exp (d*u)*Real.cos (a+g*u)

private theorem wave_integrable (T d g a : ℝ) :
    Integrable (dampedCosine d g a) (gaussianReal T (2*T).toNNReal) := by
  apply (integrable_exp_mul_gaussianReal d).mono' (by unfold dampedCosine; fun_prop)
  filter_upwards with u
  simp only [dampedCosine, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

private theorem wave_mean_le {T : ℝ} (ht : 0 ≤ T) (d g a : ℝ) :
    (∫ u, dampedCosine d g a u ∂gaussianReal T (2*T).toNNReal) ≤
    Real.exp ((d+d^2-g^2)*T) := by
  let z : ℂ := d+(g:ℂ)*Complex.I
  let p := Complex.exp ((a:ℂ)*Complex.I)
  let μ := gaussianReal T (2*T).toNNReal
  have hp : ‖p‖ = 1 := by simp [p,Complex.norm_exp]
  have hz : z.re = d := by simp [z]
  have hz' : z.im = g := by simp [z]
  have he (u : ℝ) : (p*Complex.exp (z*u)).re = dampedCosine d g a u := by
    have heq : p*Complex.exp (z*u) = (Real.exp (d*u):ℂ) *
        Complex.exp (((a+g*u:ℝ):ℂ)*Complex.I) := by
      dsimp only [p]
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      unfold z
      ring
    rw [heq]
    simp only [dampedCosine, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  have hi : Integrable (fun u : ℝ => p*Complex.exp (z*u)) μ := by
    apply (integrable_exp_mul_gaussianReal d).mono' (by fun_prop)
    filter_upwards with u
    simp [hp,Complex.norm_exp,Complex.mul_re,hz]
  have hh : (∫ u : ℝ, p*Complex.exp (z*u) ∂μ) =
      p*Complex.exp (z*T+(((2*T).toNNReal:NNReal):ℂ)*z^2/2) := by
    rw [integral_const_mul]
    exact congrArg (p*·) (complexMGF_id_gaussianReal (μ := T) (v := (2*T).toNNReal) z)
  have hreal : (∫ u, dampedCosine d g a u ∂μ) = (∫ u : ℝ, p*Complex.exp (z*u) ∂μ).re := by
    simp_rw [← he]
    exact integral_re hi
  rw [hreal, hh]
  apply (Complex.re_le_norm _).trans_eq
  rw [norm_mul, hp, one_mul, Complex.norm_exp]
  congr 1
  have hv : ((2*T).toNNReal:ℝ) = 2*T := Real.coe_toNNReal _ (by positivity)
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  simp [Complex.mul_re, hz, hz', hv, pow_two]
  ring

/-- An elementary two-harmonic majorant pays the positive part of a
modulated exponential under the actual Gaussian measure. -/
theorem positive_cosine_mean {T : ℝ} (ht : 0 ≤ T) (d g a : ℝ) :
    (∫ u, max (dampedCosine d g a u) 0 ∂gaussianReal T (2*T).toNNReal) ≤
      (3/8 + (5/8)*Real.exp (-g^2*T))*Real.exp ((d+d^2)*T) := by
  let μ := gaussianReal T (2*T).toNNReal
  let f (u : ℝ) := (3/8:ℝ)*Real.exp (d*u)
  let b (u : ℝ) := (1/2:ℝ)*dampedCosine d g a u
  let c (u : ℝ) := (1/8:ℝ)*dampedCosine d (2*g) (2*a) u
  have hf : Integrable f μ := (integrable_exp_mul_gaussianReal d).const_mul _
  have hb : Integrable b μ := (wave_integrable T d g a).const_mul _
  have hc : Integrable c μ := (wave_integrable T d (2*g) (2*a)).const_mul _
  have hw (u : ℝ) : max (dampedCosine d g a u) 0 ≤ f u+b u+c u := by
    dsimp only [f,b,c,dampedCosine]
    rw [show 2*a+2*g*u = 2*(a+g*u) by ring, Real.cos_two_mul]
    apply max_le
    · nlinarith [mul_nonneg (Real.exp_pos (d*u)).le (sq_nonneg (Real.cos (a+g*u)-1))]
    · nlinarith [mul_nonneg (Real.exp_pos (d*u)).le (sq_nonneg (Real.cos (a+g*u)+1))]
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => le_max_right (dampedCosine d g a u) 0))
    ((hf.add hb).add hc) (Filter.Eventually.of_forall hw)
  have hab : Integrable (fun u => f u + b u) μ := hf.add hb
  simp only [Pi.add_apply] at h
  rw [integral_add hab hc, integral_add hf hb] at h
  dsimp only [f,b,c,μ] at h
  rw [integral_const_mul, integral_const_mul, integral_const_mul, scaled_exp_mean T d ht] at h
  have h₂ := wave_mean_le ht d (2*g) (2*a)
  have h₂' : Real.exp ((d+d^2-(2*g)^2)*T) ≤ Real.exp ((d+d^2-g^2)*T) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg g]) ht)
  have he : Real.exp ((d+d^2-g^2)*T) = Real.exp (-g^2*T)*Real.exp ((d+d^2)*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₁ := wave_mean_le ht d g a
  rw [he] at h₁ h₂'
  linarith

private def posAtom (ρ : NontrivialZetaZero) (u : ℝ) : ℝ :=
  max (coefficient ρ * Complex.exp (rate ρ 0*u)).re 0

private theorem atom_norm (ρ : NontrivialZetaZero) (u : ℝ) :
    ‖coefficient ρ * Complex.exp (rate ρ 0*u)‖ =
      ‖coefficient ρ‖*Real.exp ((ρ.1.re-1/2)*u) := by
  simp [rate, Complex.norm_exp, Complex.mul_re]

private theorem atom_re (ρ : NontrivialZetaZero) (u : ℝ) :
    (coefficient ρ * Complex.exp (rate ρ 0*u)).re =
      ‖coefficient ρ‖ * dampedCosine (ρ.1.re-1/2) ρ.1.im (coefficient ρ).arg u := by
  let c := coefficient ρ
  have he : c * Complex.exp (rate ρ 0*u) =
      ((‖c‖*Real.exp ((ρ.1.re-1/2)*u) : ℝ):ℂ) *
        Complex.exp (((c.arg+ρ.1.im*u:ℝ):ℂ)*Complex.I) := by
    conv_lhs => lhs; rw [← Complex.norm_mul_exp_arg_mul_I c]
    push_cast
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    rw [show rate ρ 0 = (ρ.1.re:ℂ) + (ρ.1.im:ℂ)*Complex.I - 1/2 by simp [rate]]
    ring
  rw [show coefficient ρ = c by rfl, he]
  simp only [dampedCosine,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.exp_ofReal_mul_I_re,mul_assoc]

private theorem posAtom_mean {T : ℝ} (hT : 0 ≤ T) (ρ : NontrivialZetaZero) :
    (∫ u, posAtom ρ u ∂gaussianReal T (2*T).toNNReal) ≤
      (3/8+(5/8)*Real.exp (-196*T)) *
        (‖coefficient ρ‖*Real.exp ((ρ.1.re^2-1/4)*T)) := by
  have he (u : ℝ) : posAtom ρ u = ‖coefficient ρ‖ *
      max (dampedCosine (ρ.1.re-1/2) ρ.1.im (coefficient ρ).arg u) 0 := by
    rw [posAtom,atom_re,mul_max_of_nonneg _ _ (norm_nonneg _), mul_zero]
  simp_rw [he]
  rw [integral_const_mul]
  have h := positive_cosine_mean hT (ρ.1.re-1/2) ρ.1.im (coefficient ρ).arg
  rw [show ρ.1.re-1/2+(ρ.1.re-1/2)^2 = ρ.1.re^2-1/4 by ring] at h
  apply (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans
  rw [mul_left_comm]
  have hg := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
  have hsq : 196 ≤ ρ.1.im^2 := by
    nlinarith [sq_abs ρ.1.im,
      mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 14) hg.le]
  gcongr

/-- The Gaussian positive part of one critical-line mode retains the
oscillatory saving uniformly in its phase. -/
theorem critical_mode_positive_mean {T : ℝ} (hT : 0 ≤ T) (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re = 1/2) :
    (∫ u : ℝ, max (coefficient ρ*Complex.exp (rate ρ 0*u)).re 0 ∂gaussianReal T (2*T).toNNReal) ≤
      (3/8+(5/8)*Real.exp (-196*T))*‖coefficient ρ‖ := by
  have h := posAtom_mean hT ρ
  rw [hρ] at h
  norm_num at h
  simpa only [posAtom,neg_mul] using h

private theorem absCoeff_summable : Summable (fun ρ => ‖coefficient ρ‖) := by
  simpa [coefficient] using RosserSchoenfeldZeroMass.norm_square_mass_summable

private theorem atom_bound (ρ : NontrivialZetaZero) (u : ℝ) :
    ‖coefficient ρ * Complex.exp (rate ρ 0*u)‖ ≤
      ‖coefficient ρ‖ * (Real.exp (1*u)+Real.exp ((-1)*u)) := by
  rw [atom_norm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rcases le_total 0 u with hu | hu
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [ρ.re_lt_one]) hu)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith [ρ.zero_lt_re]) hu)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

private theorem mode_positive_integral {T : ℝ} (hT : 4 ≤ T) :
    windowPositiveAverage T ≤ ∑' ρ, ∫ u, posAtom ρ u ∂gaussianReal T (2*T).toNNReal := by
  let μ := gaussianReal T (2*T).toNNReal
  let g (u : ℝ) := Real.exp (1*u)+Real.exp ((-1)*u)
  have hg : Integrable g μ := (integrable_exp_mul_gaussianReal 1).add (integrable_exp_mul_gaussianReal (-1))
  have hb (ρ : NontrivialZetaZero) (u : ℝ) : posAtom ρ u ≤ ‖coefficient ρ‖ * g u :=
    (max_le (Complex.re_le_norm _) (norm_nonneg _)).trans (atom_bound ρ u)
  have hn (ρ : NontrivialZetaZero) (u : ℝ) : 0 ≤ posAtom ρ u := le_max_right _ _
  have hnorm (ρ : NontrivialZetaZero) (u : ℝ) : ‖posAtom ρ u‖ = posAtom ρ u := Real.norm_of_nonneg (hn ρ u)
  have hm (ρ : NontrivialZetaZero) : Measurable (posAtom ρ) := by unfold posAtom; fun_prop
  have hs (u : ℝ) : Summable (fun ρ => posAtom ρ u) :=
    (absCoeff_summable.mul_right _).of_nonneg_of_le (fun ρ => hn ρ u) (fun ρ => hb ρ u)
  have hi (ρ : NontrivialZetaZero) : Integrable (posAtom ρ) μ := by
    apply (hg.const_mul ‖coefficient ρ‖).mono' (hm ρ).aestronglyMeasurable
    filter_upwards with u
    rw [hnorm]
    exact hb ρ u
  have hsi : Summable (fun ρ => ∫ u, ‖posAtom ρ u‖ ∂μ) := by
    simp_rw [hnorm]
    apply (absCoeff_summable.mul_right (∫ u, g u ∂μ)).of_nonneg_of_le (fun ρ => integral_nonneg (hn ρ))
    intro ρ
    rw [← integral_const_mul]
    exact integral_mono (hi ρ) (hg.const_mul _) (hb ρ)
  have hsum : Integrable (fun u => ∑' ρ, posAtom ρ u) μ := by
    apply (hg.const_mul (∑' ρ, ‖coefficient ρ‖)).mono' (Measurable.tsum hm).aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_of_nonneg (tsum_nonneg fun ρ => hn ρ u)]
    exact ((hs u).tsum_le_tsum (fun ρ => hb ρ u) (absCoeff_summable.mul_right _)).trans_eq tsum_mul_right
  rw [integral_tsum_of_summable_integral_norm hi hsi]
  unfold windowPositiveAverage
  rw [← integral_indicator measurableSet_Icc]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => Set.indicator_nonneg
    (fun _ _ => le_max_right _ _) _)) hsum
  filter_upwards with u
  by_cases hu : u ∈ Set.Icc (T/4) (4*T)
  · rw [Set.indicator_of_mem hu]
    apply max_le _ (tsum_nonneg fun ρ => hn ρ u)
    apply (discrepancy_re_le_modes (by linarith [hu.1] : 1 ≤ u)).trans
    have hc := ((absCoeff_summable.mul_right (g u)).of_nonneg_of_le
      (fun ρ => norm_nonneg _) (fun ρ => atom_bound ρ u)).of_norm
    rw [modes, Complex.re_tsum hc]
    exact (Complex.reCLM.summable hc).tsum_le_tsum (fun ρ => le_max_left _ _) (hs u)
  · simp only [Set.indicator_of_notMem hu]
    exact tsum_nonneg (fun ρ => hn ρ u)

/-- A zero-tail bound for moving a prime checkpoint in logarithmic time.
The low zeros pay their frequency times the mesh width and every high zero
pays only its reciprocal-square mass. -/
theorem discrepancy_increment {B H u v : ℝ} (hB : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B)
    (hhalf : 1/2 ≤ B) (hH : 2 ≤ H) (hv : 0 ≤ v) (hvu : v ≤ u)
    (hmesh : (1+H)*(u-v) ≤ 1) :
    ‖discrepancy u-discrepancy v‖ ≤ 2*Real.exp (-v/2) +
      2*Real.exp ((B-1/2)*u)*((463/10000)*(1+H)*(u-v)+(8+2*Real.log H)/H) := by
  let E := Real.exp ((B-1/2)*u)
  let L := (1+H)*(u-v)
  let wave (ρ : NontrivialZetaZero) (t : ℝ) := coefficient ρ * Complex.exp (rate ρ 0*t)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hL : 0 ≤ L := mul_nonneg (by linarith) (sub_nonneg.mpr hvu)
  have hpoint (ρ : NontrivialZetaZero) {t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
      ‖wave ρ t‖ ≤ ‖coefficient ρ‖*E := by
    change ‖coefficient ρ * Complex.exp (rate ρ 0*t)‖ ≤ _
    rw [atom_norm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (sub_le_sub_right (hB ρ) _) ht).trans
      (mul_le_mul_of_nonneg_left htu (sub_nonneg.mpr hhalf)))
  have hs {t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : Summable (wave · t) :=
    ((absCoeff_summable.mul_right E).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun ρ => hpoint ρ ht htu)).of_norm
  have hatom (ρ : NontrivialZetaZero) :
      ‖wave ρ u-wave ρ v‖ ≤ (‖coefficient ρ‖*L+RosserSchoenfeldZeroTail.term H ρ)*(2*E) := by
    by_cases hz : |ρ.1.im| < H
    · have hr : ‖rate ρ 0‖ ≤ 1+H := by
        apply (Complex.norm_le_abs_re_add_abs_im _).trans
        simp only [rate, Complex.ofReal_zero, zero_mul, sub_zero, Complex.sub_re, Complex.div_ofNat_re,
          Complex.one_re, Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div]
        linarith [(abs_le.mpr (show -1 ≤ ρ.1.re-1/2 ∧ ρ.1.re-1/2 ≤ 1 by
          constructor <;> linarith [ρ.zero_lt_re,ρ.re_lt_one]))]
      have hn : ‖rate ρ 0*((u-v:ℝ):ℂ)‖ ≤ L := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hvu)]
        exact mul_le_mul_of_nonneg_right hr (sub_nonneg.mpr hvu)
      have he : wave ρ u-wave ρ v = wave ρ v*(Complex.exp (rate ρ 0*((u-v:ℝ):ℂ))-1) := by
        simp only [wave, mul_sub, mul_one, mul_assoc, ← Complex.exp_add, Complex.ofReal_sub]
        ring_nf
      rw [he,norm_mul]
      have hb := mul_le_mul (hpoint ρ hv hvu)
        ((Complex.norm_exp_sub_one_le (hn.trans hmesh)).trans (by linarith : 2*‖_‖ ≤ 2*L))
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) hE)
      simpa only [RosserSchoenfeldZeroTail.term,ite_eq_right (not_le.mpr hz),add_zero] using
        hb.trans_eq (by ring : ‖coefficient ρ‖*E*(2*L) = (‖coefficient ρ‖*L)*(2*E))
    · have ht : RosserSchoenfeldZeroTail.term H ρ = ‖coefficient ρ‖ := by
        simp [RosserSchoenfeldZeroTail.term,le_of_not_gt hz,coefficient]
      rw [ht]
      have hh := (norm_sub_le _ _).trans (add_le_add
        (hpoint ρ (hv.trans hvu) le_rfl) (hpoint ρ hv hvu))
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (coefficient ρ)) hL) hE]
  have hsum := ((absCoeff_summable.mul_right L).add
    (RosserSchoenfeldZeroTail.summable_term H)).mul_right (2*E)
  have hnorm := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hatom
  have hm : ‖modes 0 u-modes 0 v‖ ≤
      2*E*((463/10000)*L+(8+2*Real.log H)/H) := by
    change ‖(∑' ρ, wave ρ u)-(∑' ρ, wave ρ v)‖ ≤ _
    rw [← (hs (hv.trans hvu) le_rfl).tsum_sub (hs hv hvu)]
    apply (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hatom hsum).trans _)
    rw [tsum_mul_right,(absCoeff_summable.mul_right L).tsum_add (RosserSchoenfeldZeroTail.summable_term H),
      tsum_mul_right,mul_comm (2*E)]
    have hc : (∑' ρ, ‖coefficient ρ‖) ≤ 463/10000 := by
      simpa [coefficient] using RosserSchoenfeldZeroMass.norm_square_mass_lt.le
    exact mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right hc hL)
      (RosserSchoenfeldZeroTail.value_le hH)) (by positivity)
  have htri : ‖discrepancy u-discrepancy v‖ ≤
      ‖discrepancy u-modes 0 u‖+‖modes 0 u-modes 0 v‖+‖discrepancy v-modes 0 v‖ := by
    calc
      _ = ‖((discrepancy u-modes 0 u)+(modes 0 u-modes 0 v))-(discrepancy v-modes 0 v)‖ := by abel_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hu := (norm_discrepancy_sub_modes u).trans (Real.exp_le_exp.mpr
    (show -(1/2:ℝ)*u ≤ -v/2 by linarith))
  have he := norm_discrepancy_sub_modes v
  rw [show -(1/2:ℝ)*v = -v/2 by ring] at he
  dsimp only [L,E] at hm
  linarith

/-- A pointwise upper bound on the actual finite prime sum, retaining the
phases of any selected zeros and charging the entire omitted mass. -/
theorem discrepancy_le_finite_spectrum (S : Finset NontrivialZetaZero) {H u : ℝ} (hH : 2 ≤ H)
    (hu : 1 ≤ u) (hver : ∀ ρ : NontrivialZetaZero, |ρ.1.im| < H → ρ.1.re = 1/2) :
    (discrepancy u).re ≤
      (∑ ρ ∈ S, (coefficient ρ * Complex.exp (rate ρ 0*u)).re) +
      (463/10000 - ∑ ρ ∈ S, ‖coefficient ρ‖) +
      ((8+2*Real.log H)/H)*Real.exp ((3/8:ℝ)*u) := by
  let w (ρ : NontrivialZetaZero) := coefficient ρ*Complex.exp (rate ρ 0*u)
  let E := Real.exp ((3/8:ℝ)*u)
  have hu0 : 0 ≤ u := by linarith
  have he : 0 ≤ E := (Real.exp_pos _).le
  have hb (ρ : NontrivialZetaZero) : ‖w ρ‖ ≤ ‖coefficient ρ‖ + RosserSchoenfeldZeroTail.term H ρ*E := by
    change ‖coefficient ρ*Complex.exp (rate ρ 0*u)‖ ≤ _
    rw [atom_norm]
    by_cases h : |ρ.1.im| < H
    · simp [hver ρ h,RosserSchoenfeldZeroTail.term,not_le.mpr h]
    · have ht : RosserSchoenfeldZeroTail.term H ρ = ‖coefficient ρ‖ := by
        simp [RosserSchoenfeldZeroTail.term,le_of_not_gt h,coefficient]
      rw [ht]
      apply le_add_of_nonneg_of_le (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [suzukiLocalZero_re_le_seven_eighths ρ]) hu0)
  have htail := RosserSchoenfeldZeroTail.summable_term H
  have hs := absCoeff_summable.add (htail.mul_right E)
  have hw := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hz := (hw.subtype (· ∈ (S : Set NontrivialZetaZero)ᶜ)).tsum_le_tsum
    (fun ρ : ↥(S : Set NontrivialZetaZero)ᶜ => hb ρ.1) (hs.subtype _)
  have hcs : Summable (fun ρ : ↥(S : Set NontrivialZetaZero)ᶜ => ‖coefficient ρ.1‖) :=
    absCoeff_summable.subtype _
  have hts : Summable (fun ρ : ↥(S : Set NontrivialZetaZero)ᶜ => RosserSchoenfeldZeroTail.term H ρ.1) :=
    htail.subtype _
  rw [hcs.tsum_add (hts.mul_right E),tsum_mul_right] at hz
  have hc := absCoeff_summable.sum_add_tsum_compl (s := S)
  have hm : (∑' ρ, ‖coefficient ρ‖) ≤ 463/10000 := by
    simpa [coefficient] using RosserSchoenfeldZeroMass.norm_square_mass_lt.le
  have hrest := (Summable.tsum_subtype_le (RosserSchoenfeldZeroTail.term H) (· ∈ (S : Set NontrivialZetaZero)ᶜ)
    (RosserSchoenfeldZeroTail.term_nonneg H) htail).trans (RosserSchoenfeldZeroTail.value_le hH)
  apply (discrepancy_re_le_modes hu).trans
  change (∑' ρ, w ρ).re ≤ _
  rw [← hw.of_norm.sum_add_tsum_compl (s := S),Complex.add_re,Complex.re_sum]
  have hbound := ((Complex.re_le_norm _).trans (norm_tsum_le_tsum_norm (hw.subtype _))).trans hz
  have hcm : (∑' ρ : ↥(S : Set NontrivialZetaZero)ᶜ, ‖coefficient ρ.1‖) ≤
      463/10000 - ∑ ρ ∈ S, ‖coefficient ρ‖ := by linarith
  rw [add_assoc]
  exact add_le_add le_rfl (hbound.trans (add_le_add hcm (mul_le_mul_of_nonneg_right hrest he)))

/-- The positive prime window is bounded explicitly from a critical-line
verification through H. The entire unverified tail is included. -/
theorem window_le_of_verified_height {H T : ℝ} (hH : 2 ≤ H) (hT : 4 ≤ T)
    (hver : ∀ ρ : NontrivialZetaZero, |ρ.1.im| < H → ρ.1.re = 1/2) :
    windowPositiveAverage T ≤ (3/8+(5/8)*Real.exp (-196*T)) *
      (463/10000 + ((8+2*Real.log H)/H)*Real.exp ((33/64:ℝ)*T)) := by
  let K := 3/8+(5/8)*Real.exp (-196*T)
  let E := Real.exp ((33/64:ℝ)*T)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h0 : 0 ≤ T := by linarith
  have hpoint (ρ : NontrivialZetaZero) :
      ‖coefficient ρ‖*Real.exp ((ρ.1.re^2-1/4)*T) ≤
      ‖coefficient ρ‖ + RosserSchoenfeldZeroTail.term H ρ * E := by
    by_cases hv : |ρ.1.im| < H
    · simp [hver ρ hv,RosserSchoenfeldZeroTail.term,not_le.mpr hv]
      norm_num
    · have hβ := suzukiLocalZero_re_le_seven_eighths ρ
      have hh := mul_self_le_mul_self ρ.zero_lt_re.le hβ
      have he : Real.exp ((ρ.1.re^2-1/4)*T) ≤ E :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by nlinarith) h0)
      have ht : RosserSchoenfeldZeroTail.term H ρ = ‖coefficient ρ‖ := by
        simp [RosserSchoenfeldZeroTail.term,le_of_not_gt hv,coefficient]
      rw [ht]
      exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans (le_add_of_nonneg_left (norm_nonneg _))
  have hs := (absCoeff_summable.add ((RosserSchoenfeldZeroTail.summable_term H).mul_right E)).mul_left K
  have hh (ρ : NontrivialZetaZero) := (posAtom_mean h0 ρ).trans (mul_le_mul_of_nonneg_left (hpoint ρ) hK)
  have hsi := hs.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => le_max_right _ _) hh
  apply (mode_positive_integral hT).trans ((hsi.tsum_le_tsum hh hs).trans _)
  rw [tsum_mul_left, absCoeff_summable.tsum_add ((RosserSchoenfeldZeroTail.summable_term H).mul_right E),
    tsum_mul_right]
  have hmass : (∑' ρ, ‖coefficient ρ‖) ≤ 463/10000 := by
    simpa [coefficient] using RosserSchoenfeldZeroMass.norm_square_mass_lt.le
  exact mul_le_mul_of_nonneg_left (add_le_add hmass (mul_le_mul_of_nonneg_right
    (RosserSchoenfeldZeroTail.value_le hH) (Real.exp_pos _).le)) hK

/-- Inserting the published verification height suffices on the whole
interval [4,40]. The verification itself is an explicit hypothesis. -/
theorem window_le_through_forty {T : ℝ} (hT : T ∈ Set.Icc 4 40)
    (hver : ∀ ρ : NontrivialZetaZero, |ρ.1.im| < 3000000000000 → ρ.1.re = 1/2) :
    windowPositiveAverage T < 1/40 := by
  have h := window_le_of_verified_height (by norm_num : (2:ℝ) ≤ 3000000000000) hT.1 hver
  have hlog : Real.log 3000000000000 ≤ 29 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    rw [show (29:ℝ) = (29:ℕ)*1 by norm_num,Real.exp_nat_mul]
    apply le_trans _ (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 271/100)
      (by linarith [Real.exp_one_gt_d9] : (271/100:ℝ) ≤ Real.exp 1) 29)
    norm_num
  have hexp : Real.exp ((33/64:ℝ)*T) ≤ 910000000 := by
    apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT.2 (by norm_num : (0:ℝ) ≤ 33/64))).trans
    apply le_of_pow_le_pow_left₀ (n := 8) (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul, show (↑(8:ℕ):ℝ)*(33/64*40) = (165:ℕ)*1 by norm_num,
      Real.exp_nat_mul]
    apply (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 165).trans
    norm_num
  have hsmall : Real.exp (-196*T) ≤ 1/1000 := by
    apply (Real.exp_le_exp.mpr (by linarith [hT.1] : -196*T ≤ -10)).trans
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    rw [show (10:ℝ) = (10:ℕ)*1 by norm_num,Real.exp_nat_mul]
    exact (by norm_num : (1000:ℝ) ≤ 2^10).trans (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 10)
  apply h.trans_lt
  calc
    _ ≤ (3/8+(5/8)*(1/1000:ℝ)) * (463/10000+((8+2*29)/3000000000000)*910000000) := by
      gcongr
    _ < _ := by norm_num

/-- The continuum interval through time 40 uses two finite inputs: a
prime-prefix certificate at small scales and the critical-line verification
at large heights. -/
theorem window_le_zero_through_forty
    (hprime : ∀ x ∈ Set.Icc (1:ℝ) (2^27), primeError x ≤ (1/40)*Real.sqrt x)
    (hver : ∀ ρ : NontrivialZetaZero, |ρ.1.im| < 3000000000000 → ρ.1.re = 1/2)
    {T : ℝ} (ht : T ∈ Set.Icc 0 40) : windowPositiveAverage T ≤ 1/40 := by
  rcases le_total 4 T with h | h
  · exact (window_le_through_forty ⟨h,ht.2⟩ hver).le
  · apply window_le_of_primeError_bound ht.1 (by norm_num)
    intro x hx
    apply hprime
    refine ⟨(Real.one_le_exp_iff.mpr (by linarith [ht.1])).trans hx.1, hx.2.trans ?_⟩
    apply (Real.exp_le_exp.mpr (show 4*T ≤ (16:ℕ)*1 by norm_num; linarith)).trans
    rw [Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 16).trans (by norm_num)

/-- The positive window on RH admits a uniform bound at every time at
least four, with a numerical margin below one fortieth. -/
theorem window_le_of_rh (h : RiemannHypothesis) {T : ℝ} (ht : 4 ≤ T) :
    windowPositiveAverage T ≤ (3/8+(5/8)*Real.exp (-196*T)) * (463/10000) := by
  let K := 3/8+(5/8)*Real.exp (-196*T)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hh (ρ : NontrivialZetaZero) :
      (∫ u, posAtom ρ u ∂gaussianReal T (2*T).toNNReal) ≤ K*‖coefficient ρ‖ := by
    have hb := posAtom_mean (by linarith : 0 ≤ T) ρ
    rw [h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2] at hb
    norm_num at hb
    simpa only [K, neg_mul] using hb
  have hs := absCoeff_summable.mul_left K
  have hi := hs.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => le_max_right _ _) hh
  apply (mode_positive_integral ht).trans ((hi.tsum_le_tsum hh hs).trans _)
  rw [tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hK
  simpa [coefficient] using RosserSchoenfeldZeroMass.norm_square_mass_lt.le

/-- Testing all times from four onwards is equivalent to RH. One
strict violation would already contradict RH. -/
theorem riemannHypothesis_iff_every_window :
    RiemannHypothesis ↔ ∀ T : ℝ, 4 ≤ T → windowPositiveAverage T ≤ 1/40 := by
  refine ⟨fun h T ht => (window_le_of_rh h ht).trans ?_,?_⟩
  · have he : Real.exp (-196*T) ≤ 1/8 := by
      rw [show -196*T = -(196*T) by ring,Real.exp_neg,← one_div]
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [Real.add_one_le_exp (196*T)]
    linarith
  · intro h
    exact riemannHypothesis_iff_window_le_one_fortieth.mpr
      (((Filter.eventually_ge_atTop (4:ℝ)).mono h).frequently)

/-- The fully arithmetic interpolation loss for a cubic cell, before
square-root normalization. -/
theorem cubic_prefix_loss {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : x ∈ Set.Icc ((m:ℝ)^3) (((m:ℝ)+1)^3)) :
    prefixUpper (m^3) x - primeError x ≤ 49*m*Real.log x := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have ha : ((m^3 : ℕ):ℝ) ≤ x := by simpa only [Nat.cast_pow] using hx.1
  have h := prefix_loss_le (pow_pos hm 3) ha
  simp only [Nat.cast_pow] at h
  have h12 : (m:ℝ) ≤ m^2 := by nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm1)]
  have hgap : x-(m:ℝ)^3 ≤ 7*m^2 := by nlinarith [hx.2]
  have hs := mul_self_le_mul_self (sub_nonneg.mpr hx.1) hgap
  have hb : (x-(m:ℝ)^3)^2/(m:ℝ)^3 ≤ 49*m := by
    apply (div_le_iff₀ (pow_pos hm0 3)).mpr
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right hb (Real.log_nonneg ((one_le_pow₀ hm1).trans hx.1)))

/-- Cubic checkpoints on the physical x scale give an approximation
using just the two arithmetic prefix sums at each retained integer cube. -/
def cubicPositive (u : ℝ) : ℝ :=
  Real.exp (-(1/2:ℝ)*u) * max (prefixUpper (⌊Real.exp (u/3)⌋₊^3) (Real.exp u)) 0

private theorem real_discrepancy {u : ℝ} (hu : 0 ≤ u) :
    (discrepancy u).re = Real.exp (-(1/2:ℝ)*u)*primeError (Real.exp u) := by
  simp only [discrepancy, hu, ↓reduceIte, primeError, Real.log_exp,
    RosserSchoenfeldExplicitFormula.mainTerm_eq, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- Uniform pointwise enclosure after normalizing by the square root.
The error is exponentially small in logarithmic time. -/
theorem cubicPositive_error {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cubicPositive u - max (discrepancy u).re 0 ∧
    cubicPositive u - max (discrepancy u).re 0 ≤ 49*u*Real.exp (-u/6) := by
  let m := ⌊Real.exp (u/3)⌋₊
  have hpos := Real.exp_pos (u/3)
  have hm : 0 < m := Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr (by linarith))
  have hlo : (m:ℝ) ≤ Real.exp (u/3) := Nat.floor_le hpos.le
  have hhi : Real.exp (u/3) ≤ (m:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have he : Real.exp (u/3)^3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hx : Real.exp u ∈ Set.Icc ((m:ℝ)^3) (((m:ℝ)+1)^3) := by
    rw [← he]
    exact ⟨pow_le_pow_left₀ (Nat.cast_nonneg _) hlo 3,pow_le_pow_left₀ hpos.le hhi 3⟩
  have hlow := (prefix_loss (pow_pos hm 3) (show ((m^3 : ℕ) : ℝ) ≤ Real.exp u by
    simpa only [Nat.cast_pow] using hx.1)).1
  have hhigh := cubic_prefix_loss hm hx
  rw [Real.log_exp] at hhigh
  have hmax : max (prefixUpper (m^3) (Real.exp u)) 0 - max (primeError (Real.exp u)) 0 ≤
      49*m*u := by
    rcases le_total 0 (prefixUpper (m^3) (Real.exp u)) with h | h
    · rw [max_eq_left h]
      linarith [le_max_left (primeError (Real.exp u)) 0]
    · rw [max_eq_right h]
      have := mul_nonneg (show 0 ≤ 49*(m:ℝ) by positivity) hu
      linarith [le_max_right (primeError (Real.exp u)) 0]
  rw [real_discrepancy hu, show max (Real.exp (-(1/2:ℝ)*u)*primeError (Real.exp u)) 0 =
    Real.exp (-(1/2:ℝ)*u)*max (primeError (Real.exp u)) 0 by
      rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le,mul_zero]]
  unfold cubicPositive
  rw [← mul_sub]
  refine ⟨mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (max_le_max (sub_nonneg.mp hlow) le_rfl)), ?_⟩
  apply (mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le).trans
  calc
    _ ≤ Real.exp (-(1/2:ℝ)*u)*(49*Real.exp (u/3)*u) := by gcongr
    _ = 49*u*(Real.exp (-(1/2:ℝ)*u)*Real.exp (u/3)) := by ring
    _ = _ := by rw [← Real.exp_add,show -(1/2:ℝ)*u+u/3 = -u/6 by ring]

/-- The computable upper approximation to the finite Gaussian window. -/
def cubicWindow (T : ℝ) : ℝ :=
  ∫ u in Set.Icc (T/4) (4*T), cubicPositive u ∂gaussianReal T (2*T).toNNReal

/-- At every time the entire difference between the sparse upper
approximation and the actual positive window is explicitly bounded. -/
theorem cubicWindow_error {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ cubicWindow T-windowPositiveAverage T ∧
    cubicWindow T-windowPositiveAverage T ≤ 196*T*Real.exp (-T/24) := by
  let μ := (gaussianReal T (2*T).toNNReal).restrict (Set.Icc (T/4) (4*T))
  let f (u : ℝ) := max (discrepancy u).re 0
  let E := 196*T*Real.exp (-T/24)
  have hmem : ∀ᵐ u ∂μ, u ∈ Set.Icc (T/4) (4*T) := ae_restrict_mem measurableSet_Icc
  have hpoint : ∀ᵐ u ∂μ, 0 ≤ cubicPositive u - f u ∧ cubicPositive u - f u ≤ E := by
    filter_upwards [hmem] with u hu
    have hu0 : 0 ≤ u := (by positivity : 0 ≤ T/4).trans hu.1
    refine ⟨(cubicPositive_error hu0).1,(cubicPositive_error hu0).2.trans ?_⟩
    dsimp only [E]
    have he := Real.exp_le_exp.mpr (show -u/6 ≤ -T/24 by linarith [hu.1])
    exact (mul_le_mul (by linarith [hu.2] : 49*u ≤ 196*T) he (Real.exp_pos _).le (by positivity))
  have hme : Measurable cubicPositive := by
    let i (u : ℝ) := ⌊Real.exp (u/3)⌋₊^3
    have hi : Measurable i := by dsimp [i]; fun_prop
    have h1 : Measurable (fun u => logMoment (i u)) := (measurable_of_countable logMoment).comp hi
    have h2 : Measurable (fun u => Chebyshev.psi (i u)) :=
      (measurable_of_countable (fun n : ℕ => Chebyshev.psi n)).comp hi
    unfold cubicPositive prefixUpper
    fun_prop (disch := assumption)
  have hf : Integrable f μ := (positive_integrable T).restrict
  have he : Integrable (fun u => cubicPositive u-f u) μ := by
    apply (integrable_const E).mono' _ (hpoint.mono fun u hu => (Real.norm_of_nonneg hu.1).trans_le hu.2)
    exact hme.aestronglyMeasurable.sub hf.aestronglyMeasurable
  have hsum := integral_add he hf
  simp only [sub_add_cancel] at hsum
  change 0 ≤ (∫ u, cubicPositive u ∂μ) - (∫ u, f u ∂μ) ∧ _
  have heq : cubicWindow T - windowPositiveAverage T = ∫ u, cubicPositive u-f u ∂μ := by
    change (∫ u, cubicPositive u ∂μ) - (∫ u, f u ∂μ) = _
    linarith
  change 0 ≤ cubicWindow T - windowPositiveAverage T ∧ _
  rw [heq]
  refine ⟨integral_nonneg_of_ae (hpoint.mono fun _ h => h.1),?_⟩
  have hb := integral_mono_ae he (integrable_const E) (hpoint.mono fun _ h => h.2)
  rw [integral_const, smul_eq_mul] at hb
  have hprob : μ.real Set.univ ≤ 1 := by
    dsimp only [μ]
    rw [measureReal_restrict_apply_univ]
    exact measureReal_le_one
  exact hb.trans (mul_le_of_le_one_left (by dsimp [E]; positivity) hprob)

open Filter Topology

/-- The same numerical RH criterion needs only cubic prime checkpoints.
The threshold has room for the vanishing interpolation error on RH. -/
theorem riemannHypothesis_iff_cubicWindow_le_one_fortieth :
    RiemannHypothesis ↔ ∃ᶠ T : ℝ in atTop, cubicWindow T ≤ 1/40 := by
  constructor
  · intro h
    have he : Tendsto (fun T : ℝ => 196*T*Real.exp (-T/24)) atTop (𝓝 0) := by
      have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/24) (by norm_num)).const_mul (196:ℝ)
      simpa only [Real.rpow_one, mul_zero, mul_assoc, show ∀ T : ℝ, -(1/24:ℝ)*T = -T/24 by
        intro T; ring] using hh
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (0:ℝ),eventually_window_le_of_rh h (c := 24/1000) (by norm_num),
      (tendsto_order.mp he).2 (1/1000) (by norm_num)] with T hT hw herr
    linarith [(cubicWindow_error hT).2]
  · intro h
    apply riemannHypothesis_iff_window_le_one_fortieth.mpr
    exact (h.and_eventually (eventually_ge_atTop (0:ℝ))).mono fun T ⟨hh,ht⟩ =>
      (sub_nonneg.mp (cubicWindow_error ht).1).trans hh

end
end RiemannGaussian.QuasiRHPrimeWindowBounds
