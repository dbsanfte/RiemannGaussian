/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeBandAbel
import RiemannGaussian.RosserSchoenfeldLargeChebyshev
import RiemannGaussian.ZetaRieszOwnerCountEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative signed prime-period errors

The actual prime sum is compared with its signed smooth moment on one finite
interval. Both endpoints are retained. The explicit Chebyshev error is used
only after the phase has been kept in the smooth moment; no source-normalized
transport or estimate for a packet with deleted sectors is asserted.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszQuantitativePrimePeriod

private def primeCoefficient (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private theorem primeCoefficient_sum (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeCoefficient n) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc,Finset.sum_filter]
  rfl

/-- The exact actual-prime Abel formula, retaining both exterior endpoints
and the signed integral against the Chebyshev discrepancy. -/
theorem prime_abel (f : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hi : IntegrableOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, f p*Real.log p)-
      (∫ x in Set.Ioc a b, f x) =
      f b*(Chebyshev.theta b-b)-f a*(Chebyshev.theta a-a)+
        ∫ x in Set.Ioc a b, deriv f x*(x-Chebyshev.theta x) := by
  have hs := sum_mul_eq_sub_sub_integral_mul primeCoefficient ha hab hd hi
  simp_rw [primeCoefficient_sum] at hs
  have he : (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, f p*Real.log p) =
      ∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f p*primeCoefficient p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> simp [primeCoefficient,hp]
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := f) (u' := deriv f)
    (v := fun x : ℝ => x) (v' := fun _ : ℝ => 1)
    (fun x hx => (hd x (by simpa only [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x _ => hasDerivAt_id x)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi) intervalIntegrable_const
  simp only [mul_one,intervalIntegral.integral_of_le hab] at hip
  have htheta := integrableOn_mul_sum_Icc primeCoefficient (m := 0) ha hi
  simp_rw [primeCoefficient_sum] at htheta
  have hx : IntegrableOn (fun x => deriv f x*x) (Set.Ioc a b) := by
    exact (hi.mul_continuousOn continuous_id.continuousOn isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hid : (∫ x in Set.Ioc a b, deriv f x*x)-
      (∫ x in Set.Ioc a b, deriv f x*Chebyshev.theta x) =
      ∫ x in Set.Ioc a b, deriv f x*(x-Chebyshev.theta x) := by
    rw [← integral_sub hx (htheta.mono_set Set.Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    exact (mul_sub _ _ _).symm
  rw [he,hs]
  linarith only [hip,hid]

/-- The actual Chebyshev discrepancy integral is integrable under the
same derivative hypothesis as the finite Abel formula. -/
theorem integrable_prime_error (f : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hi : IntegrableOn (deriv f) (Set.Icc a b)) :
    IntegrableOn (fun x => deriv f x*(x-Chebyshev.theta x)) (Set.Ioc a b) := by
  have ht := integrableOn_mul_sum_Icc primeCoefficient (m := 0) ha hi
  simp_rw [primeCoefficient_sum] at ht
  have hx := hi.mul_continuousOn continuous_id.continuousOn isCompact_Icc
  have he : (fun x => deriv f x*(x-Chebyshev.theta x)) =
      (fun x => deriv f x*id x)-(fun x => deriv f x*Chebyshev.theta x) := by
    funext x
    simp only [Pi.sub_apply,id_eq,mul_sub]
  rw [he]
  exact (hx.sub ht).mono_set Set.Ioc_subset_Icc_self

private theorem inverse_integral {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Ioc (Real.exp a) (Real.exp b), x⁻¹) = b-a := by
  rw [← intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hab),
    integral_inv_of_pos (Real.exp_pos _) (Real.exp_pos _),
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp,Real.log_exp]

/-- A finite signed prime sum pays an explicit inverse-square logarithmic
Chebyshev error. The smooth signed moment is retained and both endpoint
errors are paid. The hypotheses concern only the differentiable test kernel. -/
theorem prime_error_bound (f : ℝ → ℝ) {a b W D : ℝ}
    (ha : 5000 ≤ a) (hab : a ≤ b) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hd : ∀ x ∈ Set.Icc (Real.exp a) (Real.exp b), DifferentiableAt ℝ f x)
    (hi : IntegrableOn (deriv f) (Set.Icc (Real.exp a) (Real.exp b)))
    (hf : ∀ x ∈ Set.Icc (Real.exp a) (Real.exp b), |f x| ≤ W/(x*Real.log x))
    (hf' : ∀ x ∈ Set.Icc (Real.exp a) (Real.exp b),
      |deriv f x| ≤ D/(x^2*Real.log x)) :
    |(∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
        f p*Real.log p)-(∫ x in Set.Ioc (Real.exp a) (Real.exp b), f x)| ≤
      (41/100 : ℝ)*(2*W+D*(b-a))/a^2 := by
  have ha0 : 0 < a := by linarith
  have hab' := Real.exp_le_exp.mpr hab
  have hxpos x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : 0 < x :=
    (Real.exp_pos a).trans_le hx.1
  have hlog x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : a ≤ Real.log x :=
    (Real.le_log_iff_exp_le (hxpos x hx)).mpr hx.1
  have htheta x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |Chebyshev.theta x-x| ≤ (41/100 : ℝ)*x/Real.log x := by
    have h := RosserSchoenfeldLargeChebyshev.abs_theta_sub_exp_le (ha.trans (hlog x hx))
    rwa [Real.exp_log (hxpos x hx)] at h
  have hend x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |f x*(Chebyshev.theta x-x)| ≤ (41/100 : ℝ)*W/a^2 := by
    have hx0 := hxpos x hx
    have hl0 := ha0.trans_le (hlog x hx)
    rw [abs_mul]
    calc
      _ ≤ (W/(x*Real.log x))*((41/100 : ℝ)*x/Real.log x) :=
        mul_le_mul (hf x hx) (htheta x hx) (abs_nonneg _) (by positivity)
      _ = (41/100 : ℝ)*W/(Real.log x)^2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ ha0.le (hlog x hx) 2)
  have hint x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |deriv f x*(x-Chebyshev.theta x)| ≤ ((41/100 : ℝ)*D/a^2)*x⁻¹ := by
    have hx0 := hxpos x hx
    have hl0 := ha0.trans_le (hlog x hx)
    rw [abs_mul,abs_sub_comm x]
    calc
      _ ≤ (D/(x^2*Real.log x))*((41/100 : ℝ)*x/Real.log x) :=
        mul_le_mul (hf' x hx) (htheta x hx) (abs_nonneg _) (by positivity)
      _ = ((41/100 : ℝ)*D/(Real.log x)^2)*x⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ ha0.le (hlog x hx) 2)) (inv_nonneg.mpr hx0.le)
  have hcont : ContinuousOn (fun x : ℝ => ((41/100 : ℝ)*D/a^2)*x⁻¹)
      (Set.Icc (Real.exp a) (Real.exp b)) :=
    continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => (hxpos x hx).ne'))
  have hierr := integrable_prime_error f (Real.exp_pos a).le hi
  have hibound : IntegrableOn (fun x : ℝ => ((41/100 : ℝ)*D/a^2)*x⁻¹)
      (Set.Ioc (Real.exp a) (Real.exp b)) :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hib : |∫ x in Set.Ioc (Real.exp a) (Real.exp b), deriv f x*(x-Chebyshev.theta x)| ≤
      (41/100 : ℝ)*D/a^2*(b-a) := by
    calc
      _ ≤ ∫ x in Set.Ioc (Real.exp a) (Real.exp b), |deriv f x*(x-Chebyshev.theta x)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (Real.exp a) (Real.exp b), ((41/100 : ℝ)*D/a^2)*x⁻¹ :=
        setIntegral_mono_on hierr.abs hibound measurableSet_Ioc
          (fun x hx => hint x (Set.Ioc_subset_Icc_self hx))
      _ = _ := by rw [integral_const_mul,inverse_integral hab]
  rw [prime_abel f (Real.exp_pos a).le hab' hd hi]
  calc
    _ ≤ |f (Real.exp b)*(Chebyshev.theta (Real.exp b)-Real.exp b)|+
        |f (Real.exp a)*(Chebyshev.theta (Real.exp a)-Real.exp a)|+
        |∫ x in Set.Ioc (Real.exp a) (Real.exp b), deriv f x*(x-Chebyshev.theta x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (41/100 : ℝ)*W/a^2+(41/100 : ℝ)*W/a^2+(41/100 : ℝ)*D/a^2*(b-a) :=
      add_le_add (add_le_add (hend _ ⟨hab',le_rfl⟩) (hend _ ⟨le_rfl,hab'⟩)) hib
    _ = _ := by ring

/-- Differentiate the literal prime test kernel, including its reciprocal
prime and reciprocal logarithm. -/
theorem profile_deriv (F G : ℝ → ℝ) (c : ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => F (Real.log x+c)/(x*Real.log x))
      ((G (Real.log x+c)-F (Real.log x+c)*(1+(Real.log x)⁻¹))/(x^2*Real.log x)) x := by
  have hx0 : 0 < x := by linarith
  have hl0 := Real.log_pos hx
  have h := ((hF (Real.log x+c)).comp x ((Real.hasDerivAt_log hx0.ne').add_const c)).div
    ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')) (by positivity : x*Real.log x ≠ 0)
  apply h.congr_deriv
  simp only [Pi.mul_apply,Function.comp_apply,id_eq,one_mul]
  field_simp

/-- The common signed profile over a total-log interval is independent of
the cofactor shift `c`. All prime irregularity and reciprocal-log variation
cost an explicit extra inverse power of the lowest prime logarithm. -/
theorem signed_profile_bound (F G : ℝ → ℝ) (c : ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t) (hG : Continuous G)
    {a b W V : ℝ} (ha : 5000 ≤ a) (hab : a ≤ b) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hFW : ∀ t ∈ Set.Icc (a+c) (b+c), |F t| ≤ W)
    (hGV : ∀ t ∈ Set.Icc (a+c) (b+c), |G t| ≤ V) :
    |(∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
        F (Real.log p+c)/(p : ℝ))-(∫ t in a+c..b+c, F t)/a| ≤
      (W*(b-a)^2+(41/100 : ℝ)*(2*W+(V+2*W)*(b-a)))/a^2 := by
  have ha0 : 0 < a := by linarith
  have heab := Real.exp_le_exp.mpr hab
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hF x).continuousAt)
  let f : ℝ → ℝ := fun x => F (Real.log x+c)/(x*Real.log x)
  let f' : ℝ → ℝ := fun x =>
    (G (Real.log x+c)-F (Real.log x+c)*(1+(Real.log x)⁻¹))/(x^2*Real.log x)
  have hxp x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : 0 < x :=
    (Real.exp_pos a).trans_le hx.1
  have hxl x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      a ≤ Real.log x ∧ Real.log x ≤ b := by
    exact ⟨(Real.le_log_iff_exp_le (hxp x hx)).mpr hx.1,
      (Real.log_le_iff_le_exp (hxp x hx)).mpr hx.2⟩
  have hx1 x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : 1 < x :=
    Real.one_lt_exp_iff.mpr ha0 |>.trans_le hx.1
  have hlogc : ContinuousOn (fun x : ℝ => Real.log x+c)
      (Set.Icc (Real.exp a) (Real.exp b)) :=
    (continuousOn_id.log (fun x hx => (hxp x hx).ne')).add continuousOn_const
  have hlf x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : Real.log x ≠ 0 :=
    (ha0.trans_le (hxl x hx).1).ne'
  have hf' x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : HasDerivAt f (f' x) x :=
    profile_deriv F G c hF (hx1 x hx)
  have hfcont : ContinuousOn f (Set.Icc (Real.exp a) (Real.exp b)) :=
    fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f' (Set.Icc (Real.exp a) (Real.exp b)) := by
    dsimp only [f']
    apply ContinuousOn.div
    · exact (hG.comp_continuousOn hlogc).sub
        ((hFc.comp_continuousOn hlogc).mul (continuousOn_const.add
          ((continuousOn_id.log (fun x hx => (hxp x hx).ne')).inv₀ hlf)))
    · exact (continuousOn_id.pow 2).mul (continuousOn_id.log (fun x hx => (hxp x hx).ne'))
    · intro x hx
      exact mul_ne_zero (pow_ne_zero _ (hxp x hx).ne') (hlf x hx)
  have hfi : IntegrableOn (deriv f) (Set.Icc (Real.exp a) (Real.exp b)) :=
    hfc.integrableOn_Icc.congr_fun (fun x hx => (hf' x hx).deriv.symm) measurableSet_Icc
  have hfW x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : |f x| ≤ W/(x*Real.log x) := by
    dsimp only [f]
    rw [abs_div,abs_of_pos (mul_pos (hxp x hx) (ha0.trans_le (hxl x hx).1))]
    exact div_le_div_of_nonneg_right (hFW _ ⟨by linarith [(hxl x hx).1],by linarith [(hxl x hx).2]⟩)
      (mul_nonneg (hxp x hx).le (ha0.trans_le (hxl x hx).1).le)
  have hfV x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |deriv f x| ≤ (V+2*W)/(x^2*Real.log x) := by
    have hlog := hxl x hx
    have hx0 := hxp x hx
    have hl0 := ha0.trans_le hlog.1
    have harg : Real.log x+c ∈ Set.Icc (a+c) (b+c) :=
      ⟨by linarith [hlog.1],by linarith [hlog.2]⟩
    have hli : (Real.log x)⁻¹ ≤ 1 := (inv_le_one₀ hl0).mpr (by linarith)
    rw [(hf' x hx).deriv]
    dsimp only [f']
    rw [abs_div,abs_of_pos (mul_pos (sq_pos_of_pos hx0) hl0)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ |G (Real.log x+c)|+|F (Real.log x+c)*(1+(Real.log x)⁻¹)| := abs_sub _ _
      _ ≤ V+W*2 := by
        apply add_le_add (hGV _ harg)
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1+(Real.log x)⁻¹)]
        exact mul_le_mul (hFW _ harg) (by linarith) (by positivity) hW
      _ = _ := by ring
  have hp := prime_error_bound f ha hab hW (by positivity : 0 ≤ V+2*W)
    (fun x hx => (hf' x hx).differentiableAt) hfi hfW hfV
  have hpe : (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
      f p*Real.log p) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
        F (Real.log p+c)/(p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne'
    dsimp only [f]
    field_simp
  rw [hpe] at hp
  have hmain : (∫ x in Set.Ioc (Real.exp a) (Real.exp b), F (Real.log x+c)*x⁻¹) =
      ∫ t in a+c..b+c, F t := by
    have hh := intervalIntegral.integral_comp_mul_deriv
      (a := Real.exp a) (b := Real.exp b) (f := fun x => Real.log x+c)
      (f' := fun x => x⁻¹) (g := F)
      (fun x hx => (Real.hasDerivAt_log (hxp x (by simpa only [Set.uIcc_of_le heab] using hx)).ne').add_const c)
      (by
        rw [Set.uIcc_of_le heab]
        exact continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')) hFc
    simpa only [intervalIntegral.integral_of_le heab,Real.log_exp,Function.comp_apply] using hh
  have hmainc : ContinuousOn (fun x => F (Real.log x+c)*x⁻¹)
      (Set.Icc (Real.exp a) (Real.exp b)) :=
    (hFc.comp_continuousOn hlogc).mul (continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne'))
  have hfdiffc : ContinuousOn (fun x => f x-F (Real.log x+c)*x⁻¹/a)
      (Set.Icc (Real.exp a) (Real.exp b)) :=
    hfcont.sub (hmainc.div_const a)
  have hdiff x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |f x-F (Real.log x+c)*x⁻¹/a| ≤ (W*(b-a)/a^2)*x⁻¹ := by
    have hx0 := hxp x hx
    have hl := hxl x hx
    have hl0 := ha0.trans_le hl.1
    have harg : Real.log x+c ∈ Set.Icc (a+c) (b+c) :=
      ⟨by linarith [hl.1],by linarith [hl.2]⟩
    have hal : (Real.log x-a)/(a*Real.log x) ≤ (b-a)/a^2 := by
      apply (div_le_div_of_nonneg_left (by linarith : 0 ≤ Real.log x-a)
        (by positivity : 0 < a^2) (by nlinarith)).trans
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg a)
    have he : f x-F (Real.log x+c)*x⁻¹/a =
        -(F (Real.log x+c)*((Real.log x-a)/(a*Real.log x)))*x⁻¹ := by
      dsimp only [f]
      field_simp
      ring
    rw [he,abs_mul,abs_neg,abs_mul,abs_of_nonneg (by positivity : 0 ≤ x⁻¹),
      abs_of_nonneg (show 0 ≤ (Real.log x-a)/(a*Real.log x) from
        div_nonneg (by linarith [hl.1]) (by positivity))]
    calc
      _ ≤ W*((b-a)/a^2)*x⁻¹ := mul_le_mul_of_nonneg_right
        (mul_le_mul (hFW _ harg) hal
          (div_nonneg (by linarith [hl.1]) (by positivity)) hW) (by positivity)
      _ = _ := by ring
  have hib : |(∫ x in Set.Ioc (Real.exp a) (Real.exp b), f x)-
      (∫ t in a+c..b+c, F t)/a| ≤ W*(b-a)^2/a^2 := by
    rw [← hmain,← integral_div,← integral_sub
      (hfcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      ((hmainc.div_const a).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)]
    calc
      _ ≤ ∫ x in Set.Ioc (Real.exp a) (Real.exp b), |f x-F (Real.log x+c)*x⁻¹/a| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (Real.exp a) (Real.exp b), (W*(b-a)/a^2)*x⁻¹ :=
        setIntegral_mono_on
          (hfdiffc.abs.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
          ((continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne'))).integrableOn_Icc.mono_set
            Set.Ioc_subset_Icc_self) measurableSet_Ioc
          (fun x hx => hdiff x (Set.Ioc_subset_Icc_self hx))
      _ = _ := by rw [integral_const_mul,inverse_integral hab]; ring
  exact (abs_sub_le _ _ _).trans ((add_le_add hp hib).trans_eq (by ring))

/-- Explicit signed cosine moment on any finite prime-log interval.
The endpoint sine difference is retained instead of silently completing a
clipped period. -/
theorem cosine_interval_error {a b y : ℝ} (ha : 5000 ≤ a) (hab : a ≤ b)
    (hy : y ≠ 0) (c : ℝ) :
    |(∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
        Real.cos (y*(Real.log p+c))/(p : ℝ))-
      (Real.sin (y*(b+c))-Real.sin (y*(a+c)))/(y*a)| ≤
      ((b-a)^2+(41/100 : ℝ)*(2+(|y|+2)*(b-a)))/a^2 := by
  have h := signed_profile_bound (fun t => Real.cos (y*t)) (fun t => -y*Real.sin (y*t)) c
    (by
      intro t
      simpa only [id_eq,mul_one,neg_mul,mul_neg,mul_comm] using ((hasDerivAt_id t).const_mul y).cos)
    (by fun_prop) ha hab (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)
    (fun t _ => Real.abs_cos_le_one (y*t)) (by
      intro t _
      rw [abs_mul,abs_neg]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (y*t)) (abs_nonneg y)).trans_eq (mul_one _))
  rw [intervalIntegral.integral_comp_mul_left _ hy,integral_cos] at h
  simpa only [smul_eq_mul,one_mul,mul_one,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using h

/-- All full prime periods have a numerical inverse-square logarithmic
cost, uniformly in their cofactor shift and radial position. This is an
actual finite prime sum, with no unproved counting hypothesis. -/
theorem cosine_period_bound {a y : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|) (c : ℝ) :
    |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
      Real.cos (y*(Real.log p+c))/(p : ℝ)| ≤ 4/a^2 := by
  have hy0 : 0 < |y| := by linarith
  have hyne := abs_pos.mp hy0
  let h := 2*Real.pi/|y|
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhup : h ≤ 1/8 := by
    dsimp only [h]
    apply (div_le_iff₀ hy0).mpr
    nlinarith [Real.pi_lt_d4]
  have hyh : |y| * h = 2*Real.pi := by dsimp only [h]; field_simp
  have hsin : Real.sin (y*(a+h+c)) = Real.sin (y*(a+c)) := by
    rcases lt_or_gt_of_ne hyne with hyn | hyp
    · have he : y*(a+h+c) = y*(a+c)-2*Real.pi := by
        rw [abs_of_neg hyn] at hyh
        nlinarith only [hyh]
      rw [he,Real.sin_sub_two_pi]
    · have he : y*(a+h+c) = y*(a+c)+2*Real.pi := by
        rw [abs_of_pos hyp] at hyh
        nlinarith only [hyh]
      rw [he,Real.sin_add_two_pi]
  have hb := cosine_interval_error ha (show a ≤ a+h by linarith) hyne c
  rw [hsin,sub_self,zero_div,sub_zero,add_sub_cancel_left] at hb
  have hcost : h^2+(41/100 : ℝ)*(2+(|y|+2)*h) ≤ 4 := by
    have hh2 : h^2 ≤ (1/8 : ℝ)^2 := pow_le_pow_left₀ hh.le hhup 2
    nlinarith [Real.pi_lt_d4]
  exact hb.trans (div_le_div_of_nonneg_right hcost (sq_nonneg a))

/-- The first signed moment of a complete period centered at a cosine
extremum also has an inverse-square prime-log bound. Thus the affine
cutoff term does not pay the unsigned first moment. -/
theorem cosine_first_period_bound {a y : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (c : ℝ) (hphase : Real.sin (y*(a+Real.pi/|y|+c)) = 0) :
    |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
      ((Real.log p-a-Real.pi/|y|)*Real.cos (y*(Real.log p+c)))/(p : ℝ)| ≤ 1/a^2 := by
  have hy0 : 0 < |y| := by linarith
  have hyne := abs_pos.mp hy0
  let h := Real.pi/|y|
  let v := a+h+c
  let F : ℝ → ℝ := fun t => (t-v)*Real.cos (y*t)
  let G : ℝ → ℝ := fun t => Real.cos (y*t)-y*(t-v)*Real.sin (y*t)
  let Q : ℝ → ℝ := fun t => (t-v)*Real.sin (y*t)/y+Real.cos (y*t)/y^2
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhu : h ≤ 1/16 := by
    dsimp only [h]
    apply (div_le_iff₀ hy0).mpr
    nlinarith [Real.pi_lt_d4]
  have hyh : |y| * h = Real.pi := by dsimp only [h]; field_simp
  have hFd t : HasDerivAt F (G t) t := by
    have hd := ((hasDerivAt_id t).sub_const v).mul (((hasDerivAt_id t).const_mul y).cos)
    apply hd.congr_deriv
    simp only [id_eq,one_mul,mul_one,G]
    ring
  have hQd t : HasDerivAt Q (F t) t := by
    have hd := ((((hasDerivAt_id t).sub_const v).mul
      (((hasDerivAt_id t).const_mul y).sin)).div_const y).add
        ((((hasDerivAt_id t).const_mul y).cos).div_const (y^2))
    apply hd.congr_deriv
    simp only [id_eq,one_mul,mul_one,F]
    field_simp
    ring
  have hendpoint : Q (a+2*h+c) = Q (a+c) := by
    have hs : Real.sin (y*v) = 0 := hphase
    have ha' : a+c = v-h := by dsimp only [v]; ring
    have hb' : a+2*h+c = v+h := by dsimp only [v]; ring
    rw [ha',hb']
    rcases lt_or_gt_of_ne hyne with hyn | hyp
    · have hyh' : y*h = -Real.pi := by rw [abs_of_neg hyn] at hyh; linarith
      have hm : y*(v-h) = y*v+Real.pi := by nlinarith only [hyh']
      have hp : y*(v+h) = y*v-Real.pi := by nlinarith only [hyh']
      simp only [Q,hp,hm,Real.sin_sub_pi,Real.sin_add_pi,Real.cos_sub_pi,Real.cos_add_pi,hs,
        neg_zero,mul_zero,zero_div,zero_add]
    · have hyh' : y*h = Real.pi := by rwa [abs_of_pos hyp] at hyh
      have hm : y*(v-h) = y*v-Real.pi := by nlinarith only [hyh']
      have hp : y*(v+h) = y*v+Real.pi := by nlinarith only [hyh']
      simp only [Q,hp,hm,Real.sin_sub_pi,Real.sin_add_pi,Real.cos_sub_pi,Real.cos_add_pi,hs,
        neg_zero,mul_zero,zero_div,zero_add]
  have hi : (∫ t in a+c..a+2*h+c, F t) = 0 := by
    have hc : Continuous F := by dsimp [F]; fun_prop
    have hfi : IntervalIntegrable F volume (a+c) (a+2*h+c) := hc.intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQd t) hfi,hendpoint,sub_self]
  have hdist t (ht : t ∈ Set.Icc (a+c) (a+2*h+c)) : |t-v| ≤ h := by
    dsimp only [v]
    exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hb := signed_profile_bound F G c hFd (by dsimp [G]; fun_prop) ha
    (show a ≤ a+2*h by linarith) hh.le (by positivity : 0 ≤ 1+|y| * h)
    (by
      intro t ht
      dsimp only [F]
      rw [abs_mul]
      exact (mul_le_mul (hdist t ht) (Real.abs_cos_le_one _) (abs_nonneg _) hh.le).trans_eq (mul_one _))
    (by
      intro t ht
      dsimp only [G]
      apply (abs_sub _ _).trans
      apply add_le_add (Real.abs_cos_le_one _)
      rw [abs_mul,abs_mul]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hdist t ht) (abs_nonneg y))
        (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)).trans_eq (mul_one _))
  rw [hi,zero_div,sub_zero,add_sub_cancel_left] at hb
  have hcost : h*(2*h)^2+(41/100 : ℝ)*(2*h+(1+|y| * h+2*h)*(2*h)) ≤ 1 := by
    rw [hyh]
    have hs : h^2 ≤ (1/16 : ℝ)^2 := pow_le_pow_left₀ hh.le hhu 2
    have hc : h^3 ≤ (1/16 : ℝ)^3 := pow_le_pow_left₀ hh.le hhu 3
    nlinarith [Real.pi_lt_d4,mul_le_mul_of_nonneg_right Real.pi_lt_d4.le hh.le]
  have he : (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*h)⌋₊).filter Nat.Prime,
      F (Real.log p+c)/(p : ℝ)) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
        ((Real.log p-a-Real.pi/|y|)*Real.cos (y*(Real.log p+c)))/(p : ℝ) := by
    have hh' : 2*h = 2*Real.pi/|y| := by dsimp only [h]; ring
    rw [hh']
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [F,v,h]
    ring
  rw [he] at hb
  exact hb.trans (div_le_div_of_nonneg_right hcost (sq_nonneg a))

/-- The inverse-square prime-log cost can be summed over EVERY cofactor
prime count using actual incidence counting. Ownership and squarefreeness
are sufficient; no fixed-count decomposition is introduced. -/
theorem owner_reciprocal_square_sum {M : ℕ} (hM : 2 ≤ M) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc M (2*M)) (hSF : ∀ n ∈ S, Squarefree n)
    (w a : ℕ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ n ∈ S, |w n| ≤ W/n)
    (howner : ∀ n ∈ S, ∀ p ∈ n.primeFactors, Real.log p ≤ a n) :
    (∑ n ∈ S, |w n|/(a n)^2) ≤
      2*W*(ZetaRieszOwnerCountEnergy.primeHarmonic (2*M)^2+
        ZetaRieszOwnerCountEnergy.primeHarmonic (2*M))/(Real.log M)^2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlocal n (hn : n ∈ S) :
      |w n|/(a n)^2 ≤ (W/((M : ℝ)*(Real.log M)^2))*(n.primeFactors.card : ℝ)^2 := by
    have hns := Finset.mem_Ioc.mp (hS hn)
    have hn1 : 1 < n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnl : Real.log M ≤ Real.log n := Real.log_le_log hM0 (by exact_mod_cast hns.1.le)
    have hln0 := hlogM.trans_le hnl
    have ho := ZetaRieszOwnerCountEnergy.owner_mean_log_le hn1 (hSF n hn) (howner n hn)
    have hsq : (Real.log n/(n.primeFactors.card : ℝ))^2 ≤ (a n)^2 :=
      pow_le_pow_left₀ ho.1.le ho.2 2
    calc
      _ ≤ |w n|/(Real.log n/(n.primeFactors.card : ℝ))^2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ho.1) hsq
      _ = (|w n|/(Real.log n)^2)*(n.primeFactors.card : ℝ)^2 := by
        rw [div_pow,div_div_eq_mul_div]
        ring
      _ ≤ (W/((M : ℝ)*(Real.log M)^2))*(n.primeFactors.card : ℝ)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          _ ≤ (W/n)/(Real.log n)^2 :=
            div_le_div_of_nonneg_right (hw n hn) (sq_nonneg _)
          _ = W/((n : ℝ)*(Real.log n)^2) := by ring
          _ ≤ _ := div_le_div_of_nonneg_left hW (by positivity)
            (mul_le_mul (by exact_mod_cast hns.1.le)
              (pow_le_pow_left₀ hlogM.le hnl 2) (sq_nonneg _) hn0.le)
  have hsub : S ⊆ Finset.Icc 1 (2*M) := by
    intro n hn
    have hs := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega,hs.2⟩
  have hcount := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => sq_nonneg (n.primeFactors.card : ℝ))).trans
      (ZetaRieszOwnerCountEnergy.prime_count_second_moment (2*M))
  calc
    _ ≤ ∑ n ∈ S, (W/((M : ℝ)*(Real.log M)^2))*(n.primeFactors.card : ℝ)^2 :=
      Finset.sum_le_sum hlocal
    _ = (W/((M : ℝ)*(Real.log M)^2))*(∑ n ∈ S, (n.primeFactors.card : ℝ)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (W/((M : ℝ)*(Real.log M)^2))*((2*M : ℕ)*
        (ZetaRieszOwnerCountEnergy.primeHarmonic (2*M)^2+
          ZetaRieszOwnerCountEnergy.primeHarmonic (2*M))) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by push_cast; field_simp

/-- Joint actual-prime cancellation over an arbitrary squarefree cofactor
shell. The cofactor phase, arbitrary signed cofactor weights and moving
complete prime periods are retained. This does not permit deleting primes
inside a period or freezing a prime-dependent amplitude. -/
theorem all_count_period_bound {M : ℕ} (hM : 2 ≤ M) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc M (2*M)) (hSF : ∀ n ∈ S, Squarefree n)
    (w a : ℕ → ℝ) {W y : ℝ} (hW : 0 ≤ W) (hy : 54 ≤ |y|)
    (hw : ∀ n ∈ S, |w n| ≤ W/n) (ha : ∀ n ∈ S, 5000 ≤ a n)
    (howner : ∀ n ∈ S, ∀ p ∈ n.primeFactors, Real.log p ≤ a n) :
    |∑ n ∈ S, w n*(∑ p ∈
        (Finset.Ioc ⌊Real.exp (a n)⌋₊ ⌊Real.exp (a n+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
          Real.cos (y*(Real.log p+Real.log n))/(p : ℝ))| ≤
      8*W*(ZetaRieszOwnerCountEnergy.primeHarmonic (2*M)^2+
        ZetaRieszOwnerCountEnergy.primeHarmonic (2*M))/(Real.log M)^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ S, 4*(|w n|/(a n)^2) := Finset.sum_le_sum (by
      intro n hn
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left (cosine_period_bound (ha n hn) hy (Real.log n)) (abs_nonneg (w n))
      exact h.trans_eq (by ring))
    _ = 4*(∑ n ∈ S, |w n|/(a n)^2) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (owner_reciprocal_square_sum hM S hS hSF w a hW hw howner) (by norm_num : (0 : ℝ) ≤ 4)
      exact h.trans_eq (by ring)

/-- The joint bound is stable under arbitrary finite radial aggregation.
Only the sum of the actual amplitude budgets appears, rather than a
worst amplitude multiplied by the number of periods or prime counts. -/
theorem radial_all_count_period_bound {ι : Type*} (B : Finset ι) {M : ℕ} (hM : 2 ≤ M)
    (S : ι → Finset ℕ) (w a : ι → ℕ → ℝ) (W : ι → ℝ) {y : ℝ} (hy : 54 ≤ |y|)
    (hS : ∀ j ∈ B, S j ⊆ Finset.Ioc M (2*M))
    (hSF : ∀ j ∈ B, ∀ n ∈ S j, Squarefree n) (hW : ∀ j ∈ B, 0 ≤ W j)
    (hw : ∀ j ∈ B, ∀ n ∈ S j, |w j n| ≤ W j/n)
    (ha : ∀ j ∈ B, ∀ n ∈ S j, 5000 ≤ a j n)
    (howner : ∀ j ∈ B, ∀ n ∈ S j, ∀ p ∈ n.primeFactors, Real.log p ≤ a j n) :
    |∑ j ∈ B, ∑ n ∈ S j, w j n*(∑ p ∈
        (Finset.Ioc ⌊Real.exp (a j n)⌋₊ ⌊Real.exp (a j n+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
          Real.cos (y*(Real.log p+Real.log n))/(p : ℝ))| ≤
      8*(∑ j ∈ B, W j)*(ZetaRieszOwnerCountEnergy.primeHarmonic (2*M)^2+
        ZetaRieszOwnerCountEnergy.primeHarmonic (2*M))/(Real.log M)^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ B, 8*W j*(ZetaRieszOwnerCountEnergy.primeHarmonic (2*M)^2+
        ZetaRieszOwnerCountEnergy.primeHarmonic (2*M))/(Real.log M)^2 :=
      Finset.sum_le_sum (fun j hj => all_count_period_bound hM (S j) (hS j hj) (hSF j hj)
        (w j) (a j) (hW j hj) hy (hw j hj) (ha j hj) (howner j hj))
    _ = _ := by rw [← Finset.sum_div,← Finset.sum_mul,← Finset.mul_sum]

end RiemannGaussian.ZetaRieszQuantitativePrimePeriod
