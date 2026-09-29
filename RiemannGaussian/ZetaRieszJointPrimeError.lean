/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszQuantitativePrimePeriod
import RiemannGaussian.ZetaRieszWeightedPrimeTail
import RiemannGaussian.ZetaRieszRetainedFactorial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Sharper arithmetic errors for joined signed prime intervals

The existing complete smoothed prime formula has a stronger decay rate than
the logarithmic estimate previously used period by period. Desmoothing it
at a smaller step pays a second inverse logarithm in the actual Chebyshev
error. Joined intervals retain their common signed smooth term and pay only
their exterior endpoints. The starting point is proved but unevaluated.
-/

noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators
namespace RiemannGaussian.ZetaRieszJointPrimeError

private theorem exponential_budget_eventually :
    ∀ᶠ r : ℝ in atTop,
      (463/10000 : ℝ)*exp (-(4/15)*r)+(8+(3/4)*r)*exp (-(3/8)*r)+exp (-r^2) ≤
        1/r^12 := by
  have hlim (n : ℕ) (c : ℝ) (hc : 0 < c) :
      Tendsto (fun r : ℝ => r^n*exp (-c*r)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) c hc
  have hh := (((hlim 12 (4/15) (by norm_num)).const_mul (463/10000)).add
    (((hlim 12 (3/8) (by norm_num)).const_mul 8).add
      ((hlim 13 (3/8) (by norm_num)).const_mul (3/4)))).add
        (hlim 12 1 (by norm_num))
  norm_num only [mul_zero,add_zero] at hh
  filter_upwards [hh.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hs : exp (-r^2) ≤ exp (-r) := exp_le_exp.mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith : 0 ≤ r) 12)
  apply (le_div_iff₀ (show 0 < r^12 by positivity)).mpr
  simp only [neg_mul,one_mul] at hr hm ⊢
  nlinarith only [hr,hm]

/-- The complete arithmetic smoothed prime error has six inverse powers
of logarithmic time eventually. No unproved prime-error premise is used. -/
theorem eventually_smoothed_error :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |RosserSchoenfeldPrimePrimitive.value t-
        (exp t-1-log (2*Real.pi)*t)| ≤ exp t/t^6 := by
  obtain ⟨r₀,hr₀⟩ := eventually_atTop.mp exponential_budget_eventually
  let r₁ := max 70 r₀
  refine ⟨max 5000 (r₁^2),le_max_left _ _,fun t ht => ?_⟩
  have ht5000 : 5000 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  let r := sqrt t
  have hr0 : 0 < r := sqrt_pos.mpr ht0
  have hr2 : r^2 = t := sq_sqrt ht0.le
  have hr1 : r₁ ≤ r := by
    have hsq : r₁^2 ≤ r^2 := by rw [hr2]; exact (le_max_right _ _).trans ht
    exact (sq_le_sq₀ (le_trans (by norm_num) (le_max_left 70 r₀)) hr0.le).mp hsq
  have hr : 70 ≤ r := (le_max_left _ _).trans hr1
  have hbudget := hr₀ r ((le_max_right _ _).trans hr1)
  let H := exp ((3/8)*r)
  have hH : 2 ≤ H := RosserSchoenfeldSmoothingBudget.cutoff_ge_two hr
  have hmargin := RosserSchoenfeldSmoothingBudget.cutoff_margin hr
  change (4/15)/r ≤ zetaSignedPoleZeroMargin H at hmargin
  have hproduct : (4/15)*r ≤ zetaSignedPoleZeroMargin H*t := by
    have hh := mul_le_mul_of_nonneg_right hmargin ht0.le
    have he : ((4/15 : ℝ)/r)*t = (4/15)*r := by rw [← hr2]; field_simp
    rwa [he] at hh
  have he : exp ((1-zetaSignedPoleZeroMargin H)*t) ≤ exp t*exp (-(4/15)*r) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith)
  have htail : (8+2*log H)/H = (8+(3/4)*r)*exp (-(3/8)*r) := by
    dsimp [H]
    rw [log_exp,neg_mul,exp_neg,div_eq_mul_inv]
    ring
  have hconst : (463/10000 : ℝ)+Real.pi^2/24 ≤ 1 := by
    have hp0 := pi_pos
    have hp := pi_lt_four
    nlinarith
  have hexp : exp t*exp (-r^2) = 1 := by rw [hr2,← exp_add,add_neg_cancel,exp_zero]
  have hb := RosserSchoenfeldSmoothedError.norm_prime_sub_main_lt hH ht0.le
  have hb' : |RosserSchoenfeldPrimePrimitive.value t-(exp t-1-log (2*Real.pi)*t)| <
      (463/10000 : ℝ)*(exp ((1-zetaSignedPoleZeroMargin H)*t)+1)+
        exp t*((8+2*log H)/H)+Real.pi^2/24 := by
    simpa only [RosserSchoenfeldExplicitFormula.mainTerm_eq,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs] using hb
  apply hb'.le.trans
  calc
    _ ≤ exp t*((463/10000 : ℝ)*exp (-(4/15)*r)+
        (8+(3/4)*r)*exp (-(3/8)*r)+exp (-r^2)) := by
      rw [htail]
      have hh : exp t*((463/10000 : ℝ)*exp (-(4/15)*r)+
          (8+(3/4)*r)*exp (-(3/8)*r)+exp (-r^2)) =
          (463/10000 : ℝ)*(exp t*exp (-(4/15)*r))+
            exp t*((8+(3/4)*r)*exp (-(3/8)*r))+1 := by
        rw [mul_add,hexp]
        ring
      rw [hh]
      linarith
    _ ≤ exp t*(1/r^12) := mul_le_mul_of_nonneg_left hbudget (exp_nonneg t)
    _ = _ := by rw [show r^12 = t^6 by rw [← hr2,← pow_mul]]; ring

private theorem shifted_error {T t : ℝ} (hT : 5000 ≤ T) (ht : 2*T ≤ t)
    (herror : ∀ x : ℝ, T ≤ x →
      |RosserSchoenfeldPrimePrimitive.value x-(exp x-1-log (2*Real.pi)*x)| ≤ exp x/x^6)
    {x : ℝ} (hx : t-1/t^2 ≤ x ∧ x ≤ t+1/t^2) :
    |RosserSchoenfeldPrimePrimitive.value x-(exp x-1-log (2*Real.pi)*x)| ≤
      exp t/t^4 := by
  have ht0 : 0 < t := by linarith
  have hh0 : 0 < 1/t^2 := by positivity
  have hh : 1/t^2 ≤ 1/1000 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hxt : t/2 ≤ x := by linarith
  have hxT : T ≤ x := by
    by_cases h : T ≤ t-1/t^2
    · exact h.trans hx.1
    · have hTt : T ≤ t/2 := by linarith
      exact hTt.trans hxt
  have hex : exp x ≤ (101/100)*exp t := by
    calc
      _ ≤ exp (t+1/t^2) := exp_le_exp.mpr hx.2
      _ = exp t*exp (1/t^2) := exp_add _ _
      _ ≤ exp t*(101/100) := mul_le_mul_of_nonneg_left
        (RosserSchoenfeldChebyshevBudget.exp_small hh0.le hh) (exp_nonneg t)
      _ = _ := by ring
  have hp : (t/2)^6 ≤ x^6 := pow_le_pow_left₀ (by positivity) hxt 6
  apply (herror x hxT).trans
  apply (div_le_div_of_nonneg_right hex (pow_nonneg (by linarith : 0 ≤ x) 6)).trans
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  apply (div_le_div_iff₀ (by positivity : 0 < (t/2)^6) (by positivity)).mpr
  have ht2 : (101/100 : ℝ)*64 ≤ t^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ exp t*t^4 by positivity)
  nlinarith only [hm]

private theorem log_constant_le_square {t : ℝ} (ht : 5000 ≤ t) :
    log (2*Real.pi) ≤ exp t/t^2 := by
  have hc : log (2*Real.pi) ≤ 4 := by
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) pi_ne_zero]
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
      log_le_sub_one_of_pos pi_pos,pi_lt_four]
  apply hc.trans
  apply (le_div_iff₀ (show 0 < t^2 by positivity)).mpr
  have he := pow_div_factorial_le_exp t (by linarith : 0 ≤ t) 3
  norm_num [Nat.factorial] at he
  have hp := mul_le_mul_of_nonneg_right (show (24 : ℝ) ≤ t by linarith) (sq_nonneg t)
  nlinarith

/-- Desmoothing the stronger actual prime primitive gives two inverse
logarithms for psi. All moving endpoint errors are paid. -/
theorem eventually_psi_error :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |Chebyshev.psi (exp t)-exp t| ≤ 4*exp t/t^2 := by
  obtain ⟨T,hT,herror⟩ := eventually_smoothed_error
  refine ⟨2*T,by linarith,fun t ht => ?_⟩
  have ht5000 : 5000 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  let h := 1/t^2
  have hh0 : 0 < h := by dsimp [h]; positivity
  have hh : h ≤ 1/1000 := by
    dsimp [h]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have he0 := abs_le.mp (shifted_error hT ht herror (x := t) ⟨by linarith,by linarith⟩)
  have hep := abs_le.mp (shifted_error hT ht herror (x := t+h) ⟨by dsimp [h]; linarith,le_rfl⟩)
  have hem := abs_le.mp (shifted_error hT ht herror (x := t-h) ⟨le_rfl,by dsimp [h]; linarith⟩)
  have hc0 := RosserSchoenfeldChebyshevBudget.log_constant_nonneg
  have hc := log_constant_le_square ht5000
  have hup := RosserSchoenfeldDesmoothing.prime_increment_lower (a := t) (b := t+h) (by linarith)
  have hlo := RosserSchoenfeldDesmoothing.prime_increment_upper (a := t-h) (b := t) (by linarith)
  have heq : exp t/t^4 = exp t*h^2 := by dsimp [h]; field_simp
  have heq' : exp t/t^2 = exp t*h := by dsimp [h]; ring
  rw [heq] at he0 hep hem
  rw [heq'] at hc
  have ef := RosserSchoenfeldChebyshevBudget.exp_forward hh0.le hh
  have eb := RosserSchoenfeldChebyshevBudget.exp_backward hh0.le
  have ef' := mul_le_mul_of_nonneg_left ef (exp_nonneg t)
  have eb' := mul_le_mul_of_nonneg_left eb (exp_nonneg t)
  rw [exp_add] at hep
  rw [show exp (t-h) = exp t*exp (-h) by rw [exp_sub,exp_neg]; ring] at hem
  have hp : Chebyshev.psi (exp t)-exp t ≤ 4*exp t*h := by
    apply (mul_le_mul_iff_right₀ hh0).mp
    have hc0' := mul_nonneg hc0 hh0.le
    have hpos := mul_nonneg (exp_nonneg t) (sq_nonneg h)
    nlinarith only [hup,he0.1,hep.2,ef',hc0',hpos]
  have hm : -(4*exp t*h) ≤ Chebyshev.psi (exp t)-exp t := by
    apply (mul_le_mul_iff_right₀ hh0).mp
    have hc' := mul_le_mul_of_nonneg_right hc hh0.le
    nlinarith only [hlo,he0.1,hem.2,eb',hc']
  have hhabs := abs_le.mpr ⟨hm,hp⟩
  simpa only [h,one_div,div_eq_mul_inv,mul_assoc,one_mul] using hhabs

/-- The actual ordinary-prime Chebyshev error has a proved second inverse
logarithm eventually, after every proper prime power has been paid. -/
theorem eventually_theta_error :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |Chebyshev.theta (exp t)-exp t| ≤ 5*exp t/t^2 := by
  obtain ⟨T,hT,hpsi⟩ := eventually_psi_error
  refine ⟨T,hT,fun t ht => ?_⟩
  have ht5000 := hT.trans ht
  have ht0 : 0 < t := by linarith
  have hpower : 2*exp (t/2)*t ≤ exp t/t^2 := by
    have he := pow_div_factorial_le_exp (t/2) (by positivity : 0 ≤ t/2) 4
    norm_num [Nat.factorial] at he
    have hp := mul_le_mul_of_nonneg_right (show (768 : ℝ) ≤ t by linarith)
      (pow_nonneg ht0.le 3)
    have hh : 2*t^3 ≤ exp (t/2) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh (exp_nonneg (t/2))
    have hprod : exp (t/2)*exp (t/2) = exp t := by rw [← exp_add]; congr 1; ring
    rw [hprod] at hm
    apply (le_div_iff₀ (show 0 < t^2 by positivity)).mpr
    nlinarith only [hm]
  have hsqrt : sqrt (exp t) = exp (t/2) := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (exp_nonneg _)).mp
    rw [sq_sqrt (exp_nonneg _),pow_two,← exp_add]
    congr 1
    ring
  have hp := Chebyshev.psi_sub_theta_le (x := exp t) (one_le_exp_iff.mpr ht0.le)
  rw [hsqrt,log_exp] at hp
  have hp' : |Chebyshev.theta (exp t)-Chebyshev.psi (exp t)| ≤ exp t/t^2 := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    exact hp.trans hpower
  have hh := (abs_sub_le (Chebyshev.theta (exp t)) (Chebyshev.psi (exp t)) (exp t)).trans
    (add_le_add hp' (hpsi t ht))
  exact hh.trans_eq (by ring)

open ZetaRieszQuantitativePrimePeriod

private theorem inverse_integral {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Ioc (exp a) (exp b), x⁻¹) = b-a := by
  rw [← intervalIntegral.integral_of_le (exp_le_exp.mpr hab),
    integral_inv_of_pos (exp_pos _) (exp_pos _),
    log_div (exp_ne_zero _) (exp_ne_zero _),log_exp,log_exp]

private theorem prime_error_cube_of_theta (T : ℝ) (hT : 5000 ≤ T)
    (htheta : ∀ t : ℝ, T ≤ t → |Chebyshev.theta (exp t)-exp t| ≤ 5*exp t/t^2)
    (f : ℝ → ℝ) {a b W D : ℝ}
    (ha : T ≤ a) (hab : a ≤ b) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hd : ∀ x ∈ Set.Icc (Real.exp a) (Real.exp b), DifferentiableAt ℝ f x)
    (hi : IntegrableOn (deriv f) (Set.Icc (Real.exp a) (Real.exp b)))
    (hf : ∀ x ∈ Set.Icc (Real.exp a) (Real.exp b), |f x| ≤ W/(x*Real.log x))
    (hf' : ∀ x ∈ Set.Icc (Real.exp a) (Real.exp b),
      |deriv f x| ≤ D/(x^2*Real.log x)) :
    |(∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
        f p*Real.log p)-(∫ x in Set.Ioc (Real.exp a) (Real.exp b), f x)| ≤
      (5 : ℝ)*(2*W+D*(b-a))/a^3 := by
  have ha0 : 0 < a := by linarith
  have hab' := Real.exp_le_exp.mpr hab
  have hxpos x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : 0 < x :=
    (Real.exp_pos a).trans_le hx.1
  have hlog x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) : a ≤ Real.log x :=
    (Real.le_log_iff_exp_le (hxpos x hx)).mpr hx.1
  have htheta x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |Chebyshev.theta x-x| ≤ (5 : ℝ)*x/(Real.log x)^2 := by
    have h := htheta (Real.log x) (ha.trans (hlog x hx))
    rwa [Real.exp_log (hxpos x hx)] at h
  have hend x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |f x*(Chebyshev.theta x-x)| ≤ (5 : ℝ)*W/a^3 := by
    have hx0 := hxpos x hx
    have hl0 := ha0.trans_le (hlog x hx)
    rw [abs_mul]
    calc
      _ ≤ (W/(x*Real.log x))*((5 : ℝ)*x/(Real.log x)^2) :=
        mul_le_mul (hf x hx) (htheta x hx) (abs_nonneg _) (by positivity)
      _ = (5 : ℝ)*W/(Real.log x)^3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ ha0.le (hlog x hx) 3)
  have hint x (hx : x ∈ Set.Icc (Real.exp a) (Real.exp b)) :
      |deriv f x*(x-Chebyshev.theta x)| ≤ ((5 : ℝ)*D/a^3)*x⁻¹ := by
    have hx0 := hxpos x hx
    have hl0 := ha0.trans_le (hlog x hx)
    rw [abs_mul,abs_sub_comm x]
    calc
      _ ≤ (D/(x^2*Real.log x))*((5 : ℝ)*x/(Real.log x)^2) :=
        mul_le_mul (hf' x hx) (htheta x hx) (abs_nonneg _) (by positivity)
      _ = ((5 : ℝ)*D/(Real.log x)^3)*x⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ ha0.le (hlog x hx) 3)) (inv_nonneg.mpr hx0.le)
  have hcont : ContinuousOn (fun x : ℝ => ((5 : ℝ)*D/a^3)*x⁻¹)
      (Set.Icc (Real.exp a) (Real.exp b)) :=
    continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => (hxpos x hx).ne'))
  have hierr := integrable_prime_error f (Real.exp_pos a).le hi
  have hibound : IntegrableOn (fun x : ℝ => ((5 : ℝ)*D/a^3)*x⁻¹)
      (Set.Ioc (Real.exp a) (Real.exp b)) :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hib : |∫ x in Set.Ioc (Real.exp a) (Real.exp b), deriv f x*(x-Chebyshev.theta x)| ≤
      (5 : ℝ)*D/a^3*(b-a) := by
    calc
      _ ≤ ∫ x in Set.Ioc (Real.exp a) (Real.exp b), |deriv f x*(x-Chebyshev.theta x)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (Real.exp a) (Real.exp b), ((5 : ℝ)*D/a^3)*x⁻¹ :=
        setIntegral_mono_on hierr.abs hibound measurableSet_Ioc
          (fun x hx => hint x (Set.Ioc_subset_Icc_self hx))
      _ = _ := by rw [integral_const_mul,inverse_integral hab]
  rw [prime_abel f (Real.exp_pos a).le hab' hd hi]
  calc
    _ ≤ |f (Real.exp b)*(Chebyshev.theta (Real.exp b)-Real.exp b)|+
        |f (Real.exp a)*(Chebyshev.theta (Real.exp a)-Real.exp a)|+
        |∫ x in Set.Ioc (Real.exp a) (Real.exp b), deriv f x*(x-Chebyshev.theta x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (5 : ℝ)*W/a^3+(5 : ℝ)*W/a^3+(5 : ℝ)*D/a^3*(b-a) :=
      add_le_add (add_le_add (hend _ ⟨hab',le_rfl⟩) (hend _ ⟨le_rfl,hab'⟩)) hib
    _ = _ := by ring

/-- A joined finite prime interval pays only its exterior endpoints and
one cubic-logarithmic arithmetic error. The signed smooth integral remains
in the comparison; no prime-density substitution at source scale is claimed. -/
theorem eventually_prime_error_cube :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ (f : ℝ → ℝ) (a b W D : ℝ),
      T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ D →
      (∀ x ∈ Set.Icc (exp a) (exp b), DifferentiableAt ℝ f x) →
      IntegrableOn (deriv f) (Set.Icc (exp a) (exp b)) →
      (∀ x ∈ Set.Icc (exp a) (exp b), |f x| ≤ W/(x*log x)) →
      (∀ x ∈ Set.Icc (exp a) (exp b), |deriv f x| ≤ D/(x^2*log x)) →
      |(∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime, f p*log p)-
        (∫ x in Set.Ioc (exp a) (exp b), f x)| ≤ 5*(2*W+D*(b-a))/a^3 := by
  obtain ⟨T,hT,hθ⟩ := eventually_theta_error
  exact ⟨T,hT,fun f a b W D ha hab hW hD hd hi hf hf' =>
    prime_error_cube_of_theta T hT hθ f ha hab hW hD hd hi hf hf'⟩

private theorem profile_error_cube_of_theta (T : ℝ) (hT : 5000 ≤ T)
    (htheta : ∀ t : ℝ, T ≤ t → |Chebyshev.theta (exp t)-exp t| ≤ 5*exp t/t^2)
    (F G : ℝ → ℝ) (c : ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t) (hG : Continuous G)
    {a b W V : ℝ} (ha : T ≤ a) (hab : a ≤ b) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hFW : ∀ t ∈ Set.Icc (a+c) (b+c), |F t| ≤ W)
    (hGV : ∀ t ∈ Set.Icc (a+c) (b+c), |G t| ≤ V) :
    |(∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
        F (log p+c)/(p : ℝ))-
      (∫ x in Set.Ioc (exp a) (exp b), F (log x+c)/(x*log x))| ≤
      5*(2*W+(V+2*W)*(b-a))/a^3 := by
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
  have hp := prime_error_cube_of_theta T hT htheta f ha hab hW (by positivity : 0 ≤ V+2*W)
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
  exact hp

/-- The smooth signed profile keeps its exact reciprocal logarithm.
Joined periods and clipped exterior intervals pay the same cubic-log
arithmetic error, independently of the number of internal subdivisions. -/
theorem eventually_signed_profile_error :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ (F G : ℝ → ℝ) (c a b W V : ℝ),
      (∀ t, HasDerivAt F (G t) t) → Continuous G →
      T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ V →
      (∀ t ∈ Set.Icc (a+c) (b+c), |F t| ≤ W) →
      (∀ t ∈ Set.Icc (a+c) (b+c), |G t| ≤ V) →
      |(∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
          F (log p+c)/(p : ℝ))-
        (∫ x in Set.Ioc (exp a) (exp b), F (log x+c)/(x*log x))| ≤
        5*(2*W+(V+2*W)*(b-a))/a^3 := by
  obtain ⟨T,hT,hθ⟩ := eventually_theta_error
  exact ⟨T,hT,fun F G c a b W V hF hG ha hab hW hV hFW hGV =>
    profile_error_cube_of_theta T hT hθ F G c hF hG ha hab hW hV hFW hGV⟩

/-- The exact global factorial-amplitude maximum prevents a wide interval
from paying the product of two maxima attained at different endpoints. -/
theorem factorial_amplitude_global_bound (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |ZetaRieszWeightedPrimeTail.factorialAmplitude j t| ≤
      exp (-(j : ℝ))*(2*j)^j := by
  rw [abs_of_nonneg (by
    dsimp [ZetaRieszWeightedPrimeTail.factorialAmplitude]
    positivity)]
  by_cases hj : j=0
  · subst j
    simp only [ZetaRieszWeightedPrimeTail.factorialAmplitude,Nat.cast_zero,pow_zero,mul_one,neg_zero,exp_zero]
    exact exp_le_one_iff.mpr (by linarith)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
  have hh := pow_le_pow_left₀ (show 0 ≤ t/(2*j)*exp (-(t/(2*j))) by positivity)
    (mul_exp_neg_le_exp_neg_one (t/(2*j))) j
  have he : exp (-(t/(2*j)))^j = exp (-t/2) := by
    rw [← exp_nat_mul]
    congr 1
    field_simp
  rw [mul_pow,he,← exp_nat_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2*(j : ℝ))^j by positivity)
  have hel : (2*(j : ℝ))^j*((t/(2*j))^j*exp (-t/2)) = exp (-t/2)*t^j := by
    rw [div_pow]
    field_simp
  rw [hel] at hm
  simpa only [ZetaRieszWeightedPrimeTail.factorialAmplitude,mul_neg,mul_one,mul_comm] using hm

/-- The logarithmic factorial derivative has a uniform score on any positive interval. -/
theorem factorial_score_bound (j : ℕ) {a b t : ℝ} (ha : 0 < a)
    (ht : t ∈ Set.Icc a b) :
    |(j : ℝ)/t-1/2| ≤ ZetaRieszWeightedPrimeTail.factorialScore a (b-a) j := by
  have ht0 : 0 < t := ha.trans_le ht.1
  have hba : 0 ≤ b-a := by linarith [ht.1,ht.2]
  have hdiv : 0 ≤ (j : ℝ)/a-j/t :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left (Nat.cast_nonneg j) ha ht.1)
  have hd : (j : ℝ)/a-j/t ≤ j*(b-a)/a^2 := by
    have he : (j : ℝ)/a-j/t = j*(t-a)/(a*t) := by field_simp
    rw [he]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [ht.2] : t-a ≤ b-a) (Nat.cast_nonneg j))
        (by positivity : 0 ≤ a*t)).trans
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha)
      (by nlinarith [mul_le_mul_of_nonneg_left ht.1 ha.le])
  have hs := abs_sub_le ((j : ℝ)/t) (j/a) (1/2)
  rw [abs_sub_comm ((j : ℝ)/t) (j/a),abs_of_nonneg hdiv] at hs
  dsimp [ZetaRieszWeightedPrimeTail.factorialScore]
  linarith only [hs,hd]

/-- Every actual factorial order, including zero and one, obeys the sharper
joined-interval arithmetic error. The complete oscillatory smooth moment
remains signed and retains the cofactor phase. Exterior clipping is allowed. -/
theorem eventually_factorial_interval_error :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ (j : ℕ) (a b y c : ℝ), T ≤ a → a ≤ b →
      let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j);
      let S := ZetaRieszWeightedPrimeTail.factorialScore a (b-a) j;
      |(∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
          ZetaRieszWeightedPrimeTail.factorialAmplitude j (log p)*cos (y*(log p+c))/(p : ℝ))-
        (∫ x in Set.Ioc (exp a) (exp b),
          ZetaRieszWeightedPrimeTail.factorialAmplitude j (log x)*cos (y*(log x+c))/(x*log x))| ≤
        5*W*(2+(S+|y|+2)*(b-a))/a^3 := by
  obtain ⟨T,hT,hbound⟩ := eventually_signed_profile_error
  refine ⟨T,hT,fun j a b y c ha hab => ?_⟩
  dsimp only
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j)
  let S := ZetaRieszWeightedPrimeTail.factorialScore a (b-a) j
  let F := fun t => ZetaRieszWeightedPrimeTail.factorialAmplitude j t*cos (y*(t+c))
  let G := fun t => exp (-t/2)*((j : ℝ)*t^(j-1)-t^j/2)*cos (y*(t+c))-
    y*(exp (-t/2)*t^j)*sin (y*(t+c))
  have hF t : HasDerivAt F (G t) t := by
    have hb := (((hasDerivAt_id t).neg.div_const 2).exp).mul ((hasDerivAt_id t).pow j)
    have hc := (((hasDerivAt_id t).add_const c).const_mul y).cos
    apply (hb.mul hc).congr_deriv
    simp only [G,Pi.mul_apply,Pi.pow_apply,Pi.neg_apply,id_eq]
    ring
  have hGc : Continuous G := by dsimp [G]; fun_prop
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hS : 0 ≤ S := by
    dsimp [S,ZetaRieszWeightedPrimeTail.factorialScore]
    have hh := sub_nonneg.mpr hab
    positivity
  have ham t (ht : t ∈ Set.Icc a b) :
      |ZetaRieszWeightedPrimeTail.factorialAmplitude j t| ≤ W ∧
      |((j : ℝ)/t-1/2)*ZetaRieszWeightedPrimeTail.factorialAmplitude j t| ≤ W*S := by
    have ht0 := ha0.trans_le ht.1
    have hv := (ZetaRieszWeightedPrimeTail.factorialAmplitude_bounds j ha0 (sub_nonneg.mpr hab)
      (show t ∈ Set.Icc a (a+(b-a)) by simpa only [add_sub_cancel] using ht)).1
    simp only [add_sub_cancel] at hv
    have hw : |ZetaRieszWeightedPrimeTail.factorialAmplitude j t| ≤ W :=
      le_min hv (factorial_amplitude_global_bound j ht0.le)
    refine ⟨hw,?_⟩
    rw [abs_mul,mul_comm]
    exact mul_le_mul hw (factorial_score_bound j ha0 ht) (abs_nonneg _) hW
  have hFW t (ht : t ∈ Set.Icc (a+0) (b+0)) : |F t| ≤ W := by
    simp only [add_zero] at ht
    have h := (ham t ht).1
    dsimp only [F]
    rw [abs_mul]
    exact (mul_le_mul h (abs_cos_le_one _) (abs_nonneg _) hW).trans_eq (mul_one _)
  have hGV t (ht : t ∈ Set.Icc (a+0) (b+0)) : |G t| ≤ W*(S+|y|) := by
    simp only [add_zero] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hl := (ZetaRieszWeightedPrimeTail.factorialAmplitude_deriv j ht0).mul
      ((((hasDerivAt_id t).add_const c).const_mul y).cos)
    have hl' : HasDerivAt F
        (((j : ℝ)/t-1/2)*ZetaRieszWeightedPrimeTail.factorialAmplitude j t*cos (y*(t+c))-
          y*ZetaRieszWeightedPrimeTail.factorialAmplitude j t*sin (y*(t+c))) t := by
      apply hl.congr_deriv
      simp only [id_eq]
      ring
    rw [(hF t).unique hl']
    have hv := (ham t ht).1
    have hd := (ham t ht).2
    apply (abs_sub _ _).trans
    have h1 : |((j : ℝ)/t-1/2)*ZetaRieszWeightedPrimeTail.factorialAmplitude j t*cos (y*(t+c))| ≤ W*S := by
      rw [abs_mul]
      exact (mul_le_mul hd (abs_cos_le_one _) (abs_nonneg _) (mul_nonneg hW hS)).trans_eq (mul_one _)
    have h2 : |y*ZetaRieszWeightedPrimeTail.factorialAmplitude j t*sin (y*(t+c))| ≤ |y| * W := by
      rw [abs_mul,abs_mul]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hv (abs_nonneg y))
        (abs_sin_le_one _) (abs_nonneg _) (mul_nonneg (abs_nonneg y) hW)).trans_eq (mul_one _)
    exact (add_le_add h1 h2).trans_eq (by ring)
  have hh := hbound F G 0 a b W (W*(S+|y|)) hF hGc ha hab hW
    (mul_nonneg hW (add_nonneg hS (abs_nonneg y))) hFW hGV
  simp only [add_zero,F] at hh
  exact hh.trans_eq (by dsimp [W,S]; ring)

/-- The explicit arithmetic-discrepancy price for an entire factorial
prime interval. It contains only the two outer endpoints and interval width. -/
def factorialError (a b y : ℝ) (j : ℕ) : ℝ :=
  let W := min (exp (-a/2)*b^j) (exp (-(j : ℝ))*(2*j)^j)
  5*W*(2+(ZetaRieszWeightedPrimeTail.factorialScore a (b-a) j+|y|+2)*(b-a))/a^3

/-- The literal retained allocation has the sharper joint moment error on
one complete or clipped interval. Every cofactor count, factorial order and
signed cofactor weight remains. The Riesz cutoff response is not replaced:
this theorem pays the prime-moment discrepancy, not the full carrier. -/
theorem eventually_retained_interval_error :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ (A S : Finset ℕ) (N : ℕ) (a b y : ℝ) (w : ℕ → ℝ),
      T ≤ a → a ≤ b →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime;
      P ⊆ A → (∀ n ∈ S, ∀ p ∈ P, ¬p ∣ n) →
      ∃ B : ℕ → ℕ → ℝ,
        (∀ n ∈ S, ∀ j ≤ N+1, 0 ≤ B n j ∧ B n j ≤ ((N+1).choose j : ℝ)*(log n)^(N+1-j)) ∧
        (∀ n ∈ S, ∀ p ∈ P,
          (1-ZetaRieszJointAllocation.boundedShare A N (p*n))*(log p+log n)^(N+1) =
            ∑ j ∈ Finset.range (N+2), B n j*(log p)^j) ∧
        let J := ∑ n ∈ S, ∑ p ∈ P,
          w n*(1-ZetaRieszJointAllocation.boundedShare A N (p*n))*
            ZetaRieszWeightedPrimeTail.factorialAmplitude (N+1) (log (p*n : ℕ))*
              cos (y*log (p*n : ℕ))/(p : ℝ);
        let M := ∑ n ∈ S, w n*exp (-log n/2)*
          (∑ j ∈ Finset.range (N+2), B n j*
            (∫ x in Set.Ioc (exp a) (exp b),
              ZetaRieszWeightedPrimeTail.factorialAmplitude j (log x)*
                cos (y*(log x+log n))/(x*log x)));
        |J-M| ≤ ∑ n ∈ S, |w n| * exp (-log n/2)*
          (∑ j ∈ Finset.range (N+2), ((N+1).choose j : ℝ)*(log n)^(N+1-j)*factorialError a b y j) := by
  obtain ⟨T,hT,hbound⟩ := eventually_factorial_interval_error
  refine ⟨T,hT,fun A S N a b y w ha hab hSF hPA hcop => ?_⟩
  dsimp only at hPA hcop ⊢
  let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime
  have hex n (hn : n ∈ S) :=
    ZetaRieszRetainedFactorial.exists_retained_coefficients A N (hSF n hn).1 (hSF n hn).2
  choose B hcoef hid using hex
  let B' := fun n j => if hn : n ∈ S then B n hn j else 0
  have hB n (hn : n ∈ S) j (hj : j ≤ N+1) :
      0 ≤ B' n j ∧ B' n j ≤ ((N+1).choose j : ℝ)*(log n)^(N+1-j) := by
    dsimp only [B']
    rw [dif_pos hn]
    exact hcoef n hn j hj
  have hId n (hn : n ∈ S) p (hp : p ∈ P) :
      (1-ZetaRieszJointAllocation.boundedShare A N (p*n))*(log p+log n)^(N+1) =
        ∑ j ∈ Finset.range (N+2), B' n j*(log p)^j := by
    have hl : log (p*n : ℕ) = log p+log n := by
      rw [Nat.cast_mul,log_mul
        (by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero)
        (by exact_mod_cast (hSF n hn).1.ne_zero)]
    simpa only [B',dif_pos hn,hl] using
      hid n hn p (Finset.mem_filter.mp hp).2 (hPA hp) (hcop n hn p hp)
  refine ⟨B',hB,hId,?_⟩
  let F := fun n j => ∑ p ∈ P, ZetaRieszWeightedPrimeTail.factorialAmplitude j (log p)*
    cos (y*(log p+log n))/(p : ℝ)
  let I := fun n j => ∫ x in Set.Ioc (exp a) (exp b),
    ZetaRieszWeightedPrimeTail.factorialAmplitude j (log x)*cos (y*(log x+log n))/(x*log x)
  have hF n j : |F n j-I n j| ≤ factorialError a b y j := hbound j a b y (log n) ha hab
  have hcost j : 0 ≤ factorialError a b y j := (abs_nonneg _).trans (hF 1 j)
  have he n (hn : n ∈ S) :
      (∑ p ∈ P, w n*(1-ZetaRieszJointAllocation.boundedShare A N (p*n))*
        ZetaRieszWeightedPrimeTail.factorialAmplitude (N+1) (log (p*n : ℕ))*
          cos (y*log (p*n : ℕ))/(p : ℝ)) =
      w n*exp (-log n/2)*(∑ j ∈ Finset.range (N+2), B' n j*F n j) := by
    simp only [F,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 := (Finset.mem_filter.mp hp).2.ne_zero
    have hn0 := (hSF n hn).1.ne_zero
    have hl : log (p*n : ℕ) = log p+log n := by
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0) (by exact_mod_cast hn0)]
    have hexp : exp (-(log p+log n)/2) = exp (-log p/2)*exp (-log n/2) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hl]
    simp only [ZetaRieszWeightedPrimeTail.factorialAmplitude,hexp]
    have hh := congrArg
      (fun z : ℝ => w n*exp (-log p/2)*exp (-log n/2)*cos (y*(log p+log n))/(p : ℝ)*z)
        (hId n hn p hp)
    simp only [Finset.mul_sum] at hh
    convert hh using 1 <;> (try apply Finset.sum_congr rfl; intro j _) <;> ring
  rw [Finset.sum_congr rfl he,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [← mul_sub,← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  rw [abs_mul,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (exp_nonneg _))
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  rw [abs_mul,abs_of_nonneg (hB n hn j hjN).1]
  exact (mul_le_mul_of_nonneg_left (hF n j) (hB n hn j hjN).1).trans
    (mul_le_mul_of_nonneg_right (hB n hn j hjN).2 (hcost j))

end RiemannGaussian.ZetaRieszJointPrimeError
