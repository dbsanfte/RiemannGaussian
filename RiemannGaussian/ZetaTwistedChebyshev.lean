/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentChebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Twisted Chebyshev sums: exact arithmetic and diagnostic zero components

The cumulative sum is literal von Mangoldt arithmetic. The zero-component
identities concern one specified explicit-formula component, not a claimed
single-zero asymptotic of the actual sum. No non-coherence estimate or
additional zero-free region is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaTwistedChebyshev
open ZetaPrimeMomentCoherence ZetaPrimeMomentChebyshev

/-- The full archimedean character, with no phase freezing. -/
def phase (y x : ℝ) : ℂ := Complex.exp (-(Complex.I*y)*(Real.log x : ℂ))

/-- Literal centered twisted von Mangoldt cumulative sum, centered at one. -/
def cumulative (y X : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ioc 1 ⌊X⌋₊, phase y n*(ArithmeticFunction.vonMangoldt n : ℂ))-
    ∫ x : ℝ in Ioc 1 X, phase y x

/-- A unit logarithmic block of the same literal measure. -/
def block (y T : ℝ) : ℂ := cumulative y (Real.exp (T+1))-cumulative y (Real.exp T)

theorem phase_one (y : ℝ) : phase y 1=1 := by simp [phase]

theorem hasDerivAt_phase (y : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (phase y) (-(Complex.I*y)/(x : ℂ)*phase y x) x := by
  have h := (((Real.hasDerivAt_log hx.ne').ofReal_comp).const_mul
    (-(Complex.I*y))).cexp
  convert! h using 1
  dsimp only [phase]
  push_cast
  ring

theorem continuousOn_phase (y : ℝ) : ContinuousOn (phase y) (Ioi 0) := by
  intro x hx
  exact (hasDerivAt_phase y hx).continuousAt.continuousWithinAt

private theorem continuousOn_phase_deriv (y : ℝ) :
    ContinuousOn (deriv (phase y)) (Ioi 0) := by
  have he : EqOn (deriv (phase y))
      (fun x : ℝ => -(Complex.I*y)/(x : ℂ)*phase y x) (Ioi 0) :=
    fun x hx => (hasDerivAt_phase y hx).deriv
  apply ContinuousOn.congr _ he
  exact (continuousOn_const.div Complex.continuous_ofReal.continuousOn
    (fun x hx => by exact_mod_cast hx.ne')).mul (continuousOn_phase y)

/-- Finite partial summation, including the lower endpoint `f(1)`.
The arithmetic measure is exactly the ordinary integer von Mangoldt measure. -/
theorem finite_discrepancy_eq {X : ℝ} (hX : 1≤X) (f : ℝ→ℂ)
    (hf : ∀ x ∈ Icc 1 X, DifferentiableAt ℝ f x)
    (hi : IntegrableOn (deriv f) (Icc 1 X)) :
    (∑ n ∈ Finset.Ioc 1 ⌊X⌋₊, f n*(ArithmeticFunction.vonMangoldt n : ℂ))-
        (∫ x : ℝ in Ioc 1 X, f x) =
      f X*(Chebyshev.psi X-X : ℝ)+f 1+
        ∫ x : ℝ in Ioc 1 X, deriv f x*(x-Chebyshev.psi x : ℝ) := by
  have hp := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
    (a := (1 : ℝ)) (b := X) zero_le_one hX hf hi
  simp_rw [←Complex.ofReal_sum,←Chebyshev.psi_eq_sum_Icc] at hp
  simp only [Nat.floor_one,Chebyshev.psi_one,Complex.ofReal_zero,mul_zero,sub_zero] at hp
  have hd : IntervalIntegrable (deriv f) volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr hi
  have ht := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := deriv f) (v := fun x : ℝ => (x : ℂ))
    (v' := fun _ : ℝ => (1 : ℂ))
    (fun x hx => hf x (by simpa only [uIcc_of_le hX] using hx) |>.hasDerivAt)
    (fun x _ => (hasDerivAt_id x).ofReal_comp) hd intervalIntegrable_const
  rw [intervalIntegral.integral_of_le hX,intervalIntegral.integral_of_le hX] at ht
  simp only [mul_one,Complex.ofReal_one] at ht
  have hxd : IntegrableOn (fun x : ℝ => deriv f x*(x : ℂ)) (Ioc 1 X) :=
    (hi.mul_continuousOn Complex.continuous_ofReal.continuousOn isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hpd := integrableOn_mul_sum_Icc
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
    (a := (1 : ℝ)) (b := X) (m := 0) zero_le_one hi
  simp_rw [←Complex.ofReal_sum,←Chebyshev.psi_eq_sum_Icc] at hpd
  have he : (∫ x : ℝ in Ioc 1 X, deriv f x*(x-Chebyshev.psi x : ℝ))=
      (∫ x : ℝ in Ioc 1 X, deriv f x*(x : ℂ))-
        ∫ x : ℝ in Ioc 1 X, deriv f x*(Chebyshev.psi x : ℂ) := by
    rw [←integral_sub hxd (hpd.mono_set Ioc_subset_Icc_self)]
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    ring
  rw [hp,he,ht]
  push_cast
  ring

/-- The exact twisted sum expressed through the actual signed `psi-x` error.
The endpoint `+1` is necessary because the main integral starts at one. -/
theorem cumulative_eq_chebyshev_error (y : ℝ) {X : ℝ} (hX : 1≤X) :
    cumulative y X=phase y X*(Chebyshev.psi X-X : ℝ)+1+
      ∫ x : ℝ in Ioc 1 X,
        (Complex.I*y)/(x : ℂ)*phase y x*(Chebyshev.psi x-x : ℝ) := by
  have hs : Icc (1 : ℝ) X⊆Ioi 0 := fun x hx => zero_lt_one.trans_le hx.1
  have h := finite_discrepancy_eq hX (phase y)
    (fun x hx => (hasDerivAt_phase y (hs hx)).differentiableAt)
    ((continuousOn_phase_deriv y).mono hs |>.integrableOn_Icc)
  rw [phase_one] at h
  unfold cumulative
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [(hasDerivAt_phase y (zero_lt_one.trans hx.1)).deriv]
  push_cast
  ring

/-- One genuine-zero explicit-formula component after twisting.
This definition retains its lower-endpoint subtraction. -/
def zeroComponent (rho : ℂ) (m : ℕ) (y T : ℝ) : ℂ :=
  -(m : ℂ) * ∫ t : ℝ in 0..T, Complex.exp ((rho-Complex.I*y)*t)

/-- At the matched ordinate the component is a NONOSCILLATORY power.
The denominator becomes `beta`, not the original complex zero location. -/
theorem matched_zeroComponent {beta : ℝ} (hb : beta≠0) (y T : ℝ) (m : ℕ) :
    zeroComponent ((beta : ℂ)+Complex.I*y) m y T=
      -(m : ℂ)/(beta : ℂ)*((Real.exp (beta*T) : ℂ)-1) := by
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => Complex.exp ((beta : ℂ)*t)/(beta : ℂ))
      (Complex.exp ((beta : ℂ)*t)) t := by
    have h := (((hasDerivAt_id t).ofReal_comp).const_mul (beta : ℂ)).cexp.div_const
      (beta : ℂ)
    have hb0 : (beta : ℂ)≠0 := by exact_mod_cast hb
    simpa only [id_eq,Complex.ofReal_one,mul_one,mul_div_cancel_right₀ _ hb0] using! h
  have hi : IntervalIntegrable (fun t : ℝ => Complex.exp ((beta : ℂ)*t)) volume 0 T :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp ((beta : ℂ)*t))).intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero] at h
  simp only [zeroComponent,add_sub_cancel_right]
  rw [h,←Complex.ofReal_mul,←Complex.ofReal_exp]
  ring

/-- A general isolated diagnostic component has the exact centered source
factor `-m*(u/(s-rho))^(k+2)`. Off-frequency components are not an error in
the Chebyshev sum but can decay geometrically in the factorial transform. -/
theorem component_source {rho s : ℂ} (hrho : rho≠0) (h : 0<(s-rho).re)
    (u : ℝ) (m k : ℕ) :
    (u : ℂ)^(k+2)*(s*componentMoment rho m (k+1) s-componentMoment rho m k s)=
      -(m : ℂ)*((u : ℂ)/(s-rho))^(k+2) := by
  have hne : s-rho≠0 := by intro he; simp [he] at h
  rw [componentMoment_eq h,componentMoment_eq h,div_pow]
  simp only [inv_pow,pow_succ]
  field_simp
  ring

/-- Exact log-block size of the matched power component. This retains its
exponential scale drift; it is not a bound for the actual arithmetic block. -/
theorem matched_zeroBlock {beta : ℝ} (hb : beta≠0) (y T : ℝ) (m : ℕ) :
    zeroComponent ((beta : ℂ)+Complex.I*y) m y (T+1)-
        zeroComponent ((beta : ℂ)+Complex.I*y) m y T=
      -(m : ℂ)/(beta : ℂ)*((Real.exp beta : ℂ)-1)*
        (Real.exp (beta*T) : ℂ) := by
  rw [matched_zeroComponent hb,matched_zeroComponent hb]
  rw [show beta*(T+1)=beta*T+beta by ring,Real.exp_add]
  push_cast
  ring

/-- The archimedean phase is exactly compatible with prime dilations.
Generic phase-contagion alone cannot distinguish it from a coherent mode. -/
theorem phase_mul (y : ℝ) {x z : ℝ} (hx : 0<x) (hz : 0<z) :
    phase y (x*z)=phase y x*phase y z := by
  unfold phase
  rw [Real.log_mul hx.ne' hz.ne',Complex.ofReal_add,mul_add,Complex.exp_add]

/-- Any fixed nonzero frequency offset is geometrically invisible in the
factorial source, even though it can give positive variance across log scales. -/
theorem offset_component_tendsto {u y w : ℝ} (hu : 0<u) (hu1 : u<1)
    (hw : w≠0) (m : ℕ) :
    Tendsto (fun k : ℕ => (u : ℂ)^(k+2)*
      (center y*componentMoment (candidate u y+Complex.I*w) m (k+1) (center y)-
        componentMoment (candidate u y+Complex.I*w) m k (center y)))
      atTop (𝓝 0) := by
  have he : center y-(candidate u y+Complex.I*w)=(u : ℂ)-Complex.I*w := by
    unfold candidate
    ring
  have hrho : candidate u y+Complex.I*w≠0 := by
    intro hz
    have h := congrArg Complex.re hz
    norm_num [candidate,ZetaPrimeMomentCoherence.center] at h
    linarith
  have hd : 0<(center y-(candidate u y+Complex.I*w)).re := by
    rw [he]
    simpa using hu
  have hs : ‖(u : ℂ)-Complex.I*w‖^2=u^2+w^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp
    ring
  have hg : u<‖(u : ℂ)-Complex.I*w‖ := by
    have hp : 0<w^2 := sq_pos_of_ne_zero hw
    nlinarith [norm_nonneg ((u : ℂ)-Complex.I*w)]
  have hr : ‖(u : ℂ)/((u : ℂ)-Complex.I*w)‖<1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hu.le]
    exact (div_lt_one (hu.trans hg)).mpr hg
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).comp
    (tendsto_add_atTop_nat 2)
  convert ht.const_mul (-(m : ℂ)) using 1
  · funext k
    rw [component_source hrho hd,he]
    rfl
  · simp

/-- A matched component can coexist with an off-frequency component and
still have exactly the persistent limit. Variance in the latter does not
exclude the former. This is a diagnostic model, not a claim about primes. -/
theorem coupled_components_tendsto {u y w : ℝ} (hu : 0<u) (hu1 : u<1)
    (hw : w≠0) (m n : ℕ) :
    Tendsto (fun k : ℕ => (u : ℂ)^(k+2)*
      (center y*(componentMoment (candidate u y) m (k+1) (center y)+
          componentMoment (candidate u y+Complex.I*w) n (k+1) (center y))-
        (componentMoment (candidate u y) m k (center y)+
          componentMoment (candidate u y+Complex.I*w) n k (center y))))
      atTop (𝓝 (-(m : ℂ))) := by
  have hrho : candidate u y≠0 := by
    intro hz
    have h := congrArg Complex.re hz
    norm_num [candidate,ZetaPrimeMomentCoherence.center] at h
    linarith
  have ht := (tendsto_const_nhds (x := -(m : ℂ))).add
    (offset_component_tendsto (y := y) hu hu1 hw n)
  simp only [add_zero] at ht
  apply ht.congr
  intro k
  rw [←component_exact_source hu hrho m k]
  ring

end RiemannGaussian.ZetaTwistedChebyshev
