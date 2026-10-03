/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerPhasePrimitive

/-!
# Signed complete-window owner sums on the integer lattice

This is ordinary integer sampling, not a prime-density approximation.
The signed continuous integral is kept intact. A derivative norm pays only
the lattice error. All finite factorial orders of the old owner are kept.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszOwnerLatticePhase
open ZetaRieszOwnerMaximal ZetaRieszJointAllocation
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszOwnerPhasePrimitive

private theorem mass_le_one (n k : ℕ) {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    mass n k x≤1 := by
  by_cases hk : k≤n
  · exact (Finset.single_le_sum (fun i _ => mass_nonneg n i hx hx1)
      (Finset.mem_range.mpr (by omega : k<n+1))).trans_eq (mass_total n x)
  · simp [mass,Nat.choose_eq_zero_of_lt (by omega : n<k)]

private theorem ownerWeight_deriv {N : ℕ} (hN : 32≤N) (x : ℝ) :
    HasDerivAt (ownerWeight N)
      (((N : ℝ)+1)*(mass N (13*N/32) x-mass N (N/5+1) x)) x := by
  have he : ownerWeight N = fun v =>
      1-lowerMass (N+1) (13*N/32) v+lowerMass (N+1) (N/5+1) v := by
    funext v
    rw [ownerWeight,ownerMass_eq_difference hN]
    ring
  rw [he]
  apply (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_lowerMass (N+1) (13*N/32) x)).add
    (hasDerivAt_lowerMass (N+1) (N/5+1) x)).congr_deriv
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  ring

/-- The exact owner phase in physical total-log coordinates. -/
def ownerLogPhase (N : ℕ) (c y T : ℝ) : ℝ :=
  ownerWeight N ((T-c)/T)*radial N T*cos (y*T)

/-- Its full derivative, including the moving owner allocation. -/
def ownerLogDerivative (N : ℕ) (c y T : ℝ) : ℝ :=
  let x := (T-c)/T
  let md := ((N : ℝ)+1)*(mass N (13*N/32) x-mass N (N/5+1) x)
  let rd := exp (-T/2)*(((N : ℝ)+1)*T^N-T^(N+1)/2)/(N.factorial : ℝ)
  (md*(c/T^2)*radial N T+ownerWeight N x*rd)*cos (y*T)+
    ownerWeight N x*radial N T*(-sin (y*T)*y)

theorem ownerLogPhase_deriv {N : ℕ} (hN : 32≤N) (c y : ℝ) {T : ℝ} (hT : T≠0) :
    HasDerivAt (ownerLogPhase N c y) (ownerLogDerivative N c y T) T := by
  have hs : HasDerivAt (fun t : ℝ => (t-c)/t) (c/T^2) T := by
    apply (((hasDerivAt_id T).sub_const c).div (hasDerivAt_id T) hT).congr_deriv
    simp only [id_eq]
    field_simp
    ring
  have ho := (ownerWeight_deriv hN ((T-c)/T)).comp (h := fun t : ℝ => (t-c)/t) T hs
  have hr := radial_deriv N T
  have hp := ((hasDerivAt_id T).const_mul y).cos
  change HasDerivAt (fun t : ℝ => ownerWeight N ((t-c)/t)*radial N t*cos (y*t)) _ T
  apply ((ho.mul hr).mul hp).congr_deriv
  dsimp only [ownerLogDerivative,Function.comp_apply,Pi.mul_apply,id_eq]
  ring

private theorem ownerDerivative_bound {N : ℕ} {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    |((N : ℝ)+1)*(mass N (13*N/32) x-mass N (N/5+1) x)|≤2*((N : ℝ)+1) := by
  have h1 := mass_nonneg N (13*N/32) hx hx1
  have h2 := mass_nonneg N (N/5+1) hx hx1
  have h3 := mass_le_one N (13*N/32) hx hx1
  have h4 := mass_le_one N (N/5+1) hx hx1
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(N : ℝ)+1)]
  have hb : |mass N (13*N/32) x-mass N (N/5+1) x|≤2 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  nlinarith only [hb]

theorem ownerLogPhase_bound (N : ℕ) {c T : ℝ} (hc : 0≤c) (hcT : c≤T)
    (hT : 0<T) (y : ℝ) : |ownerLogPhase N c y T|≤radialCap N := by
  have hx : 0≤(T-c)/T := div_nonneg (by linarith) hT.le
  have hx1 : (T-c)/T≤1 := (div_le_one hT).mpr (by linarith)
  have ho := ownerWeight_bounds N hx hx1
  have hr := radial_bounds N hT.le
  unfold ownerLogPhase
  rw [abs_mul,abs_mul,abs_of_nonneg ho.1,abs_of_nonneg hr.1]
  exact ((mul_le_of_le_one_right (mul_nonneg ho.1 hr.1) (abs_cos_le_one _)).trans
    (mul_le_of_le_one_left hr.1 ho.2)).trans hr.2

/-- Only the ordinary-lattice ERROR uses this positive derivative cap. -/
theorem ownerLogDerivative_bound (N : ℕ) {c T : ℝ} (hc : 0≤c) (hcT : c≤T)
    (hT : 1≤T) (y : ℝ) :
    |ownerLogDerivative N c y T|≤(2*((N : ℝ)+1)+1+|y|)*radialCap N := by
  have ht0 : 0<T := by linarith
  have hx : 0≤(T-c)/T := div_nonneg (by linarith) ht0.le
  have hx1 : (T-c)/T≤1 := (div_le_one ht0).mpr (by linarith)
  have ho := ownerWeight_bounds N hx hx1
  have hm := ownerDerivative_bound (N := N) hx hx1
  have hr := radial_bounds N ht0.le
  have hd := radial_deriv_bound N ht0.le
  have hs : 0≤c/T^2 := by positivity
  have hs1 : c/T^2≤1 := (div_le_one (by positivity : 0<T^2)).mpr (by nlinarith)
  have hleft :
      |(((N : ℝ)+1)*(mass N (13*N/32) ((T-c)/T)-mass N (N/5+1) ((T-c)/T)))*
        (c/T^2)*radial N T|≤2*((N : ℝ)+1)*radialCap N := by
    rw [abs_mul,abs_mul,abs_of_nonneg hs,abs_of_nonneg hr.1]
    exact mul_le_mul ((mul_le_of_le_one_right (abs_nonneg _) hs1).trans hm)
      hr.2 hr.1 (by positivity)
  have hright :
      |ownerWeight N ((T-c)/T)*
        (exp (-T/2)*(((N : ℝ)+1)*T^N-T^(N+1)/2)/(N.factorial : ℝ))|≤radialCap N := by
    rw [abs_mul,abs_of_nonneg ho.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ho.2).trans hd
  have hsin : |ownerWeight N ((T-c)/T)*radial N T*(-sin (y*T)*y)|≤radialCap N*|y| := by
    rw [abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg ho.1,abs_of_nonneg hr.1]
    exact mul_le_mul ((mul_le_of_le_one_left hr.1 ho.2).trans hr.2)
      (mul_le_of_le_one_left (abs_nonneg y) (abs_sin_le_one _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (radialCap_nonneg N)
  unfold ownerLogDerivative
  dsimp only
  apply (abs_add_le _ _).trans
  have hcos := mul_le_of_le_one_right (abs_nonneg
    ((((N : ℝ)+1)*(mass N (13*N/32) ((T-c)/T)-mass N (N/5+1) ((T-c)/T)))*
      (c/T^2)*radial N T+ownerWeight N ((T-c)/T)*
        (exp (-T/2)*(((N : ℝ)+1)*T^N-T^(N+1)/2)/(N.factorial : ℝ))))
      (abs_cos_le_one (y*T))
  rw [abs_mul]
  exact (add_le_add (hcos.trans ((abs_add_le _ _).trans (add_le_add hleft hright))) hsin).trans_eq
    (by ring)

theorem ownerLogPhase_eq_re (N : ℕ) (c y : ℝ) {T : ℝ} (hT : T≠0) :
    ownerLogPhase N c y T=(ownerPhase N c (phaseDamping y) T).re := by
  rw [ownerPhase_eq_weight N c (phaseDamping y) hT]
  rw [← Complex.ofReal_pow,← Complex.ofReal_natCast,Complex.div_ofReal_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero]
  simp [ownerLogPhase,radial,phaseDamping,Complex.exp_re,Complex.mul_re]
  ring

/-- The literal smooth owner weight on the integer lattice, with full phase. -/
def ownerTest (N : ℕ) (c y x : ℝ) : ℝ := ownerLogPhase N c y (c+log x)/x

theorem ownerTest_nat (N : ℕ) (c y : ℝ) (n : ℕ) :
    ownerTest N c y n=ownerAmplitude N c n*cos (y*(c+log n))/(n : ℝ) := by
  simp only [ownerTest,ownerLogPhase,ownerAmplitude,add_sub_cancel_left]

/-- Derivative of the signed logarithmic phase divided by the literal
integer variable, retaining the exact owner-allocation derivative. -/
def ownerTestDerivative (N : ℕ) (c y x : ℝ) : ℝ :=
  (ownerLogDerivative N c y (c+log x)-ownerLogPhase N c y (c+log x))/x^2

theorem ownerTest_deriv {N : ℕ} (hN : 32≤N) {c x : ℝ} (hc : 1≤c) (hx : 1≤x)
    (y : ℝ) : HasDerivAt (ownerTest N c y) (ownerTestDerivative N c y x) x := by
  have hx0 : 0<x := by linarith
  have hl := log_nonneg hx
  have hT : c+log x≠0 := by linarith
  have hg := (ownerLogPhase_deriv hN c y hT).comp x
    ((hasDerivAt_log hx0.ne').const_add c)
  apply (hg.div (hasDerivAt_id x) hx0.ne').congr_deriv
  dsimp [ownerTestDerivative]
  field_simp

theorem ownerTestDerivative_bound (N : ℕ) {c x : ℝ} (hc : 1≤c) (hx : 1≤x) (y : ℝ) :
    |ownerTestDerivative N c y x|≤
      (2*((N : ℝ)+1)+2+|y|)*radialCap N/x^2 := by
  have hl := log_nonneg hx
  have hT : 1≤c+log x := by linarith
  have hc0 : 0≤c := by linarith
  have hct : c≤c+log x := by linarith
  have hd := ownerLogDerivative_bound N hc0 hct hT y
  have hb := ownerLogPhase_bound N hc0 hct (by linarith) y
  unfold ownerTestDerivative
  rw [abs_div,abs_of_nonneg (sq_nonneg x)]
  exact (div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hd hb))
    (sq_nonneg x)).trans_eq (by ring)

/-- Sampling a smooth signed function on the ordinary integer lattice.
Only the sampling DIFFERENCE is bounded by a derivative cap. -/
theorem integer_sampling_error {M X : ℕ} (hMX : M≤X) {f d : ℝ→ℝ} {E : ℝ}
    (hE : 0≤E) (hd : ∀ x∈Set.Icc (M : ℝ) X, HasDerivAt f (d x) x)
    (hb : ∀ x∈Set.Icc (M : ℝ) X, |d x|≤E) :
    |(∑ n∈Finset.Ioc M X, f n)-(∫ x : ℝ in (M : ℝ)..X, f x)|≤(X-M : ℕ)*E := by
  have hcont : ContinuousOn f (Set.Icc (M : ℝ) X) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have hsub (n : ℕ) (hn : n∈Finset.Ico M X) :
      Set.Icc (n : ℝ) (n+1 : ℕ)⊆Set.Icc (M : ℝ) X := by
    have hn' := Finset.mem_Ico.mp hn
    have hmn : (M : ℝ)≤n := by exact_mod_cast hn'.1
    intro x hx
    exact ⟨hmn.trans hx.1,
      hx.2.trans (by exact_mod_cast (show n+1≤X by omega))⟩
  have hi (n : ℕ) (hn : n∈Finset.Ico M X) :
      IntervalIntegrable f volume (n : ℝ) (n+1 : ℕ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ n)]
    exact hcont.mono (hsub n hn)
  have hs (n : ℕ) (hn : n∈Finset.Ico M X) :
      |f (n+1 : ℕ)-(∫ x : ℝ in (n : ℝ)..(n+1 : ℕ), f x)|≤E := by
    have hp : ∀ x∈Set.uIoc (n : ℝ) (n+1 : ℕ), ‖f (n+1 : ℕ)-f x‖≤E := by
      intro x hx
      rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ n)] at hx
      have hx' : x∈Set.Icc (M : ℝ) X := hsub n hn ⟨hx.1.le,hx.2⟩
      have hn' : ((n+1 : ℕ) : ℝ)∈Set.Icc (M : ℝ) X :=
        hsub n hn ⟨by exact_mod_cast Nat.le_succ n,le_rfl⟩
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t ht => (hd t ht).hasDerivWithinAt)
        (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ht)
        (convex_Icc (M : ℝ) X) hx' hn'
      have hlen : ‖((n+1 : ℕ) : ℝ)-x‖≤1 := by
        rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx.2)]
        push_cast
        linarith only [hx.1]
      exact h.trans (mul_le_of_le_one_right hE hlen)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hp
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi n hn),
      intervalIntegral.integral_const] at h
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_smul,
      abs_one,mul_one,Real.norm_eq_abs] using h
  have he : (∑ n∈Finset.Ioc M X, f n)=∑ n∈Finset.Ico M X, f (n+1 : ℕ) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc]
    rw [← Finset.sum_Ico_add' _ M X 1]
  have hjoin := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n : ℝ))
    hMX (fun k hk => hi k (Finset.mem_Ico.mpr hk))
  rw [he,← hjoin,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n∈Finset.Ico M X,
        |f (n+1 : ℕ)-(∫ x : ℝ in (n : ℝ)..(n+1 : ℕ), f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n∈Finset.Ico M X, E := Finset.sum_le_sum hs
    _ = _ := by simp [Nat.card_Ico]

/-- Literal smooth integer sum minus its intact signed continuous main. -/
theorem ownerTest_lattice_error {N M X : ℕ} (hN : 32≤N) (hM : 1≤M) (hMX : M≤X)
    {c : ℝ} (hc : 1≤c) (y : ℝ) :
    |(∑ n∈Finset.Ioc M X, ownerTest N c y n)-
        (∫ x : ℝ in (M : ℝ)..X, ownerTest N c y x)|≤
      (X-M : ℕ)*(2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2 := by
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hcap := radialCap_nonneg N
  let E := (2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hb x (hx : x∈Set.Icc (M : ℝ) X) : |ownerTestDerivative N c y x|≤E := by
    have hx1 : 1≤x := hm.trans hx.1
    apply (ownerTestDerivative_bound N hc hx1 y).trans
    apply div_le_div_of_nonneg_left (by positivity)
      (by positivity : (0 : ℝ)<(M : ℝ)^2)
    nlinarith only [hx.1,hm]
  have h := integer_sampling_error hMX hE
    (fun x hx => ownerTest_deriv hN hc (hm.trans hx.1) y) hb
  exact h.trans_eq (by dsimp [E]; ring)

/-- The signed continuous cofactor sum changes variables EXACTLY, with
both original endpoints. This is not phase freezing. -/
theorem ownerTest_integral {N : ℕ} (hN : 32≤N) {M X : ℕ} (hM : 1≤M) (hMX : M≤X)
    {c : ℝ} (hc : 1≤c) (y : ℝ) :
    (∫ x : ℝ in (M : ℝ)..X, ownerTest N c y x)=
      (∫ T : ℝ in (c+log M)..(c+log X), ownerPhase N c (phaseDamping y) T).re := by
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hab : (M : ℝ)≤X := by exact_mod_cast hMX
  have hcont : ContinuousOn (ownerTest N c y) (Set.Icc (M : ℝ) X) := by
    intro x hx
    exact (ownerTest_deriv hN hc (hm.trans hx.1) y).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (ownerTest N c y) volume (M : ℝ) X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont
  have hp : Continuous (ownerPhase N c (phaseDamping y)) := by
    unfold ownerPhase
    fun_prop
  have hz : phaseDamping y≠0 := by
    intro he
    have := congrArg Complex.re he
    rw [phaseDamping_re] at this
    norm_num at this
  have hreal : (∫ T : ℝ in (c+log M)..(c+log X), ownerPhase N c (phaseDamping y) T).re=
      (ownerPrimitive N c (phaseDamping y) (c+log M)).re-
        (ownerPrimitive N c (phaseDamping y) (c+log X)).re := by
    rw [ownerPhase_integral N c hz,Complex.sub_re]
  have hf x (hx : x∈Set.uIcc (M : ℝ) X) :
      HasDerivAt (fun v : ℝ => (ownerPrimitive N c (phaseDamping y) (c+log v)).re)
        (-ownerTest N c y x) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx1 := hm.trans hx.1
    have hx0 : 0<x := by linarith
    have ht0 : 0<c+log x := by linarith [log_nonneg hx1]
    have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((ownerPrimitive_deriv N c hz (c+log x)).scomp x
        ((hasDerivAt_log hx0.ne').const_add c)))
    apply h.congr_deriv
    simp only [Complex.reCLM_apply,Complex.real_smul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re]
    rw [← ownerLogPhase_eq_re N c y ht0.ne']
    dsimp [ownerTest]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint.neg
  rw [intervalIntegral.integral_neg] at h
  rw [hreal]
  linarith only [h]

private theorem normalized_cap_fast {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*radialCap N*exp (-(2/5 : ℝ)*N)≤
      2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by
  have hb : 2*u≤exp (3/20 : ℝ) := by
    have he := add_one_le_exp (3/20 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith only [hU,he]
  have hn := pow_le_pow_left₀ (mul_nonneg (by norm_num) hu) hb N
  rw [← exp_nat_mul] at hn
  have hg := mul_le_mul_of_nonneg_right hn (exp_pos (-(2/5 : ℝ)*N)).le
  rw [← exp_add] at hg
  have he : (N : ℝ)*(3/20)+-(2/5)*N=-(N : ℝ)/4 := by ring
  rw [he] at hg
  have h := mul_le_mul_of_nonneg_left hg
    (show 0≤2*u*((N : ℝ)+1) by positivity)
  calc
    _ = (2*u*((N : ℝ)+1))*((2*u)^N*exp (-(2/5 : ℝ)*N)) := by
      simp only [radialCap,pow_succ,mul_pow]
      ring
    _ ≤ _ := h

private theorem lattice_ratios {N M X : ℕ} (hM : 1≤M) (_hMX : M≤X)
    (hlarge : exp ((N : ℝ)/2)≤M) (hwide : (X : ℝ)≤M*exp ((N : ℝ)/10)) :
    1/(M : ℝ)≤exp (-(2/5 : ℝ)*N) ∧
      ((X-M : ℕ) : ℝ)/(M : ℝ)^2≤exp (-(2/5 : ℝ)*N) := by
  have hm : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hi : 1/(M : ℝ)≤exp (-(N : ℝ)/2) := by
    rw [show -(N : ℝ)/2=-((N : ℝ)/2) by ring,exp_neg,← one_div]
    exact one_div_le_one_div_of_le (exp_pos _) hlarge
  have hlow := exp_le_exp.mpr (show -(N : ℝ)/2≤-(2/5 : ℝ)*N by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  refine ⟨hi.trans hlow,?_⟩
  have hsub : ((X-M : ℕ) : ℝ)≤X := by exact_mod_cast Nat.sub_le X M
  calc
    _ ≤ (X : ℝ)/(M : ℝ)^2 := div_le_div_of_nonneg_right hsub (sq_nonneg _)
    _ ≤ (M*exp ((N : ℝ)/10))/(M : ℝ)^2 :=
      div_le_div_of_nonneg_right hwide (sq_nonneg _)
    _ = exp ((N : ℝ)/10)*(1/(M : ℝ)) := by field_simp
    _ ≤ exp ((N : ℝ)/10)*exp (-(N : ℝ)/2) :=
      mul_le_mul_of_nonneg_left hi (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

private theorem rounded_endpoint_separation {N : ℕ} (hN : 32≤N) {c T : ℝ}
    (hc : c≤(4/3 : ℝ)*N) (hT : (39/20 : ℝ)*N-1≤T)
    {y : ℝ} (hy : 54≤|y|) :
    c<T ∧ 2*((N : ℝ)+1)≤‖phaseDamping y‖*(T-c) := by
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hv : (37/60 : ℝ)*N-1≤T-c := by linarith only [hc,hT]
  have hp : 0<T-c := by linarith only [hv,hn]
  have hz := mul_le_mul_of_nonneg_right (phaseDamping_norm hy) hp.le
  exact ⟨by linarith only [hp],by nlinarith only [hn,hv,hz]⟩

/-- Both terms tend to zero. The first is the SIGNED phase endpoint cost;
the second pays only lattice sampling and endpoint rounding. -/
def ownerSamplingBudget (u y : ℝ) (N : ℕ) : ℝ :=
  (2/27 : ℝ)*((N : ℝ)+1)*u*(199/50)*exp (-(N : ℝ)/200000)+
    2*u*((N : ℝ)+1)*(2*((N : ℝ)+1)+3+|y|)*exp (-(N : ℝ)/4)

/-- A quantitative signed bound on the ACTUAL integer cofactor weight sum.
The endpoint hypotheses specify the complete original total-log window,
up to only ordinary floor rounding. No count, squarefree or rough mask is
silently imposed on the smooth main; those belong to the comparison measure. -/
theorem normalized_ownerTest_sum_bound {N M X : ℕ} (hN : 32≤N) (hM : 1≤M) (hMX : M≤X)
    {c u y : ℝ} (hc : 1≤c) (hcN : c≤(4/3 : ℝ)*N) (hy : 54≤|y|)
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hlarge : exp ((N : ℝ)/2)≤M) (hwide : (X : ℝ)≤M*exp ((N : ℝ)/10))
    (hlo : |c+log M-(39/20 : ℝ)*N|≤1/(M : ℝ))
    (hhi : |c+log X-(203/100 : ℝ)*N|≤1/(M : ℝ)) :
    |u^(N+1)*(∑ n∈Finset.Ioc M X, ownerTest N c y n)|≤ownerSamplingBudget u y N := by
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hx : (1 : ℝ)≤X := hm.trans (by exact_mod_cast hMX)
  have him : 1/(M : ℝ)≤1 := (div_le_one (by linarith : (0 : ℝ)<M)).mpr hm
  have hTa : (39/20 : ℝ)*N-1≤c+log M := by
    have h := (abs_le.mp hlo).1
    linarith only [h,him]
  have hTb : (39/20 : ℝ)*N-1≤c+log X := by
    have h := (abs_le.mp hhi).1
    nlinarith only [h,him,Nat.cast_nonneg (α := ℝ) N]
  have hc0 : 0≤c := by linarith
  have hsepA := rounded_endpoint_separation hN hcN hTa hy
  have hsepB := rounded_endpoint_separation hN hcN hTb hy
  have hz54 := phaseDamping_norm hy
  have hz : phaseDamping y≠0 := norm_pos_iff.mp (by linarith only [hz54])
  have hd : 4/‖phaseDamping y‖≤(2/27 : ℝ) :=
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤4)
      (by norm_num : (0 : ℝ)<54) hz54).trans_eq (by norm_num)
  have hi := ownerPhase_interval_norm N hc0 hsepA.1 hsepB.1 hz
    (phaseDamping_re y) hsepA.2 hsepB.2
  have hcont : |∫ x : ℝ in (M : ℝ)..X, ownerTest N c y x|≤
      (2/27 : ℝ)*(radial N (c+log M)+radial N (c+log X)) := by
    rw [ownerTest_integral hN hM hMX hc y]
    exact ((Complex.abs_re_le_norm _).trans hi).trans
      (mul_le_mul_of_nonneg_right hd (add_nonneg
        (radial_bounds N (by linarith [log_nonneg hm])).1
        (radial_bounds N (by linarith [log_nonneg hx])).1))
  have hloR : radial N (c+log M)≤radial N ((39/20 : ℝ)*N)+radialCap N/(M : ℝ) := by
    have h := radial_lipschitz N (T := c+log M) (U := (39/20 : ℝ)*N)
      (by linarith [log_nonneg hm])
      (by positivity : (0 : ℝ)≤(39/20 : ℝ)*N)
    have hb := h.trans (mul_le_mul_of_nonneg_left hlo (radialCap_nonneg N))
    have hb' := le_abs_self (radial N (c+log M)-radial N ((39/20 : ℝ)*N))
    have hh := hb'.trans hb
    ring_nf at hh ⊢
    linarith only [hh]
  have hhiR : radial N (c+log X)≤radial N ((203/100 : ℝ)*N)+radialCap N/(M : ℝ) := by
    have h := radial_lipschitz N (T := c+log X) (U := (203/100 : ℝ)*N)
      (by linarith [log_nonneg hx])
      (by positivity : (0 : ℝ)≤(203/100 : ℝ)*N)
    have hb := h.trans (mul_le_mul_of_nonneg_left hhi (radialCap_nonneg N))
    have hb' := le_abs_self (radial N (c+log X)-radial N ((203/100 : ℝ)*N))
    have hh := hb'.trans hb
    ring_nf at hh ⊢
    linarith only [hh]
  have hdisc := ownerTest_lattice_error hN hM hMX hc y
  have hlohi := ZetaRieszTaggedOwnerComparison.normalized_core_endpoint_radial hu hU N
  have hrat := lattice_ratios hM hMX hlarge hwide
  have hcap := normalized_cap_fast hu hU N
  have hn : 0≤u^(N+1) := pow_nonneg hu _
  have hsmall1 : u^(N+1)*radialCap N/(M : ℝ)≤
      2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by
    have h := mul_le_mul_of_nonneg_left hrat.1 (mul_nonneg hn (radialCap_nonneg N))
    simpa only [mul_one,one_mul,div_eq_mul_inv,mul_assoc] using h.trans hcap
  have hsmall2 : u^(N+1)*radialCap N*((X-M : ℕ) : ℝ)/(M : ℝ)^2≤
      2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by
    have h := mul_le_mul_of_nonneg_left hrat.2 (mul_nonneg hn (radialCap_nonneg N))
    simpa only [mul_div_assoc,mul_assoc] using h.trans hcap
  have hsum : |u^(N+1)*(∑ n∈Finset.Ioc M X, ownerTest N c y n)|≤
      u^(N+1)*((2/27 : ℝ)*(radial N ((39/20 : ℝ)*N)+radial N ((203/100 : ℝ)*N)+
        2*radialCap N/(M : ℝ))+
        (X-M : ℕ)*(2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2) := by
    rw [abs_mul,abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_left ?_ hn
    have h := (abs_add_le
      ((∑ n∈Finset.Ioc M X, ownerTest N c y n)-∫ x : ℝ in (M : ℝ)..X, ownerTest N c y x)
      (∫ x : ℝ in (M : ℝ)..X, ownerTest N c y x)).trans (add_le_add hdisc hcont)
    have hh := mul_le_mul_of_nonneg_left (add_le_add hloR hhiR)
      (by norm_num : (0 : ℝ)≤2/27)
    simp only [sub_add_cancel] at h
    ring_nf at h hh ⊢
    linarith only [h,hh]
  apply hsum.trans
  unfold ownerSamplingBudget
  have hB : 0≤2*((N : ℝ)+1)+2+|y| := by positivity
  have hb := mul_le_mul_of_nonneg_left hsmall2 hB
  have he := mul_le_mul_of_nonneg_left (add_le_add hlohi.1 hlohi.2)
    (by norm_num : (0 : ℝ)≤2/27)
  have hr := mul_le_mul_of_nonneg_left hsmall1 (by norm_num : (0 : ℝ)≤4/27)
  have ht : 0≤2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by positivity
  ring_nf at hb he hr ht ⊢
  nlinarith only [hb,he,hr,ht]

/-- Exact natural endpoints of the original core's total-log window. -/
def coreFloor (N : ℕ) (c a : ℝ) : ℕ := ⌊exp (a*N-c)⌋₊

private theorem floor_exp_log {v : ℝ} (hv : 1≤v) :
    1≤⌊exp v⌋₊ ∧ exp v≤2*(⌊exp v⌋₊ : ℝ) ∧
      |log (⌊exp v⌋₊ : ℝ)-v|≤1/(⌊exp v⌋₊ : ℝ) := by
  have he : 1≤exp v := by linarith only [add_one_le_exp v,hv]
  have hm : 1≤⌊exp v⌋₊ := (Nat.one_le_floor_iff (exp v)).mpr he
  have hm1 : (1 : ℝ)≤⌊exp v⌋₊ := by exact_mod_cast hm
  have hm0 : (0 : ℝ)<⌊exp v⌋₊ := by linarith only [hm1]
  have hf := Nat.floor_le (exp_pos v).le
  have htail := (Nat.lt_floor_add_one (exp v)).le
  have hl : log (⌊exp v⌋₊ : ℝ)≤v := by
    simpa only [log_exp] using log_le_log hm0 hf
  have hb := log_le_sub_one_of_pos (div_pos (exp_pos v) hm0)
  rw [log_div (exp_pos v).ne' hm0.ne',log_exp] at hb
  have hfrac : exp v/(⌊exp v⌋₊ : ℝ)-1≤1/(⌊exp v⌋₊ : ℝ) := by
    apply (le_div_iff₀ hm0).mpr
    field_simp at ⊢
    nlinarith only [htail]
  refine ⟨hm,by linarith only [htail,hm1],?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hl),neg_sub]
  exact hb.trans hfrac

/-- The rounding and physical-size premises of the signed lattice bound
are proved for the LITERAL core, not supplied as approximation assumptions. -/
theorem coreFloor_geometry {N : ℕ} (hN : 64≤N) {c : ℝ} (hc : c≤(4/3 : ℝ)*N) :
    let M := coreFloor N c (39/20)
    let X := coreFloor N c (203/100)
    1≤M ∧ M≤X ∧ exp ((N : ℝ)/2)≤M ∧ (X : ℝ)≤M*exp ((N : ℝ)/10) ∧
      |c+log M-(39/20 : ℝ)*N|≤1/(M : ℝ) ∧
      |c+log X-(203/100 : ℝ)*N|≤1/(M : ℝ) := by
  dsimp only
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hvA : 1≤(39/20 : ℝ)*N-c := by linarith only [hc,hn]
  have hvB : 1≤(203/100 : ℝ)*N-c := by linarith only [hc,hn]
  have hA := floor_exp_log hvA
  have hB := floor_exp_log hvB
  have hMX : coreFloor N c (39/20)≤coreFloor N c (203/100) := by
    apply Nat.floor_mono
    apply exp_le_exp.mpr
    nlinarith only [hn]
  have hlarge : exp ((N : ℝ)/2)≤coreFloor N c (39/20) := by
    have hmargin : 2≤exp ((7/60 : ℝ)*N) := by
      have he := add_one_le_exp ((7/60 : ℝ)*N)
      linarith only [he,hn]
    have hmul := mul_le_mul_of_nonneg_left hmargin (exp_pos ((N : ℝ)/2)).le
    rw [← exp_add] at hmul
    have he : (N : ℝ)/2+(7/60)*N=(37/60 : ℝ)*N := by ring
    rw [he] at hmul
    have hpow : exp ((37/60 : ℝ)*N)≤exp ((39/20 : ℝ)*N-c) :=
      exp_le_exp.mpr (by linarith only [hc])
    have hbound := hmul.trans (hpow.trans hA.2.1)
    change _≤(⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)
    linarith only [hbound]
  have hwide : (coreFloor N c (203/100) : ℝ)≤
      coreFloor N c (39/20)*exp ((N : ℝ)/10) := by
    have hmargin : 2≤exp ((N : ℝ)/50) := by
      have he := add_one_le_exp ((N : ℝ)/50)
      linarith only [he,hn]
    calc
      _ ≤ exp ((203/100 : ℝ)*N-c) := Nat.floor_le (exp_pos _).le
      _ = exp ((39/20 : ℝ)*N-c)*exp ((2/25 : ℝ)*N) := by
        rw [← exp_add]; congr 1; ring
      _ ≤ (2*(coreFloor N c (39/20) : ℝ))*exp ((2/25 : ℝ)*N) :=
        mul_le_mul_of_nonneg_right hA.2.1 (exp_pos _).le
      _ ≤ (coreFloor N c (39/20) : ℝ)*(exp ((N : ℝ)/50)*exp ((2/25 : ℝ)*N)) := by
        have h := mul_le_mul_of_nonneg_left hmargin
          (show 0≤(coreFloor N c (39/20) : ℝ)*exp ((2/25 : ℝ)*N) by positivity)
        calc
          _ = ((coreFloor N c (39/20) : ℝ)*exp ((2/25 : ℝ)*N))*2 := by ring
          _ ≤ _ := h
          _ = _ := by ring
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hlo : |c+log (coreFloor N c (39/20))-(39/20 : ℝ)*N|≤
      1/(coreFloor N c (39/20) : ℝ) := by
    change |c+log (⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)-(39/20 : ℝ)*N|≤_
    change _≤1/(⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)
    convert hA.2.2 using 1
    congr 1
    ring
  have hhi : |c+log (coreFloor N c (203/100))-(203/100 : ℝ)*N|≤
      1/(coreFloor N c (39/20) : ℝ) := by
    have hm0 : (0 : ℝ)<⌊exp ((39/20 : ℝ)*N-c)⌋₊ := by
      exact_mod_cast (show 0<⌊exp ((39/20 : ℝ)*N-c)⌋₊ by omega)
    have hmx : (⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)≤⌊exp ((203/100 : ℝ)*N-c)⌋₊ := by
      exact_mod_cast hMX
    have h := hB.2.2.trans (one_div_le_one_div_of_le hm0 hmx)
    change |c+log (⌊exp ((203/100 : ℝ)*N-c)⌋₊ : ℝ)-(203/100 : ℝ)*N|≤_
    change _≤1/(⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)
    convert h using 1
    congr 1
    ring
  exact ⟨hA.1,hMX,hlarge,hwide,hlo,hhi⟩

theorem coreFloor_membership (N : ℕ) (c : ℝ) {n : ℕ} (hn : 0<n) :
    n∈Finset.Ioc (coreFloor N c (39/20)) (coreFloor N c (203/100)) ↔
      (39/20 : ℝ)*N<c+log n ∧ c+log n≤(203/100 : ℝ)*N := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  simp only [Finset.mem_Ioc,coreFloor]
  rw [Nat.floor_lt (exp_pos _).le,Nat.le_floor_iff (exp_pos _).le]
  rw [← exp_log hn0,exp_lt_exp,exp_le_exp]
  simp only [log_exp]
  constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨by linarith,by linarith⟩

/-- Complete literal integer core sum, with exact factorial owner weights,
moving physical endpoints and product phase. No exposed-zero assumption. -/
theorem normalized_core_lattice_sum_bound {N : ℕ} (hN : 64≤N) {c u y : ℝ}
    (hc : 1≤c) (hcN : c≤(4/3 : ℝ)*N) (hy : 54≤|y|) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    |u^(N+1)*∑ n∈Finset.Ioc (coreFloor N c (39/20)) (coreFloor N c (203/100)),
      ownerAmplitude N c n*cos (y*(c+log n))/(n : ℝ)|≤ownerSamplingBudget u y N := by
  obtain ⟨hM,hMX,hlarge,hwide,hlo,hhi⟩ := coreFloor_geometry hN hcN
  have h := normalized_ownerTest_sum_bound (by omega : 32≤N) hM hMX hc hcN hy hu hU
    hlarge hwide hlo hhi
  simpa only [ownerTest_nat] using h

theorem ownerSamplingBudget_tendsto (u y : ℝ) :
    Tendsto (ownerSamplingBudget u y) atTop (𝓝 0) := by
  have h0 : 0<exp (-(1/4 : ℝ)) := exp_pos _
  have h1 : exp (-(1/4 : ℝ))<1 := exp_lt_one_iff.mpr (by norm_num)
  have hlin := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 h0 h1
  have hquad := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2 h0 h1
  have h := (ownerPhase_core_budget_tendsto u).add
    ((hquad.const_mul (4*u)).add (hlin.const_mul (2*u*(3+|y|))))
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [pow_one,← exp_nat_mul]
  dsimp [ownerSamplingBudget]
  ring

/-- The saving survives any FIXED polynomial aggregation cost. -/
theorem ownerSamplingBudget_polynomial_tendsto (d : ℕ) (u y : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ)+1)^d*ownerSamplingBudget u y N) atTop (𝓝 0) := by
  have hf0 : 0<exp (-(1/200000 : ℝ)) := exp_pos _
  have hf1 : exp (-(1/200000 : ℝ))<1 := exp_lt_one_iff.mpr (by norm_num)
  have hl0 : 0<exp (-(1/4 : ℝ)) := exp_pos _
  have hl1 : exp (-(1/4 : ℝ))<1 := exp_lt_one_iff.mpr (by norm_num)
  have he := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    (d+1) hf0 hf1).const_mul ((2/27 : ℝ)*u*(199/50))
  have hq := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    (d+2) hl0 hl1).const_mul (4*u)
  have hs := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    (d+1) hl0 hl1).const_mul (2*u*(3+|y|))
  have h := he.add (hq.add hs)
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [← exp_nat_mul,pow_add,pow_one]
  dsimp [ownerSamplingBudget]
  ring

/-- A signed main limit, without a zero or prime-density hypothesis.
Only complete core windows are asserted, not arbitrary internal masks. -/
theorem tendsto_core_lattice_sum {u y : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (c : ℕ→ℝ) (hc : ∀ᶠ N in atTop, 1≤c N ∧ c N≤(4/3 : ℝ)*N) :
    Tendsto (fun N : ℕ => u^(N+1)*
      ∑ n∈Finset.Ioc (coreFloor N (c N) (39/20)) (coreFloor N (c N) (203/100)),
        ownerAmplitude N (c N) n*cos (y*(c N+log n))/(n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (ownerSamplingBudget_tendsto u y)
  filter_upwards [hc,eventually_ge_atTop (64 : ℕ)] with N hN h64
  simpa only [Real.norm_eq_abs] using
    normalized_core_lattice_sum_bound h64 hN.1 hN.2 hy hu hU

end RiemannGaussian.ZetaRieszOwnerLatticePhase
