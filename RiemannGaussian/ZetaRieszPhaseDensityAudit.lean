/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianSimplePoleHeat

/-!
# A resonant density error survives the factorial observation

This is a test of a proposed inference from local density estimates to
opposite-phase cancellation, not a model asserted for the actual primes.
A real density perturbation, smaller than every fixed inverse power of
the log variable, can have any prescribed finite normalized source.
The original phase and the growing factorial radial window are retained.
No estimate for the literal Riesz carrier is inferred from this audit.
-/

namespace RiemannGaussian.ZetaRieszPhaseDensityAudit
noncomputable section
open Filter Topology MeasureTheory Set
open GaussianSimplePoleHeat

/-- The real relative counting error used only in this inference audit. -/
def densityError (a u y T : ℝ) : ℝ :=
  a * Real.exp (-(u-1/2)*T) * Real.cos (y*T)

/-- The density error is exponentially small before observing its phase. -/
theorem abs_densityError_le (a u y T : ℝ) :
    |densityError a u y T| ≤ |a| * Real.exp (-(u-1/2)*T) := by
  unfold densityError
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- Every fixed inverse-logarithmic accuracy permits this error. -/
theorem densityError_faster_than_inverse_power {u : ℝ} (hu : 1/2 < u)
    (a y : ℝ) (b : ℕ) :
    Tendsto (fun T : ℝ => T^b*densityError a u y T) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b : ℝ)
    (u-1/2) (by linarith)).const_mul |a|
  simp only [Real.rpow_natCast,mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hT _)]
  nlinarith [mul_le_mul_of_nonneg_left (abs_densityError_le a u y T)
    (pow_nonneg hT b)]

/-- The perturbed model density is eventually strictly positive, for
every fixed real amplitude; positivity of counts does not remove the bias. -/
theorem eventually_density_positive {u : ℝ} (hu : 1/2 < u) (a y : ℝ) :
    ∀ᶠ T : ℝ in atTop, 0 < 1+densityError a u y T := by
  have h := densityError_faster_than_inverse_power hu a y 0
  simp only [pow_zero,one_mul] at h
  filter_upwards [h.eventually_const_lt (by norm_num : (-1 : ℝ) < 0)] with T hT
  linarith

/-- An opposite-phase shift flips both the density bias and the observation.
Their product reinforces, up to the exact positive exponential attenuation. -/
theorem densityError_half_period (a u y T h : ℝ) (hh : y*h = Real.pi) :
    densityError a u y (T+h) =
      -Real.exp (-(u-1/2)*h)*densityError a u y T := by
  simp only [densityError,mul_add,hh,Real.cos_add_pi]
  rw [Real.exp_add]
  ring

/-- The real observed bias has a fixed sign: its two cosine factors
are correlated. Opposite-phase windows cannot cancel it by sign alone. -/
theorem densityError_observed (a u y T : ℝ) :
    densityError a u y T*Real.cos (y*T) =
      a*Real.exp (-(u-1/2)*T)*(Real.cos (y*T))^2 := by
  unfold densityError
  ring

/-- Exact reinforcement across a half-period, including the decaying
amplitude. This is not a free rotation of the arithmetic coefficients. -/
theorem observed_half_period (a u y T h : ℝ) (hh : y*h = Real.pi) :
    densityError a u y (T+h)*Real.cos (y*(T+h)) =
      Real.exp (-(u-1/2)*h)*(densityError a u y T*Real.cos (y*T)) := by
  rw [densityError_half_period a u y T h hh]
  simp only [mul_add,hh,Real.cos_add_pi]
  ring

/-- Exact demodulation before integration or taking any norm. -/
theorem cosine_phase (x : ℝ) :
    (Real.cos x : ℂ)*Complex.exp (-Complex.I*x) =
      (1+Complex.exp (-2*Complex.I*x))/2 := by
  have hc := Complex.two_cos (x : ℂ)
  rw [← Complex.ofReal_cos] at hc
  have h := congrArg (fun z : ℂ => z*Complex.exp (-Complex.I*x)) hc
  rw [add_mul,← Complex.exp_add,← Complex.exp_add] at h
  simp only [show (x : ℂ)*Complex.I+-Complex.I*x = 0 by ring,Complex.exp_zero] at h
  rw [show -(x : ℂ)*Complex.I+-Complex.I*x = -2*Complex.I*x by ring] at h
  linear_combination h/2

/-- The exact relative-density error times the original factorial kernel. -/
theorem error_atom_eq (N : ℕ) (a u y T : ℝ) :
    (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T =
      (a/2 : ℂ)*(laplace N (u : ℂ) T+laplace N ((u : ℂ)+2*Complex.I*y) T) := by
  have he : (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T =
      (a : ℂ)*laplace N (u : ℂ) T*
        ((Real.cos (y*T) : ℂ)*Complex.exp (-Complex.I*(y*T))) := by
    simp only [densityError,laplace,Complex.ofReal_mul,Complex.ofReal_exp,
      Complex.ofReal_neg,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_ofNat]
    rw [show -(1/2+Complex.I*(y : ℂ))*(T : ℂ) =
      -(1/2 : ℂ)*T+-Complex.I*(y*T) by ring,Complex.exp_add]
    rw [show -(u : ℂ)*T = -((u : ℂ)-1/2)*T+(-(1/2 : ℂ)*T) by ring,Complex.exp_add]
    ring
  have hc := cosine_phase (y*T)
  simp only [Complex.ofReal_mul] at hc
  rw [he,hc]
  unfold laplace
  rw [show -((u : ℂ)+2*Complex.I*y)*T = -(u : ℂ)*T+-2*Complex.I*(y*T) by ring,
    Complex.exp_add]
  ring

/-- The perturbation has an exact finite-order normalized source. -/
theorem integral_error (N : ℕ) {u : ℝ} (hu : 0 < u) (a y : ℝ) :
    (u : ℂ)^(N+1)*(∫ T : ℝ in Ioi 0,
      (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T) =
      (a/2 : ℂ)*(1+((u : ℂ)/((u : ℂ)+2*Complex.I*y))^(N+1)) := by
  simp_rw [error_atom_eq]
  rw [integral_const_mul,integral_add
    (integrableOn_laplace N (by simpa using hu))
    (integrableOn_laplace N (by simpa using hu)),
    integral_laplace N (by simpa using hu),integral_laplace N (by simpa using hu)]
  have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hone : (u : ℂ)^(N+1)*(u : ℂ)⁻¹^(N+1) = 1 := by
    rw [← mul_pow,mul_inv_cancel₀ hne,one_pow]
  simp only [div_eq_mul_inv]
  linear_combination (a/2 : ℂ)*hone

/-- The doubled-frequency alias decays; the constant resonant term does not. -/
theorem alias_norm_lt_one {u y : ℝ} (hu : 0 < u) (hy : y ≠ 0) :
    ‖(u : ℂ)/((u : ℂ)+2*Complex.I*y)‖ < 1 := by
  have hz : (u : ℂ)+2*Complex.I*y ≠ 0 := by
    intro hz
    have := congrArg Complex.re hz
    simp at this
    linarith
  rw [norm_div,div_lt_one (norm_pos_iff.mpr hz),Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hu]
  apply (sq_lt_sq₀ hu.le (norm_nonneg _)).mp
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  simp
  nlinarith [sq_pos_of_ne_zero hy]

/-- Any fixed real source can survive despite an arbitrarily accurate
inverse-logarithmic density approximation and the full oscillating phase. -/
theorem tendsto_error_source {u y : ℝ} (hu : 0 < u) (hy : y ≠ 0) (a : ℝ) :
    Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*(∫ T : ℝ in Ioi 0,
      (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T))
      atTop (𝓝 (a/2 : ℂ)) := by
  simp_rw [integral_error _ hu]
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (alias_norm_lt_one hu hy)).comp
    (tendsto_add_atTop_nat 1)
  simpa using (ht.const_add 1).const_mul (a/2 : ℂ)

private theorem gammaWeight_mul (N : ℕ) {u : ℝ} (hu : 0 < u) (T : ℝ) :
    gammaWeight N u T*T = ((N : ℝ)+1)/u*gammaWeight (N+1) u T := by
  simp only [gammaWeight,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

private theorem integrable_gamma_center (N : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun T : ℝ => gammaWeight N u T*(T-(N : ℝ)/u)^2) (Ioi 0) := by
  have hi : IntegrableOn (fun T : ℝ => gammaWeight N u T*T) (Ioi 0) := by
    simp_rw [gammaWeight_mul N hu]
    exact (integrableOn_gammaWeight (N+1) hu).const_mul _
  have hj := ((integrableOn_gammaWeight_mul_sq N hu).sub
    (hi.const_mul (2*(N : ℝ)/u))).add
    ((integrableOn_gammaWeight N hu).const_mul (((N : ℝ)/u)^2))
  apply hj.congr
  filter_upwards with T
  dsimp
  ring

/-- Exact second moment around the moving saddle `N/u`. -/
theorem integral_gamma_center (N : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ T : ℝ in Ioi 0, gammaWeight N u T*(T-(N : ℝ)/u)^2) =
      ((N : ℝ)+2)/u^2 := by
  have hi : IntegrableOn (fun T : ℝ => gammaWeight N u T*T) (Ioi 0) := by
    simp_rw [gammaWeight_mul N hu]
    exact (integrableOn_gammaWeight (N+1) hu).const_mul _
  have hf : (fun T : ℝ => gammaWeight N u T*(T-(N : ℝ)/u)^2) =
      (fun T => gammaWeight N u T*T^2-(2*(N : ℝ)/u)*(gammaWeight N u T*T)+
        ((N : ℝ)/u)^2*gammaWeight N u T) := by ext T; ring
  have hs : IntegrableOn (fun T : ℝ => gammaWeight N u T*T^2-
      (2*(N : ℝ)/u)*(gammaWeight N u T*T)) (Ioi 0) :=
    (integrableOn_gammaWeight_mul_sq N hu).sub (hi.const_mul _)
  rw [hf,integral_add hs
    ((integrableOn_gammaWeight N hu).const_mul _),
    integral_sub (integrableOn_gammaWeight_mul_sq N hu) (hi.const_mul _),
    integral_const_mul,integral_const_mul,integral_gammaWeight_mul_sq N hu,
    integral_gammaWeight N hu]
  simp_rw [gammaWeight_mul N hu]
  rw [integral_const_mul,integral_gammaWeight (N+1) hu]
  simp only [secondMoment,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_one]
  field_simp
  ring

/-- The literal core endpoints contain the critical-error saddle with
a fixed rational margin, uniformly over the restricted radius interval. -/
theorem outside_core_gap {u T : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ 10001/20000)
    {N : ℕ} (hT : T ∉ Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N)) :
    (N : ℝ)^2/10000 ≤ (T-(N : ℝ)/u)^2 := by
  have hu0 : 0 < u := by linarith
  have hlo : (199/100 : ℝ) ≤ 1/u := (le_div_iff₀ hu0).mpr (by nlinarith)
  have hhi : 1/u ≤ (2 : ℝ) := (div_le_iff₀ hu0).mpr (by linarith)
  have hln := mul_le_mul_of_nonneg_left hlo (show (0 : ℝ) ≤ N by positivity)
  have hun := mul_le_mul_of_nonneg_left hhi (show (0 : ℝ) ≤ N by positivity)
  simp only [mul_one_div] at hln hun
  have hg : (N : ℝ)/100 ≤ |T-(N : ℝ)/u| := by
    apply le_abs.mpr
    simp only [mem_Ioc,not_and_or,not_lt,not_le] at hT
    rcases hT with hl | hh
    · right
      nlinarith only [hln,hl,Nat.cast_nonneg (α := ℝ) N]
    · left
      nlinarith only [hun,hh,Nat.cast_nonneg (α := ℝ) N]
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)/100) hg 2
  norm_num [sq_abs,div_pow] at hs ⊢
  exact hs

/-- The actual core window retains asymptotically all of the demodulated
error. This bound concerns the audit's positive gamma density only. -/
theorem gamma_outside_core_bound {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ 10001/20000)
    {N : ℕ} (hN : 0 < N) :
    (∫ T : ℝ in Ioi 0 \ Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
      gammaWeight N u T) ≤ 10000*((N : ℝ)+2)/(u^2*(N : ℝ)^2) := by
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := (integrableOn_gammaWeight N hu0).mono_set
    (sdiff_subset : Ioi (0 : ℝ) \ Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N) ⊆ Ioi 0)
  have hj : IntegrableOn (fun T : ℝ => (10000/(N : ℝ)^2)*
      (gammaWeight N u T*(T-(N : ℝ)/u)^2)) (Ioi 0) :=
    (integrable_gamma_center N hu0).const_mul _
  have hle : (∫ T : ℝ in Ioi 0 \ Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
      gammaWeight N u T) ≤
      ∫ T : ℝ in Ioi 0, (10000/(N : ℝ)^2)*
        (gammaWeight N u T*(T-(N : ℝ)/u)^2) := by
    apply (integral_mono_ae hi (hj.mono_set sdiff_subset) ?_).trans
      (setIntegral_mono_set hj ?_ (Filter.Eventually.of_forall fun _ h => h.1))
    · filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Ioc)] with T hT
      have hg := gammaWeight_nonneg N hu0.le (le_of_lt hT.1)
      have hs := outside_core_gap hu hU hT.2
      have hh : 1 ≤ (10000/(N : ℝ)^2)*(T-(N : ℝ)/u)^2 := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (sq_pos_of_pos hn0)).mpr
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hh hg]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      exact mul_nonneg (by positivity)
        (mul_nonneg (gammaWeight_nonneg N hu0.le hT.le) (sq_nonneg _))
  rw [integral_const_mul,integral_gamma_center N hu0] at hle
  convert hle using 1
  ring

/-- The audit's normalized density-error atom is dominated by its own
unit-mass gamma weight, not by the growing absolute carrier envelope. -/
theorem norm_error_atom_le (N : ℕ) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    (a y : ℝ) :
    ‖(u : ℂ)^(N+1)*((densityError a u y T : ℂ)*
      laplace N (1/2+Complex.I*y) T)‖ ≤ |a| * gammaWeight N u T := by
  have hl : ‖laplace N (1/2+Complex.I*y) T‖ =
      (T^N/N.factorial)*Real.exp (-T/2) := by
    have hx : (-(1/2+Complex.I*(y : ℂ))*(T : ℂ)).re = -T/2 := by
      simp
      ring
    simp only [laplace,norm_mul,norm_div,norm_pow,Complex.norm_exp,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT,Complex.norm_natCast,hx]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,hl]
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (abs_densityError_le a u y T)
      (show 0 ≤ (T^N/N.factorial)*Real.exp (-T/2) by positivity))
    (pow_nonneg hu (N+1))
  refine hb.trans_eq ?_
  unfold gammaWeight
  rw [show -u*T = -(u-1/2)*T+(-T/2) by ring,Real.exp_add]
  ring

private theorem integrable_error (N : ℕ) {u : ℝ} (hu : 0 < u) (a y : ℝ) :
    IntegrableOn (fun T : ℝ => (densityError a u y T : ℂ)*
      laplace N (1/2+Complex.I*y) T) (Ioi 0) := by
  simp_rw [error_atom_eq]
  exact ((integrableOn_laplace N (by simpa using hu)).add
    (integrableOn_laplace N (by simpa using hu))).const_mul _

/-- Both exterior boundaries of the original core window are paid for
the resonant error itself. This does not transport a density model to primes. -/
theorem norm_full_sub_core_error_le {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ 10001/20000) {N : ℕ} (hN : 0 < N) (a y : ℝ) :
    ‖(u : ℂ)^(N+1)*((∫ T : ℝ in Ioi 0,
        (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T)-
      (∫ T : ℝ in Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
        (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T))‖ ≤
      |a| * (10000*((N : ℝ)+2)/(u^2*(N : ℝ)^2)) := by
  have hu0 : 0 < u := by linarith
  have hc : Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N) ⊆ Ioi (0 : ℝ) := by
    intro T hT
    exact lt_of_le_of_lt (by positivity) hT.1
  rw [← setIntegral_sdiff measurableSet_Ioc (integrable_error N hu0 a y) hc,
    ← integral_const_mul]
  have hi : IntegrableOn (fun T : ℝ => |a| * gammaWeight N u T)
      (Ioi 0 \ Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N)) :=
    ((integrableOn_gammaWeight N hu0).mono_set sdiff_subset).const_mul _
  have hn := norm_integral_le_of_norm_le hi (by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Ioc)] with T hT
    exact norm_error_atom_le N hu0.le hT.1.le a y)
  refine hn.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (gamma_outside_core_bound hu hU hN) (abs_nonneg a)

/-- The paid exterior error tends to zero with the actual growing core. -/
theorem tendsto_full_sub_core_error {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ 10001/20000) (a y : ℝ) :
    Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*((∫ T : ℝ in Ioi 0,
        (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T)-
      (∫ T : ℝ in Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
        (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T))) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb := ((ht.add ((ht.pow 2).const_mul 2)).const_mul (10000/u^2)).const_mul |a|
  simp only [zero_pow (by omega : (2 : ℕ) ≠ 0),mul_zero,add_zero] at hb
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  refine (norm_full_sub_core_error_le hu hU (by omega) a y).trans_eq ?_
  field_simp

/-- The resonant source survives with both literal radial endpoints,
the exact factorial and the full complex phase. All inverse-logarithmic
density accuracies therefore still leave this particular mechanism open. -/
theorem tendsto_core_error_source {u y : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ 10001/20000) (hy : y ≠ 0) (a : ℝ) :
    Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*
      (∫ T : ℝ in Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
        (densityError a u y T : ℂ)*laplace N (1/2+Complex.I*y) T))
      atTop (𝓝 (a/2 : ℂ)) := by
  have h := (tendsto_error_source (by linarith : 0 < u) hy a).sub
    (tendsto_full_sub_core_error hu hU a y)
  simp only [sub_zero] at h
  convert h using 1
  ext N
  ring

/-- A permitted density-error model can shift the observed core below
the simple-zero floor. This is not an assertion about the actual prime sum. -/
theorem eventually_core_error_below_floor {u y : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ 10001/20000) (hy : y ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      ((u : ℂ)^(N+1)*
        (∫ T : ℝ in Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
          (densityError (-1/5) u y T : ℂ)*laplace N (1/2+Complex.I*y) T)).re < -79/1000 := by
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_core_error_source hu hU hy (-1/5))
  exact h.eventually_lt_const (by norm_num)

/-- An eventually positive density model also permits an observed error
above the multiple-zero ceiling. The same missing correlation affects both
directions of the multiplicity-safe criterion. -/
theorem eventually_core_error_above_ceiling {u y : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ 10001/20000) (hy : y ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      (3/2 : ℝ) < ((u : ℂ)^(N+1)*
        (∫ T : ℝ in Ioc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
          (densityError 4 u y T : ℂ)*laplace N (1/2+Complex.I*y) T)).re := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_core_error_source hu hU hy 4)
  exact h.eventually_const_lt (by norm_num)

end
end RiemannGaussian.ZetaRieszPhaseDensityAudit
