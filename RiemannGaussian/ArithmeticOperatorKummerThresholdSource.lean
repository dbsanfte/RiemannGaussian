/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerThresholdAudit
import RiemannGaussian.ArithmeticOperatorFloorSourceAudit

/-!
# Source-sensitive balanced Kummer intersections still join to one scalar

The diagnostic uses the PRIME-LEG twist, not a cofactor-phased Gamma
evaluation. Its matched exponent is real beta, and its Mellin coefficient
is strictly positive. Exact two-scale density cancellation retains this
source. All these observations also hold for arbitrary column measures;
the joined threshold kernel supplies no independent prime estimate.

The power response is an actual convergent logarithmic-coordinate integral.
It is not asserted to be an asymptotic of a literal finite prime packet.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerThresholdSource
noncomputable section
open Complex MeasureTheory Set
open ArithmeticOperatorKummerThresholdAudit ArithmeticOperatorDilationAudit
open scoped BigOperators Classical

/-- The exact quotient interval selected by the consecutive balanced rows. -/
def quotientColour (r : ℕ) (x : ℝ) : ℝ :=
  if (r : ℝ)≤(r+1 : ℕ)*Int.fract x then 1 else 0

/-- No endpoint convention is changed in passing to logarithmic variables. -/
def logColour (r : ℕ) (t : ℝ) : ℝ := quotientColour r (Real.exp t)

theorem quotientColour_nonneg (r : ℕ) (x : ℝ) : 0≤quotientColour r x := by
  unfold quotientColour
  split_ifs <;> norm_num

theorem quotientColour_le_one (r : ℕ) (x : ℝ) : quotientColour r x≤1 := by
  unfold quotientColour
  split_ifs <;> norm_num

theorem intersection_eq_quotientColour {d : ℕ} (hd : 0<d) (r N : ℕ) :
    (intersection r N d : ℝ)=quotientColour r ((N : ℝ)/d) := by
  rw [intersection_eq_threshold hd]
  unfold quotientColour
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hd' : (0 : ℝ)<d := by exact_mod_cast hd
  have he : (r : ℝ)≤(r+1 : ℕ)*((N%d : ℕ) : ℝ)/d ↔
      r*d≤(r+1)*(N%d) := by
    rw [le_div_iff₀ hd']
    exact_mod_cast Iff.rfl
  simp only [←mul_div_assoc,he]
  split_ifs <;> norm_num

theorem measurable_logColour (r : ℕ) : Measurable (logColour r) := by
  unfold logColour quotientColour
  exact measurable_const.ite (measurableSet_le measurable_const
    (measurable_const.mul (Real.measurable_exp.fract))) measurable_const

/-- A uniform lower support boundary, safely away from its endpoint. -/
theorem logColour_eq_zero {r : ℕ} (hr : 0<r) {t : ℝ}
    (ht : t≤ -Real.log 3) : logColour r t=0 := by
  have hx0 := Real.exp_pos t
  have hx : Real.exp t≤1/3 := by
    calc
      _ ≤ Real.exp (-Real.log 3) := Real.exp_le_exp.mpr ht
      _ = 1/3 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  have hf := Int.fract_eq_self.mpr ⟨hx0.le,(by linarith : Real.exp t<1)⟩
  have hr' : (1 : ℝ)≤r := by exact_mod_cast hr
  have hbad : ¬ (r : ℝ)≤(r+1 : ℕ)*Int.fract (Real.exp t) := by
    rw [hf]
    push_cast
    nlinarith
  simp only [logColour,quotientColour,ite_eq_right hbad]

/-- The first quotient interval has positive length for every finite row count. -/
theorem logColour_eq_one {r : ℕ} (hr : 0<r) {t : ℝ}
    (ht : t ∈ Ioo (Real.log ((r : ℝ)/(r+1 : ℕ))) 0) : logColour r t=1 := by
  have hr' : (0 : ℝ)<r := by exact_mod_cast hr
  have ha : (0 : ℝ)<(r : ℝ)/(r+1 : ℕ) := by positivity
  have hx0 := Real.exp_pos t
  have hx1 : Real.exp t<1 := by simpa using Real.exp_lt_exp.mpr ht.2
  have hx : (r : ℝ)/(r+1 : ℕ)<Real.exp t := by
    simpa only [Real.exp_log ha] using Real.exp_lt_exp.mpr ht.1
  have hgood : (r : ℝ)≤(r+1 : ℕ)*Int.fract (Real.exp t) := by
    rw [Int.fract_eq_self.mpr ⟨hx0.le,hx1⟩]
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ)<(r+1 : ℕ))).mp hx
    linarith
  simp only [logColour,quotientColour,ite_eq_left hgood]

/-- Actual convergent Mellin observation of the entire joined carry mask. -/
def mellin (r : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s*t)*(logColour r t : ℂ)

/-- The real matched-exponent observation, with its actual positive density. -/
def realMellin (r : ℕ) (beta : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-beta*t)*logColour r t

theorem integrable_mellin {r : ℕ} (hr : 0<r) {s : ℂ} (hs : 0<s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s*t)*(logColour r t : ℂ)) := by
  have hi : Integrable ((Ioi (-Real.log 3)).indicator
      (fun t : ℝ => Real.exp (-s.re*t))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith : -s.re<0) (-Real.log 3))
  have hm : Measurable (fun t : ℝ => Complex.exp (-s*t)*(logColour r t : ℂ)) := by
    exact (by fun_prop : Measurable (fun t : ℝ => Complex.exp (-s*t))).mul
      (Complex.measurable_ofReal.comp (measurable_logColour r))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with t
  by_cases ht : -Real.log 3<t
  · rw [indicator_of_mem (show t ∈ Ioi (-Real.log 3) from ht),norm_mul,Complex.norm_exp,Complex.norm_real,
      Real.norm_of_nonneg (show 0≤logColour r t from quotientColour_nonneg _ _)]
    have he : (-s*(t : ℂ)).re = -s.re*t := by simp
    rw [he]
    exact (mul_le_mul_of_nonneg_left (quotientColour_le_one _ _) (Real.exp_pos _).le).trans_eq
      (mul_one _)
  · rw [logColour_eq_zero hr (le_of_not_gt ht),Complex.ofReal_zero,mul_zero,norm_zero,
      indicator_of_notMem (show t ∉ Ioi (-Real.log 3) from ht)]

theorem integrable_realMellin {r : ℕ} (hr : 0<r) {beta : ℝ} (hb : 0<beta) :
    Integrable (fun t : ℝ => Real.exp (-beta*t)*logColour r t) := by
  have hi := (integrable_mellin hr (s := (beta : ℂ)) (by simpa using hb)).re
  simpa only [RCLike.re_to_complex,Complex.mul_re,Complex.exp_re,Complex.neg_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.neg_im,
    neg_zero,zero_mul,add_zero,Real.cos_zero,mul_one] using hi

theorem mellin_real (r : ℕ) (beta : ℝ) :
    mellin r (beta : ℂ)=(realMellin r beta : ℂ) := by
  unfold mellin realMellin
  rw [←integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_exp]

/-- Prime-only twisting matches a real exponent; it must not be replaced by
the untwisted complex Gamma Mellin observation. -/
theorem realMellin_pos {r : ℕ} (hr : 0<r) {beta : ℝ} (hb : 0<beta) :
    0<realMellin r beta := by
  have ha : (0 : ℝ)<(r : ℝ)/(r+1 : ℕ) := by positivity
  have ha1 : (r : ℝ)/(r+1 : ℕ)<1 := by
    rw [div_lt_one (by positivity : (0 : ℝ)<(r+1 : ℕ))]
    push_cast
    linarith
  have hlog : Real.log ((r : ℝ)/(r+1 : ℕ))<0 := Real.log_neg ha ha1
  apply (integral_pos_iff_support_of_nonneg
    (fun t => mul_nonneg (Real.exp_pos _).le (quotientColour_nonneg _ _))
    (integrable_realMellin hr hb)).mpr
  have hs : Ioo (Real.log ((r : ℝ)/(r+1 : ℕ))) 0 ⊆
      Function.support (fun t : ℝ => Real.exp (-beta*t)*logColour r t) := by
    intro t ht
    rw [Function.mem_support,logColour_eq_one hr ht,mul_one]
    exact (Real.exp_pos _).ne'
  have hv : 0<volume (Ioo (Real.log ((r : ℝ)/(r+1 : ℕ))) 0) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hv.trans_le (measure_mono hs)

theorem mellin_real_ne_zero {r : ℕ} (hr : 0<r) {beta : ℝ} (hb : 0<beta) :
    mellin r (beta : ℂ)≠0 := by
  rw [mellin_real,Complex.ofReal_ne_zero]
  exact (realMellin_pos hr hb).ne'

/-- The full diagnostic observation in logarithmic coordinates, before
factoring its scale. The prime-leg twist is included in the exponent s. -/
def modeObservation (r : ℕ) (s : ℂ) (X : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (s*t)*(logColour r (Real.log X-t) : ℂ)

private theorem mode_integrand_eq (r : ℕ) (s : ℂ) (X t : ℝ) :
    Complex.exp (s*t)*(logColour r (Real.log X-t) : ℂ)=
      powerResponse s X*(Complex.exp (-s*((Real.log X-t : ℝ) : ℂ))*
        (logColour r (Real.log X-t) : ℂ)) := by
  unfold powerResponse
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem integrable_modeObservation {r : ℕ} (hr : 0<r) {s : ℂ}
    (hs : 0<s.re) (X : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(logColour r (Real.log X-t) : ℂ)) := by
  have hi := ((integrable_mellin hr hs).comp_sub_left (Real.log X)).const_mul
    (powerResponse s X)
  exact hi.congr (Filter.Eventually.of_forall (fun t => (mode_integrand_eq r s X t).symm))

/-- Exact power response of the threshold operator, not a local-residue
inference about any nonlinear actual prime statistic. -/
theorem modeObservation_eq (r : ℕ) (s : ℂ) (X : ℝ) :
    modeObservation r s X=powerResponse s X*mellin r s := by
  unfold modeObservation
  simp_rw [mode_integrand_eq]
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ => powerResponse s X*z)
    (integral_sub_left_eq_self
      (fun t : ℝ => Complex.exp (-s*t)*(logColour r t : ℂ)) volume (Real.log X))

/-- The lower physical endpoint x=1 is kept, not silently completed. -/
def physicalObservation (r : ℕ) (s : ℂ) (X : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (s*t)*(logColour r (Real.log X-t) : ℂ)

/-- Completing x in (0,1] costs only a uniform constant. It cannot
manufacture the retained power-scale diagnostic source. -/
theorem norm_mode_sub_physical_le {r : ℕ} (hr : 0<r) {s : ℂ}
    (hs : 0<s.re) (X : ℝ) :
    ‖modeObservation r s X-physicalObservation r s X‖≤1/s.re := by
  have hi := integrable_modeObservation hr hs X
  have he := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hi
  rw [compl_Iic] at he
  change (∫ t in Iic (0 : ℝ), Complex.exp (s*t)*(logColour r (Real.log X-t) : ℂ))+
    physicalObservation r s X=modeObservation r s X at he
  rw [←he,add_sub_cancel_right]
  have hb := integrableOn_exp_mul_Iic hs (0 : ℝ)
  calc
    _ ≤ ∫ t in Iic (0 : ℝ), ‖Complex.exp (s*t)*(logColour r (Real.log X-t) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Iic (0 : ℝ), Real.exp (s.re*t) := by
      apply integral_mono_ae (hi.integrableOn.norm) hb
      filter_upwards with t
      rw [norm_mul,Complex.norm_exp,Complex.norm_real,
        Real.norm_of_nonneg (show 0≤logColour r (Real.log X-t) from quotientColour_nonneg _ _)]
      have ht : (s*(t : ℂ)).re=s.re*t := by simp
      rw [ht]
      exact (mul_le_mul_of_nonneg_left (quotientColour_le_one _ _)
        (Real.exp_pos _).le).trans_eq (mul_one _)
    _ = _ := by rw [integral_exp_mul_Iic hs];simp

/-- Native positive integer endpoints use exactly the same profile. -/
theorem native_logColour_eq {N d : ℕ} (hN : 0<N) (hd : 0<d) (r : ℕ) :
    logColour r (Real.log N-Real.log d)=(intersection r N d : ℝ) := by
  rw [logColour,Real.exp_sub,Real.exp_log (by exact_mod_cast hN : (0 : ℝ)<N),
    Real.exp_log (by exact_mod_cast hd : (0 : ℝ)<d)]
  exact (intersection_eq_quotientColour hd r N).symm

/-- Twisting the diagnostic derivative -m*x^(beta+i*y-1) by x^(-i*y)
retains the matched real beta. No cofactor phase is introduced. -/
theorem prime_twist_matches_real_exponent (beta y t : ℝ) (m : ℂ) :
    (-m*Complex.exp (((beta : ℂ)+I*y)*t))*Complex.exp (-(I*y)*t)=
      -m*Complex.exp ((beta : ℂ)*t) := by
  rw [mul_assoc,←Complex.exp_add]
  congr 2
  ring

/-- A fixed positive row count detects the matched diagnostic source. -/
theorem matched_modeObservation_ne_zero {r : ℕ} (hr : 0<r)
    {beta : ℝ} (hb : 0<beta) (X : ℝ) {m : ℂ} (hm : m≠0) :
    -m*modeObservation r (beta : ℂ) X≠0 := by
  rw [modeObservation_eq]
  exact mul_ne_zero (neg_ne_zero.mpr hm)
    (mul_ne_zero (Complex.exp_ne_zero _) (mellin_real_ne_zero hr hb))

/-- One joint two-scale code; no separate norm payment is used. -/
def centeredObservation (r : ℕ) (p s : ℂ) (X : ℝ) : ℂ :=
  modeObservation r s (2*X)-Complex.exp (p*(Real.log 2 : ℂ))*modeObservation r s X

theorem centeredObservation_eq (r : ℕ) (p s : ℂ) (X : ℝ) :
    centeredObservation r p s X=
      (powerResponse s (2*X)-Complex.exp (p*(Real.log 2 : ℂ))*powerResponse s X)*mellin r s := by
  unfold centeredObservation
  rw [modeObservation_eq,modeObservation_eq]
  ring

/-- The full twisted continuous density mode cancels, not merely a
principal Ramanujan coefficient or an untwisted scalar average. -/
theorem centered_density_zero {X : ℝ} (hX : 0<X) (r : ℕ) (p : ℂ) :
    centeredObservation r p p X=0 := by
  rw [centeredObservation_eq,density_response_cancels hX,zero_mul]

/-- Both lower physical boundaries are explicit and uniformly bounded
after the joint density centering. This is not an actual prime estimate. -/
theorem norm_physical_center_sub_complete_le {r : ℕ} (hr : 0<r) {s : ℂ}
    (hs : 0<s.re) (p : ℂ) (X : ℝ) :
    ‖physicalObservation r s (2*X)-Complex.exp (p*(Real.log 2 : ℂ))*physicalObservation r s X-
      centeredObservation r p s X‖≤(1+‖Complex.exp (p*(Real.log 2 : ℂ))‖)/s.re := by
  have h1 := norm_mode_sub_physical_le hr hs (2*X)
  have h2 := norm_mode_sub_physical_le hr hs X
  rw [norm_sub_rev] at h1 h2
  have he : physicalObservation r s (2*X)-Complex.exp (p*(Real.log 2 : ℂ))*physicalObservation r s X-
      centeredObservation r p s X=
        (physicalObservation r s (2*X)-modeObservation r s (2*X))-
          Complex.exp (p*(Real.log 2 : ℂ))*(physicalObservation r s X-modeObservation r s X) := by
    unfold centeredObservation
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  calc
    _ ≤ 1/s.re+‖Complex.exp (p*(Real.log 2 : ℂ))‖*(1/s.re) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ = _ := by ring

/-- The density code keeps the matched zero source, for every height. -/
theorem centered_matched_source_ne_zero {r : ℕ} (hr : 0<r)
    {beta : ℝ} (hb : 0<beta) (hb1 : beta<1) (y : ℝ)
    {X : ℝ} (hX : 0<X) {m : ℂ} (hm : m≠0) :
    -m*centeredObservation r (1-I*y) (beta : ℂ) X≠0 := by
  rw [centeredObservation_eq]
  have hs := matched_source_response_nonzero hX
    (p := 1-I*y) (s := (beta : ℂ))
    (by simpa using (ne_of_gt hb1 : (1 : ℝ)≠beta)) (neg_ne_zero.mpr hm)
  rw [←mul_assoc]
  exact mul_ne_zero hs (mellin_real_ne_zero hr hb)

/-- The source-normalized diagnostic response is EXACTLY a fixed
nonzero coefficient. This is not a Tauberian claim for actual primes. -/
theorem scaled_centered_source_eq {X : ℝ} (hX : 0<X) (r : ℕ)
    (beta y : ℝ) (m : ℂ) :
    Complex.exp (-((beta : ℂ)*(Real.log X : ℂ)))*
      (-m*centeredObservation r (1-I*y) (beta : ℂ) X)=
        -m*(Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ))-
          Complex.exp ((1-I*y)*(Real.log 2 : ℂ)))*mellin r (beta : ℂ) := by
  rw [centeredObservation_eq,powerResponse_two_scale hX,←sub_mul,powerResponse]
  calc
    _ = (-m*(Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ))-
          Complex.exp ((1-I*y)*(Real.log 2 : ℂ)))*mellin r (beta : ℂ))*
        (Complex.exp (-((beta : ℂ)*(Real.log X : ℂ)))*
          Complex.exp ((beta : ℂ)*(Real.log X : ℂ))) := by ring
    _ = _ := by rw [←Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one]

/-- Literal two-scale kernel; all original phases may stay inside w. -/
def centeredKernel (r N d : ℕ) (p : ℂ) : ℂ :=
  (intersection r (2*N) d : ℂ)-Complex.exp (p*(Real.log 2 : ℂ))*(intersection r N d : ℂ)

theorem centered_native_join (D : Finset ℕ) (r N : ℕ) (p : ℂ) (w : ℕ → ℂ) :
    (∑ d ∈ D, w d*(intersection r (2*N) d : ℂ))-
      Complex.exp (p*(Real.log 2 : ℂ))*(∑ d ∈ D, w d*(intersection r N d : ℂ))=
        ∑ d ∈ D, w d*centeredKernel r N d p := by
  unfold centeredKernel
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Delta columns refute EVERY estimate inferred from this joined identity
alone unless the source-sensitive kernel has become identically zero. -/
theorem centered_bound_forall_weights_iff (D : Finset ℕ) (r N : ℕ) (p : ℂ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖∑ d ∈ D, w d*centeredKernel r N d p‖≤B) ↔
      0≤B ∧ ∀ d ∈ D, centeredKernel r N d p=0 :=
  ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff D _ B

end
end RiemannGaussian.ArithmeticOperatorKummerThresholdSource
