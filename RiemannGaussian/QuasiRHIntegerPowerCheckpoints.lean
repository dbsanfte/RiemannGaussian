import RiemannGaussian.QuasiRHPrimeWindowBounds

/-! # Sampling the prime discrepancy at integer powers

The checkpoint in logarithmic time is the logarithm of an integer kth power.
The zero-tail estimate controls the loss of the positive Gaussian average.
-/

namespace RiemannGaussian.QuasiRHIntegerPowerCheckpoints
noncomputable section
open Filter Topology MeasureTheory ProbabilityTheory
open QuasiRHPrimePrimitiveHeat QuasiRHPrimeWindowBounds

/-- The logarithm of the last integer kth power at or below the cutoff. -/
def powerTime (k : ℕ) (u : ℝ) : ℝ := k * Real.log ⌊Real.exp (u/k)⌋₊

/-- The Gaussian probability weights attached to the kth-power checkpoints
multiply the positive normalized prime discrepancy at those checkpoints. -/
def powerWindow (k : ℕ) (T : ℝ) : ℝ :=
  ∫ u in Set.Icc (T/4) (4*T), max (discrepancy (powerTime k u)).re 0 ∂gaussianReal T (2*T).toNNReal

/-- The physical cutoff defining the sampled prime sum is an integer power. -/
theorem exp_powerTime (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (powerTime k u) = (⌊Real.exp (u/k)⌋₊ : ℝ)^k := by
  have hm : 1 ≤ ⌊Real.exp (u/k)⌋₊ := (Nat.le_floor_iff (Real.exp_pos _).le).mpr (by
    simpa using Real.one_le_exp_iff.mpr (div_nonneg hu (Nat.cast_nonneg k)))
  rw [powerTime, Real.exp_nat_mul,Real.exp_log (by exact_mod_cast (show 0 < ⌊Real.exp (u/k)⌋₊ by omega))]

/-- The logarithmic width of a power cell decreases exponentially. -/
theorem powerTime_gap {k : ℕ} (hk : 0 < k) {u : ℝ} (hr : 2 ≤ Real.exp (u/k)) :
    0 ≤ powerTime k u ∧ powerTime k u ≤ u ∧
      u-powerTime k u ≤ 2*k/Real.exp (u/k) := by
  let r := Real.exp (u/k)
  let m := ⌊r⌋₊
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hr' : 0 < r := Real.exp_pos _
  have h1 : 1 ≤ m := (Nat.le_floor_iff hr'.le).mpr (by norm_num; linarith)
  have h1' : (1:ℝ) ≤ m := by exact_mod_cast h1
  have hm : 0 < (m:ℝ) := by linarith
  have hmr : (m:ℝ) ≤ r := Nat.floor_le hr'.le
  have hrm : r < (m:ℝ)+1 := Nat.lt_floor_add_one r
  have heq : (k:ℝ)*Real.log r = u := by
    rw [show Real.log r = u/k by exact Real.log_exp _]
    field_simp
  change 0 ≤ (k:ℝ)*Real.log m ∧ (k:ℝ)*Real.log m ≤ u ∧ u-(k:ℝ)*Real.log m ≤ 2*k/r
  refine ⟨mul_nonneg hk'.le (Real.log_nonneg h1'),heq ▸ mul_le_mul_of_nonneg_left
    (Real.log_le_log hm hmr) hk'.le,?_⟩
  have hl := Real.log_le_sub_one_of_pos (div_pos hr' hm)
  rw [Real.log_div hr'.ne' hm.ne'] at hl
  have hsmall : r/(m:ℝ)-1 ≤ 1/m := by
    apply (le_div_iff₀ hm).mpr
    field_simp
    linarith
  have hdiv : 1/(m:ℝ) ≤ 2/r := (div_le_div_iff₀ hm hr').mpr (by linarith)
  calc
    _ = (k:ℝ)*(Real.log r-Real.log m) := by rw [mul_sub,heq]
    _ ≤ (k:ℝ)*(2/r) := mul_le_mul_of_nonneg_left (hl.trans (hsmall.trans hdiv)) hk'.le
    _ = _ := by ring

/-- Sampling at kth powers saves a fixed positive amount in the exponential
rate of the interpolation error for every upper bound on the zero real parts. -/
theorem eventually_power_error {k : ℕ} (hk : 0 < k) {B : ℝ} (hhalf : 1/2 ≤ B)
    (hB : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∀ᶠ u : ℝ in atTop, ‖discrepancy u-discrepancy (powerTime k u)‖ ≤
      2*Real.exp 1*Real.exp (-u/2) +
      (8*k+24)*Real.exp ((B-1/2-1/(4*k))*u) := by
  have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ht : Tendsto (fun u : ℝ => Real.exp (u/(4*k))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by positivity : 0 < (4:ℝ)*k))
  filter_upwards [ht.eventually_ge_atTop (4*k)] with u hu
  let z := u/(4*k)
  let A := Real.exp z
  let H := A^2
  let v := powerTime k u
  have hA : 4*(k:ℝ) ≤ A := hu
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := Real.exp_pos _
  have hAH : A ≤ H := by dsimp [H]; nlinarith [mul_nonneg hA0.le (sub_nonneg.mpr hA1)]
  have hH : 2 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hr : Real.exp (u/k) = H^2 := by
    dsimp only [H,A,z]
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    ring
  have hg := powerTime_gap hk (u := u) (by rw [hr]; nlinarith)
  change 0 ≤ v ∧ v ≤ u ∧ u-v ≤ _ at hg
  rw [hr] at hg
  have hL : (1+H)*(u-v) ≤ 4*k/H := by
    apply (mul_le_mul_of_nonneg_left hg.2.2 (by linarith : 0 ≤ 1+H)).trans
    field_simp
    nlinarith [mul_nonneg hk'.le (show 0 ≤ H-1 by linarith)]
  have hone : 4*k/H ≤ 1 := (div_le_one hH0).mpr (hA.trans hAH)
  have hstep := discrepancy_increment hB hhalf hH hg.1 hg.2.1 (hL.trans hone)
  have hv : u-v ≤ 1 := by nlinarith [mul_nonneg hH0.le (sub_nonneg.mpr hg.2.1), hL.trans hone]
  have hvexp : Real.exp (-v/2) ≤ Real.exp 1*Real.exp (-u/2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlog : Real.log H = 2*z := by simp [H,A,Real.log_pow]
  have hz : z ≤ A := by linarith [Real.add_one_le_exp z]
  have hsmall : (463/10000)*(1+H)*(u-v)+(8+2*Real.log H)/H ≤ (4*k+12)/A := by
    rw [mul_assoc, hlog]
    have hcoef := mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ) ≤ 463/10000)
    apply (add_le_add hcoef le_rfl).trans
    dsimp only [H]
    field_simp
    nlinarith [mul_nonneg hk'.le (sub_nonneg.mpr hA1)]
  have hfactor : Real.exp ((B-1/2-1/(4*k))*u) = Real.exp ((B-1/2)*u)/A := by
    dsimp only [A,z]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hfactor]
  apply hstep.trans
  have hh := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 2*Real.exp ((B-1/2)*u))
  exact (add_le_add (mul_le_mul_of_nonneg_left hvexp (by norm_num : (0:ℝ) ≤ 2)) hh).trans_eq (by ring)

/-- An explicit bound for the difference of the two positive Gaussian windows.
In its second exponential the spectral abscissa is reduced by one fourth
of the reciprocal of the checkpoint degree. -/
theorem eventually_powerWindow_error {k : ℕ} (hk : 0 < k) {B : ℝ} (hhalf : 1/2 ≤ B)
    (hB : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∀ᶠ T : ℝ in atTop, |windowPositiveAverage T-powerWindow k T| ≤
      2*Real.exp 1*Real.exp (-(1/4:ℝ)*T) +
      (8*k+24)*Real.exp (((B-1/(4*k))^2-1/4)*T) := by
  obtain ⟨U,hU⟩ := eventually_atTop.mp (eventually_power_error hk hhalf hB)
  filter_upwards [eventually_ge_atTop (4*U),eventually_ge_atTop (0:ℝ)] with T hT hT0
  let μ := gaussianReal T (2*T).toNNReal
  let s := Set.Icc (T/4) (4*T)
  let f (u : ℝ) := max (discrepancy u).re 0
  let g (u : ℝ) := f (powerTime k u)
  let d : ℝ := B-1/2-1/(4*k)
  let P (u : ℝ) := 2*Real.exp 1*Real.exp (-(1/2:ℝ)*u) + (8*k+24)*Real.exp (d*u)
  have hi : Integrable P μ := ((integrable_exp_mul_gaussianReal (-(1/2:ℝ))).const_mul _).add
    ((integrable_exp_mul_gaussianReal d).const_mul _)
  have hnon : ∀ u, 0 ≤ P u := fun u => by dsimp [P]; positivity
  have hpoint : ∀ᵐ u ∂μ.restrict s, ‖f u-g u‖ ≤ P u := by
    filter_upwards [ae_restrict_mem (μ := μ) (s := s) measurableSet_Icc] with u hu
    have hlu : T/4 ≤ u := hu.1
    have hh := hU u (by linarith)
    have hcl := abs_max_sub_max_le_abs (discrepancy u).re (discrepancy (powerTime k u)).re 0
    rw [← Complex.sub_re] at hcl
    apply (hcl.trans (Complex.abs_re_le_norm _)).trans
    simpa only [P,d,show -u/2 = -(1/2:ℝ)*u by ring] using hh
  have hfi : Integrable f (μ.restrict s) := (positive_integrable T).restrict
  have hgm : Measurable g := by
    have hm : Measurable (fun u : ℝ => ⌊Real.exp (u/k)⌋₊) := by fun_prop
    exact (measurable_of_countable (fun n : ℕ => f (k*Real.log n))).comp hm
  have hdiff : Integrable (fun u => f u-g u) (μ.restrict s) :=
    hi.restrict.mono' (hfi.aestronglyMeasurable.sub hgm.aestronglyMeasurable) hpoint
  have hgi : Integrable g (μ.restrict s) := by
    convert hfi.sub hdiff using 1
    ext u
    simp
  change |(∫ u in s, f u ∂μ)-(∫ u in s, g u ∂μ)| ≤ _
  rw [← integral_sub hfi hgi,← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le hi.restrict hpoint).trans
    ((setIntegral_le_integral hi (Eventually.of_forall hnon)).trans_eq _)
  dsimp only [P,μ]
  rw [integral_add ((integrable_exp_mul_gaussianReal (-(1/2:ℝ))).const_mul _)
    ((integrable_exp_mul_gaussianReal d).const_mul _),integral_const_mul,integral_const_mul,
    scaled_exp_mean T _ hT0,scaled_exp_mean T _ hT0]
  dsimp only [d]
  ring_nf


private theorem exp_vanish {a : ℝ} (ha : a < 0) :
    Tendsto (fun T : ℝ => Real.exp (a*T)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg ha)

/-- An off-line zero forces divergence even when the only arithmetic
observations are taken at integer kth powers, for any fixed positive k. -/
theorem powerWindow_tendsto_of_right_zero {k : ℕ} (hk : 0 < k) (ρ₀ : NontrivialZetaZero)
    (hρ₀ : 1/2 < ρ₀.1.re) : Tendsto (powerWindow k) atTop atTop := by
  let S := Set.range (fun ρ : NontrivialZetaZero => ρ.1.re)
  let B := sSup S
  have hbdd : BddAbove S := ⟨1,fun _ ⟨ρ,he⟩ => he ▸ ρ.re_lt_one.le⟩
  have hB (ρ : NontrivialZetaZero) : ρ.1.re ≤ B := le_csSup hbdd ⟨ρ,rfl⟩
  have hhalf := hρ₀.trans_le (hB ρ₀)
  let δ : ℝ := 1/(4*k)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1/4 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [show (1:ℝ) ≤ k by exact_mod_cast hk])
  obtain ⟨_, ⟨ρ,rfl⟩, hρ⟩ := exists_lt_of_lt_csSup (s := S) ⟨ρ₀.1.re,ρ₀,rfl⟩
    (show max (1/2) (B-δ) < B from max_lt hhalf (by linarith))
  let p := ρ.1.re^2-1/4
  let q := (B-δ)^2-1/4
  have hρ₁ := (max_lt_iff.mp hρ).1
  have hρ₂ := (max_lt_iff.mp hρ).2
  have hp : 0 < p := by dsimp [p]; nlinarith [mul_pos (sub_pos.mpr hρ₁) ρ.zero_lt_re]
  have hq : q < p := by
    dsimp [p,q]
    nlinarith [mul_pos (sub_pos.mpr hρ₂) (show 0 < ρ.1.re+(B-δ) by linarith)]
  obtain ⟨C,hC,hc⟩ := exponential_le_absoluteAverage ρ
  have herr := eventually_powerWindow_error hk hhalf.le hB
  have hs : Tendsto (fun T => (response T 0).re) atTop (𝓝 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp tendsto_signed_response_zero
  apply tendsto_atTop.2
  intro K
  let A : ℝ := 8*k+24
  have hn : Tendsto (fun T : ℝ => (C*(11+2*K+4*Real.exp 1))*Real.exp ((-p)*T) +
      (2*C*A)*Real.exp ((q-p)*T)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((exp_vanish (neg_lt_zero.mpr hp)).const_mul (C*(11+2*K+4*Real.exp 1))).add
        ((exp_vanish (sub_neg.mpr hq)).const_mul (2*C*A))
  filter_upwards [hc,herr,(tendsto_order.mp hn).2 1 zero_lt_one,(tendsto_order.mp hs).1 (-1) (by norm_num),
    eventually_ge_atTop (0:ℝ)] with T hex herr hlow hsign ht
  by_contra! hsmall
  have hsep := (window_positive_error ht).2
  have hpos := twice_positiveAverage T
  have htt : positiveAverage T-windowPositiveAverage T ≤ 4 := by
    linarith [Real.exp_le_one_iff.mpr (show -(3/64:ℝ)*T ≤ 0 by linarith),
      Real.exp_le_one_iff.mpr (show -(3/4:ℝ)*T ≤ 0 by linarith)]
  change |windowPositiveAverage T-powerWindow k T| ≤ _ + A*Real.exp (q*T) at herr
  have hconst := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
    (show -(1/4:ℝ)*T ≤ 0 by linarith)) (by positivity : 0 ≤ 2*Real.exp 1)
  have hbig : 2+absoluteAverage T ≤ 11+2*K+4*Real.exp 1+2*A*Real.exp (q*T) := by
    linarith [(abs_le.mp herr).2]
  have hbound := hex.trans (mul_le_mul_of_nonneg_left hbig hC.le)
  have hprod := mul_le_mul_of_nonneg_right hbound (Real.exp_pos ((-p)*T)).le
  change Real.exp (p*T)*_ ≤ _ at hprod
  rw [← Real.exp_add,show p*T+-p*T = 0 by ring,Real.exp_zero] at hprod
  rw [show Real.exp ((q-p)*T) = Real.exp (q*T)*Real.exp ((-p)*T) by
    rw [← Real.exp_add]; congr 1; ring] at hlow
  linarith

/-- For every fixed positive k the arithmetic prime sums at kth powers
alone test RH, with the same numerical threshold and the same quantifier. -/
theorem riemannHypothesis_iff_powerWindow {k : ℕ} (hk : 0 < k) :
    RiemannHypothesis ↔ ∃ᶠ T : ℝ in atTop, powerWindow k T ≤ 1/40 := by
  constructor
  · intro h
    have hB (ρ : NontrivialZetaZero) : ρ.1.re ≤ 1/2 := (h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le
    have hd : (0:ℝ) < 1/(4*k) := by positivity
    have hd' : (1:ℝ)/(4*k) ≤ 1/4 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [show (1:ℝ) ≤ k by exact_mod_cast hk])
    have hq : (1/2-1/(4*(k:ℝ)))^2-1/4 < 0 := by
      nlinarith [mul_pos hd (show 0 < 1-1/(4*(k:ℝ)) by linarith)]
    have hn := ((exp_vanish (by norm_num : -(1/4:ℝ) < 0)).const_mul (2*Real.exp 1)).add
      ((exp_vanish hq).const_mul (8*(k:ℝ)+24))
    simp only [mul_zero,add_zero] at hn
    apply Filter.Eventually.frequently
    filter_upwards [eventually_powerWindow_error hk le_rfl hB,
      (tendsto_order.mp hn).2 (1/1000) (by norm_num),
      eventually_window_le_of_rh h (c := 24/1000) (by norm_num)] with T herr hsmall hwin
    linarith [(abs_le.mp herr).1]
  · intro hf
    have hu (ρ : NontrivialZetaZero) : ρ.1.re ≤ 1/2 := by
      by_contra! hρ
      exact hf (((powerWindow_tendsto_of_right_zero hk ρ hρ).eventually_gt_atTop (1/40)).mono
        fun _ ht => not_le.mpr ht)
    intro s hs ht ho
    let ρ : NontrivialZetaZero := ⟨s,hs,ht,ho⟩
    apply le_antisymm (hu ρ)
    have h' := hu ρ.functionalPartner
    rw [NontrivialZetaZero.functionalPartner_coe,Complex.sub_re,Complex.one_re] at h'
    change 1-s.re ≤ 1/2 at h'
    linarith

end
end RiemannGaussian.QuasiRHIntegerPowerCheckpoints
