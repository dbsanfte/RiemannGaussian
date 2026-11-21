import RiemannGaussian.QuasiRHIntegerPowerCheckpoints
import RiemannGaussian.RosserSchoenfeldLargeChebyshev

/-! # Bounds on individual sampled prime discrepancies

A low, verified zero forces both signs on every sufficiently late window.
The quantitative prime number theorem controls change near a sign crossing.
-/

namespace RiemannGaussian.QuasiRHPrimeSampleValues
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open QuasiRHPrimePrimitiveHeat

/-- The unnormalized signed discrepancy evaluated at logarithmic time. -/
def raw (u : ℝ) : ℝ := Real.exp u-1-Real.log (2*Real.pi)*u-RosserSchoenfeldPrimePrimitive.value u

private theorem real_value {u : ℝ} (hu : 0 ≤ u) :
    discrepancy u = (Real.exp (-u/2)*raw u : ℝ) := by
  simp only [discrepancy, hu, ↓reduceIte,raw,RosserSchoenfeldExplicitFormula.mainTerm_eq,
    Complex.ofReal_mul,Complex.ofReal_sub,show -(1/2:ℝ)*u = -u/2 by ring]

private theorem continuous_raw : Continuous raw := by
  unfold raw
  apply Continuous.sub _ RosserSchoenfeldPrimePrimitive.continuous_value
  fun_prop

private theorem observed_first_zero : ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, c ≤ absoluteAverage T := by
  classical
  obtain ⟨ρ, hlo, hhi, hre, _⟩ := ZetaFirstZeroCompleteness.complete_first_pair
  have he (σ : NontrivialZetaZero) : rate σ ρ.1.im = 0 ↔ σ = ρ := by
    constructor
    · intro h
      have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      simp [rate] at hr hi
      apply Subtype.ext
      apply Complex.ext <;> linarith
    · rintro rfl
      apply Complex.ext <;> simp [rate,hre]
  have h := tendsto_response_through_fiftyThree (y := ρ.1.im) (by rw [abs_of_pos (by linarith)]; linarith)
  simp_rw [he] at h
  rw [tsum_eq_single ρ (fun σ hσ => ite_eq_right hσ), ite_eq_left rfl] at h
  have hc : 0 < ‖coefficient ρ‖ := norm_pos_iff.mpr (div_ne_zero
    (by exact_mod_cast (analyticZetaZeroMultiplicity_positive ρ).ne')
    (pow_ne_zero _ (Complex.ne_zero_of_re_pos ρ.zero_lt_re)))
  refine ⟨‖coefficient ρ‖/2,by positivity,?_⟩
  filter_upwards [(tendsto_order.mp h.norm).1 (‖coefficient ρ‖/2) (by linarith)] with T ht
  exact ht.le.trans (response_le_absoluteAverage T _)

/-- Every sufficiently late window contains an actual zero of the real
prime discrepancy. Only the verified first Fourier response and the
unconditional vanishing of the signed mean enter this assertion. -/
theorem eventually_raw_crossing :
    ∀ᶠ T : ℝ in atTop, ∃ u ∈ Set.Icc (T/4) (4*T), raw u = 0 := by
  obtain ⟨c,hc,hab⟩ := observed_first_zero
  have hsg : Tendsto (fun T => |(response T 0).re|) atTop (𝓝 0) := by
    simpa using (Complex.continuous_re.continuousAt.tendsto.comp tendsto_signed_response_zero).abs
  have decay {a : ℝ} (ha : a < 0) : Tendsto (fun T : ℝ => Real.exp (a*T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg ha)
  have herr := ((decay (by norm_num : -(3/64:ℝ) < 0)).const_mul 2).add
    ((decay (by norm_num : -(3/4:ℝ) < 0)).const_mul 2)
  simp only [mul_zero,add_zero] at herr
  filter_upwards [hab,(tendsto_order.mp hsg).2 (c/4) (by positivity),
    (tendsto_order.mp herr).2 (c/4) (by positivity),eventually_ge_atTop (0:ℝ)] with T hM hs he ht
  let s := Set.Icc (T/4) (4*T)
  let μ := gaussianReal T (2*T).toNNReal
  have hu {u : ℝ} (h : u ∈ s) : 0 ≤ u := (by positivity : 0 ≤ T/4).trans h.1
  have hw := (window_positive_error ht).2
  have hav := twice_positiveAverage T
  have hpos : ∃ u ∈ s, 0 < raw u := by
    by_contra! h
    have hz : windowPositiveAverage T = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro u hum
      rw [real_value (hu hum),Complex.ofReal_re]
      exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (h u hum))
    linarith [(abs_lt.mp hs).1]
  have hneg : ∃ u ∈ s, raw u < 0 := by
    by_contra! h
    have hz : windowPositiveAverage T = ∫ u in s, ‖discrepancy u‖ ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hum
      change max (discrepancy u).re 0 = ‖discrepancy u‖
      rw [real_value (hu hum),Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs]
      have h' := mul_nonneg (Real.exp_pos (-u/2)).le (h u hum)
      simp only [abs_of_nonneg h',max_eq_left h']
    have hsplit := integral_add_compl (μ := μ) (s := s) measurableSet_Icc (integral_discrepancy T).norm
    rw [← hz] at hsplit
    change _ + _ = absoluteAverage T at hsplit
    have htail := integral_outside_window_le ht (integral_discrepancy T).norm discrepancy_norm_growth
    change (∫ u in sᶜ, ‖discrepancy u‖ ∂μ) ≤ _ at htail
    linarith [(window_positive_error ht).1,(abs_lt.mp hs).2]
  obtain ⟨a,ha,han⟩ := hneg
  obtain ⟨b,hb,hbp⟩ := hpos
  rcases le_total a b with hor | hor
  · obtain ⟨x,hx,hz⟩ := intermediate_value_Icc hor continuous_raw.continuousOn ⟨han.le,hbp.le⟩
    exact ⟨x,⟨ha.1.trans hx.1,hx.2.trans hb.2⟩,hz⟩
  · obtain ⟨x,hx,hz⟩ := intermediate_value_Icc' hor continuous_raw.continuousOn ⟨han.le,hbp.le⟩
    exact ⟨x,⟨hb.1.trans hx.1,hx.2.trans ha.2⟩,hz⟩

/-- The actual PNT error at the two endpoints bounds the change in the
unnormalized prime discrepancy, including all intervening prime powers. -/
theorem raw_increment {u b : ℝ} (hu : 5000 ≤ u) (hub : u ≤ b) :
    |raw b-raw u| ≤ (b-u)*(Real.exp b-Real.exp u+8+(2/5)*Real.exp b/u) := by
  have hu0 : 0 < u := by linarith
  have hb0 : 0 < b := hu0.trans_le hub
  have hstep := sub_nonneg.mpr hub
  have hup := RosserSchoenfeldDesmoothing.prime_increment_upper hub
  have hlo := RosserSchoenfeldDesmoothing.prime_increment_lower hub
  have heu := Real.exp_le_exp.mpr hub
  have hforward : (b-u)*Real.exp u ≤ Real.exp b-Real.exp u := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (b-u)) (Real.exp_pos u).le
    rw [← Real.exp_add,sub_add_cancel] at h
    linarith
  have hback : Real.exp b-Real.exp u ≤ (b-u)*Real.exp b := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (u-b)) (Real.exp_pos b).le
    rw [← Real.exp_add,sub_add_cancel] at h
    linarith
  have ha := (abs_le.mp (RosserSchoenfeldLargeChebyshev.abs_psi_sub_exp_le hu)).1
  have hb := (abs_le.mp (RosserSchoenfeldLargeChebyshev.abs_psi_sub_exp_le (hu.trans hub))).2
  have hnum := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left heu
    (by norm_num : (0:ℝ) ≤ 2/5)) hu0.le
  have hden := div_le_div_of_nonneg_left (by positivity : 0 ≤ (2/5:ℝ)*Real.exp b) hu0 hub
  have hlog : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hc : Real.log (2*Real.pi) ≤ 8 := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2*Real.pi),Real.pi_lt_four]
  unfold raw
  apply abs_le.mpr
  constructor
  · linarith [mul_le_mul_of_nonneg_left (by linarith : Chebyshev.psi (Real.exp b) ≤
        Real.exp b+(2/5)*Real.exp b/u) hstep,
      mul_le_mul_of_nonneg_right hc hstep]
  · linarith [mul_le_mul_of_nonneg_left (by linarith : Real.exp u-(2/5)*Real.exp b/u ≤
        Chebyshev.psi (Real.exp u)) hstep,mul_nonneg hstep hlog]

/-- The PNT controls interpolation at every square checkpoint, for all
intervening real samples as well as the integer endpoints. -/
theorem square_increment {u : ℝ} (hu : 5000 ≤ u)
    {m : ℝ} (hm : m ∈ Set.Icc (Real.exp (u/2)) (Real.exp (u/2)+u)) :
    |raw (2*Real.log m)-raw u| / m ≤ 4*(m-Real.exp (u/2))/u := by
  let r := Real.exp (u/2)
  let b := 2*Real.log m
  let h := m-r
  have hu0 : 0 < u := by linarith
  have hr : 0 < r := Real.exp_pos _
  have hrm : r ≤ m := hm.1
  have hm0 := hr.trans_le hrm
  have hh : 0 ≤ h := sub_nonneg.mpr hrm
  have hhu : h ≤ u := by dsimp [h,r]; linarith [hm.2]
  have hpow : 4*u ≤ Real.exp (u/4) := by
    have hsmall : u/8 ≤ Real.exp (u/8) := by linarith [Real.add_one_le_exp (u/8)]
    have hh' := mul_self_le_mul_self (by positivity : 0 ≤ u/8) hsmall
    rw [← Real.exp_add,show u/8+u/8 = u/4 by ring] at hh'
    nlinarith [mul_nonneg hu0.le (show 0 ≤ u-256 by linarith)]
  have hbig : 16*u^2 ≤ r := by
    have h' := mul_self_le_mul_self (by positivity : 0 ≤ 4*u) hpow
    rw [← Real.exp_add,show u/4+u/4 = u/2 by ring] at h'
    dsimp only [r]; nlinarith
  have hr1 : 1 ≤ r := Real.one_le_exp_iff.mpr (by positivity)
  have hru : u ≤ r := by nlinarith [mul_nonneg hu0.le (show 0 ≤ u-1 by linarith)]
  have heq : Real.exp u = r^2 := by dsimp [r]; rw [sq,← Real.exp_add]; congr 1; ring
  have heq' : Real.exp b = m^2 := by
    dsimp [b]
    rw [two_mul,Real.exp_add,Real.exp_log hm0,sq]
  have hub : u ≤ b := Real.exp_le_exp.mp (by rw [heq,heq']; exact pow_le_pow_left₀ hr.le hrm 2)
  have hgap : b-u ≤ 2*h/r := by
    have hl := Real.log_le_sub_one_of_pos (div_pos hm0 hr)
    rw [Real.log_div hm0.ne' hr.ne',show Real.log r = u/2 from Real.log_exp _] at hl
    dsimp only [b,h]
    field_simp at hl ⊢
    linarith
  have hm2 : m ≤ 2*r := by dsimp only [h] at hhu; linarith
  have hd : (m^2-r^2)*u ≤ 3*r*u^2 := by
    have h' := mul_le_mul hhu (by linarith : m+r ≤ 3*r) (by linarith : 0 ≤ m+r) hu0.le
    dsimp only [h] at h'
    nlinarith [mul_le_mul_of_nonneg_right h' hu0.le]
  have hcap : Real.exp b-Real.exp u+8+(2/5)*Real.exp b/u ≤ 2*r^2/u := by
    rw [heq,heq']
    apply (le_div_iff₀ hu0).mpr
    field_simp
    nlinarith [mul_self_le_mul_self hm0.le hm2, mul_le_mul_of_nonneg_left hbig hr.le,
      mul_nonneg (by linarith : 0 ≤ r-u) (by linarith : 0 ≤ r+u),
      mul_nonneg hu0.le (show 0 ≤ u-80 by linarith)]
  have hraw := raw_increment hu hub
  apply (div_le_iff₀ hm0).mpr
  apply hraw.trans ((mul_le_mul_of_nonneg_left hcap (sub_nonneg.mpr hub)).trans _)
  have hg := mul_le_mul_of_nonneg_right hgap (by positivity : 0 ≤ 2*r^2/u)
  change _ ≤ 4*h/u*m
  apply hg.trans
  calc
    _ = 4*h/u*r := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrm (by positivity)


/-- A uniform bound on each actual square sample in a block starting
at a zero of the prime discrepancy. In the square-root coordinate its
magnitude grows by at most four per unit of relative logarithmic width. -/
theorem square_samples_of_crossing {u : ℝ} (hu : 5000 ≤ u) (hz : raw u = 0)
    {m : ℝ} (hm : m ∈ Set.Icc (Real.exp (u/2)) (Real.exp (u/2)+u)) :
    |raw (2*Real.log m)| / m ≤ 4*(m-Real.exp (u/2))/u := by
  simpa only [hz,sub_zero] using square_increment hu hm

/-- An unconditional block of consecutive integer square samples in every
sufficiently late logarithmic window. The jth individually normalized
prime discrepancy costs at most 4(j+1)/u. -/
theorem eventually_consecutive_square_samples :
    ∀ᶠ T : ℝ in atTop, ∃ u ∈ Set.Icc (T/4) (4*T), ∀ j : ℕ, (j:ℝ)+1 ≤ u →
      let m := ⌈Real.exp (u/2)⌉₊+j
      |raw (2*Real.log m)|/(m:ℝ) ≤ 4*((j:ℝ)+1)/u := by
  filter_upwards [eventually_raw_crossing,eventually_ge_atTop (20000:ℝ)] with T hx ht
  obtain ⟨u,hu,hz⟩ := hx
  have hlu : 5000 ≤ u := by linarith [hu.1]
  refine ⟨u,hu,fun j hj => ?_⟩
  let r := Real.exp (u/2)
  have hm : (r:ℝ) ≤ (⌈r⌉₊+j:ℕ) := by
    rw [Nat.cast_add]
    linarith [Nat.le_ceil r,Nat.cast_nonneg (α := ℝ) j]
  have hgap : ((⌈r⌉₊+j:ℕ):ℝ)-r ≤ (j:ℝ)+1 := by
    rw [Nat.cast_add]
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (u/2)).le]
  apply (square_samples_of_crossing hlu hz ⟨hm,by change ((⌈r⌉₊+j:ℕ):ℝ) ≤ r+u; linarith⟩).trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by norm_num)) (by linarith)


/-- At every large real cutoff the discrepancy at the preceding square
approximates the actual normalized prime discrepancy. This controls the
full square mesh independently of the sign of either value. -/
theorem floor_square_error {u : ℝ} (hu : 5002 ≤ u) :
    ‖discrepancy u-discrepancy (QuasiRHIntegerPowerCheckpoints.powerTime 2 u)‖ ≤ 5/(u-2) := by
  let r := Real.exp (u/2)
  let n : ℝ := ⌊r⌋₊
  let v := 2*Real.log n
  have hr : 0 < r := Real.exp_pos _
  have hn : 1 ≤ n := by
    change (1:ℝ) ≤ (⌊r⌋₊:ℝ)
    exact_mod_cast (Nat.le_floor_iff hr.le).mpr
      (show ((1:ℕ):ℝ) ≤ r by simpa [r] using Real.one_le_exp_iff.mpr (by linarith : 0 ≤ u/2))
  have hn0 : 0 < n := by linarith
  have hnr : n ≤ r := Nat.floor_le hr.le
  have hrn : r < n+1 := Nat.lt_floor_add_one r
  have hvexp : Real.exp (v/2) = n := by dsimp only [v]; ring_nf; exact Real.exp_log hn0
  have hl : Real.log (r/n) ≤ r/n-1 := Real.log_le_sub_one_of_pos (div_pos hr hn0)
  rw [Real.log_div hr.ne' hn0.ne',show Real.log r = u/2 from Real.log_exp _] at hl
  have hdiff : u-v ≤ 2 := by
    have : r/n ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
    dsimp only [v]; linarith
  have hv : 5000 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hraw := square_increment hv (m := r) (by rw [hvexp]; exact ⟨hnr,by linarith⟩)
  rw [show 2*Real.log r = u by rw [show Real.log r = u/2 from Real.log_exp _]; ring,hvexp] at hraw
  have hsize := (RosserSchoenfeldLargeSmoothed.abs_prime_sub_main_lt (show 4900 ≤ v by linarith)).le
  rw [abs_sub_comm] at hsize
  change |raw v| ≤ _ at hsize
  have hv2 : Real.exp v = n^2 := by rw [← hvexp,sq,← Real.exp_add]; congr 1; ring
  rw [hv2] at hsize
  have hden : |raw v| * ((r-n)/(n*r)) ≤ 1/(64*v^2) := by
    apply (mul_le_mul_of_nonneg_right hsize (div_nonneg (sub_nonneg.mpr hnr) (mul_pos hn0 hr).le)).trans
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (show r-n ≤ 1 by linarith) hn0.le]
  have hsplit : raw u/r-raw v/n = (raw u-raw v)/r-raw v*((r-n)/(n*r)) := by field_simp; ring
  change ‖discrepancy u-discrepancy v‖ ≤ _
  rw [real_value (by linarith),real_value hv0.le,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [show Real.exp (-u/2)*raw u = raw u/r by dsimp [r]; rw [neg_div,Real.exp_neg]; ring,
    show Real.exp (-v/2)*raw v = raw v/n by rw [neg_div,Real.exp_neg,hvexp]; ring,hsplit]
  apply (abs_sub _ _).trans
  rw [abs_div,abs_of_pos hr,abs_mul,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hnr) (mul_pos hn0 hr).le)]
  apply (add_le_add hraw hden).trans
  have hv1 : 1/(64*v^2) ≤ 1/v := one_div_le_one_div_of_le hv0 (by nlinarith [sq_nonneg (v-1)])
  have hdist : 4*(r-n)/v ≤ 4/v := div_le_div_of_nonneg_right (by linarith) hv0.le
  have hfrac : 5/v ≤ 5/(u-2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  exact ((add_le_add hdist hv1).trans_eq (by ring)).trans hfrac


/-- The entire positive sampled sum differs from the positive prime window
by a vanishing unconditional error at every sufficiently large time. -/
theorem square_window_error {T : ℝ} (hT : 20008 ≤ T) :
    |windowPositiveAverage T-QuasiRHIntegerPowerCheckpoints.powerWindow 2 T| ≤ 5/(T/4-2) := by
  let μ := gaussianReal T (2*T).toNNReal
  let s := Set.Icc (T/4) (4*T)
  let f (u : ℝ) := max (discrepancy u).re 0
  let g (u : ℝ) := f (QuasiRHIntegerPowerCheckpoints.powerTime 2 u)
  let C := 5/(T/4-2)
  have hC : 0 ≤ C := div_nonneg (by norm_num) (by linarith)
  have hp : ∀ᵐ u ∂μ.restrict s, ‖f u-g u‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := μ) (s := s) measurableSet_Icc] with u hu
    have hlow : T/4 ≤ u := hu.1
    have hh := Complex.abs_re_le_norm (discrepancy u - discrepancy (QuasiRHIntegerPowerCheckpoints.powerTime 2 u))
    rw [Complex.sub_re] at hh
    exact ((abs_max_sub_max_le_abs _ _ _).trans hh).trans ((floor_square_error (by linarith)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)))
  have hf : Integrable f (μ.restrict s) := (positive_integrable T).restrict
  have hm : Measurable g := by
    have hn : Measurable (fun u : ℝ => ⌊Real.exp (u/(2:ℕ))⌋₊) := by fun_prop
    exact (measurable_of_countable (fun n : ℕ => f ((2:ℕ)*Real.log n))).comp hn
  have hd : Integrable (fun u => f u-g u) (μ.restrict s) :=
    (integrable_const C).mono' (hf.aestronglyMeasurable.sub hm.aestronglyMeasurable) hp
  have hg : Integrable g (μ.restrict s) := by
    convert hf.sub hd using 1
    ext u
    simp
  change |(∫ u in s, f u ∂μ)-(∫ u in s, g u ∂μ)| ≤ C
  rw [← integral_sub hf hg,← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le (integrable_const C) hp
  rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at h
  exact h.trans (mul_le_of_le_one_left hC measureReal_le_one)


/-- Each zero gives its own exponential lower bound on the actual
positive square samples at every sufficiently large time. -/
theorem exponential_le_square_samples (ρ : NontrivialZetaZero) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, Real.exp ((ρ.1.re^2-1/4)*T) ≤
      C*(13+2*QuasiRHIntegerPowerCheckpoints.powerWindow 2 T) := by
  obtain ⟨C,hC,hbound⟩ := exponential_le_absoluteAverage ρ
  refine ⟨C,hC,?_⟩
  have hs : Tendsto (fun T => (response T 0).re) atTop (𝓝 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp tendsto_signed_response_zero
  filter_upwards [hbound,eventually_ge_atTop (20008:ℝ),(tendsto_order.mp hs).1 (-1) (by norm_num)] with T hb ht hr
  apply hb.trans (mul_le_mul_of_nonneg_left _ hC.le)
  have hmesh := (abs_le.mp (square_window_error ht)).2
  have hnum : 5/(T/4-2) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have herr := (window_positive_error (show 0 ≤ T by linarith)).2
  linarith [twice_positiveAverage T, Real.exp_le_one_iff.mpr (by linarith : -(3/64:ℝ)*T ≤ 0),
    Real.exp_le_one_iff.mpr (by linarith : -(3/4:ℝ)*T ≤ 0)]

/-- The contradiction requires only subexponential returns for the full
positive square-sampled sum. Constants and polynomial growth are allowed. -/
theorem riemannHypothesis_iff_subexponential_square_samples :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ T : ℝ in atTop,
      QuasiRHIntegerPowerCheckpoints.powerWindow 2 T ≤ Real.exp (ε*T) := by
  constructor
  · intro h ε hε
    have hf := (QuasiRHIntegerPowerCheckpoints.riemannHypothesis_iff_powerWindow (k := 2) (by decide)).mp h
    exact (hf.and_eventually (eventually_ge_atTop (0:ℝ))).mono fun T ⟨hh,ht⟩ =>
      hh.trans ((by norm_num : (1/40:ℝ) ≤ 1).trans (Real.one_le_exp_iff.mpr (mul_nonneg hε.le ht)))
  · intro h
    have hright (ρ : NontrivialZetaZero) : ρ.1.re ≤ 1/2 := by
      by_contra! hρ
      let p := ρ.1.re^2-1/4
      have hp : 0 < p := by dsimp [p]; nlinarith [mul_pos (sub_pos.mpr hρ) ρ.zero_lt_re]
      obtain ⟨C,hC,hb⟩ := exponential_le_square_samples ρ
      have he : Tendsto (fun T : ℝ => Real.exp ((p/2)*T)) atTop atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (half_pos hp))
      obtain ⟨T,⟨hh,hb'⟩,hv,ht⟩ := (((h (p/2) (half_pos hp)).and_eventually hb).and_eventually
        ((he.eventually_gt_atTop (15*C)).and (he.eventually_ge_atTop 1))).exists
      have hw := mul_le_mul_of_nonneg_left (show 13+2*QuasiRHIntegerPowerCheckpoints.powerWindow 2 T ≤
        15*Real.exp (p/2*T) by linarith) hC.le
      have ha : Real.exp (p*T) = Real.exp (p/2*T)*Real.exp (p/2*T) := by rw [← Real.exp_add]; congr 1; ring
      change Real.exp (p*T) ≤ _ at hb'
      rw [ha] at hb'
      nlinarith [mul_lt_mul_of_pos_right hv (Real.exp_pos (p/2*T))]
    intro s hs ht ho
    let ρ : NontrivialZetaZero := ⟨s,hs,ht,ho⟩
    apply le_antisymm (hright ρ)
    have hl := hright ρ.functionalPartner
    rw [NontrivialZetaZero.functionalPartner_coe,Complex.sub_re,Complex.one_re] at hl
    change 1-s.re ≤ 1/2 at hl
    linarith


end
end RiemannGaussian.QuasiRHPrimeSampleValues
