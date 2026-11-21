import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData
import Formalism.GammaFactorNonvanishing.RhOfRight
import RiemannGaussian.AlpogeZetaShortIntervals
import Lean.Util.CollectAxioms

/-! # The fixed dyadic band in the window criterion -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Complex Set MeasureTheory Filter Topology Deduction

private abbrev principalFamily : CharFamily := famD 1 ∅ 1 one_pos

private theorem principal_signal (x : ℝ) : Gm principalFamily x = Deduction.G x := by
  classical
  have hc (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _,map_one]
  let i₀ : principalFamily.ι := none
  let f (i : principalFamily.ι) := principalFamily.a i*(Gchi (principalFamily.χ i) x).re
  change (∑ i, f i) = _
  calc
    _ = f i₀ := Finset.sum_eq_single i₀ (fun i _ hi => by
      cases i with
      | none => exact (hi rfl).elim
      | some ξ => exact (Finset.notMem_empty _ ξ.2.1).elim) (by simp)
    _ = _ := by
      change 1*(Gchi (1 : DirichletCharacter ℂ 1) x).re = Deduction.G x
      simp [Gchi,hc,Deduction.G]

private def delay (h : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  if h < u then g (u-h) else 0

private theorem delay_meas {g : ℝ → ℝ} (hg : Measurable g) (h : ℝ) :
    Measurable (delay h g) :=
  Measurable.ite measurableSet_Ioi (hg.comp (measurable_id.sub_const h)) measurable_const

private theorem delay_growth {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C*Real.exp (2*u)) {h : ℝ} (hh : 0 ≤ h) :
    ∀ u : ℝ, 0 ≤ u → |delay h g u| ≤ C*Real.exp (2*u) := by
  intro u _
  by_cases hu : h < u
  · rw [delay,ite_eq_left hu]
    exact (hg _ (sub_nonneg.mpr hu.le)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) hC)
  · simp [delay,hu,mul_nonneg hC (Real.exp_pos _).le]

private theorem laplace_int {g : ℝ → ℝ} (hm : Measurable g) {C : ℝ}
    (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C*Real.exp (2*u)) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => (g u:ℂ)*cexp (-s*u)) (Ioi 0) := by
  have hi := (iteratedDeriv_laplace_int 0 (s.re-2) (by linarith)).const_mul C
  apply Integrable.mono' hi (by fun_prop)
  apply (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  simpa only [pow_zero,mul_one] using
    iteratedDeriv_laplace_bound g C hg 0 (s.re-2) s (by linarith) u hu

private theorem laplace_delay (g : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) (s : ℂ) :
    (∫ u in Ioi (0:ℝ), (delay h g u:ℂ)*cexp (-s*u)) =
      cexp (-s*h)*(∫ u in Ioi (0:ℝ), (g u:ℂ)*cexp (-s*u)) := by
  let F := (Ioi (0:ℝ)).indicator (fun v : ℝ => (g v:ℂ)*cexp (-s*v))
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  change _ = cexp (-s*h)*(∫ v : ℝ, F v)
  rw [← integral_sub_right_eq_self F h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : h < u
  · rw [Set.indicator_of_mem (s := Ioi (0:ℝ)) (hh.trans_lt hu)]
    simp only [delay,ite_eq_left hu,F,Set.indicator_of_mem (s := Ioi (0:ℝ)) (sub_pos.mpr hu)]
    rw [mul_left_comm,← Complex.exp_add,Complex.ofReal_sub]
    congr 2
    ring
  · have hz : u-h ∉ Ioi (0:ℝ) := not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hu))
    simp only [F,indicator_of_notMem hz,mul_zero]
    by_cases hp : 0 < u
    · simp [delay,hu]
    · exact indicator_of_notMem hp _

private def localSignal (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  3*delay (Real.log 2) g u-g u-2*delay (2*Real.log 2) g u

private def symbol (s : ℂ) : ℂ :=
  let z := cexp (-s*(Real.log 2:ℝ))
  (1-z)*(2*z-1)

private theorem symbol_analytic (s : ℂ) : AnalyticAt ℂ symbol s := by
  unfold symbol
  fun_prop

/-- Both roots of the delay polynomial lie on boundary lines. -/
theorem dyadic_multiplier_nonzero {s : ℂ} (hs : 0 < s.re) (hs₁ : s.re < 1) :
    (1-cexp (-s*(Real.log 2:ℝ)))*(2*cexp (-s*(Real.log 2:ℝ))-1) ≠ 0 := by
  let z := cexp (-s*(Real.log 2:ℝ))
  have he : ‖z‖ = Real.exp (-s.re*Real.log 2) := by
    simp only [z,Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hz : ‖z‖ < 1 := by rw [he,← Real.exp_zero]; exact Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (Real.log_pos (by norm_num)))
  have htwo : (1/2:ℝ) < ‖z‖ := by
    rw [he,show (1/2:ℝ) = Real.exp (-Real.log 2) by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num]
    apply Real.exp_lt_exp.mpr
    nlinarith only [mul_lt_mul_of_pos_right hs₁ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  change (1-z)*(2*z-1) ≠ 0
  apply mul_ne_zero
  · intro h
    rw [← sub_eq_zero.mp h,norm_one] at hz
    exact (lt_irrefl _ hz)
  · intro h
    have hz' : z = (1/2:ℂ) := by linear_combination (norm := ring) (1/2:ℂ)*h
    rw [hz'] at htwo
    norm_num at htwo

private theorem local_pole_data {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hp : PoleData g Φ Z)
    (hstrip : ∀ z ∈ Z, z.re < 1) :
    PoleData (localSignal g) (fun s => symbol s * Φ s) Z := by
  obtain ⟨C₀,hC₀⟩ := hp.growth
  let C := max 0 C₀
  have hC : 0 ≤ C := le_max_left _ _
  have hg (u : ℝ) (hu : 0 ≤ u) := (hC₀ u hu).trans (mul_le_mul_of_nonneg_right
    (le_max_right 0 C₀) (Real.exp_pos _).le)
  have hℓ := (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
  have h₁ := delay_growth (C := C) hC hg hℓ
  have h₂ := delay_growth (C := C) hC hg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hℓ)
  refine ⟨((measurable_const.mul (delay_meas hp.meas _)).sub hp.meas).sub
    (measurable_const.mul (delay_meas hp.meas _)),⟨6*C,fun u hu => ?_⟩,?_,hp.pos,
    ((show Differentiable ℂ symbol from fun s => (symbol_analytic s).differentiableAt).differentiableOn.mul hp.diff),hp.iso,?_⟩
  · unfold localSignal
    calc _ ≤ |3*delay (Real.log 2) g u-g u|+|2*delay (2*Real.log 2) g u| := abs_sub _ _
         _ ≤ _ := by
           have ht := abs_sub (3*delay (Real.log 2) g u) (g u)
           rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at ht
           rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
           linarith only [ht,h₁ u hu,h₂ u hu,hg u hu]
  · intro s hs
    let f (g : ℝ → ℝ) (u : ℝ) := (g u:ℂ)*cexp (-s*u)
    have i₀ := laplace_int hp.meas hg hs
    have i₁ := laplace_int (delay_meas hp.meas _) h₁ hs
    have i₂ := laplace_int (delay_meas hp.meas _) h₂ hs
    have he (u : ℝ) : f (localSignal g) u = 3*f (delay (Real.log 2) g) u-f g u-
        2*f (delay (2*Real.log 2) g) u := by simp only [f,localSignal,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat]; ring
    change _ = ∫ u in Ioi (0:ℝ), f (localSignal g) u
    simp_rw [he]
    dsimp only [f]
    rw [integral_sub (show IntegrableOn (fun u : ℝ => 3*f (delay (Real.log 2) g) u - f g u) (Ioi 0) volume from (i₁.const_mul (3:ℂ)).sub i₀) (i₂.const_mul (2:ℂ)),
      integral_sub (i₁.const_mul (3:ℂ)) i₀,integral_const_mul,integral_const_mul]
    rw [laplace_delay _ hℓ,laplace_delay _ (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hℓ),← hp.laplace s hs]
    rw [Complex.ofReal_mul,Complex.ofReal_ofNat,show -s*(2*(Real.log 2:ℝ)) =
      -s*(Real.log 2:ℝ)+ -s*(Real.log 2:ℝ) by ring,Complex.exp_add]
    unfold symbol
    ring
  · intro z hz
    obtain ⟨c,hc,hreal,f,hf,he⟩ := hp.pole z hz
    refine ⟨symbol z*c,mul_ne_zero (dyadic_multiplier_nonzero (hp.pos z hz) (hstrip z hz)) hc,
      fun hi => ?_,fun s => c*dslope symbol z s+symbol s*f s,
      (analyticAt_const.mul (poleData_dslope (symbol_analytic z))).add ((symbol_analytic z).mul hf),?_⟩
    · -- On the real interval (0,1) both factors of the symbol are positive.
      have hre : z = (z.re:ℂ) := Complex.ext rfl (by simpa using hi)
      let a := Real.exp (-z.re*Real.log 2)
      have ha : 1/2 < a := by
        rw [show (1/2:ℝ) = Real.exp (-Real.log 2) by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num]
        apply Real.exp_lt_exp.mpr
        nlinarith only [mul_lt_mul_of_pos_right (hstrip z hz) (Real.log_pos (by norm_num : (1:ℝ)<2))]
      have ha₁ : a < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos (hp.pos z hz)) (Real.log_pos (by norm_num)))
      have hzsym : symbol z = (((1-a)*(2*a-1):ℝ):ℂ) := by
        unfold symbol
        rw [show cexp (-z*(Real.log 2:ℝ)) = (a:ℂ) by
          dsimp only [a]; rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,← hre]]
        push_cast
        rfl
      obtain ⟨hcpos,hci⟩ := hreal hi
      rw [hzsym,Complex.mul_re,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,hci]
      constructor
      · nlinarith only [mul_pos (mul_pos (sub_pos.mpr ha₁) (by linarith : 0 < 2*a-1)) hcpos]
      · ring
    filter_upwards [he,self_mem_nhdsWithin] with s hs hsz
    rw [hs,dslope_of_ne _ (show s ≠ z from hsz),slope_def_field]
    field_simp [sub_ne_zero.mpr (show s ≠ z from hsz)]
    ring

/-- The physical dyadic signal at the upper endpoint x. -/
def dyadicContrast (x : ℝ) : ℝ := 3*Deduction.G (x/2)-Deduction.G x-2*Deduction.G (x/4)

private theorem localSignal_log {x : ℝ} (hx : 4 < x) :
    localSignal (gm principalFamily) (Real.log x) = dyadicContrast x := by
  have hx0 : 0 < x := by linarith
  have hL : 2*Real.log 2 = Real.log 4 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]; norm_num
  have h₂ := Real.log_lt_log (by norm_num : (0:ℝ)<2) (show 2 < x by linarith)
  have h₄ := Real.log_lt_log (by norm_num : (0:ℝ)<4) hx
  simp only [localSignal,delay,ite_eq_left h₂,hL,ite_eq_left h₄,gm,principal_signal,Real.exp_sub,
    Real.exp_log hx0,Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_log (by norm_num : (0:ℝ)<4),
    dyadicContrast]

private theorem zeta_strip (z : ℂ) (hz : z ∈ zeroSet principalFamily) : z.re < 1 := by
  obtain ⟨_,i,hh⟩ := hz
  cases i with
  | some ξ => exact (Finset.notMem_empty _ ξ.2.1).elim
  | none =>
    rcases hh with hh|hh
    · exact lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h
        (by simpa [principalFamily,famD,DirichletCharacter.LFunction_modOne_eq] using hh)
    · have hzero : riemannZeta ((starRingEnd ℂ) z) = 0 := by
        simpa [principalFamily,famD,DirichletCharacter.LFunction_modOne_eq] using hh
      exact lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re
        (s := (starRingEnd ℂ) z) (by simpa using h) hzero

/-- The triangular weight of an ordinary prime. It is supported on x/4 < p < x. -/
def dyadicPrimeWeight (x : ℝ) (p : ℕ) : ℝ :=
  max (x/p-1) 0-3*max ((x/2)/p-1) 0+2*max ((x/4)/p-1) 0

theorem dyadicPrimeWeight_formula {x : ℝ} (_hx : 0 ≤ x) {p : ℕ} (hp : 0 < p) :
    dyadicPrimeWeight x p =
      if (p:ℝ) ≤ x/4 then 0 else if (p:ℝ) ≤ x/2 then 2-x/(2*p)
      else if (p:ℝ) ≤ x then x/p-1 else 0 := by
  have hp0 : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have pos (y : ℝ) (hy : (p:ℝ) ≤ y) : 0 ≤ y/p-1 := sub_nonneg.mpr ((one_le_div hp0).mpr hy)
  have neg (y : ℝ) (hy : y ≤ (p:ℝ)) : y/p-1 ≤ 0 := sub_nonpos.mpr ((div_le_one hp0).mpr hy)
  unfold dyadicPrimeWeight
  split_ifs with h₁ h₂ h₃
  · rw [max_eq_left (pos _ (by linarith)),max_eq_left (pos _ (by linarith)),max_eq_left (pos _ h₁)]
    ring
  · rw [max_eq_left (pos _ (by linarith)),max_eq_left (pos _ h₂),max_eq_right (neg _ (le_of_not_ge h₁))]
    ring
  · rw [max_eq_left (pos _ h₃),max_eq_right (neg _ (le_of_not_ge h₂)),max_eq_right (neg _ (le_of_not_ge h₁))]
    ring
  · rw [max_eq_right (neg _ (le_of_not_ge h₃)),max_eq_right (neg _ (le_of_not_ge h₂)),
      max_eq_right (neg _ (le_of_not_ge h₁))]
    ring

/-- The expected mass minus the weighted ordinary primes on one fixed band. -/
def dyadicPrimeDeficit (x : ℝ) : ℝ :=
  x*Real.log 2/2 - ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p * dyadicPrimeWeight x p

private theorem ramp_expand {x X : ℝ} (hx : 0 ≤ x) (hX : x ≤ X) :
    (Deduction.ramp (fun _ => 1) x).re =
      ∑ d ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt d*max (x/d-1) 0 := by
  unfold Deduction.ramp
  rw [Complex.re_sum]
  simp only [mul_one,← Complex.ofReal_mul,Complex.ofReal_re]
  have hsub : Finset.Ioc 0 ⌊X⌋₊ ⊆ Finset.range (⌊X⌋₊+1) := by
    intro d hd; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hd).2)
  rw [Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono hX))) (fun d _ hn => ?_)]
  · exact (Finset.sum_subset hsub (by
      intro d hd hn
      have hd0 : d = 0 := by simp only [Finset.mem_range,Finset.mem_Ioc,not_and_or] at *; omega
      simp [hd0])).symm
  · have hd : ⌊x⌋₊ < d := by simp only [Finset.mem_range,not_lt] at hn; omega
    have hh := (Nat.floor_lt hx).mp hd
    rw [max_eq_right (sub_nonpos.mpr ((div_le_one (hx.trans_lt hh)).mpr hh.le)),mul_zero]

/-- The signed contrast counts all prime powers in the fixed band. -/
theorem dyadicContrast_prime_power {x : ℝ} (hx : 0 < x) :
    dyadicContrast x = x*Real.log 2/2 -
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d*dyadicPrimeWeight x d := by
  unfold dyadicContrast Deduction.G
  rw [ramp_expand (by positivity : 0 ≤ x/2) (by linarith : x/2 ≤ x),
      ramp_expand hx.le (le_refl x), ramp_expand (by positivity : 0 ≤ x/4) (by linarith : x/4 ≤ x)]
  simp only [dyadicPrimeWeight,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp_rw [show ∀ (a b : ℝ), a*(3*b)=3*(a*b) by intros; ring,
    show ∀ (a b : ℝ), a*(2*b)=2*(a*b) by intros; ring]
  rw [← Finset.mul_sum,← Finset.mul_sum,Real.log_div hx.ne' (by norm_num),
    Real.log_div hx.ne' (by norm_num),show Real.log 4 = 2*Real.log 2 by
      rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]; norm_num]
  ring

theorem dyadicContrast_le_primeDeficit {x : ℝ} (hx : 0 < x) :
    dyadicContrast x ≤ dyadicPrimeDeficit x := by
  rw [dyadicContrast_prime_power hx,dyadicPrimeDeficit]
  apply sub_le_sub_left
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) Nat.Prime]
  have he := Finset.sum_congr (s₁ := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime) rfl
    fun p hp => congrArg (fun v : ℝ => v*dyadicPrimeWeight x p)
      (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2)
  rw [he]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro d hd
  have hd₀ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd₀
  apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
  rw [dyadicPrimeWeight_formula hx.le hd₀]
  split_ifs with h₁ h₂ h₃
  · exact le_rfl
  · apply sub_nonneg.mpr ((div_le_iff₀ (by positivity : 0 < 2*(d:ℝ))).mpr _)
    linarith only [not_le.mp h₁]
  · exact sub_nonneg.mpr ((one_le_div hdR).mpr h₃)
  · exact le_rfl

/-- Proper prime powers change the fixed-band deficit by at most square-root size
on every real argument, uniformly before taking the positive part. -/
theorem dyadicPrimeDeficit_power_cost : ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x →
    0 ≤ dyadicPrimeDeficit x-dyadicContrast x ∧ dyadicPrimeDeficit x-dyadicContrast x ≤ K*Real.sqrt x := by
  obtain ⟨K,hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max 0 K,le_max_left _ _,fun {x} hx => ⟨sub_nonneg.mpr (dyadicContrast_le_primeDeficit hx),?_⟩⟩
  let S := Finset.Ioc 0 ⌊x⌋₊
  have split (w : ℕ → ℝ) :
      (∑ d ∈ S, ArithmeticFunction.vonMangoldt d*w d) -
        (∑ d ∈ S.filter Nat.Prime, Real.log d*w d) =
          ∑ d ∈ S.filter (fun p => ¬p.Prime), ArithmeticFunction.vonMangoldt d*w d := by
    have he := Finset.sum_congr (s₁ := S.filter Nat.Prime) rfl fun d hd =>
      congrArg (fun v : ℝ => v*w d) (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hd).2)
    rw [← Finset.sum_filter_add_sum_filter_not S Nat.Prime,he,add_sub_cancel_left]
  have hun := split (fun _ => 1)
  simp only [mul_one] at hun
  change Chebyshev.psi x-Chebyshev.theta x = _ at hun
  rw [dyadicPrimeDeficit,dyadicContrast_prime_power hx,sub_sub_sub_cancel_left,split]
  apply le_trans _ (hun.ge.trans ((hK x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg x))))
  apply Finset.sum_le_sum
  intro p hp
  have hp₀ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp₀
  apply mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
  rw [dyadicPrimeWeight_formula hx.le hp₀]
  split_ifs with h₁ h₂ h₃
  · norm_num
  · have he : 1 ≤ x/(2*p) := (one_le_div (by positivity)).mpr (by linarith)
    linarith
  · have he : x/(p:ℝ) ≤ 2 := (div_le_iff₀ hpR).mpr (by linarith only [not_le.mp h₂])
    linarith
  · norm_num

theorem fixedBand_G_eq_native (x : ℝ) : Deduction.G x = AlpogeZetaSamples.G x := by
  unfold Deduction.G Deduction.ramp AlpogeZetaSamples.G AlpogeZetaSamples.ramp
  rw [Complex.re_sum]
  simp only [mul_one,← Complex.ofReal_mul,Complex.ofReal_re]

/-- Interpolation with the actual linear weights, in both directions. -/
private theorem interp_G {a x b u v : ℝ} (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u+v=1) (hx : x=u*a+v*b) :
    let e := Deduction.G x-u*Deduction.G a-v*Deduction.G b;
    -(b-a+1)*Real.log b*((b-a)/a) ≤ e ∧ e ≤ (b-a)^2/a := by
  simp only [fixedBand_G_eq_native]
  have ha₀ := zero_lt_one.trans_le ha
  have hx₀ := ha₀.trans_le hax
  have hb₀ := hx₀.trans_le hxb
  have he : u*(a-x)+v*(b-x)=0 := by linear_combination -hx - x*hs
  constructor
  · obtain ⟨s,ht⟩ := AlpogeZetaSamples.G_affine_upper ha hax hxb
    have h₁ := mul_le_mul_of_nonneg_left (ht a le_rfl (hax.trans hxb)) hu
    have h₂ := mul_le_mul_of_nonneg_left (ht b (hax.trans hxb) le_rfl) hv
    have hc := congrArg (fun t => t * (AlpogeZetaSamples.G x+(b-a+1)*Real.log b*((b-a)/a))) hs
    nlinarith only [h₁,h₂,hc,congrArg (fun t => s*t) he]
  · have hlog {t : ℝ} (ht : 0 < t) : t*(Real.log t-Real.log x) ≤ t*(t/x-1) := by
      rw [← Real.log_div ht.ne' hx₀.ne']
      exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht hx₀)) ht.le
    have hvar (t : ℝ) (ht : a ≤ t) (ht' : t ≤ b) : (t-x)^2 ≤ (b-a)^2 := by
      apply sq_le_sq' <;> linarith
    have hvar' := add_le_add (mul_le_mul_of_nonneg_left (hvar a le_rfl (hax.trans hxb)) hu)
      (mul_le_mul_of_nonneg_left (hvar b (hax.trans hxb) le_rfl) hv)
    rw [← add_mul,hs,one_mul] at hvar'
    have herr : u*(a*(a/x-1))+v*(b*(b/x-1)) ≤ (b-a)^2/a := by
      apply le_trans _ (div_le_div_of_nonneg_left (sq_nonneg (b-a)) ha₀ hax)
      apply (le_div_iff₀ hx₀).mpr
      field_simp [hx₀.ne']
      nlinarith only [hvar',congrArg (fun t => x*t) he]
    have hc := AlpogeZetaSamples.ramp_le_chord ha₀.le hax hxb hu hv hs hx
    unfold AlpogeZetaSamples.G
    nlinarith only [hc,herr,mul_le_mul_of_nonneg_left (hlog ha₀) hu,
      mul_le_mul_of_nonneg_left (hlog hb₀) hv,congrArg (fun t => t*Real.log x) hx,
      congrArg (fun t => (1+Real.eulerMascheroniConstant)*t) hx]

private theorem dyadic_fourth_cell {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx : x ∈ Icc ((n:ℝ)^4) (((n:ℝ)+1)^4)) :
    dyadicContrast x ≤ max (dyadicPrimeDeficit ((n:ℝ)^4)) (dyadicPrimeDeficit (((n:ℝ)+1)^4)) +
      3000*(n:ℝ)^2*(1+Real.log (((n:ℝ)+1)^4)) := by
  let a := (n:ℝ)^4
  let b := ((n:ℝ)+1)^4
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n:ℝ) := by linarith
  have h₁ : (1:ℝ) ≤ n := by linarith
  have ha : 4 ≤ a := by
    dsimp [a]; nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hnR 4]
  have hab : a < b := pow_lt_pow_left₀ (by linarith) hn₀.le (by decide)
  obtain ⟨hax,hxb⟩ := hx
  change a ≤ x at hax
  change x ≤ b at hxb
  let u := (b-x)/(b-a)
  let v := (x-a)/(b-a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hxb) (sub_pos.mpr hab).le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hax) (sub_pos.mpr hab).le
  have hs : u+v=1 := by dsimp only [u,v]; field_simp [(sub_pos.mpr hab).ne']; ring
  have hcenter : x=u*a+v*b := by dsimp only [u,v]; field_simp [(sub_pos.mpr hab).ne']; ring
  have h₀ := (interp_G (by linarith : 1 ≤ a) hax hxb hu hv hs hcenter).1
  have h₂ := (interp_G (by linarith : 1 ≤ a/2) (by linarith : a/2 ≤ x/2)
    (by linarith : x/2 ≤ b/2) hu hv hs (by linarith only [hcenter] : x/2=u*(a/2)+v*(b/2))).2
  have h₄ := (interp_G (by linarith : 1 ≤ a/4) (by linarith : a/4 ≤ x/4)
    (by linarith : x/4 ≤ b/4) hu hv hs (by linarith only [hcenter] : x/4=u*(a/4)+v*(b/4))).1
  have hgap : b-a ≤ 15*(n:ℝ)^3 := by
    dsimp only [a,b]; nlinarith only [mul_nonneg (sub_nonneg.mpr h₁)
      (show 0 ≤ 11*(n:ℝ)^2+5*n+1 by positivity)]
  have hgap' : b-a+1 ≤ 16*(n:ℝ)^3 := by linarith only [hgap,one_le_pow₀ h₁ (n := 3)]
  have hprod : (b-a+1)*((b-a)/a) ≤ 240*(n:ℝ)^2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < a)).mpr
    exact (mul_le_mul hgap' hgap (sub_pos.mpr hab).le (by positivity)).trans_eq (by dsimp [a]; ring)
  have hsq : (b-a)^2/a ≤ 240*(n:ℝ)^2 := by
    apply le_trans _ hprod
    rw [← mul_div_assoc,pow_two]; gcongr; linarith
  have hlog := Real.log_nonneg (by linarith : 1 ≤ b)
  have hlog₄ := Real.log_le_log (by linarith : 0 < b/4) (by linarith : b/4 ≤ b)
  have hprod₄ : (b/4-a/4+1)*((b/4-a/4)/(a/4)) ≤ 240*(n:ℝ)^2 := by
    rw [show (b/4-a/4)/(a/4)=(b-a)/a by ring]
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith)
      (div_nonneg (sub_pos.mpr hab).le (by linarith))) hprod
  have herr₄ := mul_le_mul hprod₄ hlog₄ (Real.log_nonneg (by linarith)) (by positivity)
  have herr₁ := mul_le_mul_of_nonneg_right hprod hlog
  have hsq₂ : (b/2-a/2)^2/(a/2) = (b-a)^2/a/2 := by ring
  rw [hsq₂] at h₂
  let D := max (dyadicPrimeDeficit a) (dyadicPrimeDeficit b)
  have hends := add_le_add (mul_le_mul_of_nonneg_left
    ((dyadicContrast_le_primeDeficit (by linarith : 0 < a)).trans (le_max_left _ (dyadicPrimeDeficit b))) hu)
    (mul_le_mul_of_nonneg_left
    ((dyadicContrast_le_primeDeficit (by linarith : 0 < b)).trans (le_max_right (dyadicPrimeDeficit a) _)) hv)
  rw [← add_mul,hs,one_mul] at hends
  change dyadicContrast x ≤ D+3000*(n:ℝ)^2*(1+Real.log b)
  change u*dyadicContrast a+v*dyadicContrast b ≤ D at hends
  unfold dyadicContrast at hends ⊢
  nlinarith only [hends,h₀,h₂,h₄,herr₄,herr₁,hsq,sq_nonneg (n:ℝ),
    mul_nonneg (sq_nonneg (n:ℝ)) hlog]

private theorem G_cont_at {x : ℝ} (hx : 0 < x) : ContinuousAt Deduction.G x := by
  have he : Deduction.G =ᶠ[𝓝 x] fun y =>
      (∑ d ∈ Finset.Ioc 0 ⌊x+1⌋₊, ArithmeticFunction.vonMangoldt d*max (y/d-1) 0) -
      y*Real.log y+(1+Real.eulerMascheroniConstant)*y := by
    filter_upwards [lt_mem_nhds hx,gt_mem_nhds (show x < x+1 by linarith)] with y hy hh
    exact congrArg (fun z => z - y*Real.log y+(1+Real.eulerMascheroniConstant)*y) (ramp_expand hy.le hh.le)
  apply ContinuousAt.congr_of_eventuallyEq _ he
  fun_prop (disch := positivity)

private theorem contrast_cont_at {x : ℝ} (hx : 0 < x) : ContinuousAt dyadicContrast x := by
  unfold dyadicContrast
  have h (k : ℝ) (hk : 0 < k) : ContinuousAt (fun y : ℝ => Deduction.G (y/k)) x :=
    (G_cont_at (div_pos hx hk)).comp (f := fun y : ℝ => y/k) (continuousAt_id.div_const k)
  exact ((continuousAt_const.mul (h 2 (by norm_num))).sub (G_cont_at hx)).sub
    (continuousAt_const.mul (h 4 (by norm_num)))

private def grid (n : ℕ) : ℝ := 4*Real.log n
private def weighted (u : ℝ) : ℝ := max (dyadicContrast (Real.exp u)) 0 * Real.exp (-u/2)

private theorem weighted_cont : Continuous weighted := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (((contrast_cont_at (Real.exp_pos u)).comp Real.continuous_exp.continuousAt).sup
    continuousAt_const).mul (by fun_prop)

private theorem grid_exp {n : ℕ} (hn : 0 < n) : Real.exp (grid n) = (n:ℝ)^4 := by
  have he := Real.exp_log (pow_pos (Nat.cast_pos.mpr hn : 0 < (n:ℝ)) 4)
  rwa [Real.log_pow,Nat.cast_ofNat] at he

private theorem grid_mono {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) : grid m ≤ grid n :=
  mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmn)) (by norm_num)

/-- Positive ordinary-prime shortfall, with the weight of this fourth-power observation. -/
def fixedBandSample (n : ℕ) : ℝ := max (dyadicPrimeDeficit ((n:ℝ)^4)) 0/(n:ℝ)^3

/-- Total positive shortfall on the indicated complete window. -/
def fixedBandMass (m b : ℕ) : ℝ := ∑ n ∈ Finset.Icc m b, fixedBandSample n

private theorem sample_nonneg (n : ℕ) : 0 ≤ fixedBandSample n :=
  div_nonneg (le_max_right _ _) (by positivity)

private theorem sample_upper {n : ℕ} (hn : 0 < n) :
    dyadicPrimeDeficit ((n:ℝ)^4) ≤ (n:ℝ)^3*fixedBandSample n := by
  unfold fixedBandSample
  rw [mul_div_cancel₀ _ (pow_ne_zero 3 (Nat.cast_ne_zero.mpr hn.ne'))]
  exact le_max_left _ _

private theorem cell_weighted {n : ℕ} (hn : 2 ≤ n) :
    (∫ u in grid n..grid (n+1), weighted u) ≤ 4*(fixedBandSample n+8*fixedBandSample (n+1)+
      3000*(1+Real.log (((n:ℝ)+1)^4))/(n:ℝ)) := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 ≤ Real.log (((n:ℝ)+1)^4) := Real.log_nonneg (one_le_pow₀ (by linarith))
  let M := fixedBandSample n+8*fixedBandSample (n+1)+3000*(1+Real.log (((n:ℝ)+1)^4))/(n:ℝ)
  have hM : 0 ≤ M := by dsimp only [M]; positivity [sample_nonneg n,sample_nonneg (n+1)]
  have hgrid := grid_mono hn0 (Nat.le_succ n)
  have hw : grid (n+1)-grid n ≤ 4/(n:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hnR.ne'] at h
    simp only [grid,Nat.cast_add_one]
    have ht : ((n:ℝ)+1)/n -1 = 1/(n:ℝ) := by field_simp; ring
    rw [ht] at h
    calc _ = 4*(Real.log ((n:ℝ)+1)-Real.log n) := by ring
         _ ≤ 4*(1/(n:ℝ)) := by linarith only [h]
         _ = _ := by ring
  have point (u : ℝ) (hu : u ∈ Icc (grid n) (grid (n+1))) : weighted u ≤ (n:ℝ)*M := by
    have hl := Real.exp_le_exp.mpr hu.1
    have ht := Real.exp_le_exp.mpr hu.2
    rw [grid_exp hn0] at hl
    rw [grid_exp (Nat.succ_pos n),Nat.cast_add_one] at ht
    have hcell := dyadic_fourth_cell hn ⟨hl,ht⟩
    have he := sample_upper (Nat.succ_pos n)
    rw [Nat.cast_add_one] at he
    have h3 : ((n:ℝ)+1)^3 ≤ 8*(n:ℝ)^3 := calc
      _ ≤ (2*(n:ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by ring
    have hbase : max (dyadicPrimeDeficit ((n:ℝ)^4)) (dyadicPrimeDeficit (((n:ℝ)+1)^4)) ≤
        (n:ℝ)^3*(fixedBandSample n+8*fixedBandSample (n+1)) := by
      apply max_le
      · nlinarith only [sample_upper hn0,mul_nonneg (pow_nonneg hnR.le 3) (sample_nonneg (n+1))]
      · nlinarith only [he,mul_le_mul_of_nonneg_right h3 (sample_nonneg (n+1)),
          mul_nonneg (pow_nonneg hnR.le 3) (sample_nonneg n)]
    have hscale : (n:ℝ)^3*M = (n:ℝ)^3*(fixedBandSample n+8*fixedBandSample (n+1))+
        3000*(n:ℝ)^2*(1+Real.log (((n:ℝ)+1)^4)) := by dsimp only [M]; field_simp
    have H : max (dyadicContrast (Real.exp u)) 0 ≤ (n:ℝ)^3*M :=
      max_le (by linarith only [hcell,hbase,hscale]) (by positivity)
    have hweight : Real.exp (-u/2) ≤ ((n:ℝ)^2)⁻¹ := by
      rw [← Real.exp_log (pow_pos hnR 2),← Real.exp_neg,Real.log_pow,Nat.cast_ofNat]
      apply Real.exp_le_exp.mpr
      have := hu.1
      dsimp only [grid] at this
      linarith
    exact (mul_le_mul H hweight (Real.exp_pos _).le (by positivity)).trans_eq (by field_simp)
  have h := intervalIntegral.integral_mono_on (μ := volume) hgrid (weighted_cont.intervalIntegrable _ _)
    intervalIntegrable_const point
  rw [intervalIntegral.integral_const,smul_eq_mul] at h
  change _ ≤ 4*M
  exact h.trans ((mul_le_mul_of_nonneg_right hw (mul_nonneg hnR.le hM)).trans_eq (by field_simp))

/-- A bound on the whole critical-weight integral in terms of the prime shortfall
on the same grid. The interpolation error costs only a squared logarithm. -/
theorem fixedBand_window_integral {m b : ℕ} (hm : 2 ≤ m) (hmb : m ≤ b) :
    (∫ u in 4*Real.log m..4*Real.log b, max (dyadicContrast (Real.exp u)) 0 * Real.exp (-u/2)) ≤
      36*fixedBandMass m b+48000*(1+Real.log b)^2 := by
  change (∫ u in grid m..grid b, weighted u) ≤ _
  have hsub : Finset.Ico m b ⊆ Finset.Icc m b := fun n hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hn).1,(Finset.mem_Ico.mp hn).2.le⟩
  have hmass (s : Finset ℕ) (hs : s ⊆ Finset.Icc m b) :
      ∑ n ∈ s, fixedBandSample n ≤ fixedBandMass m b :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => sample_nonneg n)
  have hshift : ∑ n ∈ Finset.Ico m b, fixedBandSample (n+1) ≤ fixedBandMass m b := by
    rw [Finset.sum_Ico_add']
    apply hmass
    intro n hn
    have h := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hinv : ∑ n ∈ Finset.Ico m b, (n:ℝ)⁻¹ ≤ 1+Real.log b := by
    have hh := harmonic_le_one_add_log b
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hh
    exact (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Ico.mp hn).1; omega,(Finset.mem_Ico.mp hn).2.le⟩)
      (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hh
  have hlog := Real.log_natCast_nonneg b
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (a := grid) hmb
    (fun _ _ => weighted_cont.intervalIntegrable _ _)]
  calc
    _ ≤ ∑ n ∈ Finset.Ico m b, 4*(fixedBandSample n+8*fixedBandSample (n+1)+
          (3000*(1+4*Real.log b))*(n:ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := cell_weighted (hm.trans (Finset.mem_Ico.mp hn).1)
        have hnb := (Finset.mem_Ico.mp hn).2
        have hl := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos n) : (0:ℝ) < (n+1:ℕ))
          (Nat.cast_le.mpr (Nat.succ_le_of_lt hnb) : ((n+1:ℕ):ℝ) ≤ b)
        rw [Nat.cast_add_one] at hl
        rw [Real.log_pow,Nat.cast_ofNat,div_eq_mul_inv] at h
        apply h.trans
        gcongr
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      nlinarith only [hmass _ hsub,hshift,mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ 3000*(1+4*Real.log b) by positivity),sq_nonneg (Real.log b),hlog]

private theorem fixedBand_log_budget {α θ δ : ℝ} (hα : 0 < α) (hgap : α < 4*(θ-1/2))
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hw : ∀ A : ℕ, ∃ m ≥ A, fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) :
    WindowHypU (localSignal (gm principalFamily)) θ δ := by
  let ε := θ-1/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  intro η hη U₀
  let K := 36+48000*(1+4/α)^2
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < 4*ε-α by dsimp [ε]; linarith)).eventually_ge_atTop K)
  obtain ⟨m,hm,hMass⟩ := hw (max 2 ⌈max T (Real.exp U₀)⌉₊)
  have hm2 : 2 ≤ m := by omega
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hm₀ := zero_lt_one.trans_le hmR
  have hlarge := Nat.ceil_le.mp ((le_max_right _ _).trans hm)
  let b := ⌈(m:ℝ)^(1+δ)⌉₊
  let U := grid m
  let V := (1+δ)*U
  have hmb : m ≤ b := by
    have hw := Real.rpow_le_rpow_of_exponent_le hmR (show (1:ℝ) ≤ 1+δ by linarith)
    rw [Real.rpow_one] at hw
    exact_mod_cast hw.trans (Nat.le_ceil _)
  have hb : b ≤ m^2 := Nat.ceil_le.mpr (by
    rw [Nat.cast_pow,← Real.rpow_natCast (m:ℝ) 2]
    apply Real.rpow_le_rpow_of_exponent_le hmR
    norm_num; linarith)
  have hb₀ : 0 < (b:ℝ) := hm₀.trans_le (Nat.cast_le.mpr hmb)
  have hlogm := Real.log_nonneg hmR
  have hU : 0 ≤ U := by dsimp [U,grid]; positivity
  have hstart : U₀ ≤ U := by
    have hs := Real.log_le_log (Real.exp_pos U₀) ((le_max_right _ _).trans hlarge)
    rw [Real.log_exp] at hs
    dsimp [U,grid]; linarith
  have hUV : U ≤ V := by dsimp [V]; nlinarith only [mul_nonneg hδ.le hU]
  have hend : V ≤ grid b := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hm₀ _) (Nat.le_ceil ((m:ℝ)^(1+δ)))
    rw [Real.log_rpow hm₀] at hlog
    dsimp only [V,U,grid,b]; linarith only [hlog]
  have hlogb := Real.log_le_log hb₀ (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hb)
  rw [Real.log_pow,Nat.cast_ofNat] at hlogb
  have hL : (1+Real.log b)^2 ≤ (1+4/α)^2*(m:ℝ)^α := by
    have hp := Real.one_le_rpow hmR (show 0 ≤ α/2 by positivity)
    have hl := Real.log_le_rpow_div hm₀.le (show 0 < α/2 by positivity)
    have hlog : 1+Real.log b ≤ (1+4/α)*(m:ℝ)^(α/2) := by
      rw [show (1+4/α)*(m:ℝ)^(α/2) = (m:ℝ)^(α/2)+2*((m:ℝ)^(α/2)/(α/2)) by ring]
      linarith
    have hs := pow_le_pow_left₀ (by positivity [Real.log_natCast_nonneg b] : 0 ≤ 1+Real.log b) hlog 2
    rwa [mul_pow,← Real.rpow_mul_natCast hm₀.le,show α/2*(2:ℕ)=α by norm_num] at hs
  let R (u : ℝ) := max (dyadicContrast (Real.exp u)) 0
  have hR : Continuous R := continuous_iff_continuousAt.mpr fun u =>
    ((contrast_cont_at (Real.exp_pos u)).comp Real.continuous_exp.continuousAt).sup continuousAt_const
  have hF : Continuous (fun u : ℝ => R u*Real.exp (-θ*u)) := by fun_prop
  have hraw := fixedBand_window_integral hm2 hmb
  change (∫ u in grid m..grid b, weighted u) ≤ 36*fixedBandMass m b+48000*(1+Real.log b)^2 at hraw
  have hmain : (∫ u in grid m..grid b, weighted u) ≤ K*(m:ℝ)^α := by
    dsimp only [K]; nlinarith only [hraw,hL,hMass]
  have hpos (u : ℝ) : 0 ≤ weighted u := mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  have hinc := intervalIntegral.integral_mono_interval (μ := volume) (a := U) le_rfl hUV hend
    (f := weighted) (Eventually.of_forall hpos) (weighted_cont.intervalIntegrable _ _)
  let w := (m:ℝ)^(-4*ε)
  have hw₀ : 0 ≤ w := Real.rpow_nonneg hm₀.le _
  have hpoint (u : ℝ) (hu : u ∈ Icc U V) : R u*Real.exp (-θ*u) ≤ w*weighted u := by
    have hdec : Real.exp (-ε*u) ≤ w := by
      dsimp only [w]; rw [Real.rpow_def_of_pos hm₀]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hu.1 hε.le
      dsimp only [U,grid] at this
      linarith only [this]
    rw [show -θ*u = -u/2+-ε*u by dsimp [ε]; ring,Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hdec (hpos u)).trans_eq' (by dsimp [weighted,R]; ring) |>.trans_eq (by ring)
  refine ⟨U,hstart,R,hF.integrableOn_Icc,fun u hu => ⟨le_max_right _ _,?_⟩,?_⟩
  · have hE := Real.exp_le_exp.mpr hu.1
    change Real.exp (grid m) ≤ Real.exp u at hE
    rw [grid_exp (by omega)] at hE
    have h4 : 4 < Real.exp u := lt_of_lt_of_le (by
      have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm2
      linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm' 4]) hE
    simpa only [Real.log_exp] using (localSignal_log h4).le.trans (le_max_left _ 0)
  · have hmono := intervalIntegral.integral_mono_on (μ := volume) hUV (hF.intervalIntegrable _ _)
      ((continuous_const.mul weighted_cont).intervalIntegrable _ _) hpoint
    change (∫ u in U..V, R u*Real.exp (-θ*u)) ≤ ∫ u in U..V, w*weighted u at hmono
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hUV]
    apply hmono.trans
    apply (mul_le_mul_of_nonneg_left (hinc.trans hmain) hw₀).trans
    have hc := hT (m:ℝ) ((le_max_left _ _).trans hlarge)
    have hbound := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hm₀.le α)) hw₀
    dsimp only [w] at hbound
    rw [← Real.rpow_add hm₀,← Real.rpow_add hm₀,show -4*ε+(4*ε-α+α)=0 by ring,Real.rpow_zero] at hbound
    exact hbound.trans (Real.one_le_exp (mul_nonneg hη.le hU))

/-- A power bound for the fixed prime band on one cofinal sequence of windows
gives a quantitative zero-free half-plane. -/
theorem zeta_ne_zero_of_fixedBandMass {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hw : ∀ A : ℕ, ∃ m ≥ A, fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α)
    {s : ℂ} (hs : 1/2+α/4 < s.re) : riemannZeta s ≠ 0 := by
  by_cases hs₁ : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hs₁
  let θ := (1/2+α/4+s.re)/2
  have hgap : α < 4*(θ-1/2) := by dsimp [θ]; linarith
  obtain ⟨Φ,hΦ⟩ := poleData principalFamily
  have hp := local_pole_data hΦ zeta_strip
  have hW := fixedBand_log_budget hα hgap hδ hδ₁ hw
  intro hz
  have hmem : s ∈ zeroSet principalFamily := ⟨by linarith,none,Or.inl (by
    simpa [principalFamily,famD,DirichletCharacter.LFunction_modOne_eq] using hz)⟩
  have := landau_window hp (by dsimp [θ]; linarith) (by dsimp [θ]; linarith) hδ hW s hmem
  dsimp only [θ] at this
  linarith

/-- One fixed prime band per sample suffices. The input counts only ordinary
primes n⁴/4 < p < n⁴ and has no free auxiliary endpoints. -/
theorem rh_of_fixedBandMass_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) : RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨δ,hδ,hδ₁,hw⟩ := h (s.re-1/2) (by linarith)
  exact zeta_ne_zero_of_fixedBandMass (by linarith) hδ hδ₁ hw (by linarith)

/-- A logarithmic bound at arbitrarily late square windows supplies the forward
RH implication on the small analytic import closure. -/
theorem rh_of_fixedBandMass_log_squareWindows
    (hwin : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMass m (m^2) ≤ C*(1+2*Real.log m)) : RiemannHypothesis := by
  obtain ⟨C,hC,h⟩ := hwin
  apply rh_of_fixedBandMass_powerWindows
  intro α hα
  refine ⟨1,one_pos,le_rfl,fun A => ?_⟩
  have hlog := ((isLittleO_log_rpow_atTop hα).const_mul_left (3*C)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hlog.and (Real.tendsto_log_atTop.eventually_ge_atTop 1))
  obtain ⟨m,hm,hw⟩ := h (max A ⌈T⌉₊)
  obtain ⟨hs,hl⟩ := hT m (Nat.ceil_le.mp ((le_max_right _ _).trans hm))
  change ‖3*C*Real.log m‖ ≤ 1*‖(m:ℝ)^α‖ at hs
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity [show 0 ≤ Real.log m by linarith]),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _),one_mul] at hs
  refine ⟨m,(le_max_left _ _).trans hm,?_⟩
  rw [show (1:ℝ)+1=2 by norm_num,Real.rpow_two,← Nat.cast_pow,Nat.ceil_natCast]
  exact hw.trans (by nlinarith only [hs,mul_le_mul_of_nonneg_left hl hC])

/-- An off-critical zero forces a polynomial excess on every sufficiently late
window of each fixed width, with a sharp threshold determined by its real part. -/
theorem fixedBandMass_eventually_gt_of_zero {s : ℂ} (hz : riemannZeta s = 0)
    {α δ : ℝ} (hα : 0 < α) (hs : α < 4*s.re-2) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)^α < fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ := by
  by_contra hn
  have hfreq := frequently_atTop.mp (not_eventually.mp hn)
  apply zeta_ne_zero_of_fixedBandMass hα hδ hδ₁ (fun A => ?_) (by linarith : 1/2+α/4 < s.re) hz
  obtain ⟨m,hm,hh⟩ := hfreq A
  exact ⟨m,hm,le_of_not_gt hh⟩

private def cut (z c v : ℝ) := (Iic z).indicator (fun _ => c) v

private theorem cut_integral (z c : ℝ) :
    IntervalIntegrable (cut z c) volume 1 2 ∧
    (∫ v in (1:ℝ)..2, cut z c v) = c*(max (z-1) 0-max (z-2) 0) := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 2)).mpr
    ((integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by finiteness)).indicator
      measurableSet_Iic),?_⟩
  rcases le_or_gt z 1 with hz|hz
  · have he : ∫ v in (1:ℝ)..2, cut z c v = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro v hv
      exact indicator_of_notMem (s := Iic z) (not_le.mpr (hz.trans_lt hv.1)) _
    rw [he,max_eq_right (by linarith : z-1 ≤ 0),max_eq_right (by linarith : z-2 ≤ 0)]
    ring
  rcases le_or_gt z 2 with hz'|hz'
  · have hi := intervalIntegral.integral_indicator (μ := volume) (f := fun _ => c)
      (show z ∈ Icc (1:ℝ) 2 from ⟨hz.le,hz'⟩)
    rw [intervalIntegral.integral_const,smul_eq_mul] at hi
    rw [max_eq_left (by linarith : 0 ≤ z-1),max_eq_right (by linarith : z-2 ≤ 0)]
    exact hi.trans (by ring)
  · rw [max_eq_left (by linarith : 0 ≤ z-1),max_eq_left (by linarith : 0 ≤ z-2)]
    have he : (∫ v in (1:ℝ)..2, cut z c v) = ∫ _ in (1:ℝ)..2, c := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (by norm_num)] at hv
      exact indicator_of_mem (s := Iic z) (hv.2.trans hz'.le) _
    rw [he,intervalIntegral.integral_const,smul_eq_mul]; ring

private theorem theta_cut {x y v : ℝ} (hx : 0 ≤ y) (hy : y ≤ x) (hv : 1 ≤ v) :
    Chebyshev.theta (y/v) =
      ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, cut (y/p) (Real.log p) v := by
  let S := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hxy : y/v ≤ x := (div_le_self hx hv).trans hy
  have H : S.filter (fun p : ℕ => v ≤ y/p) = (Finset.Ioc 0 ⌊y/v⌋₊).filter Nat.Prime := by
    ext p
    simp only [S,Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hp,_⟩,hprime⟩,hh⟩
      have hp₀ : (0:ℝ) < p := Nat.cast_pos.mpr hp
      have hmul := (le_div_iff₀ hp₀).mp hh
      refine ⟨⟨hp,Nat.le_floor ((le_div_iff₀ hv₀).mpr ?_)⟩,hprime⟩
      linarith only [hmul]
    · rintro ⟨⟨hp,hp'⟩,hprime⟩
      have hh := (Nat.cast_le.mpr hp' : (p:ℝ) ≤ ⌊y/v⌋₊).trans (Nat.floor_le (div_nonneg hx hv₀.le))
      exact ⟨⟨⟨hp,hp'.trans (Nat.floor_mono hxy)⟩,hprime⟩,(le_div_iff₀ (Nat.cast_pos.mpr hp)).mpr
        (by simpa only [mul_comm] using (le_div_iff₀ hv₀).mp hh)⟩
  rw [Chebyshev.theta,← H,Finset.sum_filter]
  rfl

private theorem integrated_cuts (S : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (∑ p ∈ S, c p*dyadicPrimeWeight x p) =
      (∫ v in (1:ℝ)..2, ∑ p ∈ S, cut (x/p) (c p) v) -
        ∫ v in (1:ℝ)..2, ∑ p ∈ S, cut ((x/2)/p) (c p) v := by
  rw [intervalIntegral.integral_finsetSum (s := S) (fun (p : ℕ) _ => (cut_integral (x/p) (c p)).1),
    intervalIntegral.integral_finsetSum (s := S) (fun (p : ℕ) _ => (cut_integral ((x/2)/p) (c p)).1),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [(cut_integral _ _).2,(cut_integral _ _).2]
  have hscale (t : ℝ) : max (t-2) 0 = 2*max (t/2-1) 0 := by
    rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hscale (x/p),hscale ((x/2)/p)]
  unfold dyadicPrimeWeight
  rw [show x/(p:ℝ)/2=(x/2)/p by ring,show (x/2)/(p:ℝ)/2=(x/4)/p by ring]
  ring

/-- Exact average of ordinary, unweighted doubling-interval shortfalls. The
integration variable ranges over [1,2] for every physical scale x. -/
theorem dyadicPrimeDeficit_doubling_average {x : ℝ} (hx : 0 < x) :
    dyadicPrimeDeficit x = ∫ v in (1:ℝ)..2,
      (x/2)/v - (Chebyshev.theta (x/v)-Chebyshev.theta ((x/2)/v)) := by
  let S := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  let f (y v : ℝ) := ∑ p ∈ S, cut (y/p) (Real.log p) v
  have hint (y : ℝ) : IntervalIntegrable (f y) volume 1 2 := by
    simpa only [f,← Finset.sum_apply] using IntervalIntegrable.sum S
      (fun p _ => (cut_integral (y/p) (Real.log p)).1)
  have h₀ : IntervalIntegrable (fun v : ℝ => (x/2)/v) volume 1 2 :=
    (continuousOn_const.div continuousOn_id fun v hv => by
      rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hv; exact ne_of_gt (zero_lt_one.trans_le hv.1)).intervalIntegrable
  have he : (∫ v in (1:ℝ)..2, (x/2)/v - (Chebyshev.theta (x/v)-Chebyshev.theta ((x/2)/v))) =
      ∫ v in (1:ℝ)..2, (x/2)/v - (f x v-f (x/2) v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num)] at hv
    dsimp only
    rw [theta_cut hx.le le_rfl hv.1,theta_cut (by positivity : 0 ≤ x/2) (by linarith : x/2 ≤ x) hv.1]
  rw [he,intervalIntegral.integral_sub h₀ ((hint _).sub (hint _)),
    intervalIntegral.integral_sub (hint _) (hint _)]
  have hbase : (∫ v in (1:ℝ)..2, (x/2)/v) = x*Real.log 2/2 := by
    simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul,integral_inv_of_pos
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)]
    ring
  rw [hbase,dyadicPrimeDeficit]
  congr 1
  exact integrated_cuts S (fun p => Real.log p) x

/-- The integer count in the same doubling intervals gives the finite main term. -/
private theorem floor_cuts {x y v : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hv : 1 ≤ v) :
    (∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, cut (y/k) 1 v) = (⌊y/v⌋₊:ℝ) := by
  let S := Finset.Ioc 0 ⌊x⌋₊
  have hv₀ := zero_lt_one.trans_le hv
  have H : S.filter (fun k : ℕ => v ≤ y/k) = Finset.Ioc 0 ⌊y/v⌋₊ := by
    ext k
    simp only [S,Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hk,_⟩,hh⟩
      have ht := (le_div_iff₀ (Nat.cast_pos.mpr hk)).mp hh
      exact ⟨hk,Nat.le_floor ((le_div_iff₀ hv₀).mpr (by linarith only [ht]))⟩
    · rintro ⟨hk,hh⟩
      have ht := (Nat.cast_le.mpr hh : (k:ℝ) ≤ ⌊y/v⌋₊).trans (Nat.floor_le (div_nonneg hy hv₀.le))
      exact ⟨⟨hk,hh.trans (Nat.floor_mono ((div_le_self hy hv).trans hyx))⟩,
        (le_div_iff₀ (Nat.cast_pos.mpr hk)).mpr (by simpa only [mul_comm] using (le_div_iff₀ hv₀).mp ht)⟩
  change (∑ k ∈ S, if v ≤ y/k then (1:ℝ) else 0) = _
  rw [← Finset.sum_filter,H]
  simp

/-- The signed difference between ordinary integers and log-weighted primes, observed
with identical weights and endpoints. -/
def fixedBandIntegerDiscrepancy (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - if k.Prime then Real.log k else 0)*dyadicPrimeWeight x k

/-- Counting integers in a doubling interval costs at most one, uniformly
also after averaging the interval. -/
theorem fixedBandIntegerDiscrepancy_error {x : ℝ} (hx : 0 < x) :
    |dyadicPrimeDeficit x-fixedBandIntegerDiscrepancy x| ≤ 1 := by
  let S := Finset.Ioc 0 ⌊x⌋₊
  let f (y v : ℝ) := ∑ k ∈ S, cut (y/k) 1 v
  let r (v : ℝ) := (x/2)/v
  have hi (y : ℝ) : IntervalIntegrable (f y) volume 1 2 := by
    simpa only [f,← Finset.sum_apply] using IntervalIntegrable.sum S
      (fun k _ => (cut_integral (y/k) 1).1)
  have hr : IntervalIntegrable r volume 1 2 :=
    (continuousOn_const.div continuousOn_id fun v hv => by
      rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hv; exact ne_of_gt (zero_lt_one.trans_le hv.1)).intervalIntegrable
  have base : (∫ v in (1:ℝ)..2, r v) = x*Real.log 2/2 := by
    simp only [r,div_eq_mul_inv,intervalIntegral.integral_const_mul,integral_inv_of_pos
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)]
    ring
  have repr : dyadicPrimeDeficit x-fixedBandIntegerDiscrepancy x =
      ∫ v in (1:ℝ)..2, r v-(f x v-f (x/2) v) := by
    rw [intervalIntegral.integral_sub hr ((hi _).sub (hi _)),base,intervalIntegral.integral_sub (hi _) (hi _)]
    change _ = _ - ((∫ v in (1:ℝ)..2, ∑ k ∈ S, cut (x/k) 1 v) -
      ∫ v in (1:ℝ)..2, ∑ k ∈ S, cut ((x/2)/k) 1 v)
    rw [← integrated_cuts S (fun _ => 1) x]
    simp only [S,dyadicPrimeDeficit,fixedBandIntegerDiscrepancy,sub_mul,one_mul,
      Finset.sum_sub_distrib,Finset.sum_filter,ite_mul,zero_mul]
    ring
  have point {v : ℝ} (hv : v ∈ Icc (1:ℝ) 2) : |r v-(f x v-f (x/2) v)| ≤ 1 := by
    dsimp only [r,f,S]
    rw [floor_cuts hx.le le_rfl hv.1,floor_cuts (by positivity : 0 ≤ x/2) (by linarith : x/2 ≤ x) hv.1]
    have hv₀ := zero_lt_one.trans_le hv.1
    have hre : x/v = 2*((x/2)/v) := by ring
    have h₁ := Nat.floor_le (div_nonneg hx.le hv₀.le)
    have h₂ := Nat.lt_floor_add_one ((x/2)/v)
    have h₃ := Nat.lt_floor_add_one (x/v)
    have h₄ := Nat.floor_le (show 0 ≤ (x/2)/v by positivity)
    exact abs_le.mpr ⟨by linarith only [hre,h₁,h₂],by linarith only [hre,h₃,h₄]⟩
  rw [repr]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1:ℝ)) (b := 2)
    (f := fun v => r v-(f x v-f (x/2) v)) (C := 1) (fun v hv => by
      rw [uIoc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hv
      exact (Real.norm_eq_abs _).trans_le (point ⟨hv.1.le,hv.2⟩))
  simpa only [Real.norm_eq_abs,show (2:ℝ)-1=1 by norm_num,abs_one,mul_one,one_mul] using he

/-- Every positive scale has unit error when the smooth band mass is replaced
by integer lattice points. -/
theorem fixedBand_lattice_error {x : ℝ} (hx : 0 < x) :
    |x*Real.log 2/2 - ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, dyadicPrimeWeight x k| ≤ 1 := by
  have h := fixedBandIntegerDiscrepancy_error hx
  simp only [dyadicPrimeDeficit,fixedBandIntegerDiscrepancy,sub_mul,one_mul,
    Finset.sum_sub_distrib,Finset.sum_filter,ite_mul,zero_mul] at h
  convert h using 2
  ring

/-- Positive mass of the centered coefficients on the same fixed bands. -/
def fixedBandIntegerMass (m b : ℕ) : ℝ := ∑ n ∈ Finset.Icc m b,
  max (fixedBandIntegerDiscrepancy ((n:ℝ)^4)) 0/(n:ℝ)^3

/-- The total cost of using the integer main term tends to zero independently of
the last index, even after taking positive parts at each sample. -/
theorem fixedBandIntegerMass_error {m b : ℕ} (hm : 2 ≤ m) (hmb : m ≤ b) :
    |fixedBandMass m b-fixedBandIntegerMass m b| ≤ 1/(m:ℝ)^2 := by
  let f (n : ℕ) : ℝ := -(1/(n:ℝ)^2)
  unfold fixedBandMass fixedBandIntegerMass fixedBandSample
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc m b, (f (n+1)-f n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hm.trans (Finset.mem_Icc.mp hn).1
      have hn₀ : 0 < (n:ℝ) := by linarith
      rw [← sub_div,abs_div,abs_of_nonneg (pow_nonneg hn₀.le 3)]
      apply (div_le_div_of_nonneg_right ((abs_max_sub_max_le_abs _ _ 0).trans
        (fixedBandIntegerDiscrepancy_error (pow_pos hn₀ 4))) (pow_nonneg hn₀.le 3)).trans
      dsimp only [f]
      push_cast
      field_simp
      nlinarith only [mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith) (show 0 ≤ (n:ℝ)+1 by positivity)]
    _ = f (b+1)-f m := by
      rw [← Finset.Ico_succ_right_eq_Icc]
      change (∑ n ∈ Finset.Ico m (b+1), (f (n+1)-f n)) = _
      rw [Finset.sum_Ico_eq_sub _ (by omega),Finset.sum_range_sub f,Finset.sum_range_sub f]
      ring
    _ ≤ _ := by dsimp only [f]; linarith only [show 0 ≤ 1/((b+1:ℕ):ℝ)^2 by positivity]

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.dyadic_multiplier_nonzero,
      ``RiemannGaussian.AlpogeMined.dyadicPrimeWeight_formula,
      ``RiemannGaussian.AlpogeMined.dyadicContrast_le_primeDeficit,
      ``RiemannGaussian.AlpogeMined.dyadicPrimeDeficit_power_cost,
      ``RiemannGaussian.AlpogeMined.fixedBand_window_integral,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandMass_powerWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandMass_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.fixedBandMass_eventually_gt_of_zero,
      ``RiemannGaussian.AlpogeMined.fixedBandIntegerDiscrepancy_error,
      ``RiemannGaussian.AlpogeMined.fixedBandIntegerMass_error,
      ``RiemannGaussian.AlpogeMined.dyadicPrimeDeficit_doubling_average] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
