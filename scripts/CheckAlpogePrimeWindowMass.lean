import AlpogePrimeWindows
import CheckAlpogeMinedBounds

/-! # Total positive ordinary-prime deficit on fourth-power windows -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Set MeasureTheory AlpogeZetaSamples AlpogeWindow

/-- The positive shortfall at the fourth power, with its weight in the Landau integral. -/
def fourthDeficitMass (n : ℕ) : ℝ :=
  max (Real.eulerMascheroniConstant*(n:ℝ)^4 - largePrimeSum (n^4)) 0 / (n:ℝ)^3

/-- Total positive shortfall on a closed interval of fourth-power indices. -/
def primeMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc m b, fourthDeficitMass n

/-- Total positive shortfall on the indices from m to m squared, including both endpoints. -/
def primeWindowMass (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc m (m^2), fourthDeficitMass n

private theorem mass_nonneg (n : ℕ) : 0 ≤ fourthDeficitMass n :=
  div_nonneg (le_max_right _ _) (by positivity)

private theorem fourth_sample (n : ℕ) (hn : 1 ≤ n) :
    G ((n:ℝ)^4) ≤ (n:ℝ)^3 * fourthDeficitMass n + (n:ℝ)^2 := by
  obtain ⟨_,_,h⟩ := large_prime_sample_bounds
  have hu := (h (n^4) (Nat.one_le_pow _ _ hn)).2
  push_cast at hu
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hl := Real.log_le_sub_one_of_pos (pow_pos hn0 2)
  rw [Real.log_pow] at hu hl
  unfold fourthDeficitMass
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 3 hn0.ne')]
  norm_num only [Nat.cast_ofNat] at hu hl
  linarith only [hu,hl,le_max_left (Real.eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4)) 0]

private def weightedPositive (x : ℝ) := max (G x) 0 * x^(-(1/2:ℝ)-1)

private theorem weighted_continuous {a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn weightedPositive (Icc a b) := by
  have hK : 0 ≤ Real.log 4 + 7 := by positivity
  have hLip : LipschitzOnWith ⟨_,hK⟩ G (Icc a b) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    exact G_lipschitz (by linarith [hx.1]) (by linarith [hy.1])
  exact (hLip.continuousOn.sup continuousOn_const).mul
    (continuousOn_id.rpow_const (fun x hx => Or.inl (show x ≠ 0 by linarith [hx.1])))

private theorem cell_integral (n : ℕ) (hn : 1 ≤ n) :
    (∫ x in (n:ℝ)^4..((n:ℝ)+1)^4, weightedPositive x) ≤
      15 * (fourthDeficitMass n + 8 * fourthDeficitMass (n+1) + 229 / (n:ℝ)) := by
  let t : ℝ := n
  have ht : 1 ≤ t := by dsimp [t]; exact_mod_cast hn
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hnext : ((n+1:ℕ):ℝ) = t+1 := Nat.cast_add_one _
  have hle : t^4 ≤ (t+1)^4 := by gcongr; linarith
  have h1 := one_le_pow₀ ht (n := 4)
  have ht2 : (t+1)^2 ≤ 4*t^2 := by nlinarith [sq_nonneg (t-1)]
  have ht3 : (t+1)^3 ≤ 8*t^3 := by
    calc _ ≤ (2*t)^3 := by gcongr; linarith
         _ = _ := by ring
  have ha := fourth_sample n hn
  have hb := fourth_sample (n+1) (by omega)
  rw [hnext] at hb
  let M := fourthDeficitMass n + 8*fourthDeficitMass (n+1) + 229/t
  have hM : 0 ≤ M := add_nonneg (add_nonneg (mass_nonneg n) (mul_nonneg (by norm_num) (mass_nonneg (n+1)))) (by positivity)
  have bound (x : ℝ) (hx : x ∈ Icc (t^4) ((t+1)^4)) : weightedPositive x ≤ M / t^3 := by
    have hs : Real.sqrt x ≤ (t+1)^2 := (Real.sqrt_le_iff.mpr
      ⟨sq_nonneg _,by nlinarith only [hx.2]⟩)
    have hch := G_le_fourth_endpoints hn (show x ∈ Icc ((n:ℝ)^4) (((n:ℝ)+1)^4) from hx)
    have hm : max (G (t^4)) (G ((t+1)^4)) ≤
        t^3*(fourthDeficitMass n+8*fourthDeficitMass (n+1)) + 4*t^2 := by
      apply max_le
      · nlinarith only [ha, mul_nonneg (pow_nonneg ht0.le 3) (mass_nonneg (n+1)),sq_nonneg t]
      · nlinarith only [hb,ht2,mul_le_mul_of_nonneg_right ht3 (mass_nonneg (n+1)),
          mul_nonneg (pow_nonneg ht0.le 3) (mass_nonneg n)]
    have hscale : t^3*M = t^3*(fourthDeficitMass n+8*fourthDeficitMass (n+1)) + 229*t^2 := by
      dsimp only [M]; field_simp
    have hg : max (G x) 0 ≤ t^3*M := max_le (by linarith only [hm,hs,ht2,hch,hscale]) (by positivity)
    have hw := Real.rpow_le_rpow_of_nonpos (pow_pos ht0 4) hx.1
      (by norm_num : -(1/2:ℝ)-1 ≤ 0)
    rw [← Real.rpow_natCast_mul ht0.le] at hw
    norm_num [Real.rpow_neg ht0.le] at hw
    calc weightedPositive x ≤ (t^3*M) * (t^6)⁻¹ :=
          mul_le_mul hg (by convert hw using 1; norm_num) (Real.rpow_nonneg (zero_le_one.trans (h1.trans hx.1)) _) (by positivity)
         _ = M / t^3 := by field_simp
  have hi : IntervalIntegrable weightedPositive volume (t^4) ((t+1)^4) := (weighted_continuous (b := (t+1)^4) h1).intervalIntegrable_of_Icc hle
  have h := intervalIntegral.integral_mono_on hle hi (g := fun _ => M/t^3) intervalIntegrable_const bound
  rw [intervalIntegral.integral_const,smul_eq_mul] at h
  have hgap : (t+1)^4-t^4 ≤ 15*t^3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 11*t^2+5*t+1 by positivity)]
  exact h.trans ((mul_le_mul_of_nonneg_right hgap (div_nonneg hM (by positivity))).trans_eq
    (by change 15*t^3*(M/t^3) = 15*M; field_simp))


/-- Total inverse-cube mass on any interval starting at m ≥ 2. -/
theorem primeWindow_inv_cube_le {m b : ℕ} (hm : 2 ≤ m) (hmn : m ≤ b) :
    (∑ n ∈ Finset.Icc m b, 1/(n:ℝ)^3) ≤ 1/(m:ℝ)^2 := by
  let f (n : ℕ) : ℝ := -(1/(n:ℝ)^2)
  calc _ ≤ ∑ n ∈ Finset.Icc m b, (f (n+1)-f n) := by
         apply Finset.sum_le_sum
         intro n hn
         have hn2 : 2 ≤ (n:ℝ) := by exact_mod_cast hm.trans (Finset.mem_Icc.mp hn).1
         have hn0 : 0 < (n:ℝ) := by linarith
         dsimp [f]
         push_cast
         field_simp
         nlinarith only [mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith) (show 0 ≤ (n:ℝ)+1 by positivity)]
       _ = f (b+1)-f m := by
         rw [← Finset.Ico_succ_right_eq_Icc]
         change (∑ n ∈ Finset.Ico m (b+1), (f (n+1)-f n)) = _
         rw [Finset.sum_Ico_eq_sub _ (by omega),Finset.sum_range_sub f,Finset.sum_range_sub f]
         ring
       _ ≤ _ := by dsimp [f]; linarith only [show 0 ≤ 1/((b+1:ℕ):ℝ)^2 by positivity]

/-- The reciprocal index weights in a prime window have at most harmonic mass. -/
theorem primeWindow_harmonic_le {a b : ℕ} (ha : 1 ≤ a) :
    ∑ n ∈ Finset.Icc a b, (n:ℝ)⁻¹ ≤ 1+Real.log b := by
  have h := harmonic_le_one_add_log b
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at h
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left ha)
    (fun _ _ _ => by positivity)).trans h

/-- A finite window of fourth-power samples controls the intervening positive-part
Mellin integral at exponent one half. -/
theorem positive_integral_le_primeMassOn {m b : ℕ} (hm : 1 ≤ m) (hab : m ≤ b) :
    (∫ x in (m:ℝ)^4..(b:ℝ)^4, max (G x) 0 * x^(-(1/2:ℝ)-1)) ≤
      135*primeMassOn m b + 3435*(1+Real.log b) := by
  have hsub : Finset.Ico m b ⊆ Finset.Icc m b := fun _ hn =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hn).1,(Finset.mem_Ico.mp hn).2.le⟩
  have hmass (s : Finset ℕ) (hs : s ⊆ Finset.Icc m b) :
      ∑ n ∈ s, fourthDeficitMass n ≤ primeMassOn m b :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => mass_nonneg n)
  have hshift : ∑ n ∈ Finset.Ico m b, fourthDeficitMass (n+1) ≤ primeMassOn m b := by
    rw [Finset.sum_Ico_add']
    apply hmass
    intro n hn
    have h := Finset.mem_Ico.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hinv := (Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => (n:ℝ)⁻¹)
    hsub (fun _ _ _ => by positivity)).trans (primeWindow_harmonic_le hm)
  change (∫ x in (m:ℝ)^4..(b:ℝ)^4, weightedPositive x) ≤ _
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n:ℝ)^4) hab]
  · calc
      _ ≤ ∑ n ∈ Finset.Ico m b, 15 * (fourthDeficitMass n + 8*fourthDeficitMass (n+1) + 229*(n:ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa only [Nat.cast_add_one,div_eq_mul_inv] using cell_integral n (hm.trans (Finset.mem_Ico.mp hn).1)
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        linarith only [hmass _ hsub,hshift,hinv]
  · intro n hn
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hm.trans hn.1
    apply ContinuousOn.intervalIntegrable_of_Icc _ (weighted_continuous (one_le_pow₀ h1))
    gcongr
    exact_mod_cast Nat.le_succ n

/-- The interpolation estimate for the window from m to m squared. -/
theorem positive_integral_le_primeWindowMass (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (m:ℝ)^4..(m:ℝ)^8, max (G x) 0 * x^(-(1/2:ℝ)-1)) ≤
      135*primeWindowMass m + 3435*(1+2*Real.log m) := by
  have h := positive_integral_le_primeMassOn hm (Nat.le_self_pow (by decide : 2 ≠ 0) m)
  rw [show ((m^2:ℕ):ℝ)^4 = (m:ℝ)^8 by push_cast; ring] at h
  simpa only [primeWindowMass, primeMassOn, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h

/-- The first index whose fourth power reaches the right end of the power window. -/
def powerWindowEnd (δ : ℝ) (m : ℕ) : ℕ := ⌈(m:ℝ)^(1+δ)⌉₊

@[simp] theorem powerWindowEnd_one (m : ℕ) : powerWindowEnd 1 m = m^2 := by
  rw [powerWindowEnd, show (1:ℝ)+1 = (2:ℕ) by norm_num, Real.rpow_natCast, ← Nat.cast_pow,
    Nat.ceil_natCast]

theorem powerWindowEnd_bounds {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    m ≤ powerWindowEnd δ m ∧ powerWindowEnd δ m ≤ m^2 := by
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  constructor
  · have h : (m:ℝ) ≤ (m:ℝ)^(1+δ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hmR (show (1:ℝ) ≤ 1+δ by linarith)
    exact_mod_cast h.trans (Nat.le_ceil ((m:ℝ)^(1+δ)))
  · apply Nat.ceil_le.mpr
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hmR (by norm_num; linarith)

/-- A cofinal bound of order (m^α) on the positive prime mass excludes zeros
in the half-plane to the right of (1/2+α/4). -/
theorem zeta_ne_zero_of_primeMassOn_powerWindows {α θ δ C : ℝ}
    (hα : 0 < α) (hθ : 1/2+α/4 < θ) (hθ1 : θ < 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, primeMassOn m (powerWindowEnd δ m) ≤ C*(m:ℝ)^α) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  let ε := θ-(1/2:ℝ)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hslack : 0 < 4*ε-α := by dsimp [ε]; linarith
  have hw : Deduction.WindowHyp zetaFamily θ δ := by
    intro η hη Y₀
    let K := 135*C+3435*(1+2/α)
    obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp
      ((tendsto_rpow_atTop hslack).eventually_ge_atTop K)
    obtain ⟨m,hm,hbmass⟩ := h (max 1 ⌈max L Y₀⌉₊)
    let b := powerWindowEnd δ m
    let y := (m:ℝ)^4
    let z := y^(1+δ)
    have hm1 := (le_max_left _ _).trans hm
    have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast hm1
    have hm0 := zero_lt_one.trans_le hmR
    have hbig : max L Y₀ ≤ (m:ℝ) := Nat.ceil_le.mp ((le_max_right _ _).trans hm)
    obtain ⟨hmb,hbm⟩ := powerWindowEnd_bounds hm1 hδ.le hδ1
    have hb0 : 0 < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hy : 1 ≤ y := one_le_pow₀ hmR
    have hyz : y ≤ z := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hy (show (1:ℝ) ≤ 1+δ by linarith)
    have hzb : z ≤ (b:ℝ)^4 := by
      have hb : (m:ℝ)^(1+δ) ≤ (b:ℝ) := Nat.le_ceil _
      calc
        z = ((m:ℝ)^(1+δ))^4 := by
          dsimp only [z,y]
          rw [← Real.rpow_natCast_mul hm0.le, ← Real.rpow_mul_natCast hm0.le]
          congr 1
          ring
        _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hm0.le _) hb 4
    let F := fun x : ℝ => max (G x) 0 * x^(-θ-1)
    have hfactor (x : ℝ) (hx0 : 0 < x) : F x = weightedPositive x * x^(-ε) := by
      dsimp only [F, weightedPositive]
      rw [show -θ-1 = (-(1/2:ℝ)-1)+(-ε) by dsimp [ε]; ring,
        Real.rpow_add hx0, mul_assoc]
    have hF : ContinuousOn F (Icc y z) := by
      exact ((weighted_continuous hy).mul (continuousOn_id.rpow_const
        fun _ hx => Or.inl (zero_lt_one.trans_le (hy.trans hx.1)).ne')).congr
        (fun x hx => hfactor x (zero_lt_one.trans_le (hy.trans hx.1)))
    let w := (m:ℝ)^(-4*ε)
    have hpoint (x : ℝ) (hx : x ∈ Icc y z) : F x ≤ w * weightedPositive x := by
      have hx0 := zero_lt_one.trans_le (hy.trans hx.1)
      have hr := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hy) hx.1 (neg_nonpos.mpr hε.le)
      change x^(-ε) ≤ ((m:ℝ)^4)^(-ε) at hr
      rw [← Real.rpow_natCast_mul hm0.le] at hr
      have hr' : x^(-ε) ≤ w := by
        simpa only [w, Nat.cast_ofNat, mul_neg, neg_mul] using hr
      have hp : 0 ≤ weightedPositive x :=
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
      rw [hfactor x hx0, mul_comm w]
      exact mul_le_mul_of_nonneg_left hr' hp
    have hcont : ContinuousOn weightedPositive (Icc y z) := weighted_continuous hy
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hyz (hF.intervalIntegrable_of_Icc hyz)
      ((continuousOn_const.mul hcont).intervalIntegrable_of_Icc hyz) hpoint
    change (∫ x in y..z, F x) ≤ ∫ x in y..z, w*weightedPositive x at hmono
    rw [intervalIntegral.integral_const_mul] at hmono
    have hlong := intervalIntegral.integral_mono_interval (μ := volume) le_rfl hyz hzb
      (f := weightedPositive) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact mul_nonneg (le_max_right _ _)
          (Real.rpow_nonneg (zero_le_one.trans (hy.trans hx.1.le)) _))
      ((weighted_continuous hy).intervalIntegrable_of_Icc (hyz.trans hzb))
    have hlogb : Real.log b ≤ 2*Real.log m := by
      have hl := Real.log_le_log hb0 (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hbm)
      rwa [Real.log_pow, Nat.cast_ofNat] at hl
    have hbound : (∫ x in y..(b:ℝ)^4, weightedPositive x) ≤ K*(m:ℝ)^α := by
      have hi := positive_integral_le_primeMassOn hm1 hmb
      have hl := Real.log_le_rpow_div hm0.le hα
      have hr := Real.one_le_rpow hmR hα.le
      change (∫ x in y..(b:ℝ)^4, weightedPositive x) ≤ _ at hi
      calc
        _ ≤ 135*primeMassOn m b + 3435*(1+Real.log b) := hi
        _ ≤ 135*(C*(m:ℝ)^α) + 3435*((m:ℝ)^α+2*((m:ℝ)^α/α)) := by
          linarith only [hbmass, hlogb, hl, hr]
        _ = _ := by dsimp [K]; ring
    have hy₀ : Y₀ ≤ y := ((le_max_right _ _).trans hbig).trans (le_self_pow₀ hmR (by decide))
    refine ⟨y, hy₀, fun x => max (G x) 0, hF.integrableOn_Icc, ?_, ?_⟩
    · intro x _
      refine ⟨le_max_right _ _,?_⟩
      rw [gm_zeta]
      have he : Deduction.G x = G x := by
        unfold Deduction.G Deduction.ramp G ramp
        rw [Complex.re_sum]
        simp only [mul_one,← Complex.ofReal_mul,Complex.ofReal_re]
      exact he.trans_le (le_max_left _ _)
    · change (∫ x in Icc y z, F x) ≤ y^η
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyz]
      calc
        _ ≤ w * (∫ x in y..z, weightedPositive x) := hmono
        _ ≤ w * (K*(m:ℝ)^α) :=
          mul_le_mul_of_nonneg_left (hlong.trans hbound) (Real.rpow_nonneg hm0.le _)
        _ ≤ w * ((m:ℝ)^(4*ε-α)*(m:ℝ)^α) := by
          gcongr
          exact hL m ((le_max_left _ _).trans hbig)
        _ = 1 := by
          dsimp only [w]
          rw [← Real.rpow_add hm0, ← Real.rpow_add hm0, show -4*ε+(4*ε-α+α) = 0 by ring,
            Real.rpow_zero]
        _ ≤ y^η := Real.one_le_rpow hy hη.le
  intro s hs
  have hz := Deduction.lemmaL zetaFamily (show 0 < θ by linarith) hθ1 hδ hw
  simpa only [zetaFamily, DirichletCharacter.LFunction_modOne_eq] using hz () s hs

/-- For each exponent it suffices to find arbitrarily late windows of one fixed
positive power width on which the total positive mass obeys that exponent. -/
theorem rh_of_primeMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, primeMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  let α := s.re-(1/2:ℝ)
  let θ := ((1/2:ℝ)+s.re)/2
  have hα : 0 < α := by dsimp [α]; linarith
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  exact zeta_ne_zero_of_primeMassOn_powerWindows (C := 1) hα
    (by dsimp [α,θ]; linarith : 1/2+α/4 < θ) (by dsimp [θ]; linarith) hδ hδ1
    (by simpa only [one_mul] using hw) s (by dsimp [θ]; linarith)

open Finset Real Filter in
/-- A cubic logarithmic loss on each window preserves cofinal subpower bounds. -/
theorem subpowerWindows_of_log_cube_error {F G : ℕ → ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ {m b : ℕ}, 8 ≤ m → F m b ≤ G m b + K*(1+log b)^3)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, G m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, F m (powerWindowEnd δ m) ≤ (m:ℝ)^α := by
  intro α hα
  have hp := half_pos hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h (α/2) hp
  have hlog := ((isLittleO_log_rpow_rpow_atTop (3:ℝ) hp).const_mul_left (27*K)).bound
    (by norm_num : (0:ℝ)<1)
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp ((hlog.and
    (tendsto_log_atTop.eventually_ge_atTop 1)).and ((tendsto_rpow_atTop hp).eventually_ge_atTop 2))
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,hb⟩ := hw (max (max 8 A) ⌈R⌉₊)
  have hm8 : 8 ≤ m := by omega
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  let b := powerWindowEnd δ m
  obtain ⟨hmb,hbm⟩ := powerWindowEnd_bounds (by omega : 1 ≤ m) hδ.le hδ1
  obtain ⟨⟨hc,hl⟩,hr⟩ := hR m (Nat.ceil_le.mp ((le_max_right _ _).trans hm))
  have hlog0 : 0 ≤ log (m:ℝ) := log_natCast_nonneg _
  change ‖(27*K)*log (m:ℝ)^(3:ℝ)‖ ≤ 1*‖(m:ℝ)^(α/2)‖ at hc
  rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num, rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), abs_of_pos (rpow_pos_of_pos hm0 _), one_mul] at hc
  have hbl := log_le_log (show 0 < (b:ℝ) by exact_mod_cast (show 0 < b by omega))
    (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hbm)
  rw [log_pow,Nat.cast_ofNat] at hbl
  have hlog3 := pow_le_pow_left₀ (by positivity [log_natCast_nonneg b] : 0 ≤ 1+log b)
    (show 1+log b ≤ 3*log m by linarith only [hl,hbl]) 3
  have herr := hcost (b := b) hm8
  refine ⟨m,by omega,?_⟩
  calc
    F m b ≤ 2*(m:ℝ)^(α/2) := by
      nlinarith only [hb,hc,mul_le_mul_of_nonneg_left hlog3 hK,herr]
    _ ≤ (m:ℝ)^(α/2)*(m:ℝ)^(α/2) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by rw [← rpow_add hm0]; congr 1; ring

open Finset Real Filter in
/-- Paying a quadratic logarithmic allowance at every sample costs at most a
cubic logarithm across an entire normalized window. -/
theorem cubicAllowance_bounds (D : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) {m b : ℕ} (hm : 1 ≤ m) :
    let excess := ∑ n ∈ Icc m b, max (D n-C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3
    let mass := ∑ n ∈ Icc m b, max (D n) 0/(n:ℝ)^3
    excess ≤ mass ∧ mass ≤ excess+C*(1+log b)^3 := by
  let T (n : ℕ) := C*(n:ℝ)^2*(1+log n)^2
  have hT (n : ℕ) : 0 ≤ T n := by dsimp [T]; positivity
  constructor
  · apply sum_le_sum
    intro n _
    exact div_le_div_of_nonneg_right (max_le_max_right 0 (sub_le_self (D n) (hT n))) (by positivity)
  have hlogb : 0 ≤ 1+log b := by positivity [log_natCast_nonneg b]
  calc
    (∑ n ∈ Icc m b, max (D n) 0/(n:ℝ)^3) ≤ ∑ n ∈ Icc m b,
        (max (D n-T n) 0 / (n:ℝ)^3 + C*(1+log b)^2*(n:ℝ)⁻¹) := by
      apply sum_le_sum
      intro n hn
      have hn1 := hm.trans (mem_Icc.mp hn).1
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn1
      have hlog := log_le_log hn0 (show (n:ℝ) ≤ b by exact_mod_cast (mem_Icc.mp hn).2)
      have hsq := pow_le_pow_left₀ (by positivity [log_natCast_nonneg n] : (0:ℝ)≤1+log n)
        (add_le_add_right hlog 1) 2
      have herr : max (D n) 0 ≤ max (D n-T n) 0 + T n := max_le
        (by linarith only [le_max_left (D n-T n) 0])
        (add_nonneg (le_max_right _ _) (hT n))
      calc
        _ ≤ (max (D n-T n) 0 + T n)/(n:ℝ)^3 := div_le_div_of_nonneg_right herr (by positivity)
        _ = max (D n-T n) 0/(n:ℝ)^3 + C*(1+log n)^2*(n:ℝ)⁻¹ := by dsimp only [T]; field_simp
        _ ≤ _ := by gcongr
    _ = (∑ n ∈ Icc m b, max (D n-T n) 0/(n:ℝ)^3) +
        C*(1+log b)^2 * ∑ n ∈ Icc m b, (n:ℝ)⁻¹ := by rw [sum_add_distrib,mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (b := b) hm)
        (mul_nonneg hC (sq_nonneg (1+log b)))
      linarith only [h]

/-- Subpower growth of the total weighted deficit on arbitrarily late fourth-power
windows excludes every zeta zero strictly to the right of one half. -/
theorem rh_of_primeWindowMass
    (h : ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A, primeWindowMass m ≤ (m:ℝ)^ε) :
    RiemannHypothesis := by
  apply rh_of_primeMassOn_powerWindows
  intro α hα
  exact ⟨1,zero_lt_one,le_rfl,by
    simpa only [powerWindowEnd_one, primeMassOn, primeWindowMass] using h α hα⟩

open Real Filter in
/-- A squared logarithmic transfer error preserves the cofinal criterion, including
when the arithmetic comparison sum is signed. -/
theorem rh_of_primeWindowMass_le_log_sq {F : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ m : ℕ, 8 ≤ m → primeWindowMass m ≤ F m + K*(1+log m)^2)
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m ≥ N, F m ≤ (m:ℝ)^ε) : RiemannHypothesis := by
  apply rh_of_primeWindowMass
  intro ε hε N
  have hhalf := half_pos hε
  have hlog := ((isLittleO_log_rpow_rpow_atTop 2 hhalf).const_mul_left (4*K)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨L,hL⟩ := eventually_atTop.mp ((hlog.and (Real.tendsto_log_atTop.eventually_ge_atTop 1)).and
    ((tendsto_rpow_atTop hhalf).eventually_ge_atTop 2))
  obtain ⟨m,hm,hb⟩ := h _ hhalf (max (max 8 N) ⌈L⌉₊)
  have hm8 := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨⟨hc,hl⟩,hr⟩ := hL m (Nat.ceil_le.mp ((le_max_right _ _).trans hm))
  simp only [Real.rpow_two,Real.norm_eq_abs,one_mul] at hc
  rw [abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _)),abs_of_pos (Real.rpow_pos_of_pos hmpos _)] at hc
  have hs : (1+log m)^2 ≤ 4*log m^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ 3*log m+1 by linarith)]
  refine ⟨m,(le_max_right _ _).trans ((le_max_left _ _).trans hm),?_⟩
  calc primeWindowMass m ≤ F m + K*(1+log m)^2 := hcost m hm8
       _ ≤ 2*(m:ℝ)^(ε/2) := by nlinarith only [hb,hc,mul_le_mul_of_nonneg_left hs hK]
       _ ≤ (m:ℝ)^(ε/2)*(m:ℝ)^(ε/2) := mul_le_mul_of_nonneg_right hr (by positivity)
       _ = _ := by rw [← Real.rpow_add hmpos]; congr 1; ring

/-- Failure of RH forces a power-sized positive deficit on every sufficiently late
index window, with a single positive exponent for all those windows. -/
theorem primeWindowMass_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ A : ℕ, ∀ m ≥ A, (m:ℝ)^ε < primeWindowMass m := by
  by_contra! h
  exact hRH (rh_of_primeWindowMass h)

/-- A square-root deficit at the fourth powers has only logarithmic mass on a window. -/
theorem primeWindowMass_of_square_root {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n →
      Real.eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4) ≤ C*(n:ℝ)^2)
    {m : ℕ} (hm : 1 ≤ m) :
    primeWindowMass m ≤ C*(1+2*Real.log m) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc m (m^2), C*(n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 := hm.trans (Finset.mem_Icc.mp hn).1
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      unfold fourthDeficitMass
      apply (div_le_iff₀ (pow_pos hn0 3)).mpr
      rw [show C*(n:ℝ)⁻¹*(n:ℝ)^3 = C*(n:ℝ)^2 by field_simp]
      exact max_le (h n hn1) (mul_nonneg hC (sq_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hC
      have hsum := primeWindow_harmonic_le (b := m^2) hm
      rw [Nat.cast_pow,Real.log_pow] at hsum
      exact hsum

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.positive_integral_le_primeWindowMass,
      ``RiemannGaussian.AlpogeMined.zeta_ne_zero_of_primeMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_primeWindowMass,
      ``RiemannGaussian.AlpogeMined.primeWindowMass_of_not_rh,
      ``RiemannGaussian.AlpogeMined.primeWindowMass_of_square_root] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
