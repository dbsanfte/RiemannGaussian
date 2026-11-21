import RiemannGaussian.DyadicPrimeZeroBound
import RiemannGaussian.QuasiRHPrimeSampleValues

/-! # A native RH test using increments of the prime error at integer squares -/

namespace RiemannGaussian.DyadicPrime
noncomputable section
open Filter MeasureTheory ProbabilityTheory Set
open QuasiRHIntegerPowerCheckpoints QuasiRHPrimePrimitiveHeat

/-- The exact centered prime primitive at the integer square. -/
def squareError (m : ℕ) : ℝ := QuasiRHPrimeWindowBounds.primeError ((m : ℝ)^2)

private theorem window_le_of_squareError {A T : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hb : ∀ m : ℕ, 1 ≤ m → squareError m ≤ A*m) : powerWindow 2 T ≤ A := by
  let μ := gaussianReal T (2*T).toNNReal
  let s := Icc (T/4) (4*T)
  change (∫ u in s, max (discrepancy (powerTime 2 u)).re 0 ∂μ) ≤ A
  rw [← integral_indicator (show MeasurableSet s from measurableSet_Icc)]
  apply (integral_mono_of_nonneg _ (integrable_const A) _).trans_eq
  · simp
  · exact Filter.Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  · filter_upwards with u
    by_cases hu : u ∈ s
    · rw [Set.indicator_of_mem hu]
      apply max_le _ hA
      have hu0 : 0 ≤ u := (by positivity : (0 : ℝ) ≤ T/4).trans hu.1
      let m := ⌊Real.exp (u/2)⌋₊
      have hm : 1 ≤ m := Nat.le_floor (by simpa using Real.one_le_exp_iff.mpr (by linarith : 0 ≤ u/2))
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm0 := zero_lt_one.trans_le hm1
      have hv : powerTime 2 u = 2*Real.log m := by simp [powerTime,m]
      have hv0 : 0 ≤ powerTime 2 u := by rw [hv]; exact mul_nonneg (by norm_num) (Real.log_nonneg hm1)
      have hex := exp_powerTime 2 hu0
      change Real.exp (powerTime 2 u) = (m : ℝ)^2 at hex
      have hd : (discrepancy (powerTime 2 u)).re =
          Real.exp (-(1/2 : ℝ)*powerTime 2 u)*squareError m := by
        simp only [discrepancy,hv0, ↓reduceIte, RosserSchoenfeldExplicitFormula.mainTerm_eq,
          ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re, squareError, QuasiRHPrimeWindowBounds.primeError]
        rw [← hex,Real.log_exp]
      rw [hd, hv, show -(1/2:ℝ)*(2*Real.log m) = -Real.log m by ring, Real.exp_neg, Real.exp_log hm0]
      have hh := mul_le_mul_of_nonneg_left (hb m hm) (inv_nonneg.mpr hm0.le)
      exact hh.trans_eq (by field_simp)
    · simpa [Set.indicator_of_notMem hu] using hA

/-- A one-sided linear bound on the arithmetic values themselves bounds every Gaussian square window. -/
theorem rh_of_squareError_le {A : ℝ} (hA : 0 ≤ A)
    (hall : ∀ m : ℕ, 1 ≤ m → squareError m ≤ A*m) : RiemannHypothesis := by
  apply QuasiRHPrimeSampleValues.riemannHypothesis_iff_subexponential_square_samples.mpr
  intro ε hε
  have hg : Tendsto (fun T : ℝ => Real.exp (ε*T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε)
  exact ((eventually_ge_atTop (0 : ℝ)).and (hg.eventually_ge_atTop A)).frequently.mono fun _ ht =>
    (window_le_of_squareError hA ht.1 hall).trans ht.2

/-- An upper bound on the rise from the half-index square controls the whole prime sample by telescoping. -/
theorem rh_of_squareError_increment {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ m : ℕ, 2 ≤ m → squareError m - squareError (m/2) ≤ C*m) : RiemannHypothesis := by
  let A := 2*C + |squareError 1|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC' : 2*C ≤ A := le_add_of_nonneg_right (abs_nonneg _)
  have hall (m : ℕ) : 1 ≤ m → squareError m ≤ A*m := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases eq_or_lt_of_le hm with h1|hm2
      · subst m
        rw [Nat.cast_one,mul_one]
        exact (le_abs_self _).trans (le_add_of_nonneg_left (by positivity))
      have hn : 1 ≤ m/2 := by omega
      have hlt : m/2 < m := by omega
      have hhalf : 2 * ((m/2 : ℕ) : ℝ) ≤ m := by exact_mod_cast (show 2*(m/2) ≤ m by omega)
      have hh := ih (m/2) hlt hn
      have hg := h m hm2
      nlinarith only [hh,hg,mul_le_mul_of_nonneg_left hhalf hA,
        mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg (α := ℝ) m)]
  exact rh_of_squareError_le hA hall

/-- The integer samples alone give a native finite-sum test with an explicit constant. -/
theorem rh_iff_squareError_increment_le_tenth :
    RiemannHypothesis ↔ ∀ m : ℕ, 2 ≤ m → squareError m - squareError (m/2) ≤ (m:ℝ)/10 := by
  constructor
  · intro h m hm
    have ha : (1:ℝ) ≤ (m/2 : ℕ) := by exact_mod_cast (show 1 ≤ m/2 by omega)
    have hav : ((m/2 : ℕ):ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
    have hinc := centered_increment_le_of_zero_bound (one_le_pow₀ ha (n := 2))
      (pow_le_pow_left₀ (zero_le_one.trans ha) hav 2) le_rfl (by norm_num : (0 : ℝ) ≤ 1/2)
      (fun ρ => (h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
    rw [← Real.sqrt_eq_rpow,Real.sqrt_sq (Nat.cast_nonneg m)] at hinc
    unfold primePrimitiveDeficit at hinc
    unfold squareError QuasiRHPrimeWindowBounds.primeError
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · intro h
    exact rh_of_squareError_increment (C := 1/10) (by norm_num) (fun m hm => by linarith [h m hm])

private theorem raw_square {m : ℕ} (hm : 1 ≤ m) :
    QuasiRHPrimeSampleValues.raw (2*Real.log m) = squareError m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold QuasiRHPrimeSampleValues.raw squareError QuasiRHPrimeWindowBounds.primeError
  rw [show 2*Real.log m = Real.log ((m:ℝ)^2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity)]

/-- In every sufficiently late power window a specific integer square has small absolute prime error. -/
theorem eventually_small_squareError_in_power_window {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∃ k ∈ Icc (M^2) (M^32), |squareError k| ≤ ε*k := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htime := hlog.const_mul_atTop (by norm_num : (0:ℝ) < 16)
  filter_upwards [htime.eventually QuasiRHPrimeSampleValues.eventually_consecutive_square_samples,
    hlog.eventually_ge_atTop (max 1 (1/ε)),eventually_ge_atTop 1] with M hc ht hm
  obtain ⟨u,hu,h⟩ := hc
  have hlow : 4*Real.log M ≤ u := by linarith [hu.1]
  have hhi : u ≤ 64*Real.log M := by linarith [hu.2]
  have hu1 : 1 ≤ u := by linarith [(le_max_left 1 (1/ε)).trans ht]
  have hmpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let k := ⌈Real.exp (u/2)⌉₊
  have hkp : Real.exp (u/2) ≤ (k:ℝ) := Nat.le_ceil _
  have hkn : 0 < k := by exact_mod_cast (Real.exp_pos _).trans_le hkp
  have hex (p : ℕ) : Real.exp ((p:ℝ)*Real.log M) = (M:ℝ)^p := by
    rw [← Real.log_pow,Real.exp_log (by positivity)]
  have hkl : M^2 ≤ k := by
    have he := (Real.exp_le_exp.mpr (by linarith : (2:ℝ)*Real.log M ≤ u/2)).trans hkp
    rw [← Nat.cast_ofNat (R := ℝ) (n := 2),hex] at he
    exact_mod_cast he
  have hku : k ≤ M^32 := by
    apply Nat.ceil_le.mpr
    push_cast
    rw [← hex]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hb := h 0 (by simpa using hu1)
  change |QuasiRHPrimeSampleValues.raw (2*Real.log (k+0 : ℕ))|/((k+0:ℕ):ℝ) ≤ 4*((0:ℕ)+1)/u at hb
  simp only [Nat.add_zero,Nat.cast_zero,zero_add,mul_one,raw_square (by omega : 1 ≤ k)] at hb
  have hεu : 4/u ≤ ε := (div_le_iff₀ (by linarith : 0 < u)).mpr (by
    linarith [mul_le_mul_of_nonneg_right hlow hε.le,
      (div_le_iff₀ hε).mp ((le_max_right 1 (1/ε)).trans ht)])
  exact ⟨k,⟨hkl,hku⟩,(div_le_iff₀ (by exact_mod_cast hkn : (0:ℝ) < k)).mp (hb.trans hεu)⟩

/-- A uniform half-plane bound evaluated at the physical cutoff `m^2`. -/
theorem abs_squareError_le_of_re_le {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    |squareError m| ≤ (m:ℝ)^(2*B) := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 := zero_lt_one.trans_le hm1
  have hs := suzukiLocalPrimePrimitive_error_le_of_re_le hB hzero (Real.log_nonneg (one_le_pow₀ hm1 (n := 2)))
  rw [Real.exp_log (by positivity : 0 < (m:ℝ)^2)] at hs
  have he : Real.exp (B * Real.log ((m:ℝ)^2)) = (m:ℝ)^(2*B) := by
    rw [Real.log_pow,Real.rpow_def_of_pos hm0]
    congr 1
    push_cast
    ring
  rw [he] at hs
  unfold squareError QuasiRHPrimeWindowBounds.primeError
  rw [abs_sub_comm]
  have hc : (463/5000:ℝ)+Real.pi^2/24 ≤ 1 := by
    have hp := sq_lt_sq' (by linarith [Real.pi_pos] : -(4:ℝ) < Real.pi) Real.pi_lt_four
    linarith
  exact hs.trans ((mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hm0.le _)).trans_eq (one_mul _))

/-- The native seven-eighths zero-free bound at the physical cutoff `m^2`. -/
theorem abs_squareError_le_seven_fourths {m : ℕ} (hm : 1 ≤ m) :
    |squareError m| ≤ (m:ℝ)^(7/4:ℝ) := by
  convert abs_squareError_le_of_re_le (by norm_num : (0:ℝ) ≤ 7/8)
    suzukiLocalZero_re_le_seven_eighths hm using 1
  norm_num

/-- Every sufficiently late power window contains a good dyadic increment. The crossing at a
square anchors one end of a finite chain of halvings and the unconditional envelope pays its base. -/
theorem eventually_small_increment_in_power_window {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∃ m ∈ Icc M (M^32), squareError m-squareError (m/2) ≤ ε*m := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (4/ε)
  filter_upwards [eventually_small_squareError_in_power_window (by linarith : 0 < ε/4),
    hg,eventually_ge_atTop 4] with M ⟨k,hk,he⟩ hquarter hM
  change 4/ε ≤ (M:ℝ)^(1/4:ℝ) at hquarter
  have hM4 : (4:ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0:ℝ) < M := by linarith
  have hk0 : 1 ≤ k := by nlinarith only [hk.1,hM]
  have hMk : (M:ℝ)^2 ≤ k := by exact_mod_cast hk.1
  let K := (M:ℝ)^(7/4:ℝ)+ε*M
  have hpay : K ≤ (ε/2)*k := by
    have hp : (M:ℝ)^(7/4:ℝ)*(M:ℝ)^(1/4:ℝ) = (M:ℝ)^2 := by
      rw [← Real.rpow_add hM0]; norm_num
    have hdom := mul_le_mul_of_nonneg_left ((div_le_iff₀ hε).mp hquarter)
      (Real.rpow_nonneg hM0.le (7/4:ℝ))
    rw [← mul_assoc,hp] at hdom
    dsimp [K]
    nlinarith only [hdom,mul_le_mul_of_nonneg_left hMk hε.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM4 hM0.le) hε.le]
  by_contra! h
  have hlo (n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k) : ε*n-K ≤ squareError n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hmn : n < M
      · have hsize : (n:ℝ) ≤ M := by exact_mod_cast hmn.le
        have hp := Real.rpow_le_rpow (Nat.cast_nonneg n) hsize (by norm_num : (0:ℝ) ≤ 7/4)
        have he' := (abs_le.mp (abs_squareError_le_seven_fourths hn)).1
        dsimp [K]
        linarith [mul_le_mul_of_nonneg_left hsize hε.le]
      · have hmn' : M ≤ n := by omega
        have hh := ih (n/2) (by omega) (by omega) (by omega)
        have hbad := h n ⟨hmn',hnk.trans hk.2⟩
        linarith [mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) (n/2))]
  nlinarith only [hlo k hk0 le_rfl,(le_abs_self _).trans he,hpay,
    mul_pos hε (by exact_mod_cast (show 0 < k by omega) : (0:ℝ) < k)]

/-- Arbitrarily remote actual square increments meet every positive linear allowance. -/
theorem exists_small_squareError_increment {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ squareError m - squareError (m/2) ≤ ε*m := by
  obtain ⟨b,⟨m,hm,h⟩,hb⟩ := ((eventually_small_increment_in_power_window hε).and
    (eventually_ge_atTop M)).exists
  exact ⟨m,hb.trans hm.1,h⟩

/-- Nearby square samples have controlled variation over a logarithmic distance in the index. -/
theorem local_squareError_variation {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k)
    (hu : 5000 ≤ 2*Real.log m) {ε : ℝ} (hk : (k:ℝ)-m ≤ 2*Real.log m)
    (hεk : 4*((k:ℝ)-m) ≤ ε*(2*Real.log m)) :
    |squareError k - squareError m| ≤ ε*k := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hkpos : (0:ℝ) < k := hmpos.trans_le (by exact_mod_cast hmk)
  have he : Real.exp (2*Real.log m/2) = m := by
    rw [show 2*Real.log m/2 = Real.log m by ring, Real.exp_log hmpos]
  have hmem : (k:ℝ) ∈ Icc (Real.exp (2*Real.log m/2)) (Real.exp (2*Real.log m/2) + 2*Real.log m) := by
    rw [he]
    exact ⟨by exact_mod_cast hmk, by linarith⟩
  have h := QuasiRHPrimeSampleValues.square_increment hu hmem
  rw [he,raw_square hm,raw_square (hm.trans hmk)] at h
  exact (div_le_iff₀ hkpos).mp (h.trans ((div_le_iff₀ (by linarith : 0 < 2*Real.log m)).mpr hεk))

/-- Arbitrarily late blocks of every prescribed finite length meet the one-sided bound for the actual increments. -/
theorem exists_block_squareError_increment {ε : ℝ} (hε : 0 < ε) (M L : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ ∀ j : ℕ, j ≤ L →
      squareError (m+j) - squareError ((m+j)/2) ≤ ε*(m+j : ℕ) := by
  let u := max 5000 (max (L:ℝ) (16*L/ε))
  let b := ⌈Real.exp u⌉₊
  obtain ⟨m,hm,hsmall⟩ := exists_small_squareError_increment (by linarith : 0 < ε/4) (max M (2*b))
  have hmb := (le_max_right M (2*b)).trans hm
  have hb : b ≤ m/2 := by omega
  have hex : Real.exp u ≤ ((m/2 : ℕ) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hpos : (0 : ℝ) < (m/2 : ℕ) := (Real.exp_pos _).trans_le hex
  have hlog : u ≤ Real.log (m/2 : ℕ) := (Real.le_log_iff_exp_le hpos).mpr hex
  have hbase : 5000 ≤ u := le_max_left _ _
  have hL : (L:ℝ) ≤ u := (le_max_left _ _).trans (le_max_right _ _)
  have hcost : 16*(L:ℝ) ≤ u*ε := (div_le_iff₀ hε).mp ((le_max_right _ _).trans (le_max_right _ _))
  have hlarge (a : ℕ) (ha : m/2 ≤ a) : u ≤ Real.log a :=
    hlog.trans (Real.log_le_log hpos (by exact_mod_cast ha))
  have hvariation (a k : ℕ) (ha : m/2 ≤ a) (hak : a ≤ k) (hkl : k ≤ a+L) :
      |squareError k - squareError a| ≤ (ε/4)*k := by
    have ha1 : 1 ≤ a := by
      have hn : 0 < m/2 := by exact_mod_cast hpos
      omega
    have hka : (k:ℝ) ≤ a+L := by exact_mod_cast hkl
    have hla := hlarge a ha
    apply local_squareError_variation ha1 hak (by linarith) (by linarith)
    nlinarith only [hka,hcost,mul_le_mul_of_nonneg_right hla hε.le]
  refine ⟨m,(le_max_left _ _).trans hm,fun j hj => ?_⟩
  have ht := hvariation m (m+j) (Nat.div_le_self _ _) (by omega) (by omega)
  have hb' := hvariation (m/2) ((m+j)/2) le_rfl (by omega) (by omega)
  have hquot : (((m+j)/2 : ℕ):ℝ) ≤ (m+j:ℕ) := by exact_mod_cast Nat.div_le_self (m+j) 2
  have hstart : (m:ℝ) ≤ (m+j:ℕ) := by exact_mod_cast (show m ≤ m+j by omega)
  nlinarith only [hsmall,(abs_le.mp ht).2,(abs_le.mp hb').1,
    mul_le_mul_of_nonneg_left hquot hε.le,mul_le_mul_of_nonneg_left hstart hε.le,
    mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) (m+j))]

/-- The residual at the two actual square samples, with the full high-zero tail already paid. -/
def squareZeroIncrement (m : ℕ) : ℝ :=
  (∑ ρ ∈ rightZeros (cutoff ((m:ℝ)^2)), zeroIncrement (((m/2 : ℕ) : ℝ)^2) ((m:ℝ)^2) ρ).re

theorem squareError_increment_le {m : ℕ} (hm : 2 ≤ m) :
    squareError m - squareError (m/2) ≤ squareZeroIncrement m + m := by
  have ha : (1:ℝ) ≤ (m/2 : ℕ) := by exact_mod_cast (show 1 ≤ m/2 by omega)
  have hav : ((m/2 : ℕ):ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
  have h := centered_increment_le_finite_add_sqrt
    (one_le_pow₀ ha (n := 2)) (pow_le_pow_left₀ (zero_le_one.trans ha) hav 2) le_rfl
  rw [Real.sqrt_sq (Nat.cast_nonneg m)] at h
  unfold squareError QuasiRHPrimeWindowBounds.primeError squareZeroIncrement
  unfold primePrimitiveDeficit at h
  linarith

/-- A one-sided linear bound on the sampled finite sums implies Mathlib's RH, using native modules only. -/
theorem rh_iff_finite_squareZeroIncrement :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → squareZeroIncrement m ≤ C*m := by
  constructor
  · intro h
    refine ⟨0,le_rfl,fun m _ => ?_⟩
    have he (T : ℝ) : rightZeros T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ρ hρ
      have hr := (Finset.mem_filter.mp hρ).2
      exact (lt_irrefl _ : ¬ (1/2 : ℝ) < 1/2) ((h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2) ▸ hr)
    simp [squareZeroIncrement,he]
  · rintro ⟨C,hC,h⟩
    apply rh_of_squareError_increment (C := C+1) (by linarith)
    intro m hm
    linarith [squareError_increment_le hm, h m hm]

open Complex in
/-- A single right-half-plane term grows faster than the sample allowance even at even indices. -/
theorem tendsto_normalized_zeroIncrement_of_right_zero (ρ : NontrivialZetaZero) (hβ : 1/2 < ρ.1.re) :
    Tendsto (fun k : ℕ => ‖zeroIncrement ((k:ℝ)^2) ((2*(k:ℝ))^2) ρ‖ / (2*k)) atTop atTop := by
  let c : ℂ := ((analyticZetaZeroMultiplicity ρ : ℂ)/ρ.1^2) *
    (Complex.exp (ρ.1*(Real.log 4 : ℝ))-1)
  have hne : Complex.exp (ρ.1*(Real.log 4 : ℝ)) ≠ 1 := by
    intro h
    have hnorm := congrArg norm h
    rw [Complex.norm_exp, norm_one, Real.exp_eq_one_iff, Complex.mul_re] at hnorm
    simp only [Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero] at hnorm
    exact (mul_pos ρ.zero_lt_re (Real.log_pos (by norm_num : (1 : ℝ) < 4))).ne' hnorm
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr (mul_ne_zero
    (div_ne_zero (by exact_mod_cast (analyticZetaZeroMultiplicity_positive ρ).ne')
      (pow_ne_zero _ (Complex.ne_zero_of_re_pos ρ.zero_lt_re))) (sub_ne_zero.mpr hne))
  have he {k : ℕ} (hk : 0 < k) : ‖zeroIncrement ((k:ℝ)^2) ((2*(k:ℝ))^2) ρ‖ / (2*k) =
      (‖c‖/2)*(k:ℝ)^(2*ρ.1.re-1) := by
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hid : zeroIncrement ((k:ℝ)^2) ((2*(k:ℝ))^2) ρ = c*Complex.exp (ρ.1*(Real.log ((k:ℝ)^2) : ℝ)) := by
      rw [zeroIncrement,RosserSchoenfeldZeroPrimitive.term,RosserSchoenfeldZeroPrimitive.term,
        RosserSchoenfeldZeroPrimitive.atom,RosserSchoenfeldZeroPrimitive.atom]
      rw [show (2*(k:ℝ))^2 = 4*(k:ℝ)^2 by ring,Real.log_mul (by norm_num) (pow_ne_zero _ hk0.ne'),
        Complex.ofReal_add,mul_add,Complex.exp_add]
      dsimp [c]
      ring
    rw [hid,norm_mul,Complex.norm_exp,Complex.mul_re]
    simp only [Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero]
    rw [Real.log_pow,Real.rpow_sub hk0,Real.rpow_one,Real.rpow_def_of_pos hk0 (2*ρ.1.re)]
    norm_num
    ring_nf
  apply Tendsto.congr' (f₁ := fun k : ℕ => (‖c‖/2)*(k:ℝ)^(2*ρ.1.re-1))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
    exact (he hk).symm
  · exact ((tendsto_rpow_atTop (by linarith : 0 < 2*ρ.1.re-1)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop (by linarith)

end
end RiemannGaussian.DyadicPrime
