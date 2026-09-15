/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCountFrequency

/-!
# A wider frequency sector paid by the retained prime count

Keep a square count threshold and enlarge the natural frequency interval
by its square root. The full count power still buys exponential decay.
-/

namespace RiemannGaussian.ZetaRieszPrimeCountWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeFourier ZetaRieszSignedFrequency ZetaRieszPrimeCountFrequency

/-- The square-root count window retains enough prime denominators to
save B^(B^2+4) in the entire paired quotient. -/
theorem norm_quotient_le_square_count {n B : ℕ} (hn : Squarefree n)
    (hB : 2 ≤ B) (hk : B ^ 2 ≤ n.primeFactors.card) (L xi : ℝ)
    (hxi : |xi| * Real.log n ≤ (B : ℝ)) :
    ‖primePair n L xi / (xi : ℂ) ^ 2‖ ≤
      2 * |xi| ^ 2 * Real.log n ^ 4 / (B : ℝ) ^ (B ^ 2 + 4) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hB4 : 4 ≤ B ^ 2 := by nlinarith
  have hc : (0 : ℝ) < n.primeFactors.card := by exact_mod_cast (show 0 < n.primeFactors.card by omega)
  have hcount : (B : ℝ) ^ 2 ≤ n.primeFactors.card := by exact_mod_cast hk
  have hbase : |xi| * (Real.log n / (n.primeFactors.card : ℝ)) ≤ 1 / (B : ℝ) := by
    calc
      _ = (|xi| * Real.log n) / (n.primeFactors.card : ℝ) := by ring
      _ ≤ (B : ℝ) / (n.primeFactors.card : ℝ) := div_le_div_of_nonneg_right hxi hc.le
      _ ≤ (B : ℝ) / (B : ℝ) ^ 2 := div_le_div_of_nonneg_left hB0.le (sq_pos_of_pos hB0) hcount
      _ = _ := by field_simp
  have ht : (|xi| * (Real.log n / (n.primeFactors.card : ℝ))) ^ (n.primeFactors.card - 4) ≤
      (1 / (B : ℝ)) ^ (B ^ 2 - 4) := by
    apply (pow_le_pow_left₀ (by positivity) hbase _).trans
    exact pow_le_pow_of_le_one (by positivity) ((div_le_one hB0).mpr hB1) (by omega)
  have hlog : Real.log n / (n.primeFactors.card : ℝ) ≤ Real.log n / (B : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) (sq_pos_of_pos hB0) hcount
  have he : (B : ℝ) ^ (B ^ 2 + 4) = ((B : ℝ) ^ 2) ^ 4 * (B : ℝ) ^ (B ^ 2 - 4) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    _ ≤ 2 * |xi| ^ 2 * (Real.log n / (n.primeFactors.card : ℝ)) ^ 4 *
        (|xi| * (Real.log n / (n.primeFactors.card : ℝ))) ^ (n.primeFactors.card - 4) :=
      norm_higher_quotient_le_full_count hn (hB4.trans hk) L xi
    _ ≤ 2 * |xi| ^ 2 * (Real.log n / (B : ℝ) ^ 2) ^ 4 *
        (1 / (B : ℝ)) ^ (B ^ 2 - 4) := by gcongr
    _ = _ := by rw [he, div_pow, div_pow, one_pow]; ring

/-- The full finite signed frequency sum retains the square-count
denominator throughout its wider valid window. -/
theorem norm_band_le_square_count (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    {B : ℕ} (hB : 2 ≤ B) (hk : ∀ n ∈ S, B ^ 2 ≤ n.primeFactors.card) (xi : ℝ)
    (hxi : ∀ n ∈ S, |xi| * Real.log n ≤ (B : ℝ)) :
    ‖bandPrimePair S f L xi‖ ≤
      (2 * |xi| ^ 2 / (B : ℝ) ^ (B ^ 2 + 4)) * higherFrequencyCost S f L := by
  unfold bandPrimePair
  apply (norm_sum_le _ _).trans
  rw [higherFrequencyCost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hm := Finset.mem_filter.mp hn
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n), Real.norm_of_nonneg hL.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_quotient_le_square_count hm.2.1 hB (hk n hm.1) L xi (hxi n hm.1))
      (by positivity : 0 ≤ Real.log n / L * ‖f n‖)).trans_eq (by ring)

/-- The entire finite integral keeps the square-count saving at every
prefix of the wider frequency window. -/
theorem norm_integral_le_square_count (S : Finset ℕ) (f : ℕ → ℂ)
    {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    {B : ℕ} (hB : 2 ≤ B) (hk : ∀ n ∈ S, B ^ 2 ≤ n.primeFactors.card)
    (hwindow : ∀ n ∈ S, d * Real.log n ≤ (B : ℝ)) :
    ‖∫ xi : ℝ in 0..d, bandPrimePair S f L xi‖ ≤
      (2 / 3 : ℝ) * d ^ 3 * (higherFrequencyCost S f L / (B : ℝ) ^ (B ^ 2 + 4)) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (f := bandPrimePair S f L)
    (g := fun xi : ℝ => 2 * xi ^ 2 * (higherFrequencyCost S f L / (B : ℝ) ^ (B ^ 2 + 4))) hd
    (Filter.Eventually.of_forall fun xi hxi => by
      have hw (n : ℕ) (hn : n ∈ S) : |xi| * Real.log n ≤ (B : ℝ) := by
        rw [abs_of_pos hxi.1]
        exact (mul_le_mul_of_nonneg_right hxi.2 (Real.log_natCast_nonneg n)).trans (hwindow n hn)
      have hb := norm_band_le_square_count S f hL hB hk xi hw
      rw [sq_abs] at hb
      exact hb.trans_eq (by ring))
    (((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).intervalIntegrable 0 d)
  apply h.trans_eq
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 3 ≠ 0), sub_zero]
  ring

/-- The actual source-normalized many-prime integral at any specified
frequency prefix, retaining all count and integer masks. -/
def manyPrimePrefix (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) (d : ℝ) : ℂ :=
  (u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in 0..d, manyPrimeFrequency P u y N K xi)

/-- Every prefix of the square-root enlarged window has its complete
arithmetic cost paid. The estimate is independent of the frequency prefix,
height and tested radius within the displayed intervals. -/
theorem norm_manyPrimePrefix_le_square_count (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u U q d : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (hq : 0 < q) (hqhalf : q < 1 / 2)
    {B : ℕ} (hB : 2 ≤ B) (hd : 0 ≤ d)
    (hdB : d ≤ (B : ℝ) * (3 / (8 * ((N : ℝ) + 1)))) :
    ‖manyPrimePrefix P u y N (B ^ 2) d‖ ≤
      (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q) *
        (((N : ℝ) + 1) ^ 2 * (U / q) ^ N) / (B : ℝ) ^ (B ^ 2 + 1) := by
  let S := (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => B ^ 2 ≤ n.primeFactors.card)
  let f : ℕ → ℂ := fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n
  let L := SquarefreeVaughanLogSource.length u N
  have hL1 : 1 ≤ L := ZetaRieszHeadOrders.one_le_length u N
  have hL : 0 < L := by linarith
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hk : ∀ n ∈ S, B ^ 2 ≤ n.primeFactors.card := fun _ hn => (Finset.mem_filter.mp hn).2
  have hlog : ∀ n ∈ S, Real.log n ≤ (8 / 3 : ℝ) * N :=
    fun _ hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2
  have hb := norm_integral_le_square_count S f hL hd hB hk (fun n hn => by
    calc
      d * Real.log n ≤ ((B : ℝ) * (3 / (8 * ((N : ℝ) + 1)))) * ((8 / 3 : ℝ) * N) := by gcongr; exact hlog n hn
      _ = (B : ℝ) * ((3 / (8 * ((N : ℝ) + 1))) * ((8 / 3 : ℝ) * N)) := by ring
      _ ≤ (B : ℝ) * 1 := mul_le_mul_of_nonneg_left (natural_frequency_window N).2 hB0.le
      _ = _ := mul_one _)
  have ht := ZetaRieszFrequencyDecay.higherFrequencyCost_le_tilt S P N y
    hL1 (show 0 ≤ (8 / 3 : ℝ) * N by positivity) hq hqhalf hlog
  have hp : (1 + (8 / 3 : ℝ) * N) ^ 5 ≤ 1024 * ((N : ℝ) + 1) ^ 5 := by
    calc
      _ ≤ (4 * ((N : ℝ) + 1)) ^ 5 := by gcongr; have := Nat.cast_nonneg (α := ℝ) N; linarith
      _ = _ := by ring
  have hmass := ZetaRieszFrequencyDecay.frequencyTiltMass_nonneg P hq
  have hcost : higherFrequencyCost S f L ≤
      1024 * ((N : ℝ) + 1) ^ 5 *
        (q⁻¹ ^ N * ZetaRieszFrequencyDecay.frequencyTiltMass P q) :=
    ht.trans (mul_le_mul_of_nonneg_right hp (by positivity))
  have hU : 0 ≤ U := hu.trans huU
  have hC := higherFrequencyCost_nonneg S f hL
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  change ‖(u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in 0..d, bandPrimePair S f L xi)‖ ≤ _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, hc,
    ← mul_assoc]
  calc
    _ ≤ (u ^ (N + 1) * (1 / (2 * Real.pi))) *
        ((2 / 3 : ℝ) * d ^ 3 * (higherFrequencyCost S f L / (B : ℝ) ^ (B ^ 2 + 4))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (U ^ (N + 1) * (1 / (2 * Real.pi))) *
        ((2 / 3 : ℝ) * ((B : ℝ) * (3 / (8 * ((N : ℝ) + 1)))) ^ 3 *
          ((1024 * ((N : ℝ) + 1) ^ 5 *
          (q⁻¹ ^ N * ZetaRieszFrequencyDecay.frequencyTiltMass P q)) / (B : ℝ) ^ (B ^ 2 + 4))) := by gcongr
    _ = _ := by
      rw [show (B : ℝ) ^ (B ^ 2 + 4) = (B : ℝ) ^ 3 * (B : ℝ) ^ (B ^ 2 + 1) by
        rw [← pow_add]; congr 1; omega]
      simp only [mul_pow, div_pow, inv_pow, pow_succ U N]
      field_simp
      ring

/-- A parameter version of the dyadic count saving: only two finite
rational-power comparisons are needed to propagate an exponential gain. -/
theorem dyadic_count_power_saving_of {R : ℝ} (hR : 0 ≤ R)
    (hbase : R ^ 32 ≤ 8) (hstep : R ^ 8 ≤ 2) (j : ℕ) :
    R ^ dyadicMomentOrder j ≤ (dyadicPrimeCount j : ℝ) ^ dyadicPrimeCount j := by
  have h (j : ℕ) : R ^ (8 * (j + 4)) ≤ (2 : ℝ) ^ (j + 3) := by
    induction j with
    | zero => convert hbase using 1; norm_num
    | succ j ih =>
      rw [show 8 * (j + 1 + 4) = 8 * (j + 4) + 8 by omega, pow_add,
        show j + 1 + 3 = (j + 3) + 1 by omega, pow_succ (2 : ℝ) (j + 3)]
      exact mul_le_mul ih hstep (pow_nonneg hR _) (by positivity)
  have he := pow_le_pow_left₀ (pow_nonneg hR _) (h j) (dyadicPrimeCount j)
  simpa only [← pow_mul, dyadicMomentOrder, dyadicPrimeCount, Nat.cast_pow, Nat.cast_ofNat] using he

/-- The square thresholds are already a subsequence of the exact
count schedule, without rounding or a new arithmetic support convention. -/
theorem dyadicPrimeCount_twice_add_three (j : ℕ) :
    dyadicPrimeCount (2 * j + 3) = dyadicPrimeCount j ^ 2 := by
  unfold dyadicPrimeCount
  rw [← pow_mul]
  congr 1
  omega

/-- The cofinal orders paired with the square count threshold. -/
def wideMomentOrder (j : ℕ) : ℕ := dyadicMomentOrder (2 * j + 3)

/-- The wider-window moment orders tend to infinity. -/
theorem tendsto_wideMomentOrder : Tendsto wideMomentOrder atTop atTop := by
  have h : Tendsto (fun j : ℕ => 2 * j + 3) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro j
    change j ≤ 2 * j + 3
    omega
  exact tendsto_dyadicMomentOrder.comp h

/-- Even after enlarging the frequency interval by the square root of
the prime count, its complete allowance retains an exponential saving. -/
theorem wide_count_power_saving (j : ℕ) :
    (33 / 32 : ℝ) ^ wideMomentOrder j ≤
      (dyadicPrimeCount j : ℝ) ^ (dyadicPrimeCount j ^ 2 + 1) := by
  have h := dyadic_count_power_saving_of
    (by norm_num : 0 ≤ (33 / 32 : ℝ) ^ 2)
    (by norm_num : ((33 / 32 : ℝ) ^ 2) ^ 32 ≤ 8)
    (by norm_num : ((33 / 32 : ℝ) ^ 2) ^ 8 ≤ 2) (2 * j + 3)
  rw [dyadicPrimeCount_twice_add_three, Nat.cast_pow] at h
  have hs : (33 / 32 : ℝ) ^ wideMomentOrder j ≤
      (dyadicPrimeCount j : ℝ) ^ (dyadicPrimeCount j ^ 2) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [wideMomentOrder, ← pow_mul, Nat.mul_comm] using h
  apply hs.trans
  apply pow_le_pow_right₀ _ (Nat.le_succ _)
  have hb := four_le_dyadicPrimeCount j
  exact_mod_cast (show 1 ≤ dyadicPrimeCount j by omega)

/-- An explicit geometric bound for every prefix of the enlarged sector,
including its full arithmetic cost. -/
theorem norm_wide_prefix_le (P : Polynomial ℂ) (y : ℝ) (j : ℕ)
    {u U q d : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (hq : 0 < q) (hqhalf : q < 1 / 2)
    (hd : 0 ≤ d)
    (hdB : d ≤ (dyadicPrimeCount j : ℝ) * (3 / (8 * ((wideMomentOrder j : ℝ) + 1)))) :
    ‖manyPrimePrefix P u y (wideMomentOrder j) (dyadicPrimeCount j ^ 2) d‖ ≤
      (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q) *
        (((wideMomentOrder j : ℝ) + 1) ^ 2 * (32 * U / (33 * q)) ^ wideMomentOrder j) := by
  have hU := hu.trans huU
  have hm := ZetaRieszFrequencyDecay.frequencyTiltMass_nonneg P hq
  apply (norm_manyPrimePrefix_le_square_count P y (wideMomentOrder j) hu huU hq hqhalf
    (by have := four_le_dyadicPrimeCount j; omega) hd hdB).trans
  calc
    _ ≤ (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q) *
        (((wideMomentOrder j : ℝ) + 1) ^ 2 * (U / q) ^ wideMomentOrder j) /
          (33 / 32 : ℝ) ^ wideMomentOrder j :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (wide_count_power_saving j)
    _ = _ := by
      simp only [mul_div_assoc, ← div_pow]
      congr 3
      field_simp

/-- Every radius ceiling below 33/64 admits a summable tilt for the
enlarged many-prime window. This is a sufficient component criterion. -/
theorem exists_wide_tilt {U : ℝ} (hU : 0 < U) (hU1 : U < 33 / 64) :
    ∃ q : ℝ, 0 < q ∧ q < 1 / 2 ∧ 32 * U < 33 * q := by
  refine ⟨(32 * U / 33 + 1 / 2) / 2, ?_, ?_, ?_⟩ <;> linarith

/-- The entire selected arithmetic response decays at every moving
prefix of the enlarged interval, uniformly over all displayed radii and
heights. There is no hypothetical-zero assumption. -/
theorem tendsto_wide_prefix_moving (P : Polynomial ℂ) (u y d : ℕ → ℝ)
    {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 33 / 64) (hd : ∀ j, 0 ≤ d j)
    (hdB : ∀ j, d j ≤ (dyadicPrimeCount j : ℝ) *
      (3 / (8 * ((wideMomentOrder j : ℝ) + 1)))) :
    Tendsto (fun j => manyPrimePrefix P (u j) (y j) (wideMomentOrder j)
      (dyadicPrimeCount j ^ 2) (d j)) atTop (𝓝 0) := by
  obtain ⟨q, hq, hqhalf, hrate⟩ := exists_wide_tilt hU hU1
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (show 0 < 32 * U / (33 * q) by positivity)
    ((div_lt_one (by positivity : 0 < 33 * q)).mpr hrate)).comp tendsto_wideMomentOrder
  apply squeeze_zero_norm (fun j => norm_wide_prefix_le P (y j) j
    (hu j) (huU j) hq hqhalf (hd j) (hdB j))
  simpa only [Function.comp_apply, mul_zero] using
    ht.const_mul (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q)

/-- The enlarged-window component estimate still covers the original
annular exposed-zero source range. -/
theorem exp_neg_two_thirds_lt_wide_radius :
    Real.exp (-(2 / 3 : ℝ)) < 33 / 64 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos (2 / 3 : ℝ))).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) 5
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- The complementary prime counts retain their signed low-frequency
prefix separately from the many-prime prefix. -/
def fewPrimePrefix (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) (d : ℝ) : ℂ :=
  (u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in 0..d, fewPrimeFrequency P u y N K xi)

/-- The two count classes partition each actual finite frequency prefix
exactly. The phases have not been bounded or discarded. -/
theorem nonlinear_prefix_eq (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    {K : ℕ} (hK : 4 ≤ K) {d : ℝ} (hd : 0 ≤ d) :
    (u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in 0..d, nonlinearFrequency P u y N xi) =
        fewPrimePrefix P u y N K d + manyPrimePrefix P u y N K d := by
  have he : nonlinearFrequency P u y N =
      fun xi => fewPrimeFrequency P u y N K xi + manyPrimeFrequency P u y N K xi :=
    funext (nonlinearFrequency_eq_few_add_many P u y N hK)
  have hf : IntervalIntegrable (fewPrimeFrequency P u y N K) MeasureTheory.volume 0 d :=
    intervalIntegrable_bandPrimePair _ _ _ hd
  have hm : IntervalIntegrable (manyPrimeFrequency P u y N K) MeasureTheory.volume 0 d :=
    intervalIntegrable_bandPrimePair _ _ _ hd
  rw [he, intervalIntegral.integral_add hf hm]
  unfold fewPrimePrefix manyPrimePrefix
  ring

/-- Every former shrinking cutoff lies in the newly enlarged many-prime
window, so its overlap also has an independently vanishing bound. -/
theorem geometric_cutoff_le_wide {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (j : ℕ) :
    ZetaRieszFrequencyDecay.geometricFrequencyCutoff r (wideMomentOrder j) ≤
      (dyadicPrimeCount j : ℝ) * (3 / (8 * ((wideMomentOrder j : ℝ) + 1))) := by
  have hd := (natural_frequency_window (wideMomentOrder j)).1.le
  have hb : (1 : ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (show 1 ≤ dyadicPrimeCount j by have := four_le_dyadicPrimeCount j; omega)
  calc
    _ ≤ (3 / (8 * ((wideMomentOrder j : ℝ) + 1))) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) hd
    _ ≤ _ := by nlinarith

/-- The old all-count low sector minus its controlled many-prime overlap
gives an independently vanishing few-prime low sector. This is subtraction
of exact signed integrals, not addition of overlapping deletion budgets. -/
theorem tendsto_few_shrinking_prefix (P : Polynomial ℂ) {u : ℝ} (y : ℝ)
    (hu : 0 < u) (hu1 : u < 33 / 64) :
    Tendsto (fun j => fewPrimePrefix P u y (wideMomentOrder j) (dyadicPrimeCount j ^ 2)
      (ZetaRieszFrequencyDecay.geometricFrequencyCutoff (3 / 4) (wideMomentOrder j)))
      atTop (𝓝 0) := by
  have ha := (ZetaRieszFrequencyDecay.tendsto_nonlinear_low_frequency_moving P
    (fun _ => u) (fun _ => y) (fun _ => hu.le) (fun _ => show u ≤ (1 : ℝ) by linarith)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1) (by norm_num : 2 * (1 : ℝ) * (3 / 4) ^ 3 < 1)).comp
      tendsto_wideMomentOrder
  have hm := tendsto_wide_prefix_moving P (fun _ => u) (fun _ => y)
    (fun j => ZetaRieszFrequencyDecay.geometricFrequencyCutoff (3 / 4) (wideMomentOrder j))
    (fun _ => hu.le) (fun _ => le_rfl) hu hu1
    (fun j => (ZetaRieszFrequencyDecay.geometricFrequencyCutoff_valid
      (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) (wideMomentOrder j)).1.le)
    (geometric_cutoff_le_wide (by norm_num) (by norm_num))
  have h := ha.sub hm
  simp only [Function.comp_apply, sub_zero] at h
  apply h.congr'
  filter_upwards [] with j
  have hb := four_le_dyadicPrimeCount j
  rw [nonlinear_prefix_eq P u y (wideMomentOrder j) (by nlinarith : 4 ≤ dyadicPrimeCount j ^ 2)
    (ZetaRieszFrequencyDecay.geometricFrequencyCutoff_valid
      (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) (wideMomentOrder j)).1.le]
  simp

/-- At different frequency cutoffs for the two count classes, the
remaining response is exactly the sum of their two complementary integrals. -/
theorem nonlinearResponse_sub_two_prefixes_eq (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    {K : ℕ} (hK : 4 ≤ K) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N +
        ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse P u y N) -
          (fewPrimePrefix P u y N K a + manyPrimePrefix P u y N K b) =
      (u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
        ((∫ xi : ℝ in Set.Ioi a, fewPrimeFrequency P u y N K xi) +
         (∫ xi : ℝ in Set.Ioi b, manyPrimeFrequency P u y N K xi))) := by
  obtain ⟨hf, hm⟩ := integrable_few_many_frequency P u y N K
  rw [nonlinearResponse_eq_integral]
  have he : nonlinearFrequency P u y N =
      fun xi => fewPrimeFrequency P u y N K xi + manyPrimeFrequency P u y N K xi :=
    funext (nonlinearFrequency_eq_few_add_many P u y N hK)
  rw [he, MeasureTheory.integral_add hf hm]
  unfold fewPrimePrefix manyPrimePrefix
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hf ha,
    ← intervalIntegral.integral_Ioi_sub_Ioi hm hb]
  ring

/-- The wider many-prime window, with its exact count and moment schedule. -/
def wideCutoff (j : ℕ) : ℝ :=
  (dyadicPrimeCount j : ℝ) * (3 / (8 * ((wideMomentOrder j : ℝ) + 1)))

/-- The actual many-prime contribution on the entire enlarged interval
tends to zero independently of any hypothetical zero or source theorem. -/
theorem tendsto_many_wide_prefix (P : Polynomial ℂ) {u : ℝ} (y : ℝ)
    (hu : 0 < u) (hu1 : u < 33 / 64) :
    Tendsto (fun j => manyPrimePrefix P u y (wideMomentOrder j) (dyadicPrimeCount j ^ 2)
      (wideCutoff j)) atTop (𝓝 0) :=
  tendsto_wide_prefix_moving P (fun _ => u) (fun _ => y) wideCutoff
    (fun _ => hu.le) (fun _ => le_rfl) hu hu1
    (fun _ => by unfold wideCutoff; positivity) (fun _ => le_rfl)

/-- Both independently paid sectors are removed without counting their
overlap twice. The original source remains in the explicit two-frequency
remainder and tapered wing, with every multiplicity and domain premise. -/
theorem tendsto_two_cutoff_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun j : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (wideMomentOrder j + 1) *
      ((1 / (2 * (Real.pi : ℂ))) *
        ((∫ xi : ℝ in Set.Ioi (ZetaRieszFrequencyDecay.geometricFrequencyCutoff (3 / 4) (wideMomentOrder j)),
            fewPrimeFrequency 1 (3 / 2 - rho.1.re) rho.1.im (wideMomentOrder j) (dyadicPrimeCount j ^ 2) xi) +
         (∫ xi : ℝ in Set.Ioi (wideCutoff j),
            manyPrimeFrequency 1 (3 / 2 - rho.1.re) rho.1.im (wideMomentOrder j) (dyadicPrimeCount j ^ 2) xi)) +
        ZetaRieszCompletedCarrier.taperedWing (3 / 2 - rho.1.re) rho.1.im (wideMomentOrder j)))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 := huh.trans exp_neg_two_thirds_lt_wide_radius
  have hd := (tendsto_few_shrinking_prefix 1 rho.1.im hu hu1).add
    (tendsto_many_wide_prefix 1 rho.1.im hu hu1)
  have hs := (ZetaRieszCentralHarmonicCost.tendsto_three_unpaid_exact_source
    rho hrho hexposed huh).comp tendsto_wideMomentOrder
  have h := hs.sub hd
  simp only [Function.comp_apply, add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with j
  have hB := four_le_dyadicPrimeCount j
  have he := nonlinearResponse_sub_two_prefixes_eq 1 (3 / 2 - rho.1.re) rho.1.im
    (wideMomentOrder j) (by nlinarith : 4 ≤ dyadicPrimeCount j ^ 2)
    (ZetaRieszFrequencyDecay.geometricFrequencyCutoff_valid
      (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) (wideMomentOrder j)).1.le
    (show 0 ≤ wideCutoff j by unfold wideCutoff; positivity)
  linear_combination he

end
end RiemannGaussian.ZetaRieszPrimeCountWindow
