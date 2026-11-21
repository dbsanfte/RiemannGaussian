import AlpogeIntegerPrimeBand
import CheckAlpogePrimeWindowMass

/-! # Positive prime versus integer discrepancy on fourth-power windows -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real

/-- The positive discrepancy on a window after adding a supplied correction at each square. -/
def integerDiscrepancyWindow (correction : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Icc m (m^2), max (integerPrimeDiscrepancy (n^2) + correction (n^2)) 0 / (n:ℝ)^3

private theorem max_error {a b c : ℝ} (ha : 0 ≤ a-b) (hb : a-b ≤ c) :
    0 ≤ max a 0-max b 0 ∧ max a 0-max b 0 ≤ c := by
  refine ⟨sub_nonneg.mpr (max_le_max (by linarith) le_rfl),?_⟩
  exact (max_sub_max_le_max a 0 b 0).trans (max_le hb (by linarith))

private theorem two_squares (n : ℕ) : (n^2)^2 = n^4 := by ring

private theorem fourth_discrepancy (n : ℕ) (hn : 1 ≤ n) :
    let m := max (integerPrimeDiscrepancy (n^2)+smallResidueCorrection (n^2)) 0 / (n:ℝ)^3
    0 ≤ fourthDeficitMass n - m ∧ fourthDeficitMass n - m ≤ (3/2)/(n:ℝ)^3 := by
  have he := corrected_discrepancy_error (Nat.one_le_pow 2 n hn)
  dsimp only at he
  rw [two_squares,Nat.cast_pow,show ((n:ℝ)^2)^2 = (n:ℝ)^4 by ring] at he
  obtain ⟨ha,hb⟩ := max_error he.1 he.2
  dsimp only [fourthDeficitMass]
  rw [← sub_div]
  exact ⟨div_nonneg ha (by positivity),div_le_div_of_nonneg_right hb (by positivity)⟩

/-- Across the full window the replacement error in positive mass is at most 3/(2m²). -/
theorem corrected_window_error {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ primeWindowMass m - integerDiscrepancyWindow smallResidueCorrection m ∧
      primeWindowMass m - integerDiscrepancyWindow smallResidueCorrection m ≤ (3/2)/(m:ℝ)^2 := by
  unfold primeWindowMass integerDiscrepancyWindow
  rw [← sum_sub_distrib]
  refine ⟨sum_nonneg (fun n hn => (fourth_discrepancy n (by have := (mem_Icc.mp hn).1; omega)).1),?_⟩
  calc
    _ ≤ ∑ n ∈ Icc m (m^2), (3/2)*(1/(n:ℝ)^3) := by
      apply sum_le_sum
      intro n hn
      have h1 : 1 ≤ n := by have := (mem_Icc.mp hn).1; omega
      simpa only [div_eq_mul_inv,one_mul] using (fourth_discrepancy n h1).2
    _ ≤ _ := by rw [← mul_sum,div_eq_mul_one_div (3/2)]; gcongr; exact primeWindow_inv_cube_le hm (Nat.le_self_pow (by decide) _)

/-- Dropping the small-denominator rational correction from the prime comparison
costs at most one harmonic sum on the complete window. -/
theorem raw_window_upper {m : ℕ} (hm : 2 ≤ m) :
    primeWindowMass m ≤ integerDiscrepancyWindow (fun _ => 0) m +
      (1+2*log m) + (3/2)/(m:ℝ)^2 := by
  have term (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      (max (integerPrimeDiscrepancy (n^2)+smallResidueCorrection (n^2)) 0 -
        max (integerPrimeDiscrepancy (n^2)+0) 0) / (n:ℝ)^3 ≤ (n:ℝ)⁻¹ := by
    have hpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    have hc := (smallResidueCorrection_bounds (n^2)).2
    rw [Nat.cast_pow] at hc
    have ht := max_sub_max_le_max (integerPrimeDiscrepancy (n^2)+smallResidueCorrection (n^2))
      0 (integerPrimeDiscrepancy (n^2)+0) 0
    apply (div_le_iff₀ (pow_pos hpos 3)).mpr
    rw [show (n:ℝ)⁻¹*(n:ℝ)^3 = (n:ℝ)^2 by field_simp]
    apply ht.trans
    exact max_le (by linarith) (by linarith only [sq_nonneg (n:ℝ)])
  have hh := primeWindow_harmonic_le (b := m^2) (by omega : 1 ≤ m)
  rw [Nat.cast_pow,log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hdiff : integerDiscrepancyWindow smallResidueCorrection m -
        integerDiscrepancyWindow (fun _ => 0) m ≤ 1+2*log m := by
    unfold integerDiscrepancyWindow
    rw [← sum_sub_distrib]
    simpa only [sub_div] using (sum_le_sum term).trans hh
  linarith only [hdiff,(corrected_window_error hm).2]

/-- The raw comparison underestimates the positive prime deficit at every sample of the window. -/
theorem raw_window_le {m : ℕ} (hm : 1 ≤ m) :
    integerDiscrepancyWindow (fun _ => 0) m ≤ primeWindowMass m := by
  apply sum_le_sum
  intro n hn
  have he := (raw_fourth_error (hm.trans (mem_Icc.mp hn).1)).1
  simp only [add_zero, fourthDeficitMass]
  exact div_le_div_of_nonneg_right (max_le_max (by linarith only [he]) le_rfl) (by positivity)

/-- An upper bound for the positive weighted excess of integer density over primes
on cofinal windows suffices. The arithmetic hypothesis uses only d strictly above n². -/
theorem rh_of_integerPrimeDiscrepancy
    (h : ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A,
      integerDiscrepancyWindow (fun _ => 0) m ≤ (m:ℝ)^ε) : RiemannHypothesis := by
  apply rh_of_primeWindowMass_le_log_sq (K := 3) (by norm_num) _ h
  intro m hm
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlog := log_nonneg hmR
  have hp : 0 < (m:ℝ)^2 := pow_pos (zero_lt_one.trans_le hmR) 2
  have hfrac : (3/2)/(m:ℝ)^2 ≤ 3/2 := (div_le_iff₀ hp).mpr
    (by nlinarith only [one_le_pow₀ hmR (n := 2)])
  nlinarith only [raw_window_upper (by omega : 2 ≤ m),hfrac,hlog,sq_nonneg (log m)]

/-- Positive excess in a single observation at each fourth power, after the
quadratic logarithmic allowance. Every denominator in the sum is above n². -/
def singlePrimeExcessOn (C : ℝ) (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (integerPrimeDiscrepancy (n^2)-C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3

/-- On the very same interval the single-observation statistic recovers the
positive prime mass with only a cubic logarithmic error. -/
theorem singlePrimeExcessOn_bounds {C : ℝ} (hC : 0 ≤ C) {m b : ℕ} (hm : 1 ≤ m) :
    singlePrimeExcessOn C m b ≤ primeMassOn m b ∧
      primeMassOn m b ≤ singlePrimeExcessOn C m b + (C+3)*(1+log b)^3 := by
  let D (n : ℕ) := eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4)
  have hcost := cubicAllowance_bounds D (C := C+3) (by linarith) (b := b) hm
  constructor
  · apply sum_le_sum
    intro n hn
    have he := (raw_fourth_error (hm.trans (mem_Icc.mp hn).1)).1
    unfold fourthDeficitMass
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply max_le_max_right
    linarith only [he,show 0 ≤ C*(n:ℝ)^2*(1+log n)^2 by positivity]
  · apply hcost.2.trans (add_le_add ?_ le_rfl)
    apply sum_le_sum
    intro n hn
    have hn1 := hm.trans (mem_Icc.mp hn).1
    have hn2 := one_le_pow₀ (Nat.one_le_cast.mpr hn1 : 1 ≤ (n:ℝ)) (n := 2)
    have he := (raw_fourth_error hn1).2
    have hlog := one_le_pow₀ (by linarith only [log_natCast_nonneg n] : (1:ℝ) ≤ 1+log n) (n := 2)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply max_le_max_right
    dsimp only [D]
    nlinarith only [he,hn2,mul_le_mul_of_nonneg_left hlog (sq_nonneg (n:ℝ))]

/-- One central residue sum per index suffices on arbitrarily late power windows.
The width may depend on the exponent and the allowance is fixed across all windows. -/
theorem rh_of_singlePrimeExcessOn_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, singlePrimeExcessOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_primeMassOn_powerWindows
  exact subpowerWindows_of_log_cube_error (show 0 ≤ C+3 by linarith)
    (fun {_ _} hm => (singlePrimeExcessOn_bounds hC (by omega : 1 ≤ _)).2) h


/-- The signed single-observation prime discrepancy represents G(n⁴) to square-root
accuracy before taking the positive part. -/
theorem singlePrime_central_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |AlpogeZetaSamples.G ((n:ℝ)^4)-integerPrimeDiscrepancy (n^2)| ≤ K*(n:ℝ)^2 := by
  obtain ⟨K,hK,h⟩ := large_prime_sample_bounds
  refine ⟨K+4,by positivity,fun n hn => ?_⟩
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn2 := one_le_pow₀ hnR (n := 2)
  have hr : 0 < (n:ℝ)^2 := by positivity [zero_lt_one.trans_le hnR]
  have hlog := log_le_sub_one_of_pos hr
  rw [log_pow,Nat.cast_ofNat] at hlog
  obtain ⟨hl,hu⟩ := h (n^4) (Nat.one_le_pow _ _ hn)
  have he := raw_fourth_error hn
  dsimp only at he
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at hu
  rw [Nat.cast_pow,show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _),
    show ((n:ℝ)^2)^2=(n:ℝ)^4 by ring] at hl
  apply abs_le.mpr
  constructor <;> nlinarith only [hl,hu,he.1,he.2,hn2,hlog,mul_nonneg hK (sq_nonneg (n:ℝ))]


/-- A zero with real part σ > 1/2 forces the single-observation excess above
m^α on every sufficiently late window of any fixed power width when α < 4σ−2. -/
theorem singlePrimeExcessOn_eventually_gt_of_zero {s : ℂ} (hz : riemannZeta s = 0)
    {α δ C : ℝ} (hC : 0 ≤ C) (hα : 0 < α) (hs : 1/2+α/4 < s.re)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ A : ℕ, ∀ m ≥ A, (m:ℝ)^α < singlePrimeExcessOn C m (powerWindowEnd δ m) := by
  have hr : s.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz
  obtain ⟨θ,hθ,hθs⟩ := exists_between hs
  by_contra! h
  let t := α/3
  have ht : 0 < t := by dsimp only [t]; positivity
  let K := 1+(C+3)*(1+2/t)^3
  apply zeta_ne_zero_of_primeMassOn_powerWindows (C := K) hα hθ (hθs.trans hr) hδ hδ₁ _ s hθs hz
  intro A
  obtain ⟨m,hm,hx⟩ := h (max 1 A)
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast hm1
  have hm0 := zero_lt_one.trans_le hmR
  let b := powerWindowEnd δ m
  obtain ⟨hmb,hb⟩ := powerWindowEnd_bounds hm1 hδ.le hδ₁
  have hlog := log_le_log (Nat.cast_pos.mpr (hm1.trans hmb : 0 < b))
    (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hb)
  rw [log_pow,Nat.cast_ofNat] at hlog
  have hl : 1+log b ≤ (1+2/t)*(m:ℝ)^t := by
    have h1 := Real.one_le_rpow hmR ht.le
    have h2 := Real.log_le_rpow_div hm0.le ht
    rw [show (1+2/t)*(m:ℝ)^t = (m:ℝ)^t+2*((m:ℝ)^t/t) by ring]
    linarith only [hlog,h1,h2]
  have hc := pow_le_pow_left₀ (by positivity [log_natCast_nonneg b] : 0 ≤ 1+log b) hl 3
  rw [mul_pow,← Real.rpow_mul_natCast hm0.le,
    show t*(3:ℕ)=α by dsimp [t]; norm_num] at hc
  have hmass := (singlePrimeExcessOn_bounds (b := b) hC hm1).2
  refine ⟨m,(le_max_right _ _).trans hm,?_⟩
  dsimp only [K]
  nlinarith only [hmass,hx,mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ C+3)]


end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.corrected_integerBand_bounds,
      ``RiemannGaussian.AlpogeMined.corrected_discrepancy_error,
      ``RiemannGaussian.AlpogeMined.corrected_window_error,
      ``RiemannGaussian.AlpogeMined.raw_window_upper,
      ``RiemannGaussian.AlpogeMined.raw_window_le,
      ``RiemannGaussian.AlpogeMined.rh_of_singlePrimeExcessOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.singlePrimeExcessOn_eventually_gt_of_zero,
      ``RiemannGaussian.AlpogeMined.rh_of_integerPrimeDiscrepancy] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
