import CheckAlpogeZetaWindows
import CheckAlpogeIntegerBaseline

/-! # Large ordinary primes at the fourth-power samples of the analytic criterion -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Filter Set AlpogeWindow

private theorem fourth_sqrt (n : ℕ) : Real.sqrt (((n^4:ℕ):ℝ)) = (n:ℝ)^2 := by
  push_cast
  rw [show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]

/-- Each global upper bound for G gives a lower bound of the same order for the
positive prime sum at every integer, including the samples inside the power windows. -/
theorem large_prime_deficit_of_G_upper {B : ℝ} (hB : 1/2 ≤ B)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → Deduction.G x ≤ C*x^B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      Real.eulerMascheroniConstant*N - largePrimeSum N ≤ D*(N:ℝ)^B := by
  obtain ⟨C,hC,h⟩ := h
  obtain ⟨K,hK,hb⟩ := large_prime_sample_bounds
  refine ⟨C+K,add_nonneg hC hK,fun N hN => ?_⟩
  have hR : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hh := h N hR
  rw [G_native] at hh
  have hr := Real.rpow_le_rpow_of_exponent_le hR hB
  rw [← Real.sqrt_eq_rpow] at hr
  linarith only [(hb N hN).1,hh,mul_le_mul_of_nonneg_left hr hK]

/-- The full prime deficit has an unconditional seven-eighths bound at every integer. -/
theorem large_prime_deficit_seven_eighths :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      Real.eulerMascheroniConstant*N - largePrimeSum N ≤ D*(N:ℝ)^(7/8:ℝ) :=
  large_prime_deficit_of_G_upper (by norm_num) G_le_seven_eighths

/-- On each arbitrarily late power window it suffices to bound only the prime deficit on
its bracketing fourth-power samples, allowing any exponent strictly above one half. -/
theorem rh_of_large_prime_windows
    (h : ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧
      ∀ A : ℝ, ∃ Y ≥ A, ∀ n ∈ Finset.Icc ⌊Y^(1/4:ℝ)⌋₊ (⌊(Y^(1+δ))^(1/4:ℝ)⌋₊+1),
        Real.eulerMascheroniConstant*(n:ℝ)^4 - largePrimeSum (n^4) ≤ C*((n:ℝ)^4)^θ) :
    RiemannHypothesis := by
  obtain ⟨_,_,hb⟩ := large_prime_sample_bounds
  apply rh_of_fourth_power_G_windows
  intro θ ht hθ
  obtain ⟨δ,C,hd,hC⟩ := h θ ht hθ
  refine ⟨δ,C+1,hd,fun A => ?_⟩
  obtain ⟨Y,hy,hp⟩ := hC (max 1 A)
  have hY : 1 ≤ Y := (le_max_left _ _).trans hy
  refine ⟨Y,(le_max_right _ _).trans hy,fun n hn => ?_⟩
  have hfloor : 1 ≤ ⌊Y^(1/4:ℝ)⌋₊ := Nat.le_floor (by simpa using Real.one_le_rpow hY (by norm_num : 0 ≤ (1/4:ℝ)))
  have hn1 := hfloor.trans (Finset.mem_Icc.mp hn).1
  have hN : 1 ≤ n^4 := Nat.one_le_pow _ _ hn1
  have hR : 1 ≤ ((n^4:ℕ):ℝ) := by exact_mod_cast hN
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (zero_lt_one.trans_le hR))
  rw [Real.log_sqrt (zero_le_one.trans hR)] at hlog
  have hr : Real.sqrt ((n^4:ℕ):ℝ) ≤ (((n^4:ℕ):ℝ))^θ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hR ht.le
  have hu := (hb (n^4) hN).2
  rw [G_native]
  push_cast at hu hlog hr
  linarith only [hu,hlog,hr,hp n hn]

/-- RH is equivalent to a single uniform square-root deficit bound for positive weights on
ordinary primes in the bands from n squared to n to the fourth power. -/
theorem rh_iff_large_prime_fourth :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      Real.eulerMascheroniConstant*(n:ℝ)^4 - largePrimeSum (n^4) ≤ C*(n:ℝ)^2 := by
  constructor
  · intro hRH
    obtain ⟨C,hC,h⟩ := G_le_of_zero_halfplane (B := 1/2) (by norm_num) (by norm_num)
      (fun ρ => (hRH ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
    obtain ⟨K,hK,hb⟩ := large_prime_sample_bounds
    refine ⟨C+K,add_nonneg hC hK,fun n hn => ?_⟩
    have hN : 1 ≤ n^4 := Nat.one_le_pow _ _ hn
    have hh := h ((n^4:ℕ):ℝ) (by exact_mod_cast hN)
    rw [G_native,← Real.sqrt_eq_rpow, fourth_sqrt] at hh
    have hl := (hb (n^4) hN).1
    rw [fourth_sqrt] at hl
    push_cast at hh hl
    linarith only [hh,hl]
  · rintro ⟨C,hC,h⟩
    apply rh_of_large_prime_windows
    intro θ ht _
    refine ⟨1,C,by norm_num,fun A => ⟨max 1 A,le_max_right _ _,fun n hn => ?_⟩⟩
    have hfloor : 1 ≤ ⌊(max 1 A)^(1/4:ℝ)⌋₊ := Nat.le_floor (by
      simpa using Real.one_le_rpow (le_max_left 1 A) (by norm_num : 0 ≤ (1/4:ℝ)))
    have hn1 := hfloor.trans (Finset.mem_Icc.mp hn).1
    have hR : 1 ≤ ((n^4:ℕ):ℝ) := by exact_mod_cast Nat.one_le_pow 4 n hn1
    have hr := Real.rpow_le_rpow_of_exponent_le hR ht.le
    rw [← Real.sqrt_eq_rpow, fourth_sqrt] at hr
    push_cast at hr
    exact (h n hn1).trans (mul_le_mul_of_nonneg_left hr hC)

/-- RH gives logarithmic positive mass on every fourth-power window. -/
theorem primeWindowMass_of_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → primeWindowMass m ≤ C*(1+2*Real.log m) := by
  obtain ⟨C,hC,h⟩ := rh_iff_large_prime_fourth.mp hRH
  exact ⟨C,hC,fun _ hm => primeWindowMass_of_square_root hC h hm⟩

/-- The cofinal positive-mass condition is also necessary. -/
theorem rh_iff_primeWindowMass :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A, primeWindowMass m ≤ (m:ℝ)^ε := by
  refine ⟨fun hRH ε hε A => ?_,rh_of_primeWindowMass⟩
  obtain ⟨C,hC,h⟩ := primeWindowMass_of_rh hRH
  have hlog := ((isLittleO_log_rpow_atTop hε).const_mul_left (3*C)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlog.and (Real.tendsto_log_atTop.eventually_ge_atTop 1))
  let m := max (max 1 A) ⌈L⌉₊
  have hm1 : 1 ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨hc,hl⟩ := hL m (Nat.ceil_le.mp (le_max_right _ _))
  change ‖3*C*Real.log m‖ ≤ 1*‖(m:ℝ)^ε‖ at hc
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity [show 0 ≤ Real.log m by linarith] :
    0 ≤ 3*C*Real.log m),abs_of_pos (Real.rpow_pos_of_pos hmpos _),one_mul] at hc
  refine ⟨m,(le_max_right _ _).trans (le_max_left _ _),(h _ hm1).trans ?_⟩
  nlinarith only [hc,mul_le_mul_of_nonneg_left hl hC]

/-- RH is equivalent to the cofinal positive-mass bound for the discrepancy of
log-weighted primes against ordinary integers on the same band of denominators. -/
theorem rh_iff_integerPrimeDiscrepancy :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A,
      integerDiscrepancyWindow (fun _ => 0) m ≤ (m:ℝ)^ε := by
  refine ⟨fun hRH ε hε A => ?_,rh_of_integerPrimeDiscrepancy⟩
  obtain ⟨m,hm,hb⟩ := rh_iff_primeWindowMass.mp hRH ε hε (max 1 A)
  exact ⟨m,(le_max_right _ _).trans hm,(raw_window_le ((le_max_left _ _).trans hm)).trans hb⟩

/-- The required square-root deficit already holds at every integer of long negative
subintervals, with one constant for all their locations and all subinterval exponents. -/
theorem eventually_good_prime_subintervals :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α δ : ℝ, 0 ≤ α → α < 1 → 0 < δ →
      ∀ᶠ Y : ℝ in atTop, ∃ a : ℝ, Y ≤ a ∧ a+a^α ≤ Y^(1+δ) ∧
        ∀ N : ℕ, (N:ℝ) ∈ Icc a (a+a^α) →
          Real.eulerMascheroniConstant*N - largePrimeSum N ≤ K*Real.sqrt N := by
  obtain ⟨K,hK,h⟩ := large_prime_sample_bounds
  refine ⟨K,hK,fun α δ hα hα' hd => ?_⟩
  filter_upwards [eventually_negative_subintervals hα hα' hd,eventually_ge_atTop (1:ℝ)]
    with Y hh hY
  obtain ⟨a,ha,hb,hs⟩ := hh
  refine ⟨a,ha,hb,fun N hN => ?_⟩
  have hn : (1:ℝ) ≤ N := (hY.trans ha).trans hN.1
  have hl := (h N (by exact_mod_cast hn)).1
  have hz := hs N hN
  rw [G_native] at hz
  linarith

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.large_prime_deficit_of_G_upper,
      ``RiemannGaussian.AlpogeMined.large_prime_deficit_seven_eighths,
      ``RiemannGaussian.AlpogeMined.rh_of_large_prime_windows,
      ``RiemannGaussian.AlpogeMined.rh_iff_large_prime_fourth,
      ``RiemannGaussian.AlpogeMined.rh_iff_primeWindowMass,
      ``RiemannGaussian.AlpogeMined.rh_iff_integerPrimeDiscrepancy,
      ``RiemannGaussian.AlpogeMined.eventually_good_prime_subintervals] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
