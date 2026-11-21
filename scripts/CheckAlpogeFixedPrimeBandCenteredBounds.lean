import CheckAlpogeFixedPrimeBandCorner
import CheckAlpogeFixedPrimeBandBounds
import CheckAlpogeFixedPrimeBandMoments

/-! # Size of the negative part of the square-root Möbius quadratic form -/

namespace RiemannGaussian.AlpogeMined
open Real Filter Finset

private theorem log_squareWindows_of_error (mass : ℕ → ℕ → ℝ)
    (herr : ∃ K : ℝ, 0 ≤ K ∧ ∀ {m b : ℕ}, 2 ≤ m → |fixedBandMass m b-mass m b| ≤ K*(1+log b)) :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, mass m (m^2) ≤ C*(1+2*log m) := by
  rw [rh_iff_fixedBandMass_log_squareWindows]
  obtain ⟨K,hK,he⟩ := herr
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+K,by positivity,fun A => ?_⟩ <;>
    obtain ⟨m,hm,hM⟩ := h (max 2 A)
  all_goals
    have he' := abs_le.mp (he (b := m^2) ((le_max_left _ _).trans hm))
    rw [show (((m^2:ℕ):ℝ))=(m:ℝ)^2 from Nat.cast_pow _ _,Real.log_pow,Nat.cast_ofNat] at he'
    exact ⟨m,(le_max_right _ _).trans hm,by linarith only [he'.1,he'.2,hM]⟩

/-- At a single fixed window width there is just one unknown constant. -/
theorem rh_iff_fixedBandQuadratic_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandQuadraticMass m (m^2) ≤ C*(1+2*log m) :=
  log_squareWindows_of_error _ fixedBandQuadraticMass_error

/-- Trimming the boundary preserves the same cofinal logarithmic criterion. -/
theorem rh_iff_fixedBandTrimmed_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandTrimmedMass m (m^2) ≤ C*(1+2*log m) :=
  log_squareWindows_of_error _ fixedBandTrimmedMass_error

/-- The least of the energy-corrected scores at each sample preserves both
directions of the logarithmic window test. -/
theorem rh_iff_fixedBandMin_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandMinMass m (m^2) ≤ C*(1+2*log m) :=
  log_squareWindows_of_error _ fixedBandMinMass_error

/-- The adaptive criterion can discard all multiples below the new cutoff. -/
theorem rh_iff_fixedBandLateMin_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandLateMinMass m (m^2) ≤ C*(1+2*log m) :=
  log_squareWindows_of_error _ fixedBandLateMinMass_error

/-- The single Möbius tail checks the same logarithmic window criterion. -/
theorem rh_iff_fixedBandCriticalTail_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandCriticalTailMass m (m^2) ≤ C*(1+2*log m) :=
  log_squareWindows_of_error _ fixedBandCriticalTailMass_error

/-- The cofinal test with exact rational masses and integer budgets is equivalent to RH. -/
theorem rh_iff_fixedBandRationalWindowBound :
    RiemannHypothesis ↔ fixedBandRationalWindowBound :=
  (log_squareWindows_of_error (fun m b => (fixedBandRationalMass m b:ℝ))
    fixedBandRationalMass_error).trans fixedBandRationalWindowBound_iff_log.symm

/-- A uniform lower bound linear in the number of Möbius inputs is equivalent
to RH. The matrix is evaluated on the specified arithmetic vector. -/
theorem rh_iff_fixedBandQuadratic_lower : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → -(C*(n:ℝ)^2) ≤ fixedBandQuadratic (n^4) (n^2) := by
  constructor
  · intro hr
    obtain ⟨C,hC,h⟩ := fixedBand_abs_of_zero_bound (B := 1/2) le_rfl
      (fun ρ => (hr ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
    obtain ⟨K,hK,he⟩ := fixedBand_prime_quadratic_error
    refine ⟨K+C,by positivity,fun n hn => ?_⟩
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hx : (4:ℝ) ≤ (n:ℝ)^4 := (by norm_num : (4:ℝ) ≤ 2^4).trans (pow_le_pow_left₀ (by norm_num) hn2 4)
    have hh := (abs_le.mp (h _ hx)).2
    rw [← Real.sqrt_eq_rpow,show Real.sqrt ((n:ℝ)^4)=(n:ℝ)^2 by
      rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]] at hh
    linarith only [hh,(abs_le.mp (he hn)).1]
  · rintro ⟨C,hC,h⟩
    apply rh_iff_fixedBandQuadratic_log_squareWindows.mpr
    refine ⟨C,hC,fun A => ?_⟩
    let m := max 2 A
    let b := m^2
    have hb : log b = 2*log m := by rw [show (b:ℝ)=(m:ℝ)^2 from Nat.cast_pow _ _,Real.log_pow,Nat.cast_ofNat]
    refine ⟨m,le_max_right _ _,?_⟩
    change fixedBandQuadraticMass m b ≤ _
    rw [← hb]
    have hi := harmonic_le_one_add_log b
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hi
    calc
      _ ≤ ∑ n ∈ Icc m b, C*(n:ℝ)⁻¹ := by
        apply sum_le_sum
        intro n hn
        have hn2 := (le_max_left 2 A).trans (mem_Icc.mp hn).1
        have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
        apply (div_le_div_of_nonneg_right (max_le (by linarith only [h n hn2]) (by positivity : 0 ≤ C*(n:ℝ)^2))
          (pow_nonneg hn₀.le 3)).trans
        exact le_of_eq (by field_simp)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
          (Icc_subset_Icc_left (by dsimp [m]; omega : 1 ≤ m))
          (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hi) hC

end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.rh_iff_fixedBandQuadratic_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandTrimmed_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandMin_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandLateMin_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandCriticalTail_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandRationalWindowBound,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandQuarter_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandQuadratic_lower] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  let imports := (← getEnv).header.moduleNames
  logInfo m!"The arithmetic equivalence module uses {imports.size + 1} Lean modules including this module."
