import AlpogeIntegerPrimeBand
import CheckAlpogeGlobalSamples

/-! # Global zeta-only criterion for the prime versus integer discrepancy -/

namespace RiemannGaussian.AlpogeMined

/-- A one-sided bound on the ordinary-prime versus integer discrepancy at every
fourth power, with a separate constant for each exponent above one half, implies RH. -/
theorem rh_of_global_integerPrimeDiscrepancy
    (h : ∀ B : ℝ, 1/2 < B → B < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      integerPrimeDiscrepancy (n^2) ≤ C*((n:ℝ)^4)^B) : RiemannHypothesis := by
  apply rh_of_global_prime_deficit_exponents
  intro B hB hB1
  obtain ⟨C,hC,hp⟩ := h B hB hB1
  refine ⟨C+3,by linarith,fun n hn => ?_⟩
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hsq : 1 ≤ (n:ℝ)^2 := one_le_pow₀ hn1
  have hpow := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hn1 (n := 4)) hB.le
  rw [← Real.sqrt_eq_rpow,show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _),show ((n:ℝ)^2)^2 = (n:ℝ)^4 by ring] at hpow
  nlinarith only [(raw_fourth_error hn).2,hp n hn,hsq,hpow]

end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for ax in ← Lean.collectAxioms ``RiemannGaussian.AlpogeMined.rh_of_global_integerPrimeDiscrepancy do
    unless [``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax}"
