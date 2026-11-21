import AlpogeQuadraticSamples
import CheckAlpogeGlobalSamples

/-! # A single quadratic class on the shorter global zeta route -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Real Finset

/-- At every cutoff the error in partitioning the primes is below any fixed power
strictly above the square root, with one constant for all cutoffs. -/
private theorem quadratic_error_le_power {B : ℝ} (hB : 1/2 < B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      6*(1+2*(n:ℝ)^2)*log ((n:ℝ)^4+2) ≤ D*((n:ℝ)^4)^B := by
  obtain ⟨L,hL,hpow⟩ := sqrt_log_sq_le_rpow hB
  refine ⟨36*L,by positivity,fun n hn => ?_⟩
  let x := (n:ℝ)^4
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hx : 1 ≤ x := one_le_pow₀ hn1
  have hx0 := zero_lt_one.trans_le hx
  have hroot : sqrt x = (n:ℝ)^2 := by
    dsimp [x]
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _)]
  have hl0 : 0 ≤ log x := log_nonneg hx
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have h2 : log 2 ≤ 1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hc : log x ≤ log x / log 2 := (le_div_iff₀ hl2).mpr (mul_le_of_le_one_right hl0 h2)
  have hl := log_le_log (by linarith : 0 < x+2) (show x+2 ≤ 3*x by linarith)
  rw [log_mul (by norm_num) hx0.ne'] at hl
  have ht : 0 ≤ log x/log 2 := div_nonneg hl0 hl2.le
  have hlog : log (x+2) ≤ 2*(1+log x/log 2)^2 := by
    nlinarith only [hl,hc,ht,sq_nonneg (log x/log 2),log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  calc _ ≤ (18*(n:ℝ)^2)*(2*(1+log x/log 2)^2) := mul_le_mul
           (by linarith only [one_le_pow₀ hn1 (n := 2)]) hlog (log_nonneg (by linarith : 1 ≤ x+2)) (by positivity)
       _ = 36*(sqrt x*(1+log x/log 2)^2) := by rw [hroot]; ring
       _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hpow x hx) (by norm_num : (0:ℝ) ≤ 36)

/-- It suffices to furnish, at each fourth power, a lower estimate for the
positive-negative class of a pair satisfying the explicit discrepancy bound. -/
theorem rh_of_quadratic_global_samples
    (h : ∀ B : ℝ, 1/2 < B → B < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ q d : ℕ, |4*quadraticClassSum q d n-largePrimeSum (n^4)| ≤
        6*(1+2*(n:ℝ)^2)*log ((n:ℝ)^4+2) ∧
        eulerMascheroniConstant*(n:ℝ)^4-4*quadraticClassSum q d n ≤ C*((n:ℝ)^4)^B) :
    RiemannHypothesis := by
  apply rh_of_global_prime_deficit_exponents
  intro B hB hB1
  obtain ⟨C,hC,hc⟩ := h B hB hB1
  obtain ⟨D,hD,hd⟩ := quadratic_error_le_power hB
  refine ⟨C+D+1,by linarith,fun n hn => ?_⟩
  by_cases hn2 : 2 ≤ n
  · obtain ⟨q,d,he,hr⟩ := hc n hn2
    have hu := (le_abs_self _).trans (he.trans (hd n hn))
    have hp : 0 ≤ ((n:ℝ)^4)^B := Real.rpow_nonneg (by positivity) _
    linarith only [hu,hr,hp]
  · have h1 : n = 1 := by omega
    subst n
    have hz : largePrimeSum 1 = 0 := by
      unfold largePrimeSum
      apply sum_eq_zero
      intro p hp
      have hp1 := (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
      have hprime := (mem_filter.mp (mem_filter.mp hp).1).2
      have := hprime.two_le
      omega
    norm_num [hz]
    linarith only [eulerMascheroniConstant_lt_two_thirds,hC,hD]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeMined.rh_of_quadratic_global_samples
  let axioms ← Lean.collectAxioms decl
  for ax in axioms do
    unless [``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axioms}"
