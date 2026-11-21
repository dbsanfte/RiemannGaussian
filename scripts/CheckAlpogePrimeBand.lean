import CheckAlpogeResidueAverage
import CheckAlpogeGlobalSamples
import RiemannGaussian.PrimeMassFromZeroBound

/-! # Removing the reciprocal prime band through the four-sevenths power -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Real AlpogeZetaSamples PrimeMassFromZeroBound

/-- The upper endpoint of the prime band replaced by its mean at the fourth-power sample. -/
def bandEnd (n : ℕ) : ℝ := ((n:ℝ)^4)^(4/7:ℝ)

/-- The remaining prime sum after averaging the cutoffs on a symmetric block. -/
def meanPrimeTail (n : ℕ) : ℝ :=
  blockMean (n^4-n^3) (2*n^3+1) (fun M => upperPrimeSum M ⌊bandEnd n⌋₊)

private theorem band_bounds {n : ℕ} (hn : 2 ≤ n) :
    4 ≤ bandEnd n ∧ ⌊bandEnd n⌋₊ ≤ n^4-n^3 ∧ ((⌊bandEnd n⌋₊:ℕ):ℝ)^2 ≤ (n:ℝ)^5 := by
  have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hR : 1 ≤ (n:ℝ) := by linarith
  have hx : bandEnd n = (n:ℝ)^(16/7:ℝ) := by
    unfold bandEnd
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
    norm_num
  have hfloor := Nat.floor_le (show 0 ≤ bandEnd n by rw [hx]; positivity)
  have hlow := Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (2:ℝ) ≤ 16/7)
  have hhigh := Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (16/7:ℝ) ≤ 3)
  have hs := Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (16/7:ℝ) ≤ 5/2)
  rw [← hx,Real.rpow_two] at hlow
  rw [← hx,Real.rpow_ofNat] at hhigh
  rw [← hx] at hs
  have hN : ⌊bandEnd n⌋₊ ≤ n^3 := by exact_mod_cast hfloor.trans hhigh
  have h23 : 2*n^3 ≤ n^4 := by
    calc _ ≤ n*n^3 := Nat.mul_le_mul_right _ hn
         _ = _ := by ring
  refine ⟨by nlinarith [sq_nonneg ((n:ℝ)-2)],by omega,?_⟩
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) ⌊bandEnd n⌋₊) (hfloor.trans hs) 2
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),show (5/2:ℝ)*(2:ℕ)=5 by norm_num,Real.rpow_ofNat] at hh
  exact hh

/-- Unconditionally, all primes up to N to the four-sevenths power can be replaced by
half that cutoff in a one-sided estimate for the central sample. -/
theorem G_fourth_le_centered_tail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      G ((n:ℝ)^4) ≤ Real.eulerMascheroniConstant*(n:ℝ)^4-bandEnd n/2-meanPrimeTail n+
        C*(n:ℝ)^2*(1+log ((n:ℝ)^4)/log 2)^2 := by
  obtain ⟨C,hC,hmass⟩ := theta_four_sevenths
  refine ⟨8+log 4+C,by positivity,fun n hn => ?_⟩
  obtain ⟨hx,hD,hs⟩ := band_bounds hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn4 := one_le_pow₀ hn1 (n := 4)
  have hl := (abs_le.mp (hmass _ hn4 hx)).1
  change -(C*sqrt ((n:ℝ)^4)*(1+log ((n:ℝ)^4)/log 2)^2) ≤ Chebyshev.theta (bandEnd n)-bandEnd n at hl
  rw [Chebyshev.theta_eq_theta_coe_floor (bandEnd n),
    show sqrt ((n:ℝ)^4)=(n:ℝ)^2 by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]] at hl
  have hh := G_fourth_le_mean_upper_primes hn hD hs
  have hlog : 1 ≤ (1+log ((n:ℝ)^4)/log 2)^2 := one_le_pow₀ (by
    linarith [div_nonneg (log_nonneg hn4) (log_pos (by norm_num : (1:ℝ)<2)).le])
  have hc : 0 ≤ (8+log 4)*(n:ℝ)^2 := by positivity
  change G _ ≤ _-_-meanPrimeTail n+_ at hh
  nlinarith only [hh,hl,mul_le_mul_of_nonneg_left hlog hc,
    mul_nonneg (mul_nonneg hC (sq_nonneg (n:ℝ))) (sq_nonneg (1+log ((n:ℝ)^4)/log 2))]

/-- The remaining one-sided arithmetic condition involves only averaged ordinary primes
strictly above N to the four-sevenths power. Its conclusion is Mathlib's RH. -/
theorem rh_of_mean_prime_tail
    (h : ∀ B : ℝ, 1/2 < B → B < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      Real.eulerMascheroniConstant*(n:ℝ)^4-bandEnd n/2-meanPrimeTail n ≤ C*((n:ℝ)^4)^B) :
    RiemannHypothesis := by
  obtain ⟨K,hK,hg⟩ := G_fourth_le_centered_tail
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  intro s hs
  obtain ⟨B,hB,hlt⟩ := exists_between (lt_min hs (by norm_num : (1/2:ℝ)<1))
  have hB1 := hlt.trans_le (min_le_right _ _)
  obtain ⟨C,hC,h⟩ := h B hB hB1
  obtain ⟨L,hL,hl⟩ := sqrt_log_sq_le_rpow hB
  apply zeta_ne_zero_of_fourth_G_upper (m := 2) (by decide) hB.le hB1 (C := C+K*L) (by positivity) _ s (hlt.trans_le (min_le_left _ _))
  intro n hn
  have hR : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hR4 := one_le_pow₀ hR (n := 4)
  have hroot : sqrt ((n:ℝ)^4)=(n:ℝ)^2 := by
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hcost := hl _ hR4
  rw [hroot] at hcost
  linarith only [h n hn,hg n hn,mul_le_mul_of_nonneg_left hcost hK]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.PrimeMassFromZeroBound.psi_error,
      ``RiemannGaussian.PrimeMassFromZeroBound.theta_four_sevenths,
      ``RiemannGaussian.AlpogeMined.mean_low_prime_lower,
      ``RiemannGaussian.AlpogeMined.G_fourth_le_mean_upper_primes,
      ``RiemannGaussian.AlpogeMined.G_fourth_le_centered_tail,
      ``RiemannGaussian.AlpogeMined.rh_of_mean_prime_tail] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
