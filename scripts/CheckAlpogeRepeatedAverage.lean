import CheckAlpogeRepeatedWeights
import CheckAlpogeGlobalSamples

/-! # Global zeta consequences of repeated averaging -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real AlpogeZetaSamples

/-- For any fixed averaging order, a uniform square-root arithmetic deficit on the
remaining ordinary primes closes the zeta contradiction. -/
theorem rh_of_repeatedDeficit {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 2 ≤ n → 2*k ≤ n → repeatedDeficit k n ≤ C*(n:ℝ)^2) : RiemannHypothesis := by
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  apply zeta_ne_zero_of_fourth_G_upper (m := max 2 (2*k)) (by omega) (B := 1/2) le_rfl (by norm_num)
    (C := C+(2*(k:ℝ)+8+log 4)) (by positivity)
  intro n hn
  have hn2 := (le_max_left 2 (2*k)).trans hn
  have hnk := (le_max_right 2 (2*k)).trans hn
  rw [← Real.sqrt_eq_rpow,show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hg := G_fourth_le_repeated_deficit k n hn2 hnk
  rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring] at hg
  linarith only [hg,h n hn2 hnk]

/-- At any exponent strictly above one half, a uniform arithmetic bound on all
sufficiently late cubic-cutoff samples gives the same zero-free half-plane. -/
theorem zeta_ne_zero_of_cubic_prime_tail {B C : ℝ} {m : ℕ} (hm : 8 ≤ m)
    (hB : 1/2 < B) (hB1 : B < 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, m ≤ n → repeatedTailAt (Nat.log 2 n+1) n (n^3) ≤ C*((n:ℝ)^4)^B) :
    ∀ s : ℂ, B < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨K,hK,hlog⟩ := sqrt_log_sq_le_rpow hB
  let L := 10+log 4
  have hL : 2 ≤ L := by dsimp [L]; linarith [log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  apply zeta_ne_zero_of_fourth_G_upper (m := m) (by omega) hB.le hB1 (C := C+L*K)
    (by positivity [show 0 ≤ L by linarith])
  intro n hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  let x := (n:ℝ)^4
  let t := log x/log 2
  have hx : 1 ≤ x := one_le_pow₀ hn1
  have h2 := log_pos (by norm_num : (1:ℝ) < 2)
  have ht : 0 ≤ t := div_nonneg (log_nonneg hx) h2.le
  have hl := Real.natLog_le_logb n 2
  rw [← Real.log_div_log] at hl
  have hnx : (n:ℝ) ≤ x := by dsimp [x]; simpa using pow_le_pow_right₀ hn1 (by decide : 1 ≤ 4)
  have hj : ((Nat.log 2 n:ℕ):ℝ) ≤ t := hl.trans (div_le_div_of_nonneg_right
    (log_le_log (zero_lt_one.trans_le hn1) hnx) h2.le)
  have he : 2*((Nat.log 2 n:ℕ):ℝ)+10+log 4 ≤ L*(1+t)^2 := by
    have hh := mul_le_mul_of_nonneg_right hL ht
    have hlt' := mul_le_mul_of_nonneg_left (show 1+t ≤ (1+t)^2 by nlinarith only [sq_nonneg t,ht])
      (show 0 ≤ L by linarith)
    dsimp only [L] at hh hlt' ⊢
    linarith only [hh,hj,hlt']
  have hroot : sqrt x=(n:ℝ)^2 := by
    dsimp only [x]
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hcost := hlog x hx
  rw [hroot] at hcost
  change (n:ℝ)^2*(1+t)^2 ≤ K*x^B at hcost
  have ht' := h n hn
  have hg := G_fourth_le_cubic_tail n (hm.trans hn)
  change G x ≤ (C+L*K)*x^B
  change repeatedTailAt _ n _ ≤ C*x^B at ht'
  change G x ≤ _+_ at hg
  nlinarith only [hg,ht',mul_le_mul_of_nonneg_right he (sq_nonneg (n:ℝ)),
    mul_le_mul_of_nonneg_left hcost (show 0 ≤ L by linarith)]

/-- A zero to the right of B forces arbitrarily late violations of any proposed
order-B upper bound on this specific remaining prime sum. -/
theorem cubic_tail_excursions_of_zero {s : ℂ} (hz : riemannZeta s=0) {B C : ℝ}
    (hB : 1/2 < B) (hB1 : B < 1) (hs : B < s.re) (hC : 0 ≤ C) (A : ℕ) :
    ∃ n ≥ max 8 A, C*((n:ℝ)^4)^B < repeatedTailAt (Nat.log 2 n+1) n (n^3) := by
  by_contra! h
  exact zeta_ne_zero_of_cubic_prime_tail (le_max_left 8 A) hB hB1 hC h s hs hz

/-- Bounds with every exponent above one half suffice on the single remaining
averaged prime tail above N to the three-quarters power. -/
theorem rh_of_cubic_prime_tail
    (h : ∀ B : ℝ, 1/2 < B → B < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n →
      repeatedTailAt (Nat.log 2 n+1) n (n^3) ≤ C*((n:ℝ)^4)^B) : RiemannHypothesis := by
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  intro s hs
  obtain ⟨B,hB,hlt⟩ := exists_between (lt_min hs (by norm_num : (1/2:ℝ)<1))
  have hB1 := hlt.trans_le (min_le_right _ _)
  obtain ⟨C,hC,h⟩ := h B hB hB1
  exact zeta_ne_zero_of_cubic_prime_tail (m := 8) le_rfl hB hB1 hC h s (hlt.trans_le (min_le_left _ _))

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.repeated_weight_error,
      ``RiemannGaussian.AlpogeMined.G_fourth_le_repeated_deficit,
      ``RiemannGaussian.AlpogeMined.G_fourth_le_cubic_tail,
      ``RiemannGaussian.AlpogeMined.cubic_tail_excursions_of_zero,
      ``RiemannGaussian.AlpogeMined.rh_of_cubic_prime_tail] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
