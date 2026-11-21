import CheckAlpogePrimeWindowMass
import CheckAlpogeRepeatedWeights

/-! # The positive large-prime tail on one power window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Real Filter AlpogeZetaSamples

/-- The positive averaged cubic-tail deficit on a closed interval of indices. -/
def cubicMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc m b, max (repeatedTailAt (Nat.log 2 n+1) n (n^3)) 0 / (n:ℝ)^3

/-- Weighted positive tail after averaging away the primes through n cubed. -/
def cubicWindowMass (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc m (m^2),
    max (repeatedTailAt (Nat.log 2 n+1) n (n^3)) 0 / (n:ℝ)^3

/-- Removing the primes through the cubic cutoff from the total positive deficit
costs at most a constant times the square of the logarithm of the window index. -/
theorem primeMassOn_le_cubicMassOn :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m b : ℕ}, 8 ≤ m → m ≤ b → b ≤ m^2 →
      primeMassOn m b ≤ cubicMassOn m b + K*(1+log m)^2 := by
  obtain ⟨C,hC,h⟩ := large_prime_sample_bounds
  let L := C+10+log 4+4/log 2
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨2*L,by positivity,fun {m b} hm hmb hbm => ?_⟩
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlm := log_nonneg hm1
  let A := L*(1+log m)
  have hA : 0 ≤ A := mul_nonneg hL (by linarith)
  have atIndex (n : ℕ) (hn : n ∈ Finset.Icc m b) :
      fourthDeficitMass n ≤ max (repeatedTailAt (Nat.log 2 n+1) n (n^3)) 0 / (n:ℝ)^3 + A*(n:ℝ)⁻¹ := by
    obtain ⟨hn1,hnb⟩ := Finset.mem_Icc.mp hn
    have hn8 := hm.trans hn1
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hu := (h (n^4) (Nat.one_le_pow _ _ (by omega))).1
    push_cast at hu
    have hs : sqrt ((n:ℝ)^4) = (n:ℝ)^2 := by
      rw [show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
    rw [hs] at hu
    have hg := G_fourth_le_cubic_tail n hn8
    have hj := Real.natLog_le_logb n 2
    rw [← Real.log_div_log] at hj
    have hl := log_le_log hnpos (show (n:ℝ) ≤ m^2 by exact_mod_cast hnb.trans hbm)
    rw [log_pow] at hl
    have hjm := hj.trans (div_le_div_of_nonneg_right hl hl2.le)
    change ((Nat.log 2 n:ℕ):ℝ) ≤ 2*log m / log 2 at hjm
    rw [div_eq_mul_inv] at hjm
    have hcoef : C+2*((Nat.log 2 n:ℕ):ℝ)+10+log 4 ≤ A := by
      have hpos : 0 ≤ (C+10+log 4)*log m := mul_nonneg (by positivity) hlm
      dsimp [L,A]
      rw [div_eq_mul_inv]
      nlinarith only [hjm,hpos,inv_nonneg.mpr hl2.le]
    let d := repeatedTailAt (Nat.log 2 n+1) n (n^3)
    have htop : max (eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4)) 0 ≤
        max d 0 + A*(n:ℝ)^2 := by
      apply max_le
      · nlinarith only [hu,hg,le_max_left d 0,mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n:ℝ))]
      · exact add_nonneg (le_max_right _ _) (mul_nonneg hA (sq_nonneg _))
    calc fourthDeficitMass n ≤ (max d 0 + A*(n:ℝ)^2)/(n:ℝ)^3 :=
          div_le_div_of_nonneg_right htop (by positivity)
         _ = _ := by dsimp only [d]; field_simp
  have hlogb := log_le_log (show 0 < (b:ℝ) by exact_mod_cast (show 0 < b by omega))
    (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hbm)
  rw [log_pow, Nat.cast_ofNat] at hlogb
  have hinv : ∑ n ∈ Finset.Icc m b, (n:ℝ)⁻¹ ≤ 1+2*log m :=
    (primeWindow_harmonic_le (by omega : 1 ≤ m)).trans (by linarith only [hlogb])
  calc primeMassOn m b ≤ _ := by unfold primeMassOn; exact Finset.sum_le_sum atIndex
       _ = cubicMassOn m b + A*(∑ n ∈ Finset.Icc m b, (n:ℝ)⁻¹) := by
         rw [Finset.sum_add_distrib,← Finset.mul_sum]; rfl
       _ ≤ cubicMassOn m b + A*(1+2*log m) := add_le_add_right (mul_le_mul_of_nonneg_left hinv hA) _
       _ ≤ _ := by dsimp [A]; nlinarith only [mul_nonneg hL (show 0 ≤ 1+log m by linarith)]

theorem primeWindowMass_le_cubicWindowMass :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 8 ≤ m →
      primeWindowMass m ≤ cubicWindowMass m + K*(1+log m)^2 := by
  obtain ⟨K,hK,h⟩ := primeMassOn_le_cubicMassOn
  exact ⟨K,hK,fun m hm => h hm (Nat.le_self_pow (by decide) m) le_rfl⟩

/-- The cubic-tail replacement retains the quantitative exponent of the
positive-mass criterion. -/
theorem zeta_ne_zero_of_cubicMassOn_powerWindows {α θ δ : ℝ}
    (hα : 0 < α) (hθ : 1/2+α/4 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, cubicMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨K,hK,ht⟩ := primeMassOn_le_cubicMassOn
  let C := 1+K*(1+1/(α/2))^2
  apply zeta_ne_zero_of_primeMassOn_powerWindows (C := C) hα hθ hθ1 hδ hδ1
  intro A
  obtain ⟨m,hm,hb⟩ := h (max 8 A)
  have hm8 := (le_max_left _ _).trans hm
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 := zero_lt_one.trans_le hmR
  obtain ⟨hmb,hbm⟩ := powerWindowEnd_bounds (by omega : 1 ≤ m) hδ.le hδ1
  have hlog := log_le_rpow_div hm0.le (half_pos hα)
  have hone := one_le_rpow hmR (half_pos hα).le
  have hterm : 1+log m ≤ (1+1/(α/2))*(m:ℝ)^(α/2) := by
    rw [add_mul, one_mul, one_div_mul_eq_div]
    linarith only [hlog, hone]
  have hsquare := pow_le_pow_left₀ (by linarith [log_nonneg hmR] : 0 ≤ 1+log m) hterm 2
  rw [mul_pow, ← rpow_mul_natCast hm0.le, show α/2*(2:ℕ) = α by norm_num] at hsquare
  refine ⟨m,(le_max_right _ _).trans hm,?_⟩
  calc
    _ ≤ cubicMassOn m (powerWindowEnd δ m) + K*(1+log m)^2 := ht hm8 hmb hbm
    _ ≤ (m:ℝ)^α + K*((1+1/(α/2))^2*(m:ℝ)^α) :=
      add_le_add hb (mul_le_mul_of_nonneg_left hsquare hK)
    _ = _ := by dsimp [C]; ring

/-- A zero with real part greater than one half plus α/4 forces mass
larger than m^α in every sufficiently late window of the chosen length. -/
theorem cubicMassOn_eventually_gt_of_zero {s : ℂ} (hz : riemannZeta s = 0) {α δ : ℝ}
    (hα : 0 < α) (hs : 1/2+α/4 < s.re) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, ∀ m ≥ A, (m:ℝ)^α < cubicMassOn m (powerWindowEnd δ m) := by
  have h1 : s.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz
  by_contra! h
  obtain ⟨θ,hθ,ht⟩ := exists_between hs
  exact zeta_ne_zero_of_cubicMassOn_powerWindows hα hθ (ht.trans h1) hδ hδ1 h s ht hz

/-- For each positive growth exponent, a fixed window length may be chosen
as short as the arithmetic estimate allows. Bounds at arbitrarily late
windows of that length suffice. -/
theorem rh_of_cubicMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _ hz
  let α := s.re-(1/2:ℝ)
  have hα : 0 < α := by dsimp [α]; linarith
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  obtain ⟨A,hA⟩ := cubicMassOn_eventually_gt_of_zero hz hα (by dsimp [α]; linarith) hδ hδ1
  obtain ⟨m,hm,hb⟩ := hw A
  exact (not_lt_of_ge hb) (hA m hm)

/-- On cofinal windows only the aggregate positive large-prime tail needs subpower growth.
Any height or location of individual observations is allowed within this total. -/
theorem rh_of_cubicWindowMass
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m ≥ N, cubicWindowMass m ≤ (m:ℝ)^ε) :
    RiemannHypothesis := by
  obtain ⟨K,hK,hcost⟩ := primeWindowMass_le_cubicWindowMass
  exact rh_of_primeWindowMass_le_log_sq hK hcost h

/-- Failure of RH forces the positive cubic tail above a fixed power on every late window. -/
theorem cubicWindowMass_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ A : ℕ, ∀ m ≥ A, (m:ℝ)^ε < cubicWindowMass m := by
  by_contra! h
  exact hRH (rh_of_cubicWindowMass h)

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.primeWindowMass_le_cubicWindowMass,
      ``RiemannGaussian.AlpogeMined.cubicMassOn_eventually_gt_of_zero,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicWindowMass,
      ``RiemannGaussian.AlpogeMined.cubicWindowMass_of_not_rh] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
