import CheckAlpogePrimeWindowMass

/-! # Diagonal and distinct-index terms in the prime discrepancy -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real

private def primeAtom (N d : ℕ) : ℝ :=
  if d.Prime ∧ sqrt N < d then log d * weight N d else 0

/-- One summand of the centered ordinary-prime statistic at cutoff N. -/
def centeredPrimeAtom (N d : ℕ) : ℝ := eulerMascheroniConstant - primeAtom N d

/-- Total ordered product over distinct indices up to the cutoff. -/
def distinctPrimeCorrelation (N : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 N, ∑ e ∈ (Ioc 0 N).erase d, centeredPrimeAtom N d * centeredPrimeAtom N e

/-- The signed distinct-index contribution across fourth powers in a power window. -/
def primeCorrelationWindow (m : ℕ) : ℝ :=
  ∑ n ∈ Icc m (m^2), distinctPrimeCorrelation (n^4) / (n:ℝ)^5

private theorem atom_sum (N : ℕ) : ∑ d ∈ Ioc 0 N, primeAtom N d = largePrimeSum N := by
  classical
  simp only [largePrimeSum,filter_filter,Finset.sum_filter,primeAtom]

private theorem centered_sum (N : ℕ) :
    ∑ d ∈ Ioc 0 N, centeredPrimeAtom N d = eulerMascheroniConstant*N-largePrimeSum N := by
  simp [centeredPrimeAtom,sum_sub_distrib,atom_sum,mul_comm]

/-- The complete off-diagonal is signed in the exact square expansion. -/
theorem prime_deficit_square (N : ℕ) :
    (eulerMascheroniConstant*N-largePrimeSum N)^2 =
      (∑ d ∈ Ioc 0 N, centeredPrimeAtom N d ^ 2) + distinctPrimeCorrelation N := by
  classical
  rw [← centered_sum,pow_two,sum_mul,distinctPrimeCorrelation,← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [mul_sum,← sum_erase_add (Ioc 0 N) (fun e => centeredPrimeAtom N d * centeredPrimeAtom N e) hd,
    pow_two,add_comm]

/-- The diagonal has the unconditional N log N bound at every positive cutoff. -/
theorem prime_diagonal_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, centeredPrimeAtom N d ^ 2 ≤
      (eulerMascheroniConstant^2 + (log 4+4)*log N)*N := by
  have hL := log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)
  have hγ : 0 ≤ eulerMascheroniConstant := by linarith [one_half_lt_eulerMascheroniConstant]
  have atom_bounds {d : ℕ} (hd : d ∈ Ioc 0 N) : 0 ≤ primeAtom N d ∧
      primeAtom N d ≤ (if d.Prime then log d else 0) ∧ primeAtom N d ≤ log N := by
    have hd0 := (mem_Ioc.mp hd).1
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
    have hp := log_nonneg hd1
    have hlog := log_le_log (zero_lt_one.trans_le hd1) (show (d:ℝ) ≤ N by exact_mod_cast (mem_Ioc.mp hd).2)
    by_cases h : d.Prime ∧ sqrt N < d
    · rw [primeAtom,ite_eq_left h,ite_eq_left h.1]
      have hweight := weight_mem (N := N) hd0
      have hupper := mul_le_of_le_one_right hp hweight.2
      exact ⟨mul_nonneg hp hweight.1,hupper,hupper.trans hlog⟩
    · rw [primeAtom,ite_eq_right h]
      exact ⟨le_rfl,by split <;> positivity,hL⟩
  have hmass : ∑ d ∈ Ioc 0 N, primeAtom N d ≤ (log 4+4)*N := by
    calc _ ≤ ∑ d ∈ Ioc 0 N, if d.Prime then log d else 0 := sum_le_sum fun d hd => (atom_bounds hd).2.1
         _ = Chebyshev.theta N := by simp only [Chebyshev.theta,Nat.floor_natCast,Finset.sum_filter]
         _ ≤ _ := (Chebyshev.theta_le_psi _).trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N))
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, (eulerMascheroniConstant^2 + log N * primeAtom N d) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨ha,_,hb⟩ := atom_bounds hd
      unfold centeredPrimeAtom
      nlinarith only [mul_nonneg hγ ha,mul_le_mul_of_nonneg_right hb ha]
    _ ≤ _ := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
      nlinarith only [mul_le_mul_of_nonneg_left hmass hL]

/-- After summing across the window, only the signed correlations between distinct
indices can exceed a squared logarithm in this upper bound for the positive deficit. -/
theorem primeWindowMass_le_correlation :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 8 ≤ m →
      primeWindowMass m ≤ primeCorrelationWindow m + K*(1+log m)^2 := by
  let C := 1 + eulerMascheroniConstant^2 + 8*(log 4+4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨2*C,by positivity,fun m hm => ?_⟩
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlm := log_nonneg hm1
  let A := C*(1+log m)
  have hA : 0 ≤ A := mul_nonneg hC (by linarith)
  have atIndex (n : ℕ) (hn : n ∈ Icc m (m^2)) : fourthDeficitMass n ≤
      distinctPrimeCorrelation (n^4)/(n:ℝ)^5 + A*(n:ℝ)⁻¹ := by
    obtain ⟨ha,hb⟩ := mem_Icc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hD := prime_diagonal_le (n^4) (Nat.one_le_pow _ _ hn1)
    have hs := prime_deficit_square (n^4)
    push_cast at hD hs
    rw [log_pow] at hD
    have hl := log_le_log hn0 (show (n:ℝ) ≤ m^2 by exact_mod_cast hb)
    rw [log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hD hl
    have hcoef : 1+eulerMascheroniConstant^2+(log 4+4)*(4*log n) ≤ A := by
      dsimp [A,C]
      nlinarith only [mul_le_mul_of_nonneg_left hl (show 0 ≤ log 4+4 by positivity),
        mul_nonneg (show 0 ≤ 1+eulerMascheroniConstant^2 by positivity) hlm,
        show 0 ≤ log 4+4 by positivity]
    let D := eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4)
    have ht : max D 0*(n:ℝ)^2 ≤ D^2+(n:ℝ)^4 := by
      rcases le_total D 0 with h | h
      · rw [max_eq_right h,zero_mul]; positivity
      · rw [max_eq_left h]
        nlinarith only [sq_nonneg (D-(n:ℝ)^2),sq_nonneg D,sq_nonneg ((n:ℝ)^2)]
    change D^2 = _ at hs
    calc fourthDeficitMass n = (max D 0*(n:ℝ)^2)/(n:ℝ)^5 := by
          change max D 0/(n:ℝ)^3 = _; field_simp
         _ ≤ (distinctPrimeCorrelation (n^4) + A*(n:ℝ)^4)/(n:ℝ)^5 := by
           apply div_le_div_of_nonneg_right _ (by positivity)
           nlinarith only [ht,hs,hD,mul_le_mul_of_nonneg_right hcoef (pow_nonneg hn0.le 4)]
         _ = _ := by field_simp
  have hinv := primeWindow_harmonic_le (b := m^2) (by omega : 1 ≤ m)
  rw [Nat.cast_pow,log_pow] at hinv
  calc
    _ ≤ _ := sum_le_sum atIndex
    _ = primeCorrelationWindow m + A*(∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹) := by
      rw [sum_add_distrib,← mul_sum]; rfl
    _ ≤ primeCorrelationWindow m + A*(1+2*log m) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hinv hA) _
    _ ≤ _ := by dsimp [A]; nlinarith only [mul_nonneg hC (show 0 ≤ 1+log m by linarith)]

/-- Subpower upper bounds on a single signed sum of distinct-index products force RH. -/
theorem rh_of_primeCorrelationWindow
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m ≥ N, primeCorrelationWindow m ≤ (m:ℝ)^ε) :
    RiemannHypothesis := by
  obtain ⟨K,hK,hcost⟩ := primeWindowMass_le_correlation
  exact rh_of_primeWindowMass_le_log_sq hK hcost h

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.prime_diagonal_le,
      ``RiemannGaussian.AlpogeMined.primeWindowMass_le_correlation,
      ``RiemannGaussian.AlpogeMined.rh_of_primeCorrelationWindow] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
