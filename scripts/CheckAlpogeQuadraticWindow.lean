import AlpogeQuadraticSamples
import CheckAlpogePrimeWindowMass

/-! # Quadratic class mass on cofinal zeta windows -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real

/-- Difference between four times the mass of the chosen class and the full mass,
summed in absolute value with the weights of the zeta criterion. -/
def quadraticWindowError (q d m : ℕ) : ℝ :=
  ∑ n ∈ Icc m (m^2), |4*quadraticClassSum q d n - largePrimeSum (n^4)|/(n:ℝ)^3

/-- Positive deficit of a single quadratic class on the fourth-power window. -/
def quadraticWindowDeficit (q d m : ℕ) : ℝ :=
  ∑ n ∈ Icc m (m^2), max (eulerMascheroniConstant*(n:ℝ)^4-4*quadraticClassSum q d n) 0 / (n:ℝ)^3

/-- The pointwise comparison costs at most a squared logarithm after summation on
the complete window. The constant is independent of the window and of the chosen class. -/
theorem exists_quadraticWindowPair :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 2 ≤ m → ∃ q d : ℕ, quadraticWindowPair m q d ∧
      quadraticWindowError q d m ≤ K*(1+log m)^2 := by
  refine ⟨324,by norm_num,fun m hm => ?_⟩
  obtain ⟨q,d,hpair,hpoint⟩ := exists_quadraticWindowPair_pointwise m hm
  refine ⟨q,d,hpair,?_⟩
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlm := log_nonneg hmR
  let B := 162*(1+log m)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (n : ℕ) (hn : n ∈ Icc m (m^2)) :
      |4*quadraticClassSum q d n-largePrimeSum (n^4)|/(n:ℝ)^3 ≤ B*(n:ℝ)⁻¹ := by
    have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hm.trans (mem_Icc.mp hn).1
    have hn0 : 0 < (n:ℝ) := by linarith
    have hn1 : 1 ≤ (n:ℝ) := by linarith
    have hl := log_le_log hn0 (show (n:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast (mem_Icc.mp hn).2)
    rw [log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hb2 : log ((n:ℝ)^4+2) ≤ log (3*(n:ℝ)^4) := log_le_log (by positivity)
      (by linarith only [one_le_pow₀ hn1 (n := 4)])
    rw [log_mul (by norm_num) (pow_pos hn0 4).ne',log_pow] at hb2
    norm_num only [Nat.cast_ofNat] at hb2
    have hb : log ((n:ℝ)^4+2) ≤ 9*(1+log m) := by
      linarith only [hb2,hl,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3),hlm]
    apply (div_le_iff₀ (pow_pos hn0 3)).mpr
    rw [show B*(n:ℝ)⁻¹*(n:ℝ)^3=B*(n:ℝ)^2 by field_simp]
    apply (hpoint n hn 1 (-1) (Or.inl rfl) (Or.inr rfl)).trans
    dsimp [B]
    calc _ ≤ (18*(n:ℝ)^2)*(9*(1+log m)) := mul_le_mul
           (by linarith only [one_le_pow₀ hn1 (n := 2)]) hb (log_nonneg (by linarith only [one_le_pow₀ hn1 (n := 4)])) (by positivity)
         _ = _ := by ring
  have hh := primeWindow_harmonic_le (b := m^2) (by omega : 1 ≤ m)
  rw [Nat.cast_pow,log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  calc quadraticWindowError q d m ≤ ∑ n ∈ Icc m (m^2), B*(n:ℝ)⁻¹ := sum_le_sum hterm
       _ ≤ B*(1+2*log m) := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hh hB
       _ ≤ _ := by dsimp [B]; nlinarith only [hlm]

/-- Absolute window error controls the change in positive deficit for either sign. -/
theorem quadraticWindowDeficit_compare (q d m : ℕ) :
    |primeWindowMass m-quadraticWindowDeficit q d m| ≤ quadraticWindowError q d m := by
  unfold primeWindowMass quadraticWindowDeficit quadraticWindowError
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  unfold fourthDeficitMass
  rw [← sub_div,abs_div,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^3)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  let a := eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4)
  let b := eulerMascheroniConstant*(n:ℝ)^4-4*quadraticClassSum q d n
  have hv : a-b = 4*quadraticClassSum q d n-largePrimeSum (n^4) := by dsimp [a,b]; ring
  rw [← hv]
  change |max a 0-max b 0| ≤ |a-b|
  have h : max b 0-max a 0 ≤ |a-b| := (max_sub_max_le_max b 0 a 0).trans
    (max_le (by linarith only [neg_abs_le (a-b)]) (by linarith only [abs_nonneg (a-b)]))
  exact abs_le.mpr ⟨by linarith only [h],(max_sub_max_le_max a 0 b 0).trans
    (max_le (le_abs_self _) (by linarith only [abs_nonneg (a-b)]))⟩

/-- For any single choice of balanced primes per window, a cofinal bound for the
one quadratic class implies the standard Mathlib Riemann hypothesis. -/
theorem rh_of_quadraticWindowDeficit (q d : ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ m : ℕ, 8 ≤ m → quadraticWindowError (q m) (d m) m ≤ K*(1+log m)^2)
    (h : ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ m ≥ A, quadraticWindowDeficit (q m) (d m) m ≤ (m:ℝ)^ε) :
    RiemannHypothesis := by
  apply rh_of_primeWindowMass_le_log_sq hK _ h
  intro m hm
  linarith only [(abs_le.mp (quadraticWindowDeficit_compare (q m) (d m) m)).2,he m hm]


end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.QuadraticPatterns.prime_pattern,
      ``RiemannGaussian.QuadraticPrefix.prefix_four_classes,
      ``RiemannGaussian.QuadraticPrefix.reciprocal_weight_bound,
      ``RiemannGaussian.AlpogeMined.exists_quadraticWindowPair_pointwise,
      ``RiemannGaussian.AlpogeMined.exists_quadraticWindowPair,
      ``RiemannGaussian.AlpogeMined.quadraticWindowDeficit_compare,
      ``RiemannGaussian.AlpogeMined.rh_of_quadraticWindowDeficit] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
