import CheckAlpogeMinedBounds
import Formalism.ZetaNonvanishing.ZetaLandau
import Formalism.ZetaNonvanishing.RHofHalfPlane

/-! # Uniform fourth-power prime bounds suffice through the zeta Mellin transform alone -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open AlpogeZetaSamples Real

/-- A fixed power above one half absorbs the squared logarithmic loss at all x at least one. -/
theorem sqrt_log_sq_le_rpow {B : ℝ} (hB : 1/2 < B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ, 1 ≤ x → sqrt x*(1+log x/log 2)^2 ≤ L*x^B := by
  let t := (B-1/2)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hl : 0 < log 2 := log_pos (by norm_num)
  let K := 1+1/(t*log 2)
  refine ⟨K^2,sq_nonneg _,fun x hx => ?_⟩
  have hx0 := zero_lt_one.trans_le hx
  have hr := Real.one_le_rpow hx ht.le
  have hlog := Real.log_le_rpow_div hx0.le ht
  have hscale : 1+log x/log 2 ≤ K*x^t := by
    dsimp [K]
    have hh := div_le_div_of_nonneg_right hlog hl.le
    convert add_le_add hr hh using 1
    ring
  have h1 : 0 ≤ 1+log x/log 2 := by positivity [log_nonneg hx]
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 hscale 2) (sqrt_nonneg x)
  apply hh.trans_eq
  rw [mul_pow,← Real.rpow_mul_natCast hx0.le, Real.sqrt_eq_rpow]
  rw [show x^(1/2:ℝ)*(K^2*x^(t*(2:ℕ)))=K^2*(x^(1/2:ℝ)*x^(t*(2:ℕ))) by ring,
    ← Real.rpow_add hx0,show (1/2:ℝ)+t*(2:ℕ)=B by dsimp [t]; ring]

/-- A one-sided bound on every fourth power past a fixed positive index excludes zeros
strictly to the right of its exponent. -/
theorem zeta_ne_zero_of_fourth_G_upper {B C : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hB : 1/2 ≤ B) (hB1 : B < 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, m ≤ n → G ((n:ℝ)^4) ≤ C*((n:ℝ)^4)^B) :
    ∀ s : ℂ, B < s.re → riemannZeta s ≠ 0 := by
  have h1 : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hA := one_le_pow₀ h1 (n := 4)
  have hroot : ((m:ℝ)^4)^(1/4:ℝ) = m := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg m)]
    norm_num
  apply Formalism.zetaLandau 1 (Or.inl rfl) B (by linarith) hB1
  refine ⟨16*C+225/4,(m:ℝ)^4,fun x hx => ?_⟩
  rw [one_mul,← G_eq_archive (zero_le_one.trans (hA.trans hx))]
  apply G_le_on_interval_of_fourth_samples (T := x) hA hC hB hB1.le _ ⟨hx,le_rfl⟩
  intro n hn
  exact h n (by simpa only [hroot,Nat.floor_natCast] using (Finset.mem_Icc.mp hn).1)

/-- A one-sided bound on the large-prime deficit at the fourth powers excludes zeta
zeros strictly to the right of its exponent. -/
theorem zeta_ne_zero_of_prime_deficit {B C : ℝ} (hB : 1/2 ≤ B) (hB1 : B < 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n →
      Real.eulerMascheroniConstant*(n:ℝ)^4 - largePrimeSum (n^4) ≤ C*((n:ℝ)^4)^B) :
    ∀ s : ℂ, B < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨_,_,hb⟩ := large_prime_sample_bounds
  apply zeta_ne_zero_of_fourth_G_upper (m := 1) le_rfl hB hB1 (C := C+1) (by linarith)
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ n^4 := Nat.one_le_pow _ _ hn1
  have hR : 1 ≤ ((n^4:ℕ):ℝ) := by exact_mod_cast hN
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (zero_lt_one.trans_le hR))
  rw [Real.log_sqrt (zero_le_one.trans hR)] at hl
  have hr := Real.rpow_le_rpow_of_exponent_le hR hB
  rw [← Real.sqrt_eq_rpow] at hr
  have hu := (hb (n^4) hN).2
  push_cast at hl hu hr
  linarith only [hu,hl,hr,h n hn1]

/-- A square-root deficit at every fourth-power cutoff suffices through the zeta Mellin
transform and the functional equation. -/
theorem rh_of_global_large_prime_fourth {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n →
      Real.eulerMascheroniConstant*(n:ℝ)^4 - largePrimeSum (n^4) ≤ C*(n:ℝ)^2) :
    RiemannHypothesis := by
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  apply zeta_ne_zero_of_prime_deficit (B := 1/2) le_rfl (by norm_num) hC
  intro n hn
  have hs : Real.sqrt ((n:ℝ)^4) = (n:ℝ)^2 := by
    rw [show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]
  rw [← Real.sqrt_eq_rpow,hs]
  exact h n hn

/-- A different constant for every exponent above one half also suffices on all fourth powers. -/
theorem rh_of_global_prime_deficit_exponents
    (h : ∀ B : ℝ, 1/2 < B → B < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      Real.eulerMascheroniConstant*(n:ℝ)^4 - largePrimeSum (n^4) ≤ C*((n:ℝ)^4)^B) :
    RiemannHypothesis := by
  apply Formalism.riemannHypothesis_of_zero_free_halfPlane
  intro s hs
  obtain ⟨B,hl,hr⟩ := exists_between (lt_min hs (by norm_num : (1/2:ℝ) < 1))
  obtain ⟨C,hC,hp⟩ := h B hl (hr.trans_le (min_le_right _ _))
  exact zeta_ne_zero_of_prime_deficit hl.le (hr.trans_le (min_le_right _ _)) hC hp s
    (hr.trans_le (min_le_left _ _))

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for name in [``RiemannGaussian.AlpogeMined.zeta_ne_zero_of_prime_deficit,
      ``RiemannGaussian.AlpogeMined.rh_of_global_large_prime_fourth,
      ``RiemannGaussian.AlpogeMined.rh_of_global_prime_deficit_exponents] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"{name} depends on {axioms}"
