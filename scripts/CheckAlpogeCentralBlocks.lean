import CheckAlpogeCentralWindow
import CheckAlpogeZetaWindows

/-! # Arithmetic excess on blocks of negative fourth-power observations -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real Filter

/-- Every sufficiently late power window contains a block of additive length
floor(M^β) for any fixed β < 1 on which both arithmetic excesses vanish exactly.
One allowance works for every block and every choice of the exponents. -/
theorem zero_excess_blocks_in_power_windows :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {β δ : ℝ}, 0 ≤ β → β < 1 → 0 < δ →
      ∀ᶠ Y : ℝ in atTop, ∃ M : ℕ,
        let b := M+⌊(M:ℝ)^β⌋₊
        Y ≤ (M:ℝ)^4 ∧ (b:ℝ)^4 ≤ Y^(1+δ) ∧
          singlePrimeExcessOn C M b = 0 ∧ cubicMangoldtExcessOn C M b = 0 := by
  obtain ⟨K,hK,hc⟩ := cubicMangoldtTail_central_error
  obtain ⟨B,hB,hp⟩ := singlePrime_central_error
  refine ⟨K+B,by positivity,fun {β δ} hβ hβ₁ hδ => ?_⟩
  filter_upwards [AlpogeWindow.negative_polynomial_fourth_blocks hβ hβ₁ hδ,
    eventually_ge_atTop ((8:ℝ)^4)] with Y hY hY8
  obtain ⟨M,hw⟩ := hY
  let b := M+⌊(M:ℝ)^β⌋₊
  have hMb : M ≤ b := Nat.le_add_right _ _
  obtain ⟨hleft,_⟩ := hw M (mem_Icc.mpr ⟨le_rfl,hMb⟩)
  obtain ⟨hright,_⟩ := hw b (mem_Icc.mpr ⟨hMb,le_rfl⟩)
  have hm8 : 8 ≤ M := by
    by_contra! hlt
    have h := pow_lt_pow_left₀ (Nat.cast_lt.mpr hlt : (M:ℝ) < (8:ℕ)) (Nat.cast_nonneg M)
      (by decide : 4 ≠ 0)
    exact (not_lt_of_ge (hY8.trans hleft.1)) (by exact_mod_cast h)
  refine ⟨M,hleft.1,hright.2,?_⟩
  have point (n : ℕ) (hn : n ∈ Icc M b) :
      integerPrimeDiscrepancy (n^2) ≤ (K+B)*(n:ℝ)^2*(1+log n)^2 ∧
      cubicMangoldtTail n ≤ (K+B)*(n:ℝ)^2*(1+log n)^2 := by
    have hn8 := hm8.trans (mem_Icc.mp hn).1
    have hg := (hw n hn).2
    rw [AlpogeWindow.G_native] at hg
    have h1 := (abs_le.mp (hp n (by omega))).1
    have h2 := (abs_le.mp (hc n hn8)).2
    have hl := one_le_pow₀ (by linarith only [log_natCast_nonneg n] : 1 ≤ 1+log n) (n := 2)
    constructor <;> nlinarith only [h1,h2,hg,
      mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ B*(n:ℝ)^2),
      mul_nonneg (mul_nonneg hK (sq_nonneg (n:ℝ))) (sq_nonneg (1+log n)),
      mul_nonneg (mul_nonneg hB (sq_nonneg (n:ℝ))) (sq_nonneg (1+log n))]
  constructor
  · exact sum_eq_zero fun n hn => by rw [max_eq_right (sub_nonpos.mpr (point n hn).1),zero_div]
  · exact sum_eq_zero fun n hn => by rw [max_eq_right (sub_nonpos.mpr (point n hn).2),zero_div]

/-- A zero block of additive length floor(M^β) has at most this much harmonic
index weight. For fixed β < 1 the upper bound tends to zero. -/
theorem additive_block_harmonic_le {M : ℕ} (hM : 1 ≤ M) {β : ℝ} (hβ : 0 ≤ β) :
    ∑ n ∈ Icc M (M+⌊(M:ℝ)^β⌋₊), (n:ℝ)⁻¹ ≤ 2*(M:ℝ)^(β-1) := by
  have hm : 1 ≤ (M:ℝ) := by exact_mod_cast hM
  have hp := zero_lt_one.trans_le hm
  let L := ⌊(M:ℝ)^β⌋₊
  calc
    _ ≤ ∑ _n ∈ Icc M (M+L), (M:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      exact inv_anti₀ hp (Nat.cast_le.mpr (mem_Icc.mp hn).1)
    _ = ((L:ℝ)+1)/(M:ℝ) := by
      simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,show M+L+1-M=L+1 by omega,
        Nat.cast_add_one,div_eq_mul_inv]
    _ ≤ (2*(M:ℝ)^β)/M := div_le_div_of_nonneg_right
      (by linarith only [Nat.floor_le (Real.rpow_nonneg hp.le β),Real.one_le_rpow hm hβ]) hp.le
    _ = _ := by rw [Real.rpow_sub hp,Real.rpow_one]; ring

/-- The harmonic index weight of an entire power window is at least δ log m. -/
theorem power_window_harmonic_lower {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    δ*log m ≤ ∑ n ∈ Icc m (powerWindowEnd δ m), (n:ℝ)⁻¹ := by
  let b := powerWindowEnd δ m
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hp := zero_lt_one.trans_le hmR
  have hmb : m ≤ b := by
    have hr : (m:ℝ) ≤ (m:ℝ)^(1+δ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR
        (show (1:ℝ) ≤ 1+δ by linarith)
    exact_mod_cast hr.trans (Nat.le_ceil ((m:ℝ)^(1+δ)))
  have hlog := log_le_log (Real.rpow_pos_of_pos hp (1+δ)) (Nat.le_ceil ((m:ℝ)^(1+δ)))
  rw [Real.log_rpow hp] at hlog
  change (1+δ)*log m ≤ log b at hlog
  have htel : (∑ n ∈ Icc m b, (log ((n+1:ℕ):ℝ)-log n)) = log ((b+1:ℕ):ℝ)-log m := by
    rw [← Ico_succ_right_eq_Icc]
    change (∑ n ∈ Ico m (b+1), (log ((n+1:ℕ):ℝ)-log n)) = _
    rw [sum_Ico_eq_sub _ (by omega),
      sum_range_sub (fun n : ℕ => log (n:ℝ)),sum_range_sub (fun n : ℕ => log (n:ℝ))]
    ring
  calc
    δ*log m ≤ log ((b+1:ℕ):ℝ)-log m := by
      have h := log_le_log (by exact_mod_cast (show 0 < b by omega) : (0:ℝ) < b)
        (Nat.cast_le.mpr (Nat.le_succ b))
      linarith only [hlog,h]
    _ = _ := htel.symm
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (hm.trans (mem_Icc.mp hn).1)
      rw [Nat.cast_add_one,← log_div (by positivity) hn0.ne']
      apply (log_le_sub_one_of_pos (by positivity)).trans_eq
      field_simp
      ring


end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for name in [``RiemannGaussian.AlpogeMined.zero_excess_blocks_in_power_windows,
      ``RiemannGaussian.AlpogeMined.additive_block_harmonic_le,
      ``RiemannGaussian.AlpogeMined.power_window_harmonic_lower] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
