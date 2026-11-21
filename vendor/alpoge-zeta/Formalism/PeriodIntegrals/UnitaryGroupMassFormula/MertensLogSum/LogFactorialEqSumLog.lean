import Mathlib

namespace PI.PrimeLogOverPWork

open Finset ArithmeticFunction Nat

noncomputable def S (n : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 n with p.Prime, Real.log (p : ℝ) / (p : ℝ)

theorem S_mono {m n : ℕ} (h : m ≤ n) : S m ≤ S n := by
  unfold S
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans h⟩, hx.2⟩
  · intro x hx _
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast hx.1.1

theorem log_factorial_eq_sum_log (n : ℕ) :
    Real.log (n ! : ℝ) = ∑ k ∈ Ioc 0 n, Real.log (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    push_cast; ring

theorem log_factorial_eq (n : ℕ) :
    Real.log (n ! : ℝ) = ∑ d ∈ Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have h1 : ∀ k ∈ Ioc 0 n, Real.log (k : ℝ) = ∑ d ∈ k.divisors, Λ d :=
    fun k _ => vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h1,
    Finset.sum_comm' (t' := Ioc 0 n) (s' := fun d => (Ioc 0 n).filter (fun k => d ∣ k))]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro k d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk0, hkn⟩, hdk, -⟩
      exact ⟨⟨⟨hk0, hkn⟩, hdk⟩, Nat.pos_of_dvd_of_pos hdk hk0, (Nat.le_of_dvd hk0 hdk).trans hkn⟩
    · rintro ⟨⟨⟨hk0, hkn⟩, hdk⟩, -⟩
      exact ⟨⟨hk0, hkn⟩, hdk, hk0.ne'⟩

theorem log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n ! : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hanti : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hlog := Real.log_le_log (Stirling.stirlingSeq'_pos k) hanti
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num), Real.log_div hpos.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num) hpos.ne'] at hlog
  push_cast at hlog ⊢
  linarith

theorem div_sub_one_le (n d : ℕ) : (n : ℝ) / d - 1 ≤ ((n / d : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [sub_le_iff_le_add, div_le_iff₀ hd']
    have h1 : (n : ℝ) = d * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n d).symm
    have h3 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
    nlinarith

theorem log_le_of_pow_le (p a b : ℕ) (hp : 0 < p) (hb : 0 < b) (h : p ^ b ≤ 2 ^ a) :
    Real.log (p : ℝ) ≤ (a : ℝ) / b * Real.log 2 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : (p : ℝ) ^ b ≤ (2 : ℝ) ^ a := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hb']
  linarith

theorem le_log_of_pow_le (p a b : ℕ) (hb : 0 < b) (h : 2 ^ a ≤ p ^ b) :
    (a : ℝ) / b * Real.log 2 ≤ Real.log (p : ℝ) := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [zero_pow hb.ne'] at h
      have := Nat.one_le_two_pow (n := a)
      omega
    · exact hp
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : (2 : ℝ) ^ a ≤ (p : ℝ) ^ b := by exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at h2
  rw [div_mul_eq_mul_div, div_le_iff₀ hb']
  linarith

end PI.PrimeLogOverPWork
