import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.LogFactorialEqSumLog

namespace PI.PrimeLogOverPWork

open Finset

theorem u3 : Real.log (3 : ℝ) ≤ 32 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 3 32 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u5 : Real.log (5 : ℝ) ≤ 47 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 5 47 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u7 : Real.log (7 : ℝ) ≤ 57 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 7 57 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u11 : Real.log (11 : ℝ) ≤ 70 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 11 70 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u13 : Real.log (13 : ℝ) ≤ 75 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 13 75 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u17 : Real.log (17 : ℝ) ≤ 82 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 17 82 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u19 : Real.log (19 : ℝ) ≤ 85 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 19 85 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u23 : Real.log (23 : ℝ) ≤ 91 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 23 91 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u29 : Real.log (29 : ℝ) ≤ 98 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 29 98 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u31 : Real.log (31 : ℝ) ≤ 100 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 31 100 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u37 : Real.log (37 : ℝ) ≤ 105 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 37 105 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u41 : Real.log (41 : ℝ) ≤ 108 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 41 108 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u43 : Real.log (43 : ℝ) ≤ 109 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 43 109 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u47 : Real.log (47 : ℝ) ≤ 112 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 47 112 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u53 : Real.log (53 : ℝ) ≤ 115 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 53 115 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u59 : Real.log (59 : ℝ) ≤ 118 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 59 118 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem u61 : Real.log (61 : ℝ) ≤ 119 / 20 * Real.log 2 := by
  have h := log_le_of_pow_le 61 119 20 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem l3 : (31 : ℝ) / 20 * Real.log 2 ≤ Real.log (3 : ℝ) := by
  have h := le_log_of_pow_le 3 31 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem l5 : (46 : ℝ) / 20 * Real.log 2 ≤ Real.log (5 : ℝ) := by
  have h := le_log_of_pow_le 5 46 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem l11 : (69 : ℝ) / 20 * Real.log 2 ≤ Real.log (11 : ℝ) := by
  have h := le_log_of_pow_le 11 69 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith

theorem l31 : (99 : ℝ) / 20 * Real.log 2 ≤ Real.log (31 : ℝ) := by
  have h := le_log_of_pow_le 31 99 20 (by norm_num) (by norm_num)
  push_cast at h
  linarith

private theorem S_zero' : S 0 = 0 := by
  simp [S]

private theorem S_succ_eq_add_ite_prime (n : ℕ) :
    S (n + 1) = S n +
      if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) else 0 := by
  simp only [S, Finset.sum_filter]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

theorem S_1 : S 1 = 0 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']

theorem S_2 : S 2 = Real.log 2 / 2 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']

theorem S_4 : S 4 = Real.log 2 / 2 + Real.log 3 / 3 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']

theorem S_10 : S 10 = Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 + Real.log 7 / 7 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']

theorem S_30 : S 30 = Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 + Real.log 7 / 7 + Real.log 11 / 11 + Real.log 13 / 13 + Real.log 17 / 17 + Real.log 19 / 19 + Real.log 23 / 23 + Real.log 29 / 29 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']

set_option maxHeartbeats 800000 in

theorem S_63 : S 63 = Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 + Real.log 7 / 7 + Real.log 11 / 11 + Real.log 13 / 13 + Real.log 17 / 17 + Real.log 19 / 19 + Real.log 23 / 23 + Real.log 29 / 29 + Real.log 31 / 31 + Real.log 37 / 37 + Real.log 41 / 41 + Real.log 43 / 43 + Real.log 47 / 47 + Real.log 53 / 53 + Real.log 59 / 59 + Real.log 61 / 61 := by
  norm_num [S_succ_eq_add_ite_prime, S_zero']

theorem S_le_1_1 : S 1 ≤ Real.log (1 : ℝ) := by
  rw [S_1, Real.log_one]

theorem S_le_2_2 : S 2 ≤ Real.log (2 : ℝ) := by
  rw [S_2]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

theorem S_le_3_4 : S 4 ≤ Real.log (3 : ℝ) := by
  rw [S_4]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l3
  linarith

theorem S_le_5_10 : S 10 ≤ Real.log (5 : ℝ) := by
  rw [S_10]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l5
  have hb0 := u3
  have hb1 := u7
  linarith

theorem S_le_11_30 : S 30 ≤ Real.log (11 : ℝ) := by
  rw [S_30]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l11
  have hb0 := u3
  have hb1 := u5
  have hb2 := u7
  have hb3 := u13
  have hb4 := u17
  have hb5 := u19
  have hb6 := u23
  have hb7 := u29
  linarith

theorem S_le_31_63 : S 63 ≤ Real.log (31 : ℝ) := by
  rw [S_63]
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := l31
  have hb0 := u3
  have hb1 := u5
  have hb2 := u7
  have hb3 := u11
  have hb4 := u13
  have hb5 := u17
  have hb6 := u19
  have hb7 := u23
  have hb8 := u29
  have hb9 := u37
  have hb10 := u41
  have hb11 := u43
  have hb12 := u47
  have hb13 := u53
  have hb14 := u59
  have hb15 := u61
  linarith

theorem S_le_of_block {a b n : ℕ} (ha : 0 < a) (h : S b ≤ Real.log (a : ℝ)) (h1 : a ≤ n)
    (h2 : n ≤ b) : S n ≤ Real.log (n : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h1' : (a : ℝ) ≤ n := by exact_mod_cast h1
  calc S n ≤ S b := S_mono h2
    _ ≤ Real.log (a : ℝ) := h
    _ ≤ Real.log (n : ℝ) := Real.log_le_log ha' h1'

theorem S_le_small (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 63) : S n ≤ Real.log (n : ℝ) := by
  by_cases hA : n ≤ 1
  · exact S_le_of_block (a := 1) (b := 1) (by norm_num)
      (by exact_mod_cast S_le_1_1) h1 hA
  by_cases hB : n ≤ 2
  · exact S_le_of_block (a := 2) (b := 2) (by norm_num)
      (by exact_mod_cast S_le_2_2) (by omega) hB
  by_cases hC : n ≤ 4
  · exact S_le_of_block (a := 3) (b := 4) (by norm_num)
      (by exact_mod_cast S_le_3_4) (by omega) hC
  by_cases hD : n ≤ 10
  · exact S_le_of_block (a := 5) (b := 10) (by norm_num)
      (by exact_mod_cast S_le_5_10) (by omega) hD
  by_cases hE : n ≤ 30
  · exact S_le_of_block (a := 11) (b := 30) (by norm_num)
      (by exact_mod_cast S_le_11_30) (by omega) hE
  exact S_le_of_block (a := 31) (b := 63) (by norm_num)
    (by exact_mod_cast S_le_31_63) (by omega) h2

end PI.PrimeLogOverPWork
